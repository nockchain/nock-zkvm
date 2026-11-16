/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/PinsP1.lean

 **Row lemmas of the canonical side gates (trace uniqueness, P1 fragment).**

 * §1 from `Satisfies` of a side RAP to the gate list at every row node.
 * §2 compute: E2 (`inv4` is `0` off its gate) and E3 (a compute column is `0` in a state outside `Act`).
 * §3 cell: E1 (`(1−w)·id = 0`, `w·a = 0`) and E2 (`(1 − w + w·kb)·inv = 0`), both sides.
 * §4 walk: `isL·qinv = 0`; the depth-certificate aux `y` makes the remainder form unique
 (`b5 = [60 − len ≥ 32]`); consecutive root rows have strictly increasing `ridx`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
import Nock.NockVMROM.Thm54.VclL.Chips.RowBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1

noncomputable section

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)

/-! ## 1. From `Satisfies` to the gate list at a row -/

section Sat
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (b : Basis (Fin 3) (ZMod p) K) (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p))

/-- **Compute side gates at a row node.** -/
theorem canonC_row (h : (canonC b Pb).Satisfies (sideCQ tr)) {x : ZMod p} (hx : x ∈ rowNodeSet Pb.nodes) :
    ∀ g ∈ canonCGates (F := ZMod p),
      g.eval (Reify.envOfTrace (sideCQ tr) Pb.orbit.ω x (fun _ => 0) (fun _ => 0)) = 0 :=
  ((expandChip_satisfies_iff_language canonCT b _ _ Pb.orbit _ _).mp h x hx).1

/-- **Cell side gates at a row node.** -/
theorem canonM_row (h : (canonM b Pb).Satisfies (sideMQ tr ax)) {x : ZMod p} (hx : x ∈ rowNodeSet Pb.nodesC) :
    ∀ g ∈ canonMGates (F := ZMod p),
      g.eval (Reify.envOfTrace (sideMQ tr ax) Pb.orbitC.ω x (fun _ => 0) (fun _ => 0)) = 0 :=
  ((expandChip_satisfies_iff_language canonMT b _ _ Pb.orbitC _ _).mp h x hx).1

/-- **Walk side gates at a row node.** -/
theorem canonW_row (h : (canonW b Pb).Satisfies (sideWQ tr ax)) {x : ZMod p} (hx : x ∈ rowNodeSet Pb.nodesW) :
    ∀ g ∈ canonWGates (F := ZMod p),
      g.eval (Reify.envOfTrace (sideWQ tr ax) Pb.orbitW.ω x (fun _ => 0) (fun _ => 0)) = 0 :=
  ((expandChip_satisfies_iff_language canonWT b _ _ Pb.orbitW _ _).mp h x hx).1

/-- The compute row environment reads the chip's round-0 columns. -/
theorem envC_trace {x : ZMod p} {j : ℕ} (hj : j < 69) :
    (Reify.envOfTrace (sideCQ tr) Pb.orbit.ω x (fun _ => 0) (fun _ => 0)).trace j =
      (tr.C ⟨j, by omega⟩).eval x := by
  rw [envOfTrace_trace _ _ _ _ _ (by have := canonCT_width (F := ZMod p); omega)]
  rfl

/-- The cell row environment reads the chip's round-0 columns. -/
theorem envM_trace {x : ZMod p} {j : ℕ} (hj : j < 134) :
    (Reify.envOfTrace (sideMQ tr ax) Pb.orbitC.ω x (fun _ => 0) (fun _ => 0)).trace j =
      (tr.M ⟨j, by omega⟩).eval x := by
  rw [envOfTrace_trace _ _ _ _ _ (by have := canonMT_width (F := ZMod p); omega)]
  simp only [sideMQ, dif_pos hj]

/-- The walk row environment reads the chip's round-0 columns (current and next row). -/
theorem envW_trace {x : ZMod p} {j : ℕ} (hj : j < 25) :
    (Reify.envOfTrace (sideWQ tr ax) Pb.orbitW.ω x (fun _ => 0) (fun _ => 0)).trace j =
      (tr.W ⟨j, by omega⟩).eval x := by
  rw [envOfTrace_trace _ _ _ _ _ (by have := canonWT_width (F := ZMod p); omega)]
  simp only [sideWQ, dif_pos hj]

theorem envW_traceNext {x : ZMod p} {j : ℕ} (hj : j < 25) :
    (Reify.envOfTrace (sideWQ tr ax) Pb.orbitW.ω x (fun _ => 0) (fun _ => 0)).traceNext j =
      (tr.W ⟨j, by omega⟩).eval (Pb.orbitW.ω * x) := by
  rw [envOfTrace_traceNext _ _ _ _ _ (by have := canonWT_width (F := ZMod p); omega)]
  simp only [sideWQ, dif_pos hj]

end Sat


/-! ## 2. Compute: E2 and E3 -/

section Compute
variable {F : Type} [Field F]

/-- A one-hot list sum: the only nonzero summand is at `s0`. -/
theorem sum_single (L : List ℕ) (f : ℕ → F) (s0 : ℕ) (hnd : L.Nodup) (hm : s0 ∈ L) (h1 : f s0 = 1)
    (h0 : ∀ s ∈ L, s ≠ s0 → f s = 0) : (L.map f).sum = 1 := by
  induction L with
  | nil => simp at hm
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    by_cases ha : a = s0
    · subst ha
      have hz : (t.map f).sum = 0 := List.sum_eq_zero fun x hx => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
        exact h0 s (by simp [hs]) fun h => hnd.1 (h ▸ hs)
      simp [h1, hz]
    · have hat : f a = 0 := h0 a (by simp) ha
      have hmt : s0 ∈ t := by simpa [Ne.symm ha] using hm
      rw [List.map_cons, List.sum_cons, hat, zero_add]
      exact ih hnd.2 hmt (fun s hs hne => h0 s (by simp [hs]) hne)

/-- **The extra pin (E2) (compute).** `(1 − s4·fast)·inv4 = 0`: off the gate `s4·fast`, the inverse hint is `0`. -/
theorem canonC_inv4 (E : Env F) (h : ∀ g ∈ canonCGates (F := F), g.eval E = 0)
    (hg : E.trace 4 * E.trace 61 = 0) : E.trace 62 = 0 := by
  have := h _ (List.mem_cons_self ..)
  simp only [CoeffExpr.eval, cv, notE] at this
  rw [hg, sub_zero, one_mul] at this
  exact this

/-- **The extra pin (E3) (compute).** A round-0 compute column is `0` on a row whose state `s0` (one-hot among the `17`
selectors) lies outside `Act(c)`. -/
theorem canonC_offAct (E : Env F) (h : ∀ g ∈ canonCGates (F := F), g.eval E = 0) {c : ℕ} (hc : c < 69)
    {s0 : ℕ} (hs0 : s0 < 17) (hout : s0 ∉ actC c) (hone : E.trace s0 = 1)
    (hoth : ∀ s < 17, s ≠ s0 → E.trace s = 0) : E.trace c = 0 := by
  have hmem : (pinC c : CoeffExpr F) ∈ canonCGates (F := F) :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)
  have hg := h _ hmem
  simp only [pinC, CoeffExpr.eval, CoeffExpr.eval_sumList, cv] at hg
  have hsum : (((List.range 17).filter fun s => decide (s ∉ actC c)).map fun s => E.trace s).sum = 1 := by
    refine sum_single _ (fun s => E.trace s) s0 ((List.nodup_range).filter _) ?_ hone ?_
    · simp [List.mem_filter, hs0, hout]
    · intro s hs hne
      exact hoth s (List.mem_range.mp (List.mem_filter.mp hs).1) hne
  rw [hsum, one_mul] at hg
  exact hg

end Compute

/-! ## 3. Cell: E1 and E2 -/

section Cell
variable {F : Type} [Field F]

/-- The seven gates of one child side, read off at a row. -/
theorem sideM_pins (E : Env F) (w id a kb inv h l t : ℕ)
    (hs : ∀ g ∈ sideM (F := F) w id a kb inv h l t, g.eval E = 0) :
    (1 - E.trace w) * E.trace id = 0 ∧ E.trace w * E.trace a = 0 ∧
      (1 - E.trace w + E.trace w * E.trace kb) * E.trace inv = 0 := by
  have e1 := hs (.mul (notE (cv w)) (cv id)) (by simp [sideM])
  have e2 := hs (.mul (cv w) (cv a)) (by simp [sideM])
  have e3 := hs (.mul (.add (notE (cv w)) (.mul (cv w) (cv kb))) (cv inv)) (by simp [sideM])
  simp only [CoeffExpr.eval, cv, notE] at e1 e2 e3
  exact ⟨e1, e2, e3⟩

theorem canonM_left (E : Env F) (h : ∀ g ∈ canonMGates (F := F), g.eval E = 0) :
    (1 - E.trace Cell.wL) * E.trace Cell.idL = 0 ∧ E.trace Cell.wL * E.trace Cell.aL = 0 ∧
      (1 - E.trace Cell.wL + E.trace Cell.wL * E.trace CellTwinK.kbL) * E.trace CellTwinK.invL = 0 :=
  sideM_pins E _ _ _ _ _ _ _ _ fun g hg => h g (by
    unfold canonMGates
    simp only [List.mem_append]
    tauto)

theorem canonM_right (E : Env F) (h : ∀ g ∈ canonMGates (F := F), g.eval E = 0) :
    (1 - E.trace Cell.wR) * E.trace Cell.idR = 0 ∧ E.trace Cell.wR * E.trace Cell.aR = 0 ∧
      (1 - E.trace Cell.wR + E.trace Cell.wR * E.trace CellTwinK.kbR) * E.trace CellTwinK.invR = 0 :=
  sideM_pins E _ _ _ _ _ _ _ _ fun g hg => h g (by
    unfold canonMGates
    simp only [List.mem_append]
    tauto)

/-- **The extra pin (E1)**: a child that is an atom (`w = 0`) has serial `0`; a child that is a cell (`w = 1`) has atom value `0`. -/
theorem E1_of_pins {w id a : F} (h1 : (1 - w) * id = 0) (h2 : w * a = 0) :
    (w = 0 → id = 0) ∧ (w = 1 → a = 0) := by
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · rw [hw] at h1; simpa using h1
  · rw [hw] at h2; simpa using h2

/-- **The extra pin (E2) ("0 for 0")**: the inverse hint of a child is `0` unless the child is a cell (`w = 1`) with a zero
atom-kind flag `kb = 0` (the one case its inverse gate is live). -/
theorem E2_of_pin {w kb inv : F} (h : (1 - w + w * kb) * inv = 0) :
    (w = 0 → inv = 0) ∧ (w = 1 → kb ≠ 0 → inv = 0) := by
  refine ⟨fun hw => ?_, fun hw hk => ?_⟩
  · rw [hw] at h; simpa using h
  · rw [hw] at h
    have : (1 - 1 + 1 * kb) = kb := by ring
    rw [this] at h
    exact (mul_eq_zero.mp h).resolve_left hk

end Cell

/-! ## 4. Walk: `qinv`, the depth bits, the root order -/

section Walk
variable {F : Type} [Field F]

/-- **The last-row `qinv` pin**: `isL · qinv = 0`. -/
theorem canonW_qinv (E : Env F) (h : ∀ g ∈ canonWGates (F := F), g.eval E = 0) :
    E.trace WChip.isL * E.trace WChip.qinv = 0 := by
  have := h (.mul (cv WChip.isL) (cv WChip.qinv)) (by simp [canonWGates])
  simpa only [CoeffExpr.eval, cv] using this

/-- On the last row `qinv = 0`. -/
theorem canonW_qinv_last (E : Env F) (h : ∀ g ∈ canonWGates (F := F), g.eval E = 0)
    (hl : E.trace WChip.isL = 1) : E.trace WChip.qinv = 0 := by
  have := canonW_qinv E h
  rw [hl, one_mul] at this
  exact this

/-- The two `y` gates of the depth certificate, read off at a row. -/
theorem canonW_y (E : Env F) (h : ∀ g ∈ canonWGates (F := F), g.eval E = 0) :
    E.trace wy = E.trace (WChip.bit0 + 5) * (1 - E.trace (WChip.bit0 + 2)) * (1 - E.trace (WChip.bit0 + 3)) ∧
      E.trace wy * (1 - E.trace (WChip.bit0 + 4)) * (1 - E.trace WChip.bit0 * E.trace (WChip.bit0 + 1)) = 0 := by
  have e1 := h (.sub (cv wy) (.mul (.mul (WChip.bt 5) (notE (WChip.bt 2))) (notE (WChip.bt 3)))) (by simp [canonWGates])
  have e2 := h (.mul (.mul (cv wy) (notE (WChip.bt 4))) (notE (.mul (WChip.bt 0) (WChip.bt 1)))) (by simp [canonWGates])
  simp only [CoeffExpr.eval, cv, notE, WChip.bt, add_zero] at e1 e2
  exact ⟨sub_eq_zero.mp e1, e2⟩

/-- Booleans are `0` or `1` as naturals. -/
theorem bit_nat {b : F} (h : b * (b - 1) = 0) : ∃ β : ℕ, β ≤ 1 ∧ b = (β : F) := by
  rcases mul_eq_zero.mp h with h | h
  · exact ⟨0, by norm_num, by simpa using h⟩
  · exact ⟨1, le_rfl, by simpa [sub_eq_zero] using h⟩

/-- **The depth bits in `ℕ`**: with the `y` exclusion, `b5 = [32 ≤ 60 − n]`. -/
theorem depth_nat {n β0 β1 β2 β3 β4 β5 : ℕ} (h0 : β0 ≤ 1) (h1 : β1 ≤ 1) (h2 : β2 ≤ 1) (h3 : β3 ≤ 1)
    (h4 : β4 ≤ 1) (h5 : β5 ≤ 1) (hd : n + (β0 + 2 * β1 + 4 * β2 + 8 * β3 + 16 * β4) + 29 * β5 = 60)
    (hex : β5 = 1 → β2 = 0 → β3 = 0 → β4 = 0 → β0 = 1 ∧ β1 = 1) :
    β5 = if 32 ≤ 60 - n then 1 else 0 := by
  split_ifs <;> omega

/-- **The depth bits are unique in `ℕ`**: two witnesses for the same `n` agree on all six bits. -/
theorem depth_nat_unique {n β0 β1 β2 β3 β4 β5 γ0 γ1 γ2 γ3 γ4 γ5 : ℕ}
    (h0 : β0 ≤ 1) (h1 : β1 ≤ 1) (h2 : β2 ≤ 1) (h3 : β3 ≤ 1) (h4 : β4 ≤ 1) (h5 : β5 ≤ 1)
    (g0 : γ0 ≤ 1) (g1 : γ1 ≤ 1) (g2 : γ2 ≤ 1) (g3 : γ3 ≤ 1) (g4 : γ4 ≤ 1) (g5 : γ5 ≤ 1)
    (hd : n + (β0 + 2 * β1 + 4 * β2 + 8 * β3 + 16 * β4) + 29 * β5 = 60)
    (hex : β5 = 1 → β2 = 0 → β3 = 0 → β4 = 0 → β0 = 1 ∧ β1 = 1)
    (hd' : n + (γ0 + 2 * γ1 + 4 * γ2 + 8 * γ3 + 16 * γ4) + 29 * γ5 = 60)
    (hex' : γ5 = 1 → γ2 = 0 → γ3 = 0 → γ4 = 0 → γ0 = 1 ∧ γ1 = 1) :
    β0 = γ0 ∧ β1 = γ1 ∧ β2 = γ2 ∧ β3 = γ3 ∧ β4 = γ4 ∧ β5 = γ5 := by
  have e5 : β5 = γ5 := (depth_nat h0 h1 h2 h3 h4 h5 hd hex).trans (depth_nat g0 g1 g2 g3 g4 g5 hd' hex').symm
  clear hex hex'
  omega

/-- **Packing the depth witness**: with `len = n` (`n + 121 ≤ p`) the six bits are naturals `≤ 1`, the
certificate holds in `ℕ`, and the `y` exclusion holds in `ℕ`. -/
theorem depth_pack {p : ℕ} [CharP F p] {n : ℕ} (hn : n + 121 ≤ p) {b0 b1 b2 b3 b4 b5 y len : F}
    (hlen : len = (n : F)) (hb0 : b0 * (b0 - 1) = 0) (hb1 : b1 * (b1 - 1) = 0) (hb2 : b2 * (b2 - 1) = 0)
    (hb3 : b3 * (b3 - 1) = 0) (hb4 : b4 * (b4 - 1) = 0) (hb5 : b5 * (b5 - 1) = 0)
    (hd : len + (b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4) + 29 * b5 = 60)
    (hy1 : y = b5 * (1 - b2) * (1 - b3)) (hy2 : y * (1 - b4) * (1 - b0 * b1) = 0) :
    ∃ β0 β1 β2 β3 β4 β5 : ℕ, β0 ≤ 1 ∧ β1 ≤ 1 ∧ β2 ≤ 1 ∧ β3 ≤ 1 ∧ β4 ≤ 1 ∧ β5 ≤ 1 ∧
      b0 = β0 ∧ b1 = β1 ∧ b2 = β2 ∧ b3 = β3 ∧ b4 = β4 ∧ b5 = β5 ∧
      n + (β0 + 2 * β1 + 4 * β2 + 8 * β3 + 16 * β4) + 29 * β5 = 60 ∧
      (β5 = 1 → β2 = 0 → β3 = 0 → β4 = 0 → β0 = 1 ∧ β1 = 1) := by
  obtain ⟨β0, h0, rfl⟩ := bit_nat hb0
  obtain ⟨β1, h1, rfl⟩ := bit_nat hb1
  obtain ⟨β2, h2, rfl⟩ := bit_nat hb2
  obtain ⟨β3, h3, rfl⟩ := bit_nat hb3
  obtain ⟨β4, h4, rfl⟩ := bit_nat hb4
  obtain ⟨β5, h5, rfl⟩ := bit_nat hb5
  have hnat : n + (β0 + 2 * β1 + 4 * β2 + 8 * β3 + 16 * β4) + 29 * β5 = 60 := by
    have hc : ((n + (β0 + 2 * β1 + 4 * β2 + 8 * β3 + 16 * β4) + 29 * β5 : ℕ) : F) = ((60 : ℕ) : F) := by
      rw [hlen] at hd
      push_cast
      linear_combination hd
    have := (CharP.natCast_eq_natCast F p).mp hc
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  refine ⟨β0, β1, β2, β3, β4, β5, h0, h1, h2, h3, h4, h5, rfl, rfl, rfl, rfl, rfl, rfl, hnat, ?_⟩
  intro e5 e2 e3 e4
  subst e5 e2 e3 e4
  simp at hy1
  subst hy1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with rfl | rfl <;> simp_all

/-- **The depth bits**: with the `y` gadget the depth bit is `b5 = [32 ≤ 60 − n]`. -/
theorem depth_b5 {p : ℕ} [CharP F p] {n : ℕ} (hn : n + 121 ≤ p) {b0 b1 b2 b3 b4 b5 y len : F}
    (hlen : len = (n : F)) (hb0 : b0 * (b0 - 1) = 0) (hb1 : b1 * (b1 - 1) = 0) (hb2 : b2 * (b2 - 1) = 0)
    (hb3 : b3 * (b3 - 1) = 0) (hb4 : b4 * (b4 - 1) = 0) (hb5 : b5 * (b5 - 1) = 0)
    (hd : len + (b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4) + 29 * b5 = 60)
    (hy1 : y = b5 * (1 - b2) * (1 - b3)) (hy2 : y * (1 - b4) * (1 - b0 * b1) = 0) :
    b5 = ((if 32 ≤ 60 - n then 1 else 0 : ℕ) : F) := by
  obtain ⟨β0, β1, β2, β3, β4, β5, h0, h1, h2, h3, h4, h5, e0, e1, e2, e3, e4, e5, hnat, hex⟩ :=
    depth_pack hn hlen hb0 hb1 hb2 hb3 hb4 hb5 hd hy1 hy2
  rw [e5, depth_nat h0 h1 h2 h3 h4 h5 hnat hex]

/-- **The depth bits, uniqueness**: two depth witnesses for the same length have the same six bits. -/
theorem depth_bits_unique {p : ℕ} [CharP F p] {n : ℕ} (hn : n + 121 ≤ p) {len : F} (hlen : len = (n : F))
    {b0 b1 b2 b3 b4 b5 y c0 c1 c2 c3 c4 c5 z : F}
    (hb0 : b0 * (b0 - 1) = 0) (hb1 : b1 * (b1 - 1) = 0) (hb2 : b2 * (b2 - 1) = 0)
    (hb3 : b3 * (b3 - 1) = 0) (hb4 : b4 * (b4 - 1) = 0) (hb5 : b5 * (b5 - 1) = 0)
    (hd : len + (b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4) + 29 * b5 = 60)
    (hy1 : y = b5 * (1 - b2) * (1 - b3)) (hy2 : y * (1 - b4) * (1 - b0 * b1) = 0)
    (hc0 : c0 * (c0 - 1) = 0) (hc1 : c1 * (c1 - 1) = 0) (hc2 : c2 * (c2 - 1) = 0)
    (hc3 : c3 * (c3 - 1) = 0) (hc4 : c4 * (c4 - 1) = 0) (hc5 : c5 * (c5 - 1) = 0)
    (hd' : len + (c0 + 2 * c1 + 4 * c2 + 8 * c3 + 16 * c4) + 29 * c5 = 60)
    (hz1 : z = c5 * (1 - c2) * (1 - c3)) (hz2 : z * (1 - c4) * (1 - c0 * c1) = 0) :
    b0 = c0 ∧ b1 = c1 ∧ b2 = c2 ∧ b3 = c3 ∧ b4 = c4 ∧ b5 = c5 := by
  obtain ⟨β0, β1, β2, β3, β4, β5, h0, h1, h2, h3, h4, h5, e0, e1, e2, e3, e4, e5, hnat, hex⟩ :=
    depth_pack hn hlen hb0 hb1 hb2 hb3 hb4 hb5 hd hy1 hy2
  obtain ⟨γ0, γ1, γ2, γ3, γ4, γ5, g0, g1, g2, g3, g4, g5, f0, f1, f2, f3, f4, f5, hnat', hex'⟩ :=
    depth_pack hn hlen hc0 hc1 hc2 hc3 hc4 hc5 hd' hz1 hz2
  obtain ⟨u0, u1, u2, u3, u4, u5⟩ :=
    depth_nat_unique h0 h1 h2 h3 h4 h5 g0 g1 g2 g3 g4 g5 hnat hex hnat' hex'
  rw [e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5, u0, u1, u2, u3, u4, u5]
  simp

/-- **Root order**: on consecutive root rows (`isL = 0`, `rM = rM' = 1`), `ridx' = ridx + 1 + d` with `d < 2^31`. -/
theorem canonW_rootorder (E : Env F) (h : ∀ g ∈ canonWGates (F := F), g.eval E = 0)
    (hL : E.trace WChip.isL = 0) (hr : E.trace WChip.rM = 1) (hr' : E.traceNext WChip.rM = 1) :
    ∃ d : ℕ, d < 2 ^ 31 ∧ E.traceNext WChip.ridx = E.trace WChip.ridx + 1 + d := by
  have hb : ∀ i < 31, E.trace (wA + i) * (E.trace (wA + i) - 1) = 0 := fun i hi => by
    have := h (boolE (cv (wA + i))) (by
      simp only [canonWGates, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩)))
    simpa only [CoeffExpr.eval, cv] using this
  obtain ⟨d, hd, hsum⟩ := Chips.CertBound.bits_sum_nat (fun i => E.trace (wA + i)) 31 hb
  have hg := h (.mul rootPairW (.sub (.sub (.sub (nv WChip.ridx) (cv WChip.ridx)) (.const 1)) (bitSum wA 31)))
    (by simp [canonWGates])
  have hbs := eval_bitSum (F := F) wA 31 E
  simp only [CoeffExpr.eval, rootPairW, notE, cv, nv, hL, hr, hr', hbs, ← hsum] at hg
  refine ⟨d, hd, ?_⟩
  linear_combination hg

end Walk


/-! ## 5. The row statements on the traces -/

section RowStatements
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (b : Basis (Fin 3) (ZMod p) K) (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p))

/-- **The extra pin (E1) and E2 at every cell row** (left child), on the committed polynomials. -/
theorem cell_left_pins (h : (canonM b Pb).Satisfies (sideMQ tr ax)) {x : ZMod p} (hx : x ∈ rowNodeSet Pb.nodesC) :
    (1 - (tr.M ⟨Cell.wL, by decide⟩).eval x) * (tr.M ⟨Cell.idL, by decide⟩).eval x = 0 ∧
      (tr.M ⟨Cell.wL, by decide⟩).eval x * (tr.M ⟨Cell.aL, by decide⟩).eval x = 0 ∧
      (1 - (tr.M ⟨Cell.wL, by decide⟩).eval x +
          (tr.M ⟨Cell.wL, by decide⟩).eval x * (tr.M ⟨CellTwinK.kbL, by decide⟩).eval x) *
        (tr.M ⟨CellTwinK.invL, by decide⟩).eval x = 0 := by
  have := canonM_left _ (canonM_row b Pb tr ax h hx)
  rwa [envM_trace Pb tr ax (by decide), envM_trace Pb tr ax (by decide), envM_trace Pb tr ax (by decide),
    envM_trace Pb tr ax (by decide), envM_trace Pb tr ax (by decide)] at this

/-- **The extra pin (E1) and E2 at every cell row** (right child). -/
theorem cell_right_pins (h : (canonM b Pb).Satisfies (sideMQ tr ax)) {x : ZMod p} (hx : x ∈ rowNodeSet Pb.nodesC) :
    (1 - (tr.M ⟨Cell.wR, by decide⟩).eval x) * (tr.M ⟨Cell.idR, by decide⟩).eval x = 0 ∧
      (tr.M ⟨Cell.wR, by decide⟩).eval x * (tr.M ⟨Cell.aR, by decide⟩).eval x = 0 ∧
      (1 - (tr.M ⟨Cell.wR, by decide⟩).eval x +
          (tr.M ⟨Cell.wR, by decide⟩).eval x * (tr.M ⟨CellTwinK.kbR, by decide⟩).eval x) *
        (tr.M ⟨CellTwinK.invR, by decide⟩).eval x = 0 := by
  have := canonM_right _ (canonM_row b Pb tr ax h hx)
  rwa [envM_trace Pb tr ax (by decide), envM_trace Pb tr ax (by decide), envM_trace Pb tr ax (by decide),
    envM_trace Pb tr ax (by decide), envM_trace Pb tr ax (by decide)] at this

/-- **The extra pin (E3) at every compute row**: a column is `0` on a row whose one-hot state lies outside its `Act`. -/
theorem compute_offAct_row (h : (canonC b Pb).Satisfies (sideCQ tr)) {x : ZMod p} (hx : x ∈ rowNodeSet Pb.nodes)
    {c : ℕ} (hc : c < 69) {s0 : ℕ} (hs0 : s0 < 17) (hout : s0 ∉ actC c)
    (hone : (tr.C ⟨s0, by omega⟩).eval x = 1)
    (hoth : ∀ s (hs : s < 17), s ≠ s0 → (tr.C ⟨s, by omega⟩).eval x = 0) :
    (tr.C ⟨c, by omega⟩).eval x = 0 := by
  have := canonC_offAct _ (canonC_row b Pb tr h hx) hc hs0 hout
    (by rw [envC_trace Pb tr (by omega)]; exact hone)
    (fun s hs hne => by rw [envC_trace Pb tr (by omega)]; exact hoth s hs hne)
  rwa [envC_trace Pb tr hc] at this

/-- **The extra pin (E2) at every compute row**: `inv4 = 0` wherever `s4·fast = 0`. -/
theorem compute_inv4_row (h : (canonC b Pb).Satisfies (sideCQ tr)) {x : ZMod p} (hx : x ∈ rowNodeSet Pb.nodes)
    (hg : (tr.C ⟨4, by decide⟩).eval x * (tr.C ⟨61, by decide⟩).eval x = 0) :
    (tr.C ⟨62, by decide⟩).eval x = 0 := by
  have := canonC_inv4 _ (canonC_row b Pb tr h hx)
    (by rw [envC_trace Pb tr (by decide), envC_trace Pb tr (by decide)]; exact hg)
  rwa [envC_trace Pb tr (by decide)] at this

/-- **The `qinv` pin at every walk row**: `isL·qinv = 0`. -/
theorem walk_qinv_row (h : (canonW b Pb).Satisfies (sideWQ tr ax)) {x : ZMod p} (hx : x ∈ rowNodeSet Pb.nodesW) :
    (tr.W ⟨WChip.isL, by decide⟩).eval x * (tr.W ⟨WChip.qinv, by decide⟩).eval x = 0 := by
  have := canonW_qinv _ (canonW_row b Pb tr ax h hx)
  rwa [envW_trace Pb tr ax (by decide), envW_trace Pb tr ax (by decide)] at this

/-- **Root order at every walk row**: consecutive root rows have `ridx' = ridx + 1 + d`, `d < 2^31`. -/
theorem walk_rootorder_row (h : (canonW b Pb).Satisfies (sideWQ tr ax)) {x : ZMod p}
    (hx : x ∈ rowNodeSet Pb.nodesW)
    (hL : (tr.W ⟨WChip.isL, by decide⟩).eval x = 0) (hr : (tr.W ⟨WChip.rM, by decide⟩).eval x = 1)
    (hr' : (tr.W ⟨WChip.rM, by decide⟩).eval (Pb.orbitW.ω * x) = 1) :
    ∃ d : ℕ, d < 2 ^ 31 ∧ (tr.W ⟨WChip.ridx, by decide⟩).eval (Pb.orbitW.ω * x) =
      (tr.W ⟨WChip.ridx, by decide⟩).eval x + 1 + d := by
  have := canonW_rootorder _ (canonW_row b Pb tr ax h hx)
    (by rw [envW_trace Pb tr ax (by decide)]; exact hL) (by rw [envW_trace Pb tr ax (by decide)]; exact hr)
    (by rw [envW_traceNext Pb tr ax (by decide)]; exact hr')
  rwa [envW_traceNext Pb tr ax (by decide), envW_trace Pb tr ax (by decide)] at this

/-- **Root order, natural form**: with `ridx` read as naturals `a, a'` and `a + 2^31 < p`, `a < a'`. -/
theorem ridx_lt_of_rootorder {a a' d : ℕ} (hd : d < 2 ^ 31) (hap : a' < p) (hp : a + 2 ^ 31 < p)
    (h : ((a' : ℕ) : ZMod p) = (a : ZMod p) + 1 + d) : a < a' := by
  have h' : ((a' : ℕ) : ZMod p) = ((a + 1 + d : ℕ) : ZMod p) := by rw [h]; push_cast; ring
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h'
  rw [Nat.mod_eq_of_lt hap, Nat.mod_eq_of_lt (by omega)] at this
  omega

end RowStatements

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1.canonC_offAct
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1.canonC_inv4
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1.canonM_left
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1.canonM_right
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1.depth_b5
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1.depth_bits_unique
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1.canonW_qinv
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1.canonW_rootorder
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1.cell_left_pins
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1.compute_offAct_row
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1.walk_rootorder_row
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1.ridx_lt_of_rootorder
