/-
  Nock/RedTeam/Batch4882Thm54J9AComplAbsent.lean

* `hax_excludes_big_axis`: J-9 B's binder `hax` (`ProgAxOK p t`) FAILS on every generated tree with an op-0 row
    whose axis atom is `≥ p` (a big, kind-2 axis).  So `complJ9B_closed`'s hypotheses never admit a program that
    needs the J-9 A axis chip for a big axis: a J-9 A theorem that keeps `hax` verbatim is, on big axes, the absent
    regime.  (Field axes in `[2^62, p)` are excluded by `hwalk`'s depth `≤ 61`: argued, U, not compiled here.)
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AAbsent
import Nock.RedTeam.Batch4856Thm54J9BComplToy

set_option autoImplicit false

namespace Nock.RedTeam.Batch4882

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (StJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AcceptsJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAbsent
open Nock.TraceGenExe (KC deltaF powerBasis3)
open Nock.RedTeam.Batch4842 (RtT factRC charPKC algRC card_KC)
open Nock.RedTeam.Batch4856

noncomputable section

open Classical in
/-- **`complJ9A_closed_absent` at `*[(p+5) [0 1]]`**, every binder discharged, nothing carried. -/
theorem complJ9A_absent_toy :
    (∀ χ, B9T.Good χ → AcceptsJ9A deltaF powerBasis3 (pubA B9T.Pb) Nock.Jet.VerifiedRegistry.empty.R
      (ComplJ8.cJ s9 InhabJ8Base.f0 s9) χ (msgA (B9T.M χ)) (trA (B9T.tr χ)) (rowsA B9T.rows) B9T.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 KC => ¬ B9T.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 KC) ≤ B9T.epsC) ∧
    StJ9A (fun χ => trA (B9T.tr χ)) ∧ Nock.Jet.HoldsN (ComplJ8.cJ s9 InhabJ8Base.f0 s9) ∧
    (Fintype.card KC = VclL.Events.cK →
      B9T.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9A deltaF powerBasis3 (pubA B9T.Pb) Nock.Jet.VerifiedRegistry.empty.R
        (ComplJ8.cJ s9 InhabJ8Base.f0 s9) χ (msgA (B9T.M χ)) (trA (B9T.tr χ)) (rowsA B9T.rows) B9T.g) ∧
    (pubA B9T.Pb).axOn = false ∧ (pubA B9T.Pb).spOn = false :=
  complJ9A_closed_absent deltaF powerBasis3 RtT gen9 rfl hax9 hop5_9 hleaf9 hwalk9 hwalkA9
    (fun id h => absurd h (called9 id)) (fun id h => absurd h (called9 id)) h31_9

/-- **The figure at the toy, hypothesis-free**: `ε_c < 2^-120` and a coin at which `AcceptsJ9A` holds. -/
theorem complJ9A_absent_toy_figure :
    B9T.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9A deltaF powerBasis3 (pubA B9T.Pb) Nock.Jet.VerifiedRegistry.empty.R
        (ComplJ8.cJ s9 InhabJ8Base.f0 s9) χ (msgA (B9T.M χ)) (trA (B9T.tr χ)) (rowsA B9T.rows) B9T.g :=
  complJ9A_absent_toy.2.2.2.2.1 card_KC


/-- **J-9 B's `hax` excludes every big op-0 axis.** If a node of the generated tree is an op-0 row
whose axis is an atom `ax ≥ p`, then `ProgAxOK p t` is false. -/
theorem hax_excludes_big_axis {p : ℕ} {t u : NTree SkelX} (hu : InTree t u)
    (hst : (rowOfSkelX u.label).st = .s0) {ax : ℕ} (hft : (rowOfSkelX u.label).ft = .atom ax) (hp : p ≤ ax) :
    ¬ ComplJ8.ProgAxOK p t := by
  intro h
  have h1 := h u hu
  unfold ComplJ8.AxRowX at h1
  rw [hst] at h1
  exact absurd (h1 ax hft) (by omega)

end

end Nock.RedTeam.Batch4882

#print axioms Nock.RedTeam.Batch4882.complJ9A_absent_toy
#print axioms Nock.RedTeam.Batch4882.complJ9A_absent_toy_figure
#print axioms Nock.RedTeam.Batch4882.hax_excludes_big_axis
