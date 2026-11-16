/-
`acceptsJ9AL_mono_rows`, the J-9 AL twin of `J9A/InstJ9A.acceptsJ9A_mono_rows`
(itself the twin of `Batch4775.acceptsJ8V_mono_rows`).  `AcceptsJ9AL` reads the row record `r` and the group size `g` only through `hbud`
(`BudJ9AL Pb r (g + r.N)`), `hbudV` and the `nL ≤ r.AL` conjunct of `hlenL`; each is an upper bound, so the predicate is monotone in `r` and `g`.
Lets the honest acceptance of nock's `genJ9ALXJ_honest_at` (at the generator's own rows `toRowsL`, `g = 0`) be restated at the census corner
`cornerC9L`, `g = 2^31` of the datum.  Not zero-knowledge.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9AL.AccMonoJ9AL

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Module Polynomial

section Mono
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **`BudJ9AL` is monotone in the row record and `g`** (every field is an upper bound on a sum of row parameters). -/
theorem budJ9AL_mono {Pb : PubJ9AL p} {r r' : RowsJ9AL} {g g' : ℕ} (h : BudJ9AL Pb r g)
    (hN : r.N ≤ r'.N) (hD : r.D ≤ r'.D) (hW : r.W ≤ r'.W) (hJ : r.J ≤ r'.J) (hcalls : r.calls ≤ r'.calls)
    (hheads : r.heads ≤ r'.heads) (hblocks : r.blocks ≤ r'.blocks) (hrd : r.rd ≤ r'.rd)
    (hAX : r.AX ≤ r'.AX) (hSP : r.SP ≤ r'.SP) (hAL : r.AL ≤ r'.AL) (hg : g ≤ g') : BudJ9AL Pb r' g' := by
  obtain ⟨x1, x2, p1, p2, s1, s2⟩ := h
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **`acceptsJ9AL_mono_rows`**: `AcceptsJ9AL` at the rows `r` and `g` implies it at any rows `r'` and `g'` that are pointwise at least as large
(rows enter only through `hbud`, `hbudV`, and the `nL ≤ r.AL` conjunct of `hlenL`). -/
theorem acceptsJ9AL_mono_rows {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : SVFrame.Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r r' : RowsJ9AL} {g g' : ℕ}
    (h : AcceptsJ9AL.AcceptsJ9AL δ b Pb Rg c χ M tr r g)
    (hN : r.N ≤ r'.N) (hD : r.D ≤ r'.D) (hW : r.W ≤ r'.W) (hJ : r.J ≤ r'.J) (hcalls : r.calls ≤ r'.calls)
    (hheads : r.heads ≤ r'.heads) (hblocks : r.blocks ≤ r'.blocks) (hrd : r.rd ≤ r'.rd) (hmb : r.mb ≤ r'.mb)
    (hA : r.A ≤ r'.A) (hAW : r.AW ≤ r'.AW) (hAX : r.AX ≤ r'.AX) (hSP : r.SP ≤ r'.SP) (hAL : r.AL ≤ r'.AL) (hg : g ≤ g') :
    AcceptsJ9AL.AcceptsJ9AL δ b Pb Rg c χ M tr r' g' := by
  have hb := h.hbud
  have hv := h.hbudV
  have hl := h.hlenL
  exact { h with
    hbud := budJ9AL_mono (g' := g' + r'.N) hb hN hD hW hJ hcalls hheads hblocks hrd hAX hSP hAL (by omega)
    hbudV := ⟨by have := hv.1; omega, by have := hv.2.1; omega, by have := hv.2.2.1; omega, by have := hv.2.2.2.1; omega,
      by have := hv.2.2.2.2.1; omega, by have := hv.2.2.2.2.2; omega⟩
    hlenL := ⟨hl.1, by have := hl.2.1; omega, hl.2.2⟩ }

end Mono

end NockvmE2E.J9AL.AccMonoJ9AL

#print axioms NockvmE2E.J9AL.AccMonoJ9AL.budJ9AL_mono
#print axioms NockvmE2E.J9AL.AccMonoJ9AL.acceptsJ9AL_mono_rows
