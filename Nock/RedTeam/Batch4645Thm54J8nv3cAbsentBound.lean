/-
  Nock/RedTeam/Batch4645Thm54J8nv3cAbsentBound.lean

  **4644** (`Handle/FinalJ8IGA`, `HokLJ8GA`, `AbsentVJ8`,
  `AcceptsJ8Z{W,L,H}A`, `LinkJ8A`).

  * `LinkJ8A.probJ8V_absent`: the J-8 bound (< 2^-155) over `AcceptsJ8V` at `krootsV = 0`;
  * `LinkJ8A.probJ8V_final`: the same bound at every layout, at `probJ8NV_final`'s binders (no `hkV`).
  * The two replaced readouts: `AbsentVJ8.rdS_A` (#6 providers = `effP (liftP (provsJ8A.s))`, `provsJ8A.s = jProv ++
    pad8 atomIncProvs`) and `AbsentVJ8.rdAX_A` (#4 requests = the atom table's consumes only).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A

namespace Nock.RedTeam.Batch4645

open Nock.NockVMROM.Thm54.VclL.Handle

#check @LinkJ8A.probJ8V_final
#check @AbsentVJ8.RR4A
#print axioms FinalJ8IGA.acceptsJ8_holdsN_EIGA
#print axioms HokLJ8GA.acceptsJ8_holdsN_finalLGA
#print axioms AbsentVJ8.provsJ8A_s_eq
#print axioms AbsentVJ8.provsTA_congr
#print axioms AbsentVJ8.axJ8A_reads
#print axioms AbsentVJ8.rdS_A
#print axioms AbsentVJ8.rdAX_A
#print axioms AbsentVJ8.acceptsJ8ZA_of_V
#print axioms AbsentVJ8.budS_ofZA
#print axioms AbsentVJ8.hcount_ofZA
#print axioms AcceptsJ8ZWA.linkJ8_L2Z
#print axioms AcceptsJ8ZLA.row0_hdZ
#print axioms AcceptsJ8ZHA.hHXW_of_acceptsZ
#print axioms LinkJ8A.rdV_viewA
#print axioms LinkJ8A.hXW_of_ioA
#print axioms LinkJ8A.hsoundJ8ZUA
#print axioms LinkJ8A.hsoundJ8XUA
#print axioms LinkJ8A.linkXUA_of_R5
#print axioms LinkJ8A.probJ8V_absent
#print axioms LinkJ8A.probJ8V_final

/-- The two events that changed are exactly the replaced lists: every other `RR4A` readout is `RR4`'s (`rfl`). -/
example {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
    [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
    (b : Module.Basis (Fin 3) (ZMod p) K) [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
    [Algebra Nock.Atoms.Fp (Nock.NockVMROM.Thm54.T0Tower.Quad (algebraMap (ZMod p) K δ))]
    {r : FrameJ8.RowsJ8} {P g : ℕ}
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TraceJ8.TrJ8 (ZMod p)) TraceJ8.StJ8 r P)
    (Pb : AcceptsJ8.PubJ8 p) (c : Nock.NockVMROM.Thm54.P8PublicClaim) (skel : List Noun) (hs : skel.length ≤ 3)
    (hL : TraceJ8.LayLe (LinkJ8Q1.layPb Pb skel hs) r) (hP : P = 2 ^ 66)
    (hnM : (LinkJ8Q1.layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (AcceptsJ8P.censusG Pb c).length ≤ 2 ^ 31) :
    (AbsentVJ8.RR4A δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).D.cxReqs =
        (LinkJ8R4.RR4 δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).D.cxReqs ∧
      (AbsentVJ8.RR4A δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).D.svReqs =
        (LinkJ8R4.RR4 δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).D.svReqs ∧
      (AbsentVJ8.RR4A δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).D.axProvs =
        (LinkJ8R4.RR4 δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).D.axProvs ∧
      (AbsentVJ8.RR4A δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).wdC =
        (LinkJ8R4.RR4 δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).wdC :=
  ⟨rfl, rfl, rfl, rfl⟩

end Nock.RedTeam.Batch4645
