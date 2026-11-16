/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHOrb.lean

  **Honest link: `withOrbL`, the J-9 AL exec record at an arbitrary per-chip orbit.** Twin of `GenPortJ9AHOrbA` for `InJ9AL`: the nine orbits are the eight of `OrbJ9A` and
  the ALU's.

  * `OrbJ9AL`, `withOrbL`, `orbOfL`, `OrbAdmL`;
  * `rfl` lemmas: `(withOrbL I o).toInJ9A = withOrb I.toInJ9A o.toA`, and every `AL` / `aluOn` / `prims` field;
  * `validJ9AL_withOrbL`, `orbAdmL_self`, `nodes_withOrbL`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
import Nock.V1J9AL.CheckJ9ALIff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Check Nock.V1J9A
open Nock.V1J9A.CheckJ9AIff Nock.V1J9A.CheckJ9A
open Nock.V1J9AL.CheckJ9AL Nock.V1J9AL.CheckJ9ALIff
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA

/-- A per-chip orbit assignment for the nine chips. -/
structure OrbJ9AL where
  toA : OrbJ9A
  AL : Orb

/-- `I` with every chip's orbit replaced by `o`; everything else unchanged. -/
def withOrbL (I : InJ9AL) (o : OrbJ9AL) : InJ9AL :=
  { I with toInJ9A := withOrb I.toInJ9A o.toA, AL := reorb I.AL o.AL }

/-- The assignment that keeps `I`'s own orbits. -/
def orbOfL (I : InJ9AL) : OrbJ9AL := ⟨orbOf I.toInJ9A, ⟨I.AL.h, I.AL.ω⟩⟩

/-- Admissible orbits: the J-9 A ones and the ALU's. -/
structure OrbAdmL (I : InJ9AL) (o : OrbJ9AL) : Prop where
  toA : OrbAdm I.toInJ9A o.toA
  AL : OrbFits I.AL o.AL
  /-- The ALU orbit is the generator's own (the ALU's next-row gates are unguarded: no enlarged ALU orbit). -/
  ALh : o.AL.h = I.AL.h

/-! ## 1. `rfl` lemmas -/

theorem withOrbL_toInJ9A (I : InJ9AL) (o : OrbJ9AL) :
    (withOrbL I o).toInJ9A = withOrb I.toInJ9A o.toA := rfl

theorem withOrbL_self (I : InJ9AL) : withOrbL I (orbOfL I) = I := rfl

theorem withOrbL_AL (I : InJ9AL) (o : OrbJ9AL) : (withOrbL I o).AL = reorb I.AL o.AL := rfl
theorem withOrbL_pubsL (I : InJ9AL) (o : OrbJ9AL) : (withOrbL I o).pubsL = I.pubsL := rfl
theorem withOrbL_aluOn (I : InJ9AL) (o : OrbJ9AL) : (withOrbL I o).aluOn = I.aluOn := rfl
theorem withOrbL_prims (I : InJ9AL) (o : OrbJ9AL) : (withOrbL I o).prims = I.prims := rfl
theorem withOrbL_idxP (I : InJ9AL) (o : OrbJ9AL) : (withOrbL I o).idxP = I.idxP := rfl
theorem withOrbL_rkP (I : InJ9AL) (o : OrbJ9AL) : (withOrbL I o).rkP = I.rkP := rfl
theorem withOrbL_rAL (I : InJ9AL) (o : OrbJ9AL) : (withOrbL I o).rAL = I.rAL := rfl

theorem withOrbL_toMsgL (I : InJ9AL) (o : OrbJ9AL) : (withOrbL I o).toMsgL = I.toMsgL := rfl
theorem withOrbL_toRowsL (I : InJ9AL) (o : OrbJ9AL) : (withOrbL I o).toRowsL = I.toRowsL := rfl

/-! ## 2. Validity and admissibility -/

theorem validJ9AL_withOrbL {I : InJ9AL} {o : OrbJ9AL} (hv : ValidJ9AL I) (ho : OrbAdmL I o) :
    ValidJ9AL (withOrbL I o) :=
  { validJ9A_withOrb hv.toValidJ9A ho.toA with nL := hv.nL, oAL := ho.AL.1 }

theorem orbAdmL_self {I : InJ9AL} (hv : ValidJ9AL I)
    (hX : I.X.n ≤ 3 * 2 ^ I.X.h) (hC : I.C.n ≤ 3 * 2 ^ I.C.h) (hW : I.W.n ≤ 3 * 2 ^ I.W.h)
    (hJ : I.J.n ≤ 3 * 2 ^ I.J.h) (hA : I.A.n ≤ 3 * 2 ^ I.A.h) (hV : I.V.n ≤ 3 * 2 ^ I.V.h)
    (hAX : I.AX.n ≤ 3 * 2 ^ I.AX.h) (hSP : I.SP.n ≤ 3 * 2 ^ I.SP.h) (hAL : I.AL.n ≤ 3 * 2 ^ I.AL.h) :
    OrbAdmL I (orbOfL I) :=
  ⟨orbAdm_self hv.toValidJ9A hX hC hW hJ hA hV hAX hSP, ⟨hv.oAL, hAL⟩, rfl⟩

/-! ## 3. Nodes -/

/-- The ALU's `hinj` / `hadj` field shape. -/
abbrev NodesFieldsL (Pb : RealIOJ9AL.PubJ9AL p) : Prop :=
  Function.Injective Pb.nodesL ∧
    ∀ (i : Fin Pb.nL) (hi : (i : ℕ) + 1 < Pb.nL), Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesL i * Pb.orbitL.ω

theorem nodes_withOrbL {I : InJ9AL} {o : OrbJ9AL} (ho : OrbAdmL I o) (hv' : ValidJ9AL (withOrbL I o)) :
    NodesFields (mkPbA (withOrbL I o).toInJ9A hv'.toValidJ9A) ∧ NodesFieldsL (mkPbAL (withOrbL I o) hv') :=
  ⟨nodes_withOrb ho.toA hv'.toValidJ9A, nodes_ok (reorb I.AL o.AL) ho.AL.1 ho.AL.2⟩

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb in
#print axioms withOrbL_toInJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb in
#print axioms validJ9AL_withOrbL
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb in
#print axioms orbAdmL_self
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb in
#print axioms nodes_withOrbL
