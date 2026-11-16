/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHOrbA.lean

  Nothing here equates `mkPbA` records with `B.Pb`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStatic
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
import Nock.V1J9A.CheckJ9AIff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Check Nock.V1J9A
open Nock.V1J9A.CheckJ9AIff Nock.V1J9A.CheckJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (PubJ9A)

/-! ## 1. Definitions (copied from the kernel-checked `ProbeOrb.lean`) -/

/-- A per-chip orbit: height and generator. -/
structure Orb where
  h : ℕ
  ω : Nock.TraceGenExe.Gold

/-- `q` with its orbit replaced; rows and columns unchanged. -/
abbrev reorb (q : ChipIn) (O : Orb) : ChipIn := { q with h := O.h, ω := O.ω }

/-- A per-chip orbit assignment for the eight chips. -/
structure OrbJ9A where
  X : Orb
  C : Orb
  W : Orb
  J : Orb
  A : Orb
  V : Orb
  AX : Orb
  SP : Orb

/-- `I` with every chip's orbit replaced by `o`; everything else unchanged. -/
def withOrb (I : InJ9A) (o : OrbJ9A) : InJ9A :=
  { I with X := reorb I.X o.X, C := reorb I.C o.C, W := reorb I.W o.W, J := reorb I.J o.J,
           A := reorb I.A o.A, V := reorb I.V o.V, lay := I.lay,
           AX := reorb I.AX o.AX, SP := reorb I.SP o.SP }

/-- The assignment that keeps `I`'s own orbits. -/
def orbOf (I : InJ9A) : OrbJ9A :=
  ⟨⟨I.X.h, I.X.ω⟩, ⟨I.C.h, I.C.ω⟩, ⟨I.W.h, I.W.ω⟩, ⟨I.J.h, I.J.ω⟩, ⟨I.A.h, I.A.ω⟩, ⟨I.V.h, I.V.ω⟩,
    ⟨I.AX.h, I.AX.ω⟩, ⟨I.SP.h, I.SP.ω⟩⟩

/-- Admissible orbit for a chip: valid orbit and the rows fit (gives injective nodes). -/
def OrbFits (q : ChipIn) (O : Orb) : Prop := OrbOK (reorb q O) ∧ q.n ≤ 3 * 2 ^ O.h

structure OrbAdm (I : InJ9A) (o : OrbJ9A) : Prop where
  X : OrbFits I.X o.X
  C : OrbFits I.C o.C
  W : OrbFits I.W o.W
  J : OrbFits I.J o.J
  A : OrbFits I.A o.A
  V : OrbFits I.V o.V
  AX : OrbFits I.AX o.AX
  SP : OrbFits I.SP o.SP

/-! ## 2. `rfl` lemmas -/

theorem withOrb_self (I : InJ9A) : withOrb I (orbOf I) = I := rfl

theorem reorb_n (q : ChipIn) (O : Orb) : (reorb q O).n = q.n := rfl
theorem reorb_cols (q : ChipIn) (O : Orb) (c : ℕ) (i : Fin q.n) : (reorb q O).cols c i = q.cols c i := rfl
theorem reorb_h (q : ChipIn) (O : Orb) : (reorb q O).h = O.h := rfl
theorem reorb_ω (q : ChipIn) (O : Orb) : (reorb q O).ω = O.ω := rfl

theorem withOrb_X (I : InJ9A) (o : OrbJ9A) : (withOrb I o).X = reorb I.X o.X := rfl
theorem withOrb_C (I : InJ9A) (o : OrbJ9A) : (withOrb I o).C = reorb I.C o.C := rfl
theorem withOrb_W (I : InJ9A) (o : OrbJ9A) : (withOrb I o).W = reorb I.W o.W := rfl
theorem withOrb_J (I : InJ9A) (o : OrbJ9A) : (withOrb I o).J = reorb I.J o.J := rfl
theorem withOrb_A (I : InJ9A) (o : OrbJ9A) : (withOrb I o).A = reorb I.A o.A := rfl
theorem withOrb_V (I : InJ9A) (o : OrbJ9A) : (withOrb I o).V = reorb I.V o.V := rfl
theorem withOrb_AX (I : InJ9A) (o : OrbJ9A) : (withOrb I o).AX = reorb I.AX o.AX := rfl
theorem withOrb_SP (I : InJ9A) (o : OrbJ9A) : (withOrb I o).SP = reorb I.SP o.SP := rfl

theorem withOrb_c (I : InJ9A) (o : OrbJ9A) : (withOrb I o).c = I.c := rfl
theorem withOrb_M (I : InJ9A) (o : OrbJ9A) : (withOrb I o).M = I.M := rfl
theorem withOrb_χ (I : InJ9A) (o : OrbJ9A) : (withOrb I o).χ = I.χ := rfl
theorem withOrb_r (I : InJ9A) (o : OrbJ9A) : (withOrb I o).r = I.r := rfl
theorem withOrb_g (I : InJ9A) (o : OrbJ9A) : (withOrb I o).g = I.g := rfl
theorem withOrb_kroots (I : InJ9A) (o : OrbJ9A) : (withOrb I o).kroots = I.kroots := rfl
theorem withOrb_krootsV (I : InJ9A) (o : OrbJ9A) : (withOrb I o).krootsV = I.krootsV := rfl
theorem withOrb_Rt (I : InJ9A) (o : OrbJ9A) : (withOrb I o).Rt = I.Rt := rfl
theorem withOrb_regs (I : InJ9A) (o : OrbJ9A) : (withOrb I o).regs = I.regs := rfl
theorem withOrb_ids (I : InJ9A) (o : OrbJ9A) : (withOrb I o).ids = I.ids := rfl
theorem withOrb_idx (I : InJ9A) (o : OrbJ9A) : (withOrb I o).idx = I.idx := rfl
theorem withOrb_rk (I : InJ9A) (o : OrbJ9A) : (withOrb I o).rk = I.rk := rfl
theorem withOrb_pubsX (I : InJ9A) (o : OrbJ9A) : (withOrb I o).pubsX = I.pubsX := rfl
theorem withOrb_pubsS (I : InJ9A) (o : OrbJ9A) : (withOrb I o).pubsS = I.pubsS := rfl
theorem withOrb_axOn (I : InJ9A) (o : OrbJ9A) : (withOrb I o).axOn = I.axOn := rfl
theorem withOrb_spOn (I : InJ9A) (o : OrbJ9A) : (withOrb I o).spOn = I.spOn := rfl
theorem withOrb_rAX (I : InJ9A) (o : OrbJ9A) : (withOrb I o).rAX = I.rAX := rfl
theorem withOrb_rSP (I : InJ9A) (o : OrbJ9A) : (withOrb I o).rSP = I.rSP := rfl

theorem withOrb_toMsg (I : InJ9A) (o : OrbJ9A) : (withOrb I o).toMsg = I.toMsg := rfl
theorem withOrb_toRows (I : InJ9A) (o : OrbJ9A) : (withOrb I o).toRows = I.toRows := rfl

theorem interpOf_reorb (q : ChipIn) (O : Orb) (j : ℕ) :
    interpOf (reorb q O) j = Lagrange.interpolate Finset.univ (nodesOf (reorb q O)) (fun i => q.cols j i) := rfl

/-- Copy of `nodesOf_powN`. -/
theorem nodesOf_powN (q : ChipIn) (ho : OrbOK q) :
    nodesOf q = Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.powN (mkOrbit q ho) q.n :=
  funext fun i => nodesOf_eq q i

/-! ## 3. Validity -/

theorem validJ9A_withOrb {I : InJ9A} {o : OrbJ9A} (hv : ValidJ9A I) (ho : OrbAdm I o) :
    ValidJ9A (withOrb I o) :=
  ValidJ9A.mk' (withOrb I o)
    ⟨hv.nX, hv.nC, hv.nW, hv.nA, hv.nV, ho.X.1, ho.C.1, ho.W.1, ho.J.1, ho.A.1, ho.V.1⟩
    ⟨hv.nAX, ho.AX.1, hv.nSP, ho.SP.1⟩

theorem orbAdm_self {I : InJ9A} (hv : ValidJ9A I)
    (hX : I.X.n ≤ 3 * 2 ^ I.X.h) (hC : I.C.n ≤ 3 * 2 ^ I.C.h) (hW : I.W.n ≤ 3 * 2 ^ I.W.h)
    (hJ : I.J.n ≤ 3 * 2 ^ I.J.h) (hA : I.A.n ≤ 3 * 2 ^ I.A.h) (hV : I.V.n ≤ 3 * 2 ^ I.V.h)
    (hAX : I.AX.n ≤ 3 * 2 ^ I.AX.h) (hSP : I.SP.n ≤ 3 * 2 ^ I.SP.h) :
    OrbAdm I (orbOf I) :=
  ⟨⟨hv.oX, hX⟩, ⟨hv.oC, hC⟩, ⟨hv.oW, hW⟩, ⟨hv.oJ, hJ⟩, ⟨hv.oA, hA⟩, ⟨hv.oV, hV⟩,
    ⟨hv.oAX, hAX⟩, ⟨hv.oSP, hSP⟩⟩

theorem staticHyp_withOrb {I : InJ9A} {m : ℕ} (o : OrbJ9A)
    (H : GenPortJ9AHStatic.StaticHyp I m) : GenPortJ9AHStatic.StaticHyp (withOrb I o) m :=
  ⟨H.hr, H.hg, H.hAX, H.hSP, H.hJ, H.hregs, H.sX, H.sC, H.sW, H.sA, H.sV, H.sAX, H.sSP⟩

/-! ## 4. Nodes -/

/-- Injectivity and adjacency of the nodes of an admissible chip, in the `AcceptsJ9A` field shape. -/
theorem nodes_ok (q : ChipIn) (ho : OrbOK q) (hn : q.n ≤ 3 * 2 ^ q.h) :
    Function.Injective (nodesOf q) ∧
      ∀ (i : Fin q.n) (hi : (i : ℕ) + 1 < q.n), nodesOf q ⟨(i : ℕ) + 1, hi⟩ = nodesOf q i * q.ω.toZ :=
  ⟨GenPortJ9AHOrb.nodesOf_inj q ho hn, fun i hi => by
    rw [GenPortJ9AHOrb.nodesOf_adj q i hi, mul_comm]⟩

/-- The eight `hinj*`/`hadj*` field types of `AcceptsJ9A` at `Pb`. -/
abbrev NodesFields (Pb : PubJ9A p) : Prop :=
  (Function.Injective Pb.nodes ∧
    ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω) ∧
  (Function.Injective Pb.nodesC ∧
    ∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω) ∧
  (Function.Injective Pb.nodesW ∧
    ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω) ∧
  (Function.Injective Pb.nodesA ∧
    ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω)

theorem nodes_withOrb {I : InJ9A} {o : OrbJ9A} (ho : OrbAdm I o) (hv' : ValidJ9A (withOrb I o)) :
    NodesFields (mkPbA (withOrb I o) hv') :=
  ⟨nodes_ok (reorb I.X o.X) ho.X.1 ho.X.2, nodes_ok (reorb I.C o.C) ho.C.1 ho.C.2,
    nodes_ok (reorb I.W o.W) ho.W.1 ho.W.2, nodes_ok (reorb I.A o.A) ho.A.1 ho.A.2⟩

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA in
#print axioms withOrb_self
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA in
#print axioms interpOf_reorb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA in
#print axioms nodesOf_powN
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA in
#print axioms validJ9A_withOrb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA in
#print axioms orbAdm_self
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA in
#print axioms staticHyp_withOrb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA in
#print axioms nodes_ok
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA in
#print axioms nodes_withOrb
