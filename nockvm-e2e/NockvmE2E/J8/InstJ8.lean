/-
the J-8 `RapAirJ` instance on nock's 4.35 slice.
Stage 1: plumbing at nock's concrete `KC`, the flat column index, `trunc` / `compose_trunc`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface
import NockvmE2E.J8.MinusT
import NockvmE2E.Exec.J8ShapeB
import NockvmE2E.Exec.J8Shape
import Nock.TraceGenExe.K6
import Nock.TraceGenExe.PowerBasis
import Nock.V1J8.Static
import Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial

namespace NockvmE2E.J8.InstJ8

open NockvmE2E.Rap NockvmE2E.Succ
open Nock.TraceGenExe Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crC crM crW crJ crA)

/-! ## 0. plumbing: nock's concrete field -/

/-- the prime, nock's `Nock.Field.p` -/
abbrev P : ℕ := Nock.Field.p

example : P = Nock.Atoms.p := rfl

instance : Fact P.Prime := inferInstance

theorem charP_KC' : CharP KC P := charP_of_injective_algebraMap (algebraMap (ZMod P) KC).injective P

/-- the quadratic extension `𝕂′` -/
abbrev KQ' : Type := Quad (algebraMap (ZMod P) KC deltaF)

example : KQ' = KQ := rfl

open Classical in
theorem charP_KQ' : CharP KQ' P := by
  haveI := charP_KC'
  exact charP_of_injective_algebraMap (algebraMap KC KQ').injective P

/-- the coin frames agree definitionally -/
def Φ0 : CoinFrame := ⟨19, Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8.sampledAfter⟩

example : Coins Φ0 KC = Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC := rfl

theorem hcoin0 : ∀ i : Fin Φ0.n, Φ0.sampledAfter i < 2 := by decide

/-! ## 1. the flat column index -/

/-- the six chips' columns, in the flat order (compute, cell, walkJ8, jet, atom, walkHQK) -/
abbrev Ι : Type := Fin 123 ⊕ Fin 242 ⊕ Fin 166 ⊕ Fin 71 ⊕ Fin 349 ⊕ Fin 166

def colR : Ι → ℕ := Sum.elim crC (Sum.elim crM (Sum.elim crW (Sum.elim crJ (Sum.elim crA crW))))

theorem colR_le : ∀ j, colR j ≤ 2 := by
  intro j
  rcases j with j | j | j | j | j | j
  · simp only [colR, Sum.elim_inl, crC]; split_ifs <;> omega
  · simp only [colR, Sum.elim_inr, Sum.elim_inl, crM]; split_ifs <;> omega
  · simp only [colR, Sum.elim_inr, Sum.elim_inl, crW]; split_ifs <;> omega
  · simp only [colR, Sum.elim_inr, Sum.elim_inl, crJ]; split_ifs <;> omega
  · simp only [colR, Sum.elim_inr, Sum.elim_inl, crA]; split_ifs <;> omega
  · simp only [colR, Sum.elim_inr, Sum.elim_inl, crW]; split_ifs <;> omega

/-- the interface trace as nock's six chip traces -/
def unflat (tr : Ι → (ZMod P)[X]) : TrJ8 (ZMod P) where
  C j := tr (Sum.inl j)
  M j := tr (Sum.inr (Sum.inl j))
  W j := tr (Sum.inr (Sum.inr (Sum.inl j)))
  J j := tr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
  A j := tr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))
  V j := tr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))))

/-- `unflat` carries `TracesStaged` at `colR` to nock's `StJ8` -/
theorem stJ8_unflat (Q : Coins Φ0 KC → Ι → (ZMod P)[X]) (hQ : TracesStaged Φ0 colR Q) :
    StJ8 (fun χ => unflat (Q χ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j χ χ' h; exact hQ (Sum.inl j) χ χ' h
  · intro j χ χ' h; exact hQ (Sum.inr (Sum.inl j)) χ χ' h
  · intro j χ χ' h; exact hQ (Sum.inr (Sum.inr (Sum.inl j))) χ χ' h
  · intro j χ χ' h; exact hQ (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))) χ χ' h
  · intro j χ χ' h; exact hQ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) χ χ' h
  · intro j χ χ' h; exact hQ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))) χ χ' h

/-! ## 2. `trunc` / `compose_trunc` -/

section Trunc
variable {F : Type} [CommRing F]

/-- truncate a chip constraint (variables `(column, row-offset)`, offsets `0,1`) into the interface variables -/
noncomputable def truncP {w : ℕ} {ι : Type} (e : Fin w → ι) :
    MvPolynomial (Fin w × ℕ) F →ₐ[F] MvPolynomial (ι × Fin 2) F :=
  MvPolynomial.bind₁ (fun q : Fin w × ℕ => if h : q.2 < 2 then MvPolynomial.X (e q.1, ⟨q.2, h⟩) else 0)

/-- **`compose_trunc`**: the interface composition of the truncated constraint is the chip's `RAP.compose`
(`ωof` is the row shift of the table of each column, equal to the chip's `ω` on the chip's own columns) -/
theorem compose_trunc (R : Nock.Framework.RAP F) {ι : Type} (e : Fin R.w → ι) (tr : ι → F[X])
    (ωof : ι → F) (hω : ∀ j, ωof (e j) = R.ω)
    (hI : ∀ q ∈ R.I, q.2 < 2) (i : Fin R.s) :
    MvPolynomial.aeval (fun q : ι × Fin 2 => (tr q.1).comp (Polynomial.C (ωof q.1 ^ (q.2 : ℕ)) * Polynomial.X))
        (truncP e (R.C i)) = R.compose (fun j => tr (e j)) i := by
  unfold truncP Nock.Framework.RAP.compose
  rw [MvPolynomial.aeval_bind₁]
  have : ∀ q ∈ (R.C i).vars,
      MvPolynomial.aeval (fun q : ι × Fin 2 => (tr q.1).comp (Polynomial.C (ωof q.1 ^ (q.2 : ℕ)) * Polynomial.X))
        (if h : q.2 < 2 then MvPolynomial.X (e q.1, ⟨q.2, h⟩) else 0 : MvPolynomial (ι × Fin 2) F) =
      (tr (e q.1)).comp (Polynomial.C (R.ω ^ q.2) * Polynomial.X) := by
    intro q hq
    have h2 := hI q (R.C_vars i hq)
    simp [h2, hω]
  exact MvPolynomial.eval₂Hom_congr' rfl (fun q hq _ => this q hq) rfl

end Trunc


/-! ## 3. generic chip lemmas -/

section Generic
variable {F : Type} [Field F]

/-- the fixed polynomial of a column of a chip, if it is one of the chip's preprocessing columns -/
noncomputable def preOf (R : Nock.Framework.FixedPreprocessingRAP F) (c : Fin R.rap.w) : Option F[X] := by
  classical exact if h : ∃ j, R.preprocessingColumn j = c then some (R.preprocessing h.choose) else none

theorem preOf_col (R : Nock.Framework.FixedPreprocessingRAP F) (j : Fin R.fixedCount) :
    preOf R (R.preprocessingColumn j) = some (R.preprocessing j) := by
  classical
  unfold preOf
  have h : ∃ j', R.preprocessingColumn j' = R.preprocessingColumn j := ⟨j, rfl⟩
  rw [dif_pos h]
  have := (R.preprocessingColumn).injective h.choose_spec
  rw [this]

/-- the chip's vanishing, read off the interface composition -/
theorem sat_of_vanish (R : Nock.Framework.RAP F) {ι : Type} (e : Fin R.w → ι) (tr : ι → F[X])
    (ωof : ι → F) (hω : ∀ j, ωof (e j) = R.ω)
    (hI : ∀ q ∈ R.I, q.2 < 2)
    (h : ∀ i : Fin R.s, ∀ x ∈ R.H, (MvPolynomial.aeval
      (fun q : ι × Fin 2 => (tr q.1).comp (Polynomial.C (ωof q.1 ^ (q.2 : ℕ)) * Polynomial.X)) (truncP e (R.C i))).eval x = 0) :
    R.Satisfies (fun j => tr (e j)) := by
  intro i x hx
  rw [← compose_trunc R e tr ωof hω hI i]
  exact h i x hx

/-- the chip's fixed columns, bound -/
theorem binds_of_pre (R : Nock.Framework.FixedPreprocessingRAP F) {ι : Type} (e : Fin R.rap.w → ι) (tr : ι → F[X])
    (pre : ι → Option F[X]) (hpre : ∀ c q, pre (e c) = some q → tr (e c) = q)
    (he : ∀ c, pre (e c) = preOf R c) : R.BindsPreprocessing (fun j => tr (e j)) := by
  intro j
  exact hpre _ _ ((he _).trans (preOf_col R j))

/-- a chip accepted from the interface data -/
theorem chip_ok (R : Nock.Framework.FixedPreprocessingRAP F) {ι : Type} (e : Fin R.rap.w → ι) (tr : ι → F[X])
    (ωof : ι → F) (hω : ∀ j, ωof (e j) = R.rap.ω) (hI : ∀ q ∈ R.rap.I, q.2 < 2)
    (pre : ι → Option F[X]) (hpre : ∀ c q, pre (e c) = some q → tr (e c) = q) (he : ∀ c, pre (e c) = preOf R c)
    (hv : ∀ i : Fin R.rap.s, ∀ x ∈ R.rap.H, (MvPolynomial.aeval
      (fun q : ι × Fin 2 => (tr q.1).comp (Polynomial.C (ωof q.1 ^ (q.2 : ℕ)) * Polynomial.X)) (truncP e (R.rap.C i))).eval x = 0) :
    Nock.Framework.RAP.SatisfiesWithPreprocessing R (fun j => tr (e j)) :=
  ⟨sat_of_vanish R.rap e tr ωof hω hI hv, binds_of_pre R e tr pre hpre he⟩

/-- the row-offset index set of an expanded chip -/
theorem hI_expand {w : ℕ} : ∀ q ∈ (Finset.univ ×ˢ ({0, 1} : Finset ℕ) : Finset (Fin w × ℕ)), q.2 < 2 := by
  intro q hq
  have := (Finset.mem_product.mp hq).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

end Generic


/-! ## 4. the datum, the chips -/

noncomputable section Inst
open Nock.Jet.ChipJ8 (jetChipJ8 layoutJ8 PRow tvKey axPosB)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.V1J8 (PubEqJ8)
open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial Nock.NockVMROM Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4 (RR4 LL4)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5 (R0d L0d)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8NV (hsoundJ8XUG linkXUG_of_R5)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A (hsoundJ8XUA linkXUA_of_R5)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (RR4A)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (wdV_view)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8NV (layLe_ofG)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c4 c5 c6 c7 c11 c12 c15 c16 c2 c3 liftJ8 embJ8 yDep sumJ8 orderJ8 ioSummandJ8 atomDyckJ8 atomCensusJ8 zeroYJ8 bivJ8 specV specH specZY)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (sumJ8C allJ8C DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (sum40 Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (allJ8X atomFpxJ8 withFpxV)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (specVQ specHQ spec01 spec1314 v2 v3 v4 v5 v6 v7 v11 v12 v13 v14 v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (specV specH specZY)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (spec01J8 c0 c1)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (spec01J8 c0 c1)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (specV specH specZY)

/-- the fixed checked datum `(Pb, Rg, c, r, g)` of the interface -/
structure Datum where
  Pb : PubJ8 P
  Rg : Nock.Jet.Registry
  c : P8PublicClaim
  r : RowsJ8
  g : ℕ
  /-- the number of points of the union domain (the prover pads to `hN = 2^(k+1) ≥ max n_t`) -/
  hN : ℕ
  /-- the generator of the union domain `H = {ω^i : i < hN}` (`hShift = 1`) -/
  ω : ZMod P

/-- the union domain `H = {ω^i : i < hN}`: the image of `range hN` (the verifier's `{hShift · hGen^i}` with `hShift = 1`) -/
def HdomOf (d : Datum) : Finset (ZMod P) := (Finset.range d.hN).image (fun i => d.ω ^ i)

/-- the row set of each table -/
def HtOf (d : Datum) : Fin 6 → Finset (ZMod P)
  | 0 => rowNodeSet d.Pb.nodes
  | 1 => rowNodeSet d.Pb.nodesC
  | 2 => rowNodeSet d.Pb.nodesW
  | 3 => rowNodeSet d.Pb.nodesJ
  | 4 => rowNodeSet d.Pb.nodesA
  | 5 => rowNodeSet d.Pb.nodesV

/-- the binders of `soundJ8V_pointwise` / `epsilonOf_listJ8V` / `oneRound_listJ8V`, and the caps -/
structure DatumOK (d : Datum) : Prop where
  hRg : d.Rg.Faithful
  hcK : Fintype.card KC = VclL.Events.cK
  hr : RowsLe d.r EncInjJ8.cornerC
  hqM : ∀ x < ringChar (ZMod P), lenL x ≤ d.r.maxlen
  hk : 2 * fuelChip ≤ d.r.leaves
  hmax : d.Pb.nA + 2 ≤ d.r.maxlen
  hg : d.g ≤ 2 ^ 31
  hLC : d.Pb.n ≤ d.r.N
  hLM : d.Pb.nC ≤ d.r.D
  hLW : d.Pb.nW ≤ d.r.W
  hLA : d.Pb.nA ≤ d.r.A
  hLV : d.Pb.nV ≤ d.r.AW
  hnM : d.Pb.nC ≤ 2 ^ 31
  hreg : (censusG d.Pb d.c).length ≤ 2 ^ 31
  /-- `hHt`: every row set lies in the union domain (from `n_t ≤ hN`; `hHt_PbOfX`) -/
  hHt : ∀ t, HtOf d t ⊆ HdomOf d
  /-- `cap_H`: the union domain has `hN ≤ 2^26` points -/
  hcapH : d.hN ≤ 2 ^ 26

/-- the message: nock's `MsgJ8'` plus the 33 compute publics (`xp`) -/
abbrev Msg : Type := MsgJ8' P KC deltaF × (Fin 33 → ZMod P)

/-- finite codes of messages: claim message in `Fin P`, `ρ`, `ρS`, the five public slices (K-values), `xp` -/
abbrev Mcode : Type :=
  (Fin 3 → Fin P × Fin P × Fin P) × (Fin 5 → KQ') × KQ' × (Fin 6 → KC) × (Fin 8 → KC) × (Fin 4 → KC) ×
    (Fin 12 → KC) × (Fin 8 → KC) × (Fin 33 → ZMod P)

/-- extend a finite list by `0` -/
def ext0 {n : ℕ} (v : Fin n → KC) : ℕ → KC := fun j => if h : j < n then v ⟨j, h⟩ else 0

def decM (m : Mcode) : Msg :=
  (⟨fun k => ((m.1 k).1.val, (m.1 k).2.1.val, (m.1 k).2.2.val), m.2.1, m.2.2.1, ext0 m.2.2.2.1, ext0 m.2.2.2.2.1,
    ext0 m.2.2.2.2.2.1, ext0 m.2.2.2.2.2.2.1, ext0 m.2.2.2.2.2.2.2.1⟩, m.2.2.2.2.2.2.2.2)


attribute [local instance] Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinFact Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinAlg

variable (d : Datum)

def xpF (x : Fin 33 → ZMod P) : ℕ → ZMod P := fun j => if h : j < 33 then x ⟨j, h⟩ else 0

def chipC (χ : Coins Φ0 KC) (M : Msg) :=
  computeChipVCLHX d.Pb.hn d.Pb.nodes powerBasis3 deltaF (chalVJ8 powerBasis3 χ) (xpF M.2) d.Pb.orbit
def chipM (χ : Coins Φ0 KC) (M : Msg) :=
  cellChipHQKW deltaF powerBasis3 d.Pb.hnC d.Pb.nodesC d.Pb.orbitC (chalsMJ8 deltaF χ) M.1.pubsC
def chipW (χ : Coins Φ0 KC) (M : Msg) :=
  walkChipJ8 deltaF d.Pb.kroots powerBasis3 d.Pb.hnW d.Pb.nodesW d.Pb.orbitW (chalsMJ8 deltaF χ) M.1.pubsW
def chipJ (χ : Coins Φ0 KC) (M : Msg) :=
  jetChipJ8 deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (chalsJJ8 χ) M.1.pubsJ d.Pb.lay
def chipA (χ : Coins Φ0 KC) (M : Msg) :=
  atomChipHQL deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA
def chipV (χ : Coins Φ0 KC) (M : Msg) :=
  walkChipHQK deltaF d.Pb.krootsV powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (chalsAJ8Z deltaF χ) M.1.pubsV

/-- the number of constraints of each table (independent of the coins and the message) -/
def sz : Fin 6 → ℕ
  | 0 => (computeChipVCLHX d.Pb.hn d.Pb.nodes powerBasis3 deltaF (fun _ => 0) (fun _ => 0) d.Pb.orbit).rap.s
  | 1 => (cellChipHQKW deltaF powerBasis3 d.Pb.hnC d.Pb.nodesC d.Pb.orbitC (fun _ => 0) (fun _ => 0)).rap.s
  | 2 => (walkChipJ8 deltaF d.Pb.kroots powerBasis3 d.Pb.hnW d.Pb.nodesW d.Pb.orbitW (fun _ => 0) (fun _ => 0)).rap.s
  | 3 => (jetChipJ8 deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (fun _ => 0) (fun _ => 0) d.Pb.lay).rap.s
  | 4 => (atomChipHQL deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (fun _ => 0) (fun _ => 0)).rap.s
  | 5 => (walkChipHQK deltaF d.Pb.krootsV powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (fun _ => 0) (fun _ => 0)).rap.s

/-- the constraint `l` of table `t`, truncated into the interface variables -/
def consT (χ : Coins Φ0 KC) (M : Msg) : (t : Fin 6) → Fin (sz d t) → MvPolynomial (Ι × Fin 2) (ZMod P)
  | 0, l => truncP (fun j => (Sum.inl (Fin.cast (computeChipVCLHX_width d.Pb.hn d.Pb.nodes powerBasis3 deltaF
      (chalVJ8 powerBasis3 χ) (xpF M.2) d.Pb.orbit) j) : Ι)) ((chipC d χ M).rap.C l)
  | 1, l => truncP (fun j => (Sum.inr (Sum.inl (Fin.cast (CellTwinKW.cellChipHQKW_width deltaF powerBasis3 d.Pb.hnC d.Pb.nodesC
      d.Pb.orbitC (chalsMJ8 deltaF χ) M.1.pubsC) j)) : Ι)) ((chipM d χ M).rap.C l)
  | 2, l => truncP (fun j => (Sum.inr (Sum.inr (Sum.inl (Fin.cast (WalkJ8.walkChipJ8_width deltaF d.Pb.kroots powerBasis3 d.Pb.hnW
      d.Pb.nodesW d.Pb.orbitW (chalsMJ8 deltaF χ) M.1.pubsW) j))) : Ι)) ((chipW d χ M).rap.C l)
  | 3, l => truncP (fun j => (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Fin.cast (Nock.Jet.ChipJ8.jetChipJ8_width deltaF powerBasis3
      d.Pb.nodesJ d.Pb.orbitJ (chalsJJ8 χ) M.1.pubsJ d.Pb.lay) j)))) : Ι)) ((chipJ d χ M).rap.C l)
  | 4, l => truncP (fun j => (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Fin.cast (AtomChipHQL.atomChipHQL_width deltaF powerBasis3
      d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA) j))))) : Ι)) ((chipA d χ M).rap.C l)
  | 5, l => truncP (fun j => (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Fin.cast (CellTwinK.walkChipHQK_width deltaF d.Pb.krootsV
      powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (chalsAJ8Z deltaF χ) M.1.pubsV) j))))) : Ι)) ((chipV d χ M).rap.C l)


theorem truncP_deg {w : ℕ} {ι : Type} (e : Fin w → ι) (q : MvPolynomial (Fin w × ℕ) (ZMod P)) :
    (truncP e q).totalDegree ≤ q.totalDegree := by
  refine totalDegree_bind₁_le _ (fun s => ?_) q
  split_ifs
  · simp [MvPolynomial.totalDegree_X]
  · simp

/-- the row shift of each table -/
def omegaOf : Fin 6 → ZMod P
  | 0 => d.Pb.orbit.ω
  | 1 => d.Pb.orbitC.ω
  | 2 => d.Pb.orbitW.ω
  | 3 => d.Pb.orbitJ.ω
  | 4 => d.Pb.orbitA.ω
  | 5 => d.Pb.orbitV.ω

def tabΙ : Ι → Fin 6 :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (Sum.elim (fun _ => 2) (Sum.elim (fun _ => 3)
    (Sum.elim (fun _ => 4) (fun _ => 5)))))

/-- the fixed columns (zero coins: the preprocessing does not read them) -/
def preJ : Ι → Option (ZMod P)[X]
  | Sum.inl c => preOf (computeChipVCLHX d.Pb.hn d.Pb.nodes powerBasis3 deltaF (fun _ => 0) (fun _ => 0) d.Pb.orbit)
      (Fin.cast (computeChipVCLHX_width d.Pb.hn d.Pb.nodes powerBasis3 deltaF (fun _ => 0) (fun _ => 0) d.Pb.orbit).symm c)
  | Sum.inr (Sum.inl c) => preOf (cellChipHQKW deltaF powerBasis3 d.Pb.hnC d.Pb.nodesC d.Pb.orbitC (fun _ => 0) (fun _ => 0))
      (Fin.cast (CellTwinKW.cellChipHQKW_width deltaF powerBasis3 d.Pb.hnC d.Pb.nodesC d.Pb.orbitC (fun _ => 0) (fun _ => 0)).symm c)
  | Sum.inr (Sum.inr (Sum.inl c)) => preOf (walkChipJ8 deltaF d.Pb.kroots powerBasis3 d.Pb.hnW d.Pb.nodesW d.Pb.orbitW (fun _ => 0) (fun _ => 0))
      (Fin.cast (WalkJ8.walkChipJ8_width deltaF d.Pb.kroots powerBasis3 d.Pb.hnW d.Pb.nodesW d.Pb.orbitW (fun _ => 0) (fun _ => 0)).symm c)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl c))) => preOf (jetChipJ8 deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (fun _ => 0) (fun _ => 0) d.Pb.lay)
      (Fin.cast (Nock.Jet.ChipJ8.jetChipJ8_width deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (fun _ => 0) (fun _ => 0) d.Pb.lay).symm c)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c)))) => preOf (atomChipHQL deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (fun _ => 0) (fun _ => 0))
      (Fin.cast (AtomChipHQL.atomChipHQL_width deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (fun _ => 0) (fun _ => 0)).symm c)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr c)))) => preOf (walkChipHQK deltaF d.Pb.krootsV powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (fun _ => 0) (fun _ => 0))
      (Fin.cast (CellTwinK.walkChipHQK_width deltaF d.Pb.krootsV powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (fun _ => 0) (fun _ => 0)).symm c)

/-- **`Pub`**: the eight public equations, `hclI`, absent ⇒ publics `0`, the derived compute publics -/
def PubP (χ : Coins Φ0 KC) (M : Msg) : Prop :=
  PubEqJ8 deltaF powerBasis3 d.Pb d.c χ M.1 ∧
  (∀ k : Fin 3, isCellN (claimNoun d.c k) = true → (M.1.m k).1 < P) ∧
  ((d.Pb.krootsV = 0 → M.1.pubsV 0 = 0 ∧ M.1.pubsV 1 = 0 ∧ M.1.pubsV WalkHQ.pubXQ = 0 ∧ M.1.pubsV (WalkHQ.pubXQ + 1) = 0 ∧
      M.1.pubsV WalkHQ.pubPQ = 0 ∧ M.1.pubsV (WalkHQ.pubPQ + 1) = 0) ∧
    (d.Pb.nJ = 0 → M.1.pubsJ 0 = 0 ∧ M.1.pubsJ 1 = 0 ∧ M.1.pubsJ 2 = 0 ∧ M.1.pubsJ 3 = 0)) ∧
  (∀ j : Fin 33, M.2 j = pubVJ8 deltaF powerBasis3 d.c M.1.m M.1.ρ M.1.ρS χ j)

/-- the static (statement-level) conjuncts of `AcceptsJ8V` -/
structure StmtP : Prop where
  hinjX : Function.Injective d.Pb.nodes
  hadjX : ∀ (i : Fin d.Pb.n) (hi : (i : ℕ) + 1 < d.Pb.n), d.Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodes i * d.Pb.orbit.ω
  hinjC : Function.Injective d.Pb.nodesC
  hadjC : ∀ (i : Fin d.Pb.nC) (hi : (i : ℕ) + 1 < d.Pb.nC), d.Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesC i * d.Pb.orbitC.ω
  hnpC : d.Pb.nC < ringChar (ZMod P)
  hinjW : Function.Injective d.Pb.nodesW
  hadjW : ∀ (i : Fin d.Pb.nW) (hi : (i : ℕ) + 1 < d.Pb.nW), d.Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesW i * d.Pb.orbitW.ω
  hkW : 1 ≤ d.Pb.kroots
  hknW : d.Pb.kroots ≤ d.Pb.nW
  hkpW : d.Pb.kroots + d.Pb.nW < ringChar (ZMod P)
  hJst : d.Pb.nJ ≠ 0 → Function.Injective d.Pb.nodesJ ∧
    ∀ (i : Fin d.Pb.nJ) (hi : (i : ℕ) + 1 < d.Pb.nJ), d.Pb.nodesJ ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesJ i * d.Pb.orbitJ.ω
  hinjA : Function.Injective d.Pb.nodesA
  hadjA : ∀ (i : Fin d.Pb.nA) (hi : (i : ℕ) + 1 < d.Pb.nA), d.Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesA i * d.Pb.orbitA.ω
  hnpA : d.Pb.nA < P
  hVst : d.Pb.krootsV ≠ 0 → Function.Injective d.Pb.nodesV ∧
    (∀ (i : Fin d.Pb.nV) (hi : (i : ℕ) + 1 < d.Pb.nV), d.Pb.nodesV ⟨(i : ℕ) + 1, hi⟩ = d.Pb.nodesV i * d.Pb.orbitV.ω) ∧
    1 ≤ d.Pb.krootsV ∧ d.Pb.krootsV ≤ d.Pb.nV ∧ d.Pb.krootsV + d.Pb.nV < ringChar (ZMod P)
  hlay : List.ofFn d.Pb.lay = layoutJ8 d.Pb.Rt d.Pb.regs d.Pb.ids
  hsmall : ∀ q ∈ layoutJ8 d.Pb.Rt d.Pb.regs d.Pb.ids, q.id < P ∧ q.cid < P ∧ q.nid < P ∧ q.n1 < P ∧ q.n2 < P
  huniq : ((layoutJ8 d.Pb.Rt d.Pb.regs d.Pb.ids).filterMap tvKey).Nodup
  hTpl : ∀ i ∈ d.Pb.regs, d.Rg i = some ⟨(d.Pb.Rt i).toTemplate P, Nock.Jet.Autogen.compile P (d.Pb.Rt i)⟩ ∧
    axPosB (d.Pb.Rt i) = true ∧ (d.Pb.Rt i).WellTyped P
  hnd : d.Pb.regs.Nodup
  hidx : ∀ id ∈ d.Pb.regs, d.Pb.idx id < P
  hrk : ∀ id ∈ d.Pb.regs, d.Pb.rk id ≠ (0, 0)
  hlt : ∀ id ∈ d.Pb.regs, (d.Pb.rk id).1 < ringChar (ZMod P) ∧ (d.Pb.rk id).2 < ringChar (ZMod P) ∧
    d.Pb.idx id < ringChar (ZMod P)
  hclA : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v → v < P
  hclR : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → (claimNoun d.c k).internal / 2 ^ 62 < P
  hcen : ∀ x ∈ censusG d.Pb d.c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, v < P
  hlenC : 3 + d.Pb.regs.length + 2 * d.Pb.nC < P
  hlenA : d.Pb.nA + d.Pb.nV < P
  hcellF : isCellN d.c.formula = true
  hnA62 : d.Pb.nA ≤ 2 ^ 62
  hbud : RealIOJ8.BudJ8 d.Pb d.r (d.g + d.r.N)
  hbudV : d.Pb.regs.length ≤ d.g ∧ d.Pb.nA ≤ d.r.mb ∧ d.Pb.nA ≤ d.r.A ∧ d.Pb.nV ≤ d.r.AW

/-- the tables present at the J-8 side -/
def presentJ8 (t : Fin 6) : Prop := ¬(t = 3 ∧ d.Pb.nJ = 0) ∧ ¬(t = 5 ∧ d.Pb.krootsV = 0)

theorem accGen (hd : DatumOK d) (χ : Coins Φ0 KC) (M : Msg) (tr : Ι → (ZMod P)[X])
    (hv : ∀ t : Fin 6, presentJ8 d t → ∀ l : Fin (sz d t), ∀ x ∈ HtOf d t, (MvPolynomial.aeval
      (fun q : Ι × Fin 2 => (tr q.1).comp (Polynomial.C (omegaOf d (tabΙ q.1) ^ (q.2 : ℕ)) * Polynomial.X))
      (consT d χ M t l)).eval x = 0)
    (hp : PubP d χ M) (hs : StmtP d)
    (hpre : ∀ j c, presentJ8 d (tabΙ j) → preJ d j = some c → tr j = c) :
    AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 d.Pb d.Rg d.c χ M.1 (unflat tr) d.r d.g := by
  obtain ⟨hPE, hclI, ⟨habsV, habsJ⟩, hder⟩ := hp
  obtain ⟨hGx, hGp, hGS, hsumC', hbalA', hvalA0, hfxC, hfxA⟩ := hPE
  have hxp : xpF M.2 = pubVJ8 deltaF powerBasis3 d.c M.1.m M.1.ρ M.1.ρS χ := by
    funext j
    unfold xpF
    split_ifs with h
    · exact hder ⟨j, h⟩
    · have h27 : ¬ j < 27 := by omega
      have h30 : ¬ j < 30 := by omega
      simp [pubVJ8, h27, h30, h]
  have hp0 : presentJ8 d 0 := by unfold presentJ8; simp
  have hp1 : presentJ8 d 1 := by unfold presentJ8; simp
  have hp2 : presentJ8 d 2 := by unfold presentJ8; simp
  have hp4 : presentJ8 d 4 := by unfold presentJ8; simp
  have cX : ∀ pv, xpF M.2 = pv → RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX d.Pb.hn d.Pb.nodes powerBasis3 deltaF (chalVJ8 powerBasis3 χ) pv d.Pb.orbit)
      (fun j => tr (Sum.inl (Fin.cast (computeChipVCLHX_width d.Pb.hn d.Pb.nodes powerBasis3 deltaF
        (chalVJ8 powerBasis3 χ) pv d.Pb.orbit) j))) := by
    intro pv hpv
    subst hpv
    exact chip_ok (chipC d χ M) _ tr (fun q => omegaOf d (tabΙ q)) (fun j => rfl) (hI_expand) (preJ d)
      (fun c q hj => hpre _ q hp0 hj) (fun c => rfl) (fun i x hx => hv 0 hp0 i x hx)
  have cM := chip_ok (chipM d χ M) (fun j => (Sum.inr (Sum.inl (Fin.cast (CellTwinKW.cellChipHQKW_width deltaF powerBasis3
      d.Pb.hnC d.Pb.nodesC d.Pb.orbitC (chalsMJ8 deltaF χ) M.1.pubsC) j)) : Ι)) tr (fun q => omegaOf d (tabΙ q))
      (fun j => rfl) (hI_expand) (preJ d) (fun c q hj => hpre _ q hp1 hj) (fun c => rfl) (fun i x hx => hv 1 hp1 i x hx)
  have cW := chip_ok (chipW d χ M) (fun j => (Sum.inr (Sum.inr (Sum.inl (Fin.cast (WalkJ8.walkChipJ8_width deltaF d.Pb.kroots
      powerBasis3 d.Pb.hnW d.Pb.nodesW d.Pb.orbitW (chalsMJ8 deltaF χ) M.1.pubsW) j))) : Ι)) tr (fun q => omegaOf d (tabΙ q))
      (fun j => rfl) (hI_expand) (preJ d) (fun c q hj => hpre _ q hp2 hj) (fun c => rfl) (fun i x hx => hv 2 hp2 i x hx)
  have cA := chip_ok (chipA d χ M) (fun j => (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Fin.cast
      (AtomChipHQL.atomChipHQL_width deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA) j))))) : Ι))
      tr (fun q => omegaOf d (tabΙ q))
      (fun j => rfl) (hI_expand) (preJ d) (fun c q hj => hpre _ q hp4 hj) (fun c => rfl) (fun i x hx => hv 4 hp4 i x hx)
  have hJk : JGenJ8.JChipOK deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (chalsJJ8 χ) M.1.pubsJ d.Pb.lay
      (AcceptsJ8.qJ deltaF powerBasis3 d.Pb (unflat tr) (chalsJJ8 χ) M.1.pubsJ) := by
    by_cases h0 : d.Pb.nJ = 0
    · obtain ⟨a, b, c, e⟩ := habsJ h0
      exact Or.inr ⟨h0, a, b, c, e⟩
    · have hp3 : presentJ8 d 3 := by unfold presentJ8; simp [h0]
      have cJ := chip_ok (chipJ d χ M) (fun j => (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Fin.cast
        (Nock.Jet.ChipJ8.jetChipJ8_width deltaF powerBasis3 d.Pb.nodesJ d.Pb.orbitJ (chalsJJ8 χ) M.1.pubsJ d.Pb.lay) j)))) : Ι))
        tr (fun q => omegaOf d (tabΙ q)) (fun j => rfl) (hI_expand) (preJ d) (fun c q hj => hpre _ q hp3 hj) (fun c => rfl)
        (fun i x hx => hv 3 hp3 i x hx)
      obtain ⟨hinj, hadj⟩ := hs.hJst h0
      exact Or.inl ⟨cJ.1, cJ.2, hinj, Nat.pos_of_ne_zero h0, hadj⟩
  have hVk : AcceptsJ8V.AWChipOK deltaF powerBasis3 d.Pb.krootsV d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (chalsAJ8Z deltaF χ)
      M.1.pubsV (AcceptsJ8.qV deltaF powerBasis3 d.Pb (unflat tr) (chalsAJ8Z deltaF χ) M.1.pubsV) := by
    by_cases h0 : d.Pb.krootsV = 0
    · obtain ⟨a, b, c, e, f, g⟩ := habsV h0
      exact Or.inr ⟨h0, a, b, c, e, f, g⟩
    · have hp5 : presentJ8 d 5 := by unfold presentJ8; simp [h0]
      have cV := chip_ok (chipV d χ M) (fun j => (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Fin.cast
        (CellTwinK.walkChipHQK_width deltaF d.Pb.krootsV powerBasis3 d.Pb.hnV d.Pb.nodesV d.Pb.orbitV (chalsAJ8Z deltaF χ)
          M.1.pubsV) j))))) : Ι))
        tr (fun q => omegaOf d (tabΙ q)) (fun j => rfl) (hI_expand) (preJ d) (fun c q hj => hpre _ q hp5 hj) (fun c => rfl)
        (fun i x hx => hv 5 hp5 i x hx)
      obtain ⟨hinj, hadj, h1, h2, h3⟩ := hs.hVst h0
      exact Or.inl ⟨cV.1, cV.2, hinj, hadj, h1, h2, h3⟩
  have hL : (atomChipHQL deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA).rap.Satisfies
      (AcceptsJ8L.qAL deltaF powerBasis3 d.Pb (unflat tr) (chalsAJ8Z deltaF χ) M.1.pubsA) := cA.1
  have hLb : (atomChipHQL deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA).BindsPreprocessing
      (AcceptsJ8L.qAL deltaF powerBasis3 d.Pb (unflat tr) (chalsAJ8Z deltaF χ) M.1.pubsA) := cA.2
  have hA1 := AtomChipHQL.atomChipHQL_sat deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA _ hL
  have hA2 := AtomChipHQL.atomChipHQL_bind deltaF powerBasis3 d.Pb.hnA d.Pb.nodesA d.Pb.orbitA (chalsAJ8Z deltaF χ) M.1.pubsA _ hLb
  rw [AcceptsJ8L.qAL_toHQ] at hA1 hA2
  exact
    { hsatX := cX _ hxp
      hinjX := hs.hinjX
      hadjX := hs.hadjX
      hsatC := cM.1
      hbindC := cM.2
      hinjC := hs.hinjC
      hadjC := hs.hadjC
      hnpC := hs.hnpC
      hsatW := cW.1
      hbindW := cW.2
      hinjW := hs.hinjW
      hadjW := hs.hadjW
      hkW := hs.hkW
      hknW := hs.hknW
      hkpW := hs.hkpW
      hJk := hJk
      hsatA := hA1
      hbindA := hA2
      hinjA := hs.hinjA
      hadjA := hs.hadjA
      hnpA := hs.hnpA
      hVk := hVk
      hGx := hGx
      hGp := hGp
      hGS := hGS
      hlay := hs.hlay
      hsmall := hs.hsmall
      huniq := hs.huniq
      hTpl := hs.hTpl
      hnd := hs.hnd
      hidx := hs.hidx
      hrk := hs.hrk
      hlt := hs.hlt
      hsumC' := hsumC'
      hbalA' := hbalA'
      hvalA0 := hvalA0
      hfxC := hfxC
      hfxA := hfxA
      hclA := hs.hclA
      hclI := hclI
      hclR := hs.hclR
      hcen := hs.hcen
      hlenC := hs.hlenC
      hlenA := hs.hlenA
      hcellF := hs.hcellF
      hnA62 := hs.hnA62
      hbud := hs.hbud
      hbudV := hs.hbudV
      hsatL := cA.1
      hbindL := cA.2 }


/-! ## 5. the instance -/

def ns : ℕ := ∑ t : Fin 6, sz d t

def Cfun (χ : Coins Φ0 KC) (M : Msg) (i : Fin (ns d)) : MvPolynomial (Ι × Fin 2) (ZMod P) :=
  consT d χ M (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2

def tabSfun (i : Fin (ns d)) : Fin 6 := (finSigmaFinEquiv.symm i).1

theorem consT_deg (χ : Coins Φ0 KC) (M : Msg) (t : Fin 6) (l : Fin (sz d t)) : (consT d χ M t l).totalDegree ≤ 4 := by
  match t, l with
  | 0, l => exact (truncP_deg _ _).trans ((chipC d χ M).rap.C_deg l)
  | 1, l => exact (truncP_deg _ _).trans ((chipM d χ M).rap.C_deg l)
  | 2, l => exact (truncP_deg _ _).trans ((chipW d χ M).rap.C_deg l)
  | 3, l => exact (truncP_deg _ _).trans ((chipJ d χ M).rap.C_deg l)
  | 4, l => exact (truncP_deg _ _).trans ((chipA d χ M).rap.C_deg l)
  | 5, l => exact (truncP_deg _ _).trans ((chipV d χ M).rap.C_deg l)

/-- the nock summand as one of our twin -/
def ofNock {Tr : Type} {St : (Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC → Tr) → Prop}
    (s : Nock.NockVMROM.Thm54.SVFrame.BadSummand Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC Tr St) :
    NockvmE2E.Rap.BadSummand Φ0 KC Tr St where
  coins := s.coins
  dep := s.dep
  disj := s.disj
  badSet := s.badSet
  weight := s.weight
  card_le := s.card_le
  readsOn := fun Q hQ χ χ' h => s.readsOn Q hQ χ χ' h

theorem vanish_conv (χ : Coins Φ0 KC) (M : Msg) (tr : Ι → (ZMod P)[X])
    (h : ∀ i : Fin (ns d), ∀ x ∈ HtOf d (tabSfun d i), (MvPolynomial.aeval
      (fun q : Ι × Fin 2 => (tr q.1).comp (Polynomial.C (omegaOf d (tabΙ q.1) ^ (q.2 : ℕ)) * Polynomial.X))
      (Cfun d χ M i)).eval x = 0) :
    ∀ t : Fin 6, ∀ l : Fin (sz d t), ∀ x ∈ HtOf d t, (MvPolynomial.aeval
      (fun q : Ι × Fin 2 => (tr q.1).comp (Polynomial.C (omegaOf d (tabΙ q.1) ^ (q.2 : ℕ)) * Polynomial.X))
      (consT d χ M t l)).eval x = 0 := by
  intro t l x hx
  have := h (finSigmaFinEquiv ⟨t, l⟩) x (by simpa [tabSfun] using hx)
  unfold Cfun at this
  rw [Equiv.symm_apply_apply] at this
  exact this

set_option maxRecDepth 100000 in
theorem card_Ι : Fintype.card Ι = 1117 := by
  simp only [Fintype.card_sum, Fintype.card_fin]

theorem cap_H_of (hd : DatumOK d) : (HdomOf d).card ≤ 2 ^ 26 :=
  (Finset.card_image_le.trans (by simpa using hd.hcapH))

set_option maxRecDepth 100000 in
theorem len_walkJ8 (k : ℕ) : ((WalkJ8.walkTemplateJ8 deltaF k).allGates powerBasis3).length ≤ 5000 := by
  have e : ((WalkJ8.walkTemplateJ8 deltaF k).allGates powerBasis3).length =
      ((WalkJ8.walkTemplateJ8 deltaF 0).allGates powerBasis3).length := rfl
  rw [e]; decide

set_option maxRecDepth 100000 in
theorem len_walkHQK (k : ℕ) : ((CellTwinK.walkTemplateHQK deltaF k).allGates powerBasis3).length ≤ 5000 := by
  have e : ((CellTwinK.walkTemplateHQK deltaF k).allGates powerBasis3).length =
      ((CellTwinK.walkTemplateHQK deltaF 0).allGates powerBasis3).length := rfl
  rw [e]; decide

set_option maxRecDepth 100000 in
theorem len_compute : (gatesHX powerBasis3 deltaF).length ≤ 5000 := by decide

set_option maxRecDepth 100000 in
theorem len_cell : ((CellTwinKW.cellTemplateHQKW deltaF).allGates powerBasis3).length ≤ 5000 := by decide

set_option maxRecDepth 100000 in
theorem len_atom : ((AtomChipHQL.atomTemplateHQL deltaF).allGates powerBasis3).length ≤ 5000 := by decide

set_option maxRecDepth 100000 in
theorem len_jet : ((Nock.Jet.ChipJ8.jetTemplateJ8T deltaF).allGates powerBasis3).length ≤ 5000 := by decide

theorem sz_le (t : Fin 6) : sz d t ≤ 5000 := by
  fin_cases t
  · exact len_compute
  · exact len_cell
  · exact len_walkJ8 _
  · exact len_jet
  · exact len_atom
  · exact len_walkHQK _

theorem cap_ns_of : ns d ≤ 2 ^ 20 := by
  unfold ns
  calc ∑ t, sz d t ≤ ∑ _t : Fin 6, 5000 := Finset.sum_le_sum fun t _ => sz_le d t
    _ = 30000 := by simp
    _ ≤ 2 ^ 20 := by norm_num

open Classical in
/-- **the J-8 interface instance** -/
noncomputable def J8 (hd : DatumOK d) : RapAirJ (ZMod P) KC where
  Φ0 := Φ0
  ι0 := Ι
  fι := inferInstance
  dι := inferInstance
  colRound0 := colR
  hround := colR_le
  hcoin := hcoin0
  pre := preJ d
  Msg := Msg
  Mcode := Mcode
  fM := inferInstance
  dM := inferInstance
  dec := decM
  Acc χ M tr := AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 d.Pb d.Rg d.c χ M.1 (unflat tr) d.r d.g
  Holds := Nock.Jet.HoldsN d.c
  summands := (Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.listJ8V deltaF powerBasis3 d.Pb d.c d.r d.g hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg).map
    (fun s => pullback unflat stJ8_unflat (ofNock s))
  sound := by
    intro χ M tr h hs
    haveI := charP_KC'
    haveI := charP_KQ'
    refine Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.soundJ8V_pointwise deltaF powerBasis3 d.Pb hd.hRg d.c rfl hd.hr hd.hqM hd.hk hd.hmax hd.hg hd.hLC hd.hLM
      hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg χ M.1 (unflat tr) h ?_
    intro s hsL hmem
    exact hs _ (List.mem_map_of_mem hsL) hmem
  eps := by
    have h1 : NockvmE2E.Rap.epsilonOf ((Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.listJ8V deltaF powerBasis3 d.Pb d.c d.r d.g hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV
        hd.hnM hd.hreg).map (fun s => pullback unflat stJ8_unflat (ofNock s))) =
        Nock.NockVMROM.Thm54.SVFrame.epsilonOf (Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.listJ8V deltaF powerBasis3 d.Pb d.c d.r d.g hd.hLC hd.hLM hd.hLW hd.hLA
          hd.hLV hd.hnM hd.hreg) := by
      have := epsilonOf_map_pullback (K := KC) unflat stJ8_unflat
        ((Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.listJ8V deltaF powerBasis3 d.Pb d.c d.r d.g hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg).map ofNock)
      rw [List.map_map] at this
      rw [show (fun s => pullback unflat stJ8_unflat (ofNock s)) = (pullback unflat stJ8_unflat) ∘ ofNock from rfl, this]
      unfold NockvmE2E.Rap.epsilonOf Nock.NockVMROM.Thm54.SVFrame.epsilonOf
      simp only [List.map_map]
      rfl
    have h2 := Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.epsilonOf_listJ8V deltaF powerBasis3 d.Pb d.c hd.hcK hd.hr hd.hg hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV
      hd.hnM hd.hreg
    rw [h1]
    exact h2.le
  oneRound := by
    intro s hs
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hs
    have := Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.oneRound_listJ8V deltaF powerBasis3 d.Pb d.c d.r d.g hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg n hn
    exact ⟨this.ne, this.same, this.dep_le⟩
  H := HdomOf d
  T := 6
  Ht := HtOf d
  hHt := hd.hHt
  ωt := omegaOf d
  r := 2
  off t k := omegaOf d t ^ (k : ℕ)
  hoff t k := rfl
  tabC := tabΙ
  ns := ns d
  tabS := tabSfun d
  d := 4
  hd2 := Or.inl (by norm_num)
  C := Cfun d
  hdeg χ M i := consT_deg d χ M _ _
  hCreads M i χ χ' h := by
    have : χ = χ' := funext fun j => h j (Finset.mem_univ j)
    rw [this]
  Pub := PubP d
  StmtOK := StmtP d
  acc_of := by
    intro χ M tr hv hp hs hpre
    exact accGen d hd χ M tr (fun t _ => vanish_conv d χ M tr hv t) hp hs (fun j c _ => hpre j c)
  cap_ns := cap_ns_of d
  cap_d := by norm_num
  cap_m := by
    rw [card_Ι]; norm_num
  cap_H := cap_H_of d hd


set_option maxRecDepth 50000 in
/-- **`accOn_J8`**: the J-8 interface accepts as soon as the constraints of the PRESENT tables vanish (the absent jet / atom walk
are read off `PubP`'s absent publics, not off the trace) -/
theorem accOn_J8 (hd : DatumOK d) : (J8 d hd).AccOn (presentJ8 d) := by
  intro χ M tr hv hp hs hpre
  refine accGen d hd χ M tr ?_ hp hs (fun j c hj => hpre j c hj)
  intro t ht l x hx
  have e : tabSfun d (finSigmaFinEquiv ⟨t, l⟩) = t := by unfold tabSfun; rw [Equiv.symm_apply_apply]
  have ht' : presentJ8 d (tabSfun d (finSigmaFinEquiv ⟨t, l⟩)) := by rw [e]; exact ht
  have hx' : x ∈ HtOf d (tabSfun d (finSigmaFinEquiv ⟨t, l⟩)) := by rw [e]; exact hx
  have h1 := hv (finSigmaFinEquiv ⟨t, l⟩) ht' x hx'
  have h2 : (MvPolynomial.aeval
      (fun q : Ι × Fin 2 => (tr q.1).comp (Polynomial.C (omegaOf d (tabΙ q.1) ^ (q.2 : ℕ)) * Polynomial.X))
      (Cfun d χ M (finSigmaFinEquiv ⟨t, l⟩))).eval x = 0 := h1
  unfold Cfun at h2
  rw [Equiv.symm_apply_apply] at h2
  exact h2


/-! ## 6. `PbOfX`: the uniform `PubJ8` of an executable instance -/

section PbOf
open NockvmE2E.Exec.V (ExecInst TabInst)
open NockvmE2E.Exec.VL (zv)
open NockvmE2E.Exec.J8Shape (j8ShapeOk orbit_order_of_shape hle_of_shape hn32_of_shape)

/-- the table of the instance with this chip id -/
def tabOf (XI : ExecInst) (id : String) : Option TabInst := XI.tabs.toList.find? (fun t => t.chip.id == id)

/-- its row count (`0` if absent) -/
def hNof (XI : ExecInst) (id : String) : ℕ := ((tabOf XI id).map (·.hN)).getD 0

/-- the single trace-domain orbit of every table (`ω = zv hGen`, `β = 1`, exact order `3·2^(k+1)`) -/
def orbX (XI : ExecInst) (hsh : j8ShapeOk XI = true) : StrictOrbitDomain (ZMod P) 3 (XI.k + 1) :=
  ⟨zv XI.hGen, 1, by omega, by omega, orbit_order_of_shape hsh, one_ne_zero⟩

/-- the positivity side conditions of `PbOfX`: the four mandatory tables have rows (`tabsOk`: `1 ≤ t.hN`; `mandatoryOk`) -/
def PosX (XI : ExecInst) : Prop :=
  0 < hNof XI "computeChipVCLHX" ∧ 0 < hNof XI "cellChipHQKW" ∧ 0 < hNof XI "walkChipJ8" ∧ 0 < hNof XI "atomChipHQL" ∧
    ((tabOf XI "walkChipHQK").isSome → 0 < hNof XI "walkChipHQK")

/-- **`PbOfX`**: every table gets `h := k+1`, the orbit `orbX`, `n_t := hN_t` and `nodes_t i := ω^i`. An absent jet has `nJ = 0`;
an absent atom walk has `nV = 1`, `nodesV 0 = 1`, `krootsV = 0`. -/
def PbOfX (XI : ExecInst) (hsh : j8ShapeOk XI = true) (hpos : PosX XI) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) : PubJ8 P where
  h := XI.k + 1
  n := hNof XI "computeChipVCLHX"
  hn := hpos.1
  nodes i := zv XI.hGen ^ (i : ℕ)
  orbit := orbX XI hsh
  hC := XI.k + 1
  nC := hNof XI "cellChipHQKW"
  hnC := hpos.2.1
  nodesC i := zv XI.hGen ^ (i : ℕ)
  orbitC := orbX XI hsh
  kroots := kroots
  hW := XI.k + 1
  nW := hNof XI "walkChipJ8"
  hnW := hpos.2.2.1
  nodesW i := zv XI.hGen ^ (i : ℕ)
  orbitW := orbX XI hsh
  hJ := XI.k + 1
  nJ := hNof XI "jetChipJ8"
  nodesJ i := zv XI.hGen ^ (i : ℕ)
  orbitJ := orbX XI hsh
  lay := lay
  hA := XI.k + 1
  nA := hNof XI "atomChipHQL"
  hnA := hpos.2.2.2.1
  nodesA i := zv XI.hGen ^ (i : ℕ)
  orbitA := orbX XI hsh
  krootsV := if (tabOf XI "walkChipHQK").isSome then krootsV else 0
  hV := XI.k + 1
  nV := if (tabOf XI "walkChipHQK").isSome then hNof XI "walkChipHQK" else 1
  hnV := by
    by_cases h : (tabOf XI "walkChipHQK").isSome = true
    · simp only [h, if_true]; exact hpos.2.2.2.2 h
    · simp only [h, if_false]; exact Nat.one_pos
  nodesV i := zv XI.hGen ^ (i : ℕ)
  orbitV := orbX XI hsh
  Rt := Rt
  regs := regs
  ids := ids
  idx := idx
  rk := rk

theorem hNof_le (XI : ExecInst) (hsh : j8ShapeOk XI = true) (id : String) : hNof XI id ≤ XI.hN := by
  unfold hNof tabOf
  cases h : XI.tabs.toList.find? (fun t => t.chip.id == id) with
  | none => simp
  | some t => simpa using hle_of_shape hsh t (List.mem_of_find?_eq_some h)

theorem nV_le (XI : ExecInst) (hsh : j8ShapeOk XI = true) (hk : 1 ≤ XI.hN) :
    (if (tabOf XI "walkChipHQK").isSome then hNof XI "walkChipHQK" else 1) ≤ XI.hN := by
  split_ifs
  · exact hNof_le XI hsh _
  · exact hk

theorem hN_of_shape' {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.hN = 2 ^ (XI.k + 1) :=
  NockvmE2E.Exec.J8Shape.hN_of_shape h

theorem nD_of_shape' {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.nD = XI.k + 7 := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

theorem k_le_25 {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.k ≤ 25 := by
  have := hn32_of_shape h
  rw [nD_of_shape' h] at this
  omega

theorem hN_lt_p {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.hN < P := by
  rw [hN_of_shape' h]
  calc 2 ^ (XI.k + 1) ≤ 2 ^ 26 := Nat.pow_le_pow_right (by norm_num) (by have := k_le_25 h; omega)
    _ < P := by norm_num [P, Nock.Field.p]

/-- the generator as an element of `ZMod P` -/
def ω0 (XI : ExecInst) : ZMod P := zv XI.hGen

/-- injectivity of the nodes `ω^i`, `i < n ≤ hN` -/
theorem inj_pows {XI : ExecInst} (h : j8ShapeOk XI = true) {n : ℕ} (hn : n ≤ XI.hN) :
    Function.Injective (fun i : Fin n => ω0 XI ^ (i : ℕ)) := by
  intro i j hij
  have ho : orderOf (ω0 XI) = 3 * 2 ^ (XI.k + 1) := orbit_order_of_shape h
  have hlt : XI.hN < orderOf (ω0 XI) := by
    rw [ho, hN_of_shape' h, pow_succ]; have := Nat.two_pow_pos XI.k; omega
  have := pow_injOn_Iio_orderOf (x := ω0 XI) (show (i : ℕ) ∈ Set.Iio (orderOf (ω0 XI)) from
    lt_of_lt_of_le i.2 (hn.trans hlt.le)) (show (j : ℕ) ∈ Set.Iio (orderOf (ω0 XI)) from
    lt_of_lt_of_le j.2 (hn.trans hlt.le)) hij
  exact Fin.ext this

theorem adj_pows {XI : ExecInst} (hsh : j8ShapeOk XI = true) {n : ℕ} (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    ω0 XI ^ ((⟨(i : ℕ) + 1, hi⟩ : Fin n) : ℕ) = ω0 XI ^ (i : ℕ) * (orbX XI hsh).ω := by
  show ω0 XI ^ ((i : ℕ) + 1) = _
  rw [pow_succ]; rfl

theorem hN_le {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.hN ≤ 2 ^ 26 := by
  rw [hN_of_shape' h]
  exact Nat.pow_le_pow_right (by norm_num) (by have := k_le_25 h; omega)

/-- the geometric conjuncts of `StmtP` (injectivity and adjacency of the nodes, the size bounds): lemmas for `PbOfX` -/
structure Geom (Pb : PubJ8 P) : Prop where
  hinjX : Function.Injective Pb.nodes
  hadjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  hinjC : Function.Injective Pb.nodesC
  hadjC : ∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω
  hnpC : Pb.nC < ringChar (ZMod P)
  hinjW : Function.Injective Pb.nodesW
  hadjW : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω
  hJgeom : Pb.nJ ≠ 0 → Function.Injective Pb.nodesJ ∧
    ∀ (i : Fin Pb.nJ) (hi : (i : ℕ) + 1 < Pb.nJ), Pb.nodesJ ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesJ i * Pb.orbitJ.ω
  hinjA : Function.Injective Pb.nodesA
  hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω
  hnpA : Pb.nA < P
  hVgeom : Pb.krootsV ≠ 0 → Function.Injective Pb.nodesV ∧
    ∀ (i : Fin Pb.nV) (hi : (i : ℕ) + 1 < Pb.nV), Pb.nodesV ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesV i * Pb.orbitV.ω
  hlenA : Pb.nA + Pb.nV < P
  hlenAN : Pb.nV ≤ 2 ^ 26 ∧ Pb.nJ ≤ 2 ^ 26

theorem geom_PbOfX (XI : ExecInst) (hsh : j8ShapeOk XI = true) (hpos : PosX XI) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) :
    Geom (PbOfX XI hsh hpos kroots krootsV Rt regs ids idx rk lay) := by
  have hlt := hN_lt_p hsh
  have hle := hN_le hsh
  have hk1 : 1 ≤ XI.hN := by rw [hN_of_shape' hsh]; exact Nat.one_le_two_pow
  have hV := nV_le XI hsh hk1
  have hrc : ringChar (ZMod P) = P := ZMod.ringChar_zmod_n P
  refine ⟨inj_pows hsh (hNof_le XI hsh _), fun i hi => adj_pows hsh i hi, inj_pows hsh (hNof_le XI hsh _),
    fun i hi => adj_pows hsh i hi, ?_, inj_pows hsh (hNof_le XI hsh _), fun i hi => adj_pows hsh i hi,
    fun _ => ⟨inj_pows hsh (hNof_le XI hsh _), fun i hi => adj_pows hsh i hi⟩, inj_pows hsh (hNof_le XI hsh _),
    fun i hi => adj_pows hsh i hi, ?_, fun _ => ⟨inj_pows hsh hV, fun i hi => adj_pows hsh i hi⟩, ?_, ?_, ?_⟩
  · show hNof XI "cellChipHQKW" < ringChar (ZMod P)
    rw [hrc]; exact lt_of_le_of_lt (hNof_le XI hsh _) hlt
  · show hNof XI "atomChipHQL" < P
    exact lt_of_le_of_lt (hNof_le XI hsh _) hlt
  · show hNof XI "atomChipHQL" + (if (tabOf XI "walkChipHQK").isSome then hNof XI "walkChipHQK" else 1) < P
    have := hNof_le XI hsh "atomChipHQL"
    have h2 : (2 : ℕ) * 2 ^ 26 < P := by norm_num [P, Nock.Field.p]
    omega
  · show (if (tabOf XI "walkChipHQK").isSome then hNof XI "walkChipHQK" else 1) ≤ 2 ^ 26
    exact hV.trans hle
  · show hNof XI "jetChipJ8" ≤ 2 ^ 26
    exact (hNof_le XI hsh _).trans hle

/-- `hHt` for `PbOfX`: every row set lies in the union domain `{ω^i : i < hN}` (`n_t ≤ hN`) -/
theorem hHt_PbOfX (XI : ExecInst) (hsh : j8ShapeOk XI = true) (hpos : PosX XI) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) (d : Datum) (hd : d.Pb = PbOfX XI hsh hpos kroots krootsV Rt regs ids idx rk lay)
    (hN : d.hN = XI.hN) (hω : d.ω = ω0 XI) : ∀ t, HtOf d t ⊆ HdomOf d := by
  have hk1 : 1 ≤ XI.hN := by rw [hN_of_shape' hsh]; exact Nat.one_le_two_pow
  have hV := nV_le XI hsh hk1
  obtain ⟨Pb, Rg, c, r, g, hN', ω'⟩ := d
  simp only at hd hN hω
  subst hd hN hω
  intro t x hxt
  have key : ∀ {n : ℕ} (nodes : Fin n → ZMod P), (∀ i, nodes i = ω0 XI ^ (i : ℕ)) → n ≤ XI.hN →
      x ∈ rowNodeSet nodes → x ∈ HdomOf ⟨PbOfX XI hsh hpos kroots krootsV Rt regs ids idx rk lay, Rg, c, r, g, XI.hN, ω0 XI⟩ := by
    intro n nodes hn hle hxm
    unfold rowNodeSet at hxm
    obtain ⟨i, -, rfl⟩ := (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) nodes Finset.univ x).mp hxm
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le i.2 hle), (hn i).symm⟩
  fin_cases t
  · exact key _ (fun i => rfl) (hNof_le XI hsh _) hxt
  · exact key _ (fun i => rfl) (hNof_le XI hsh _) hxt
  · exact key _ (fun i => rfl) (hNof_le XI hsh _) hxt
  · exact key _ (fun i => rfl) (hNof_le XI hsh _) hxt
  · exact key _ (fun i => rfl) (hNof_le XI hsh _) hxt
  · exact key _ (fun i => rfl) hV hxt

/-- `cap_H` for `PbOfX`: `hN ≤ 2^26` -/
theorem hcapH_PbOfX (XI : ExecInst) (hsh : j8ShapeOk XI = true) (d : Datum) (hN : d.hN = XI.hN) : d.hN ≤ 2 ^ 26 := by
  rw [hN]; exact hN_le hsh

/-- **`hH_J` form**: the interface's `H` of a datum over `PbOfX XI …` is the verifier's `{hShift · hGen^i : i < hN}` (`hShift = 1`) -/
theorem H_J8_eq (XI : ExecInst) (d : Datum) (hd : DatumOK d) (hS : XI.hShift = 1) (hN : d.hN = XI.hN) (hω : d.ω = ω0 XI) :
    (J8 d hd).H = (Finset.range XI.hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i) := by
  show HdomOf d = _
  unfold HdomOf
  rw [hN, hω, hS, NockvmE2E.Exec.VL.zv_one]
  simp only [ω0, one_mul]
  congr

/-- the chip id of each J-8 table (flat order) -/
def tabId : Fin 6 → String
  | 0 => "computeChipVCLHX" | 1 => "cellChipHQKW" | 2 => "walkChipJ8" | 3 => "jetChipJ8" | 4 => "atomChipHQL"
  | 5 => "walkChipHQK"

theorem mandOk_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : NockvmE2E.Exec.J8Shape.mandatoryOk XI = true := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  tauto

theorem mand_mem {XI : ExecInst} (h : NockvmE2E.Exec.J8Shape.mandatoryOk XI = true) :
    ∀ t : Fin 6, t ≠ 3 → t ≠ 5 → tabId t ∈ XI.tabs.toList.map (·.chip.id) := by
  unfold NockvmE2E.Exec.J8Shape.mandatoryOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨-, h4⟩ := h
  intro t h3 h5
  fin_cases t
  · exact h4 _ (by simp [tabId])
  · exact h4 _ (by simp [tabId])
  · exact h4 _ (by simp [tabId])
  · exact absurd rfl h3
  · exact h4 _ (by simp [tabId])
  · exact absurd rfl h5

/-- **the only obligation of `hfree`**: every J-8-present table of `PbOfX` has a table of the instance with its chip id -/
theorem present_tab (XI : ExecInst) (hsh : j8ShapeOk XI = true) (hpos : PosX XI) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) (d : Datum) (hd : d.Pb = PbOfX XI hsh hpos kroots krootsV Rt regs ids idx rk lay)
    (t : Fin 6) (ht : presentJ8 d t) : tabId t ∈ XI.tabs.toList.map (·.chip.id) := by
  have hm := mandOk_of_shape hsh
  by_cases h3 : t = 3
  · subst h3
    have hJ : d.Pb.nJ ≠ 0 := fun h0 => ht.1 ⟨rfl, h0⟩
    rw [hd] at hJ
    have hJ' : hNof XI "jetChipJ8" ≠ 0 := hJ
    unfold hNof tabOf at hJ'
    cases hf : XI.tabs.toList.find? (fun t => t.chip.id == "jetChipJ8") with
    | none => simp [hf] at hJ'
    | some t0 =>
      have h1 := List.mem_of_find?_eq_some hf
      have h2 := List.find?_some hf
      simp only [beq_iff_eq] at h2
      exact List.mem_map.mpr ⟨t0, h1, by simpa [tabId] using h2⟩
  by_cases h5 : t = 5
  · subst h5
    have hV : d.Pb.krootsV ≠ 0 := fun h0 => ht.2 ⟨rfl, h0⟩
    rw [hd] at hV
    have hV' : (if (tabOf XI "walkChipHQK").isSome then krootsV else 0) ≠ 0 := hV
    unfold tabOf at hV'
    cases hf : XI.tabs.toList.find? (fun t => t.chip.id == "walkChipHQK") with
    | none => simp [hf] at hV'
    | some t0 =>
      have h1 := List.mem_of_find?_eq_some hf
      have h2 := List.find?_some hf
      simp only [beq_iff_eq] at h2
      exact List.mem_map.mpr ⟨t0, h1, by simpa [tabId] using h2⟩
  exact mand_mem hm t h3 h5

theorem fold_mono (f : Nat × Nat × Bool → TabInst → Nat × Nat × Bool)
    (hf : ∀ st t, (f st t).2.2 = true → st.2.2 = true ∧ 1 ≤ t.hN) :
    ∀ (l : List TabInst) (st : Nat × Nat × Bool), (l.foldl f st).2.2 = true → st.2.2 = true := by
  intro l
  induction l with
  | nil => intro st h; exact h
  | cons a l ih => intro st h; exact (hf st a (ih (f st a) h)).1

/-- the fold of `tabsOk` carries `1 ≤ t.hN` for every table -/
theorem fold_pos (f : Nat × Nat × Bool → TabInst → Nat × Nat × Bool)
    (hf : ∀ st t, (f st t).2.2 = true → st.2.2 = true ∧ 1 ≤ t.hN) :
    ∀ (l : List TabInst) (st : Nat × Nat × Bool), (l.foldl f st).2.2 = true → ∀ t ∈ l, 1 ≤ t.hN := by
  intro l
  induction l with
  | nil => intro st _ t ht; exact absurd ht List.not_mem_nil
  | cons a l ih =>
    intro st h t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact (hf st t (fold_mono f hf l (f st t) h)).2
    · exact ih (f st a) h t ht

/-- **`tabsOk`: every table has a row** -/
theorem hN_pos_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : ∀ t ∈ XI.tabs.toList, 1 ≤ t.hN := by
  have h1 := NockvmE2E.Exec.J8Shape.tabsOk_of_shape h
  unfold NockvmE2E.Exec.V.tabsOk at h1
  simp only [Bool.and_eq_true] at h1
  have h2 := h1.1.1.2
  rw [← Array.foldl_toList] at h2
  refine fold_pos _ ?_ XI.tabs.toList _ h2
  intro st t hst
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hst
  exact ⟨by tauto, by tauto⟩

theorem tabOf_isSome_of_mem (XI : ExecInst) (id : String) (h : id ∈ XI.tabs.toList.map (·.chip.id)) :
    (tabOf XI id).isSome = true := by
  unfold tabOf
  rw [List.find?_isSome]
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
  exact ⟨t, ht, by simp⟩

theorem hNof_pos_of_isSome {XI : ExecInst} (hp : ∀ t ∈ XI.tabs.toList, 1 ≤ t.hN) (id : String)
    (h : (tabOf XI id).isSome = true) : 0 < hNof XI id := by
  unfold hNof
  cases hf : tabOf XI id with
  | none => simp [hf] at h
  | some t0 => have := hp t0 (List.mem_of_find?_eq_some hf); simp only [hf, Option.map_some, Option.getD_some]; omega

/-- **`PosX` from the shape check** (`tabsOk`: `1 ≤ t.hN`; `mandatoryOk`) -/
theorem posX_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : PosX XI := by
  have hp := hN_pos_of_shape h
  have hm := mand_mem (mandOk_of_shape h)
  refine ⟨hNof_pos_of_isSome hp _ (tabOf_isSome_of_mem _ _ (hm 0 (by decide) (by decide))),
    hNof_pos_of_isSome hp _ (tabOf_isSome_of_mem _ _ (hm 1 (by decide) (by decide))),
    hNof_pos_of_isSome hp _ (tabOf_isSome_of_mem _ _ (hm 2 (by decide) (by decide))),
    hNof_pos_of_isSome hp _ (tabOf_isSome_of_mem _ _ (hm 4 (by decide) (by decide))), fun hs => hNof_pos_of_isSome hp _ hs⟩

end PbOf


/-! ## 7. vacuity witnesses -/

/-- some template (the `Rt` of the witnesses is irrelevant when `regs = []`) -/
def tplDummy : Nock.Jet.Autogen.Tpl := ⟨0, Fin.elim0, Fin.elim0, .F, .const 0⟩

/-- **`StmtP` and `PubP` are implied by nock's `AcceptsJ8V`** (with the compute publics `xp` set to `pubVJ8`): they are inhabited
wherever nock's accept predicate is (nock's `probJ8V_nonvacuous_clean`, below). -/
theorem stmt_pub_of_acc (d : Datum) (χ : Coins Φ0 KC) (M : MsgJ8' P KC deltaF) (tr : TrJ8 (ZMod P))
    (h : AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 d.Pb d.Rg d.c χ M tr d.r d.g) :
    StmtP d ∧ PubP d χ (M, fun j => pubVJ8 deltaF powerBasis3 d.c M.m M.ρ M.ρS χ j) := by
  refine ⟨⟨h.hinjX, h.hadjX, h.hinjC, h.hadjC, h.hnpC, h.hinjW, h.hadjW, h.hkW, h.hknW, h.hkpW, ?_, h.hinjA, h.hadjA, h.hnpA, ?_,
    h.hlay, h.hsmall, h.huniq, h.hTpl, h.hnd, h.hidx, h.hrk, h.hlt, h.hclA, h.hclR, h.hcen, h.hlenC, h.hlenA, h.hcellF,
    h.hnA62, h.hbud, h.hbudV⟩, ⟨h.hGx, h.hGp, h.hGS, h.hsumC', h.hbalA', h.hvalA0, h.hfxC, h.hfxA⟩, h.hclI, ⟨?_, ?_⟩,
    fun j => rfl⟩
  · intro h0
    rcases h.hJk with ⟨-, -, hinj, -, hadj⟩ | ⟨hn0, -⟩
    · exact ⟨hinj, hadj⟩
    · exact absurd hn0 h0
  · intro h0
    rcases h.hVk with ⟨-, -, hinj, hadj, h1, h2, h3⟩ | ⟨hk0, -⟩
    · exact ⟨hinj, hadj, h1, h2, h3⟩
    · exact absurd hk0 h0
  · intro h0
    rcases h.hVk with ⟨-, -, -, -, h1, -, -⟩ | ⟨-, a, b, c, e, f, g⟩
    · omega
    · exact ⟨a, b, c, e, f, g⟩
  · intro h0
    rcases h.hJk with ⟨-, -, -, hpos, -⟩ | ⟨-, a, b, c, e⟩
    · omega
    · exact ⟨a, b, c, e⟩

/-- the hypotheses of `accGen` / `accOn_J8` (`StmtP`, `PubP`) are inhabited, at nock's own accepting witness
(`probJ8V_nonvacuous_clean`: empty registry, true claim `c0`, `krootsV = 0`, `nJ = 0`) -/
theorem stmt_pub_inhabited : ∃ (d : Datum) (χ : Coins Φ0 KC) (M : Msg), StmtP d ∧ PubP d χ M := by
  obtain ⟨Pb, χ, M, tr, r, g, hacc, -⟩ := CleanJ8.probJ8V_nonvacuous_clean (K := KC) deltaF powerBasis3 rfl (fun _ => tplDummy)
  exact ⟨⟨Pb, InhabJ8Base.R0, InhabJ8Base.c0, r, g, 1, 1⟩, χ, _, (stmt_pub_of_acc ⟨Pb, InhabJ8Base.R0, InhabJ8Base.c0, r, g, 1, 1⟩ χ M tr hacc).1,
    (stmt_pub_of_acc ⟨Pb, InhabJ8Base.R0, InhabJ8Base.c0, r, g, 1, 1⟩ χ M tr hacc).2⟩

section ToyPb
open NockvmE2E.Exec.J8Shape (toyShape4 toyShape_ok)

/-- the side condition `PosX` holds on the toy instance (`tabs` have `hN = 3`) -/
theorem posX_toy : PosX toyShape4 := by
  unfold PosX hNof tabOf toyShape4
  decide

theorem hNof_toy_jet : hNof toyShape4 "jetChipJ8" = 0 := by
  unfold hNof tabOf toyShape4
  decide

/-- `PbOfX` at the toy instance, with its geometric conjuncts: the lemmas fire on a kernel-checked shape -/
noncomputable def toyPb : PubJ8 P :=
  PbOfX toyShape4 toyShape_ok posX_toy 1 0 (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0))
    (fun i => absurd (i.2.trans_eq hNof_toy_jet) (Nat.not_lt_zero _))

theorem toyPb_geom : Geom toyPb := geom_PbOfX _ _ _ _ _ _ _ _ _ _ _

end ToyPb

end Inst

end NockvmE2E.J8.InstJ8

#print axioms NockvmE2E.J8.InstJ8.J8
#print axioms NockvmE2E.J8.InstJ8.accOn_J8
#print axioms NockvmE2E.J8.InstJ8.stmt_pub_inhabited
#print axioms NockvmE2E.J8.InstJ8.toyPb_geom
#print axioms NockvmE2E.J8.InstJ8.geom_PbOfX
#print axioms NockvmE2E.J8.InstJ8.present_tab
#print axioms NockvmE2E.J8.InstJ8.hcapH_PbOfX
#print axioms NockvmE2E.J8.InstJ8.hHt_PbOfX
#print axioms NockvmE2E.J8.InstJ8.H_J8_eq
#print axioms NockvmE2E.J8.InstJ8.posX_of_shape
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.soundJ8V_pointwise
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.epsilonOf_listJ8V
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.oneRound_listJ8V
