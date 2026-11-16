/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/ServedP1.lean

 **The cell table is validity-served at P1 (single provider).**

 * `served_of_served2_nil`: an empty external provider list collapses the two-provider served form
 `ValidityServed2 t []` to `ValidityServed t`.
 * `mbVp_nil_of_pad`: under the atom-pad pin (`CanonP1.hApad`, column `mb = 196` is `0`), the atom table exports
 no validity provider, `mbVp … = []`.
 * **`cell_served_P1`**: an `AcceptsJ8V` trace at an absent atom walk (`krootsV = 0`) with the pad pin, outside
 every summand of `allJ8X X` (`X.C = withLiftC R L`), under the readout link `LinkJ8XUA` at `toMsgJ8ZA` (the one
 `probJ8V_absent` uses), has a validity-served restricted cell table: the two-provider form of
 `cellTable_accepts2` with the external list `mbVp … = []`.
 * `cell_served_P1_canon`: the same from `AcceptsCanon` (its `hApad`, and `krootsV = 0` from `Pb = canonPb`).
 * `servedC_pair_P1`: both traces of `trace_unique_good'` at once, in the form of `OpenP1.servedC` / `servedC'`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.ServedP1

noncomputable section

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM qA)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' mbVp hcountC_of')
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (DataJ8X allJ8X)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (restrictHQKWCell)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (toMsgJ8ZA acceptsJ8ZA_of_V)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A (LinkJ8XUA)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (cellTableOf)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1 (padA AcceptsCanon canonPb canonPb_consts SizesP1 AuxP1)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1 (AcceptsCanon2)

/-! ## 1. Two generic lemmas -/

/-- **An empty external provider list collapses the two-provider served form.** -/
theorem served_of_served2_nil {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp]
    {t : List (CellRow q Kfp)} (h : ValidityServed2 t []) : ValidityServed t := by
  intro c hc
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · rcases h c hc .L hw with h1 | h1
    · simpa [CellRow.fpS, CellRowB0.hiS, CellRowB0.loS, CellRowB0.idS] using h1
    · simp at h1
  · rcases h c hc .R hw with h1 | h1
    · simpa [CellRow.fpS, CellRowB0.hiS, CellRowB0.loS, CellRowB0.idS] using h1
    · simp at h1

section Pad
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Module.Basis (Fin 3) (ZMod p) K)

/-- **At the P1 pad (`hApad`) the atom table exports nothing**: `mbVp = []` (column `mb = 196` is `0`). -/
theorem mbVp_nil_of_pad (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K)
    (hpad : ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = Polynomial.C (padA j)) :
    mbVp δ b Pb.nodesA Pb.orbitA chals pubs (qA δ b Pb tr chals pubs) = [] := by
  unfold mbVp
  rw [List.flatMap_eq_nil_iff]
  intro i _
  have h196 : (AtomServedQ.aEF b Pb.nodesA Pb.orbitA chals pubs (qA δ b Pb tr chals pubs) i).trace
      AtomChipHQ.mb = 0 := by
    have hw : 196 < (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA chals pubs).rap.w := by
      rw [AtomChipHQ.atomChipHQ_width]; decide
    have e1 : (AtomServedQ.aEF b Pb.nodesA Pb.orbitA chals pubs (qA δ b Pb tr chals pubs) i).trace 196 =
        (tr.A ⟨196, by decide⟩).eval (Pb.nodesA i) := by
      simp only [AtomServedQ.aEF, Nock.Framework.Reify.envOfTrace]
      rw [dif_pos hw]; rfl
    show (AtomServedQ.aEF b Pb.nodesA Pb.orbitA chals pubs (qA δ b Pb tr chals pubs) i).trace 196 = 0
    rw [e1, hpad ⟨196, by decide⟩ (by decide)]
    simp [padA]
  rw [if_pos h196]

end Pad

/-! ## 2. The bridge -/

section Bridge
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`cell_served_P1`: the restricted cell table is validity-served.** An `AcceptsJ8V` trace at an absent atom walk
(`krootsV = 0`) with the atom-pad pin, outside every summand of `allJ8X X` with `X.C = withLiftC R L`, under the
readout link `LinkJ8XUA` at `toMsgJ8ZA`: `cellTable_accepts2`'s two-provider form has the external list
`mbVp … = []`, so it is `ValidityServed`. -/
theorem cell_served_P1 [CharP 𝕂′ p] (hpG : p = Nock.Atoms.p) {Pb : PubJ8 p} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r0 : RowsJ8} {g0 : ℕ}
    {R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g}
    {L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r}
    {X : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g}
    (hX : X.C = withLiftC R L) {rA : ℕ → ARow}
    (hacc3 : AcceptsJ8V δ b Pb Rg c χ M tr r0 g0) (h0 : Pb.krootsV = 0)
    (hpad : ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = Polynomial.C (padA j))
    (hout : ∀ s ∈ allJ8X X, ¬ s.mem tr χ)
    (hl : LinkJ8XUA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr R L rA) :
    ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) := by
  have hacc := acceptsJ8ZA_of_V hacc3 h0
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; omega
  have hF' := GeneratedField.primeFieldElems_zmod p
  have hoC : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ := by
    rw [← hX]; exact AtomFpxJ8.outsideC_of_outsideX X hout
  have O := BundleJ8.outJ8_of_outside R L b hoC
  have hz2 : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
    rw [(BundleJ8.chalsMJ8_z (δ := δ) χ).1, (BundleJ8.chalsMJ8_z (δ := δ) χ).2]
  have hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
    rw [hz2]; exact O.z_ne
  have houtC : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := O.valid hl.budV.1 hl.budV.2
  rw [hl.rdV.1, hl.rdV.2] at houtC
  have hcountC := hcountC_of' δ b Pb c χ M tr hacc3.hlenC
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (ProbJ8.chalsOK_J8 (δ := δ) χ) _ _ hacc.hsumC houtC
    hacc.hxneC hcountC _ hacc.hxC hacc.hvp0
  have h2 := htabC.served
  have hvp : (toMsgJ8ZA δ b Pb c χ M tr).vp = [] :=
    mbVp_nil_of_pad δ b Pb tr (ChalsAZJ8.chalsAJ8Z δ χ) M.pubsA hpad
  rw [hvp] at h2
  exact served_of_served2_nil h2


open Classical in
/-- **`cell_served_P1_absent`**: `cell_served_P1` at the event data of `LinkJ8A.probJ8V_absent` (the data
`probP1_final_clean` reduces to at P1), with the readout link supplied by `LinkJ8A.linkXUA_of_R5`. -/
theorem cell_served_P1_absent [CharP 𝕂′ p] (hpG : p = Nock.Atoms.p) {Pb : PubJ8 p} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
    (hr : RowsLe r EncInjJ8.cornerC) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg : (AcceptsJ8P.censusG Pb c).length ≤ 2 ^ 31)
    (hacc3 : AcceptsJ8V δ b Pb Rg c χ M tr r g) (h0 : Pb.krootsV = 0)
    (hpad : ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = Polynomial.C (padA j))
    (hout : ∀ s ∈ allJ8X (AtomFpxJ8.withFpxV δ b
      (withLiftC (AbsentVJ8.RR4A δ b (g := g + r.N)
          (LinkJ8R5.R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
          Pb c [] (by simp) (LinkJ8NV.layLe_ofG Pb hLC hLM hLW hLA hLV) rfl hnM hreg)
        (LinkJ8R4.LL4 δ b (LinkJ8R5.L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb [] (by simp)
          (LinkJ8NV.layLe_ofG Pb hLC hLM hLW hLA hLV)))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA), ¬ s.mem tr χ) :
    ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) :=
  cell_served_P1 δ b hpG rfl hacc3 h0 hpad hout
    (LinkJ8A.linkXUA_of_R5 δ b Pb c χ M tr _ _ [] (by simp) (LinkJ8NV.layLe_ofG Pb hLC hLM hLW hLA hLV) rfl hnM
      hreg hpG hr hg hmax hacc3 h0 hout)

open Classical in
/-- **Both cell tables of `trace_unique_good'` are validity-served** (`OpenP1.servedC`, `OpenP1.servedC'`): two
`AcceptsCanon2` tuples at one layout and coin, each outside the event data of `probJ8V_absent`. `krootsV = 0` and the
pad pin come from `CanonP1`. -/
theorem servedC_pair_P1 [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hr : RowsLe r EncInjJ8.cornerC) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg : (AcceptsJ8P.censusG Pb c).length ≤ 2 ^ 31)
    (hout : ∀ s ∈ allJ8X (AtomFpxJ8.withFpxV δ b
      (withLiftC (AbsentVJ8.RR4A δ b (g := g + r.N)
          (LinkJ8R5.R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
          Pb c [] (by simp) (LinkJ8NV.layLe_ofG Pb hLC hLM hLW hLA hLV) rfl hnM hreg)
        (LinkJ8R4.LL4 δ b (LinkJ8R5.L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb [] (by simp)
          (LinkJ8NV.layLe_ofG Pb hLC hLM hLW hLA hLV)))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
    (hout' : ∀ s ∈ allJ8X (AtomFpxJ8.withFpxV δ b
      (withLiftC (AbsentVJ8.RR4A δ b (g := g + r.N)
          (LinkJ8R5.R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
          Pb c [] (by simp) (LinkJ8NV.layLe_ofG Pb hLC hLM hLW hLA hLV) rfl hnM hreg)
        (LinkJ8R4.LL4 δ b (LinkJ8R5.L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb [] (by simp)
          (LinkJ8NV.layLe_ofG Pb hLC hLM hLW hLA hLV)))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA), ¬ s.mem tr' χ) :
    ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) ∧
    ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
        (qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC))) := by
  obtain ⟨⟨hA, hC⟩, -⟩ := h
  obtain ⟨⟨hA', hC'⟩, -⟩ := h'
  have h0 : Pb.krootsV = 0 := by rw [hC.hPb]; exact (canonPb_consts hpG sz c).2.2.2.1
  exact ⟨cell_served_P1_absent δ b hpG hr hmax hg hLC hLM hLW hLA hLV hnM hreg hA h0 hC.hApad hout,
    cell_served_P1_absent δ b hpG hr hmax hg hLC hLM hLW hLA hLV hnM hreg hA' h0 hC'.hApad hout'⟩

end Bridge

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.ServedP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ServedP1.served_of_served2_nil
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ServedP1.mbVp_nil_of_pad
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ServedP1.cell_served_P1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ServedP1.cell_served_P1_absent
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ServedP1.servedC_pair_P1
