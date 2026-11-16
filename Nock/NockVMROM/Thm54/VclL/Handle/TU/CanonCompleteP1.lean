/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/CanonCompleteP1.lean

 **completeness: the honest canonical transcript is accepted.**

 * §1 heights: at a P1 datum (no J rows, the pad atom row, no atom walk) `htJ8 D = sz.ht` for any sizes with the
 datum's three table sizes (`htJ8_p1`); with `Rows31`, `htJ8 D ≤ 31`, so the concrete `omegaG` orbit `orbP1` of
 height `htJ8 D` exists: the orbit given to the J8Gen chain.
 * §2 `pbOfO_eq`: the honest layout `PbOfO D orbP1` IS the canonical layout `canonPbOf hpG sz`, except for the five J
 registry fields (`Rt regs ids idx rk`).
 * §3 swaps: at `regs = ids = []` `AcceptsJ8V` reads no `Rt idx rk` (`accepts_rt_swap`); at an absent J chip and
 atom walk the J and atom-walk publics may be `0` (`accepts_pubs_zero`).
 * §4 `complJ8_P1` (`complJ8_closed'` at `j8DataCanon` and `orbP1`, every binder from `canon_run_all`);
 `accepts_canon`: at a good coin the J-8 verifier accepts `msgCanon` / `trCanon` at `canonPb hpG sz c`.
 * §5 `AcceptsCanon2` (as in `UniqueP1`), the canonical aux `axP1`, and **`canon_complete`**: `AcceptsCanon2` at the
 canonical transcript at every good coin, the extra pin (E10), `Pr[¬Good] ≤ ε_c`.
 Hypotheses: the compute side templates `hCside` (`canonC`) and `hC2side` (`canonC2`, E8/E9) at the canonical trace
 (`HonestSideCP1.honest_canonC` / `honest_canonC2'`). Size premise: `Rows31`, `RootsLeafOK`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1

noncomputable section

/-! ## 1. Heights and the orbit -/

section Height
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- At a P1 datum (no J rows, the single atom pad row, no atom walk) the largest table is the largest of the
compute, cell and walk tables. -/
theorem szJ8_p1 (D : J8Data p Rg fuel s f r) (hJ : D.jrows = []) (hA1 : D.acs.length = 1)
    (hV : D.preads = []) :
    szJ8 D = max (bfsForest [D.t]).length (max D.cells.length (walkRows D.cells D.reads).length) := by
  have hW := walk_pos D.cells D.reads
  unfold szJ8 sizesJ8 nVOf
  rw [hJ, hA1, if_pos hV]
  simp only [List.foldr_cons, List.foldr_nil, List.length_nil]
  congr 2
  omega

/-- **The height bridge**: at a P1 datum, `htJ8 D` is the `SizesP1.ht` of any sizes with the datum's three
table sizes. -/
theorem htJ8_p1 (D : J8Data p Rg fuel s f r) (hJ : D.jrows = []) (hA1 : D.acs.length = 1)
    (hV : D.preads = []) (sz : SizesP1) (hn : sz.n = (bfsForest [D.t]).length) (hnC : sz.nC = D.cells.length)
    (hnW : sz.nW = (walkRows D.cells D.reads).length) : htJ8 D = sz.ht := by
  unfold htJ8 SizesP1.ht
  rw [szJ8_p1 D hJ hA1 hV, hn, hnC, hnW]

/-- **The concrete orbit** `ω = omegaG p (htJ8 D)` at the common height, for the J8Gen chain. -/
def orbP1 [Fact (ringChar (ZMod p)).Prime] (hpG : p = Nock.Atoms.p) (D : J8Data p Rg fuel s f r) (h31 : Rows31 D) :
    StrictOrbitDomain (ZMod p) 3 (htJ8 D) :=
  orbitG hpG (htJ8 D) (one_le_ht D) ((ht_le D h31).trans (by norm_num))

theorem orbitG_heq (hpG : p = Nock.Atoms.p) {h₁ h₂ : ℕ} (e : h₁ = h₂) (a : 1 ≤ h₁) (a' : h₁ ≤ 32) (c : 1 ≤ h₂)
    (c' : h₂ ≤ 32) : HEq (orbitG hpG h₁ a a') (orbitG hpG h₂ c c') := by
  subst e; rfl

end Height

/-! ## 2. The honest layout is the canonical layout (up to the J registry fields) -/

section PbEq
variable {p : ℕ} [Fact p.Prime] [Fact (ringChar (ZMod p)).Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ}
  {s f r : Noun}

theorem heq_pow {n m : ℕ} (e : n = m) {ω ω' : ZMod p} (hω : ω = ω') :
    HEq (fun i : Fin n => ω ^ (i : ℕ)) (fun i : Fin m => ω' ^ (i : ℕ)) := by
  subst e; subst hω; rfl

theorem heq_fin0 {X : Type} {n : ℕ} (e : n = 0) (g : Fin n → X) (g' : Fin 0 → X) : HEq g g' := by
  subst e; exact heq_of_eq (funext fun i => i.elim0)

theorem pbOfO_eq (hpG : p = Nock.Atoms.p) (D : J8Data p Rg fuel s f r) (h31 : Rows31 D)
    (hC : 0 < D.cells.length) (hA : 0 < D.acs.length) (sz : SizesP1) (hJ : D.jrows = [])
    (hA1 : D.acs.length = 1) (hV : D.preads = []) (hn : sz.n = (bfsForest [D.t]).length)
    (hnC : sz.nC = D.cells.length) (hnW : sz.nW = (walkRows D.cells D.reads).length)
    (hkr : sz.kroots = krW D.cells D.reads) :
    PbOfO D (orbP1 hpG D h31) hC hA =
      { canonPbOf hpG sz with Rt := D.Rt, regs := D.regs, ids := D.ids, idx := D.idx, rk := D.rk } := by
  have hht := htJ8_p1 D hJ hA1 hV sz hn hnC hnW
  have ho : HEq (orbP1 hpG D h31) (orbitG hpG sz.ht sz.one_le_ht sz.ht_le_32) := orbitG_heq hpG hht _ _ _ _
  have hω : (orbP1 hpG D h31).ω = omegaG p sz.ht := by
    show omegaG p (htJ8 D) = _; rw [hht]
  have hJl : D.jrows.length = 0 := by rw [hJ]; rfl
  have hkV : krVOf D = 0 := by unfold krVOf; rw [if_pos hV]
  have hnV : nVOf D = 1 := by unfold nVOf; rw [if_pos hV]
  unfold PbOfO canonPbOf
  dsimp only
  congr 1
  all_goals first
    | rfl | exact hn.symm | exact hnC.symm | exact hnW.symm | exact hkr.symm | exact hht | exact hJl
    | exact hA1 | exact hkV | exact hnV | exact ho | exact proof_irrel_heq _ _
    | exact heq_pow hn.symm hω | exact heq_pow hnC.symm hω | exact heq_pow hnW.symm hω
    | exact heq_pow hJl hω | exact heq_pow hA1 hω | exact heq_pow hnV hω
    | exact heq_fin0 hJl _ _

end PbEq

/-! ## 3. Swaps: the J registry fields at no registered jet; the J and atom-walk publics when absent -/

section Swap
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **At no registered jet the predicate reads no template, index or rank of the layout.** -/
theorem accepts_rt_swap {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hr : Pb.regs = []) (hi : Pb.ids = []) (Rt' : ℕ → Nock.Jet.Autogen.Tpl) (idx' : ℕ → ℕ) (rk' : ℕ → ℕ × ℕ) :
    AcceptsJ8V δ b { Pb with Rt := Rt', idx := idx', rk := rk' } Rg c χ M tr r g :=
  { hsatX := h.hsatX
    hinjX := h.hinjX
    hadjX := h.hadjX
    hsatC := h.hsatC
    hbindC := h.hbindC
    hinjC := h.hinjC
    hadjC := h.hadjC
    hnpC := h.hnpC
    hsatW := h.hsatW
    hbindW := h.hbindW
    hinjW := h.hinjW
    hadjW := h.hadjW
    hkW := h.hkW
    hknW := h.hknW
    hkpW := h.hkpW
    hJk := h.hJk
    hsatA := h.hsatA
    hbindA := h.hbindA
    hinjA := h.hinjA
    hadjA := h.hadjA
    hnpA := h.hnpA
    hVk := h.hVk
    hGx := h.hGx
    hGp := h.hGp
    hGS := by have := h.hGS; simp only [hr] at this ⊢; exact this
    hlay := by have := h.hlay; simp only [hr, hi] at this ⊢; exact this
    hsmall := by have := h.hsmall; simp only [hr, hi] at this ⊢; exact this
    huniq := by have := h.huniq; simp only [hr, hi] at this ⊢; exact this
    hTpl := fun i hi' => by simp only [hr] at hi'; exact absurd hi' (List.not_mem_nil)
    hnd := h.hnd
    hidx := fun i hi' => by simp only [hr] at hi'; exact absurd hi' (List.not_mem_nil)
    hrk := fun i hi' => by simp only [hr] at hi'; exact absurd hi' (List.not_mem_nil)
    hlt := fun i hi' => by simp only [hr] at hi'; exact absurd hi' (List.not_mem_nil)
    hsumC' := by
      have := h.hsumC'
      simp only [AcceptsJ8P.pinRecsJ8, hr] at this ⊢; exact this
    hbalA' := h.hbalA'
    hvalA0 := h.hvalA0
    hfxC := h.hfxC
    hfxA := h.hfxA
    hclA := h.hclA
    hclI := h.hclI
    hclR := h.hclR
    hcen := by
      have := h.hcen
      simp only [AcceptsJ8P.censusG, hr] at this ⊢; exact this
    hlenC := h.hlenC
    hlenA := h.hlenA
    hcellF := h.hcellF
    hnA62 := h.hnA62
    hbud := ⟨h.hbud.1, h.hbud.2, h.hbud.3, h.hbud.4, h.hbud.5, h.hbud.6⟩
    hbudV := h.hbudV
    hsatL := h.hsatL
    hbindL := h.hbindL }

/-- **At an absent J chip and an absent atom walk the J and atom-walk publics may be `0`.** -/
theorem accepts_pubs_zero {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hJ0 : Pb.nJ = 0) (hV0 : Pb.krootsV = 0) :
    AcceptsJ8V δ b Pb Rg c χ { M with pubsJ := fun _ => 0, pubsV := fun _ => 0 } tr r g := by
  have hJ : M.pubsJ 0 = 0 ∧ M.pubsJ 1 = 0 ∧ M.pubsJ 2 = 0 ∧ M.pubsJ 3 = 0 := by
    rcases h.hJk with ⟨-, -, -, hpos, -⟩ | ⟨-, h'⟩
    · omega
    · exact h'
  obtain ⟨hV1, hV2, hV3, hV4, hV5, hV6⟩ := (aw_absent_iff δ b hV0).1 h.hVk
  obtain ⟨hJ1, hJ2, hJ3, hJ4⟩ := hJ
  exact
  { hsatX := h.hsatX
    hinjX := h.hinjX
    hadjX := h.hadjX
    hsatC := h.hsatC
    hbindC := h.hbindC
    hinjC := h.hinjC
    hadjC := h.hadjC
    hnpC := h.hnpC
    hsatW := h.hsatW
    hbindW := h.hbindW
    hinjW := h.hinjW
    hadjW := h.hadjW
    hkW := h.hkW
    hknW := h.hknW
    hkpW := h.hkpW
    hJk := Or.inr ⟨hJ0, rfl, rfl, rfl, rfl⟩
    hsatA := h.hsatA
    hbindA := h.hbindA
    hinjA := h.hinjA
    hadjA := h.hadjA
    hnpA := h.hnpA
    hVk := Or.inr ⟨hV0, rfl, rfl, rfl, rfl, rfl, rfl⟩
    hGx := by have := h.hGx; rw [hJ3, hJ4] at this; exact this
    hGp := h.hGp
    hGS := by have := h.hGS; rw [hJ1, hJ2, hV5, hV6] at this; exact this
    hlay := h.hlay
    hsmall := h.hsmall
    huniq := h.huniq
    hTpl := h.hTpl
    hnd := h.hnd
    hidx := h.hidx
    hrk := h.hrk
    hlt := h.hlt
    hsumC' := h.hsumC'
    hbalA' := by have := h.hbalA'; rw [hV3, hV4] at this; exact this
    hvalA0 := h.hvalA0
    hfxC := h.hfxC
    hfxA := by have := h.hfxA; rw [hV1, hV2] at this; exact this
    hclA := h.hclA
    hclI := h.hclI
    hclR := h.hclR
    hcen := h.hcen
    hlenC := h.hlenC
    hlenA := h.hlenA
    hcellF := h.hcellF
    hnA62 := h.hnA62
    hbud := h.hbud
    hbudV := h.hbudV
    hsatL := h.hsatL
    hbindL := h.hbindL }

end Swap

/-! ## 4. Honest acceptance of the canonical transcript -/

section Accept
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Nock.Jet.Autogen.Tpl} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

/-- The canonical datum's orbit for the J8Gen chain. -/
abbrev oP1 (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r))
    (hR : Rows31 (j8DataCanon p Rg Rt hgen)) : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataCanon p Rg Rt hgen)) :=
  orbP1 hpG (j8DataCanon p Rg Rt hgen) hR

/-- The honest record at the canonical datum and the concrete orbit. -/
abbrev BP1 (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r))
    (hR : Rows31 (j8DataCanon p Rg Rt hgen)) : ComplJ8.HonestJ8 p K δ Rg fuel s f r :=
  BRunA' δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen) (oP1 hpG hgen hR)

open Classical in
/-- **`complJ8_closed'` at the canonical datum and the `omegaG` orbit**, every binder discharged from `P1FragC`
and the two size premises. -/
theorem complJ8_P1 (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩)
    (hR : Rows31 (j8DataCanon p Rg Rt hgen)) (hL : ComplJ8Walk.RootsLeafOK (j8DataCanon p Rg Rt hgen).roots) :
    let B := BP1 δ b hpG hgen hR (K := K)
    (∀ χ, B.Good χ → AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  have R := canon_run_all (Rt := Rt) hpG hgen hc hR hL
  exact complJ8_closed' δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen) (oP1 hpG hgen hR) hpG
    R.hax R.hop5 R.hclA R.hleaf R.hwalk R.hwalkA (fun id hid => absurd hid (R.hcalled id))
    (fun id hid => absurd hid (R.hcalled id)) R.h31

/-- **Honest acceptance of the canonical transcript**: at every good coin of `BP1`, the J-8 verifier accepts the
canonical message and trace (`msgCanon`, `trCanon` at the `omegaG` orbit) at the canonical layout. -/
theorem accepts_canon (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩)
    (hR : Rows31 (j8DataCanon p Rg Rt hgen)) (hL : ComplJ8Walk.RootsLeafOK (j8DataCanon p Rg Rt hgen).roots)
    (sz : P8PublicClaim → SizesP1)
    (hsz : sz (cJ s f r) = szCanon p Rg Rt hgen (canon_fit_of_rows31 hgen hR).1)
    (χ : Coins frameJ8 K) (hχ : (BP1 δ b hpG hgen hR (K := K)).Good χ) :
    AcceptsJ8V.AcceptsJ8V δ b (canonPb hpG sz (cJ s f r)) Rg.R (cJ s f r) χ
      (msgCanon δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen).cells_pos
        (j8DataCanon_ok p Rg Rt hgen).acs_pos (oP1 hpG hgen hR) χ)
      (trCanon δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen).cells_pos
        (j8DataCanon_ok p Rg Rt hgen).acs_pos (oP1 hpG hgen hR) χ)
      (BP1 δ b hpG hgen hR (K := K)).rows (BP1 δ b hpG hgen hR (K := K)).g := by
  have R := canon_run_all (Rt := Rt) hpG hgen hc hR hL
  have hids := canon_ids (Rt := Rt) hpG hgen hc
  have h0 := (complJ8_P1 δ b hpG hgen hc hR hL (K := K)).1 χ hχ
  have hJ0 : (BP1 δ b hpG hgen hR (K := K)).Pb.nJ = 0 := by
    show (j8DataCanon p Rg Rt hgen).jrows.length = 0; rw [R.jrows]; rfl
  have hV0 : (BP1 δ b hpG hgen hR (K := K)).Pb.krootsV = 0 := by
    show krVOf (j8DataCanon p Rg Rt hgen) = 0; unfold krVOf; rw [if_pos R.preads]
  have h1 := absent_trJ_free δ b h0 hJ0 (fun _ => 0)
  have h2 := AcceptsJ8V.absent_trV_free h1 hV0 (fun _ => 0)
  have h3 := accepts_mCanon (j8DataCanon p Rg Rt hgen).H rfl h2
  have h4 := accepts_pubs_zero δ b h3 hJ0 hV0
  have e := pbOfO_eq hpG (j8DataCanon p Rg Rt hgen) hR (j8DataCanon_ok p Rg Rt hgen).cells_pos
    (j8DataCanon_ok p Rg Rt hgen).acs_pos (szCanon p Rg Rt hgen (canon_fit_of_rows31 hgen hR).1) R.jrows R.acs1
    R.preads rfl rfl rfl rfl
  have h5 : AcceptsJ8V.AcceptsJ8V δ b (PbOfO (j8DataCanon p Rg Rt hgen) (oP1 hpG hgen hR)
      (j8DataCanon_ok p Rg Rt hgen).cells_pos (j8DataCanon_ok p Rg Rt hgen).acs_pos) Rg.R (cJ s f r) χ
      (msgCanon δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen).cells_pos
        (j8DataCanon_ok p Rg Rt hgen).acs_pos (oP1 hpG hgen hR) χ)
      (trCanon δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen).cells_pos
        (j8DataCanon_ok p Rg Rt hgen).acs_pos (oP1 hpG hgen hR) χ)
      (BP1 δ b hpG hgen hR (K := K)).rows (BP1 δ b hpG hgen hR (K := K)).g := h4
  rw [e, R.regs, hids] at h5
  have h6 := accepts_rt_swap δ b h5 rfl rfl (fun _ => tpl0) (fun _ => 0) (fun _ => (0, 0))
  have ec : canonPb hpG sz (cJ s f r) = canonPbOf hpG (szCanon p Rg Rt hgen (canon_fit_of_rows31 hgen hR).1) := by
    unfold canonPb; rw [hsz]
  rw [ec]
  exact h6

end Accept

/-! ## 5. The canonicalising conjuncts: `canon_complete` -/

section Complete
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1 (auxWOf rowsW colWH canonW_walkTr canon_dummy_idx auxWOf_degree_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Cell (kbLB kbRB)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Nock.Jet.Autogen.Tpl} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

/-- **`AcceptsCanon2`**: `AcceptsCanon` and the compute side template `canonC2` (pins E8, E9). -/
def AcceptsCanon2 (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (Pb : PubJ8 p) (Rg : Nock.Jet.Registry)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p))
    (r : RowsJ8) (g : ℕ) : Prop :=
  AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g ∧ (canonC2 b Pb).Satisfies (sideC2Q tr)

/-- **The canonical aux columns** at an orbit: the cell sort gadget `auxMOf` of the honest cell columns and the
walk aux `auxWOf` of the honest walk columns. -/
def axP1 {Rg : Nock.Jet.VerifiedRegistry} (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) : AuxP1 (ZMod p) where
  M := auxMOf (CanonGenP1.nodesN o.ω D.cells.length)
    (rowsOf hC (colH δ b (γV δ χ) (ρV δ χ) (encR δ χ) (zJ δ χ) (bigOf D) D.cells (mvF D) (mxF D) (fun _ => 0)
      (fun i => (mhF D i : ZMod p))
      (HonestKW.ivW δ b hC (CanonGenP1.nodesN o.ω D.cells.length) o (chalsMJ8 δ χ) (pubsCOf δ b D hC o χ)
        (cellCol δ b (ComplJ8Enc.valsBE δ (γV δ χ) (ρV δ χ) (encR δ χ) (zJ δ χ) (bigOf D) D.cells (mvF D) (mxF D)
          (fun _ => 0)))
        (fun i => (mhF D i : ZMod p)) (kbLB (bigOf D) D.cells) (kbRB (bigOf D) D.cells))
      (HonestKW.avW δ b hC (CanonGenP1.nodesN o.ω D.cells.length) o (chalsMJ8 δ χ) (pubsCOf δ b D hC o χ)
        (cellCol δ b (ComplJ8Enc.valsBE δ (γV δ χ) (ρV δ χ) (encR δ χ) (zJ δ χ) (bigOf D) D.cells (mvF D) (mxF D)
          (fun _ => 0)))
        (fun i => (mhF D i : ZMod p)) (kbLB (bigOf D) D.cells) (kbRB (bigOf D) D.cells))))
  W := auxWOf (CanonWalkP1.nodesN o.ω (walkRows D.cells D.reads).length)
    (rowsW (walk_pos D.cells D.reads) (colWH δ b (walk_pos D.cells D.reads)
      (CanonWalkP1.nodesN o.ω (walkRows D.cells D.reads).length) o (chalsMJ8 δ χ) (pubsWOf δ b D o χ) (encR δ χ)
      (γV δ χ) (ρV δ χ) D.cells D.reads (kLW D) (vLW D) (kRW D) (vRW D)))
    (krW D.cells D.reads)

/-- `trCanon` depends on the orbit only through its value (heights equal, orbits `HEq`). -/
theorem trCanon_congr {Rg : Nock.Jet.VerifiedRegistry} (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length)
    (hA : 0 < D.acs.length) {h h' : ℕ} (e : h = h') (o : StrictOrbitDomain (ZMod p) 3 h)
    (o' : StrictOrbitDomain (ZMod p) 3 h') (ho : HEq o o') (χ : Coins frameJ8 K) :
    trCanon δ b D hC hA o χ = trCanon δ b D hC hA o' χ := by
  subst e; cases ho; rfl

open Classical in
/-- **`canon_complete`:** on a P1 claim `⟨s, f, r⟩` with a run `hgen`, at the
canonical datum `j8DataCanon` (any template table `Rt`), at the `omegaG` orbit `oP1` of height `htJ8`, under the
size premise `Rows31 ∧ RootsLeafOK` and table sizes `sz` that are the canonical generator's at the claim: at every
good coin of the honest record `BP1`, the canonical message `msgCanon`, trace `trCanon` and aux `axP1` are accepted
by `AcceptsCanon2` at the canonical layout `canonPb hpG sz c` (with the honest rows and budget), and E10 holds: with no
path read the walk's `idx` column vanishes at the first walk node. Also: `Pr[¬ Good] ≤ ε_c`.
`hCside` / `hC2side` (the compute side templates at the canonical trace) are hypotheses. -/
theorem canon_complete (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩)
    (hR : Rows31 (j8DataCanon p Rg Rt hgen)) (hL : ComplJ8Walk.RootsLeafOK (j8DataCanon p Rg Rt hgen).roots)
    (sz : P8PublicClaim → SizesP1)
    (hsz : sz (cJ s f r) = szCanon p Rg Rt hgen (canon_fit_of_rows31 hgen hR).1)
    (hCside : ∀ χ : Coins frameJ8 K, (canonC b (canonPb hpG sz (cJ s f r))).Satisfies
      (sideCQ (trCanon δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen).cells_pos
        (j8DataCanon_ok p Rg Rt hgen).acs_pos (oP1 hpG hgen hR) χ)))
    (hC2side : ∀ χ : Coins frameJ8 K, (canonC2 b (canonPb hpG sz (cJ s f r))).Satisfies
      (sideC2Q (trCanon δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen).cells_pos
        (j8DataCanon_ok p Rg Rt hgen).acs_pos (oP1 hpG hgen hR) χ))) :
    let D := j8DataCanon p Rg Rt hgen
    let hC := (j8DataCanon_ok p Rg Rt hgen).cells_pos
    let hA := (j8DataCanon_ok p Rg Rt hgen).acs_pos
    let Pb := canonPb hpG sz (cJ s f r)
    let B := BP1 δ b hpG hgen hR (K := K)
    (∀ χ, B.Good χ →
      AcceptsCanon2 δ b hpG sz Pb Rg.R (cJ s f r) χ (msgCanon δ b D hC hA (oP1 hpG hgen hR) χ)
        (trCanon δ b D hC hA (oP1 hpG hgen hR) χ) (axP1 δ b D hC Pb.orbit χ) B.rows B.g ∧
      (walkRoots D.reads = [] →
        ((trCanon δ b D hC hA (oP1 hpG hgen hR) χ).W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, Pb.hnW⟩) = 0)) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) := by
  intro D hC hA Pb B
  have R := canon_run_all (Rt := Rt) hpG hgen hc hR hL
  have hn : (sz (cJ s f r)).n = (bfsForest [D.t]).length := by rw [hsz]; rfl
  have hnC : (sz (cJ s f r)).nC = D.cells.length := by rw [hsz]; rfl
  have hnW : (sz (cJ s f r)).nW = (walkRows D.cells D.reads).length := by rw [hsz]; rfl
  have hht : htJ8 D = (sz (cJ s f r)).ht := htJ8_p1 D R.jrows R.acs1 R.preads _ hn hnC hnW
  have ho : HEq (oP1 hpG hgen hR) Pb.orbit :=
    orbitG_heq hpG hht _ _ (SizesP1.one_le_ht _) (SizesP1.ht_le_32 _)
  have hfit := (sz (cJ s f r)).fit_ht
  have hleC : D.cells.length ≤ 2 ^ (sz (cJ s f r)).ht :=
    hnC ▸ le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hfit
  have hleW : (walkRows D.cells D.reads).length ≤ 2 ^ (sz (cJ s f r)).ht :=
    hnW ▸ le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hfit
  refine ⟨fun χ hχ => ?_, (complJ8_P1 δ b hpG hgen hc hR hL (K := K)).2.1⟩
  have etr := trCanon_congr δ b D hC hA hht (oP1 hpG hgen hR) Pb.orbit ho χ
  have hacc := accepts_canon δ b hpG hgen hc hR hL sz hsz χ hχ
  have hdeg : DegOK Pb (trCanon δ b D hC hA (oP1 hpG hgen hR) χ) (axP1 δ b D hC Pb.orbit χ) := by
    rw [etr]
    refine trCanon_degOK δ b D hC hA hpG (sz (cJ s f r)) χ _ hn hnC hnW R.acs1 (fun j => ?_) (fun j => ?_)
    · rw [hnC]; exact CanonGenP1.auxMOf_degree_lt _ (powN_inj Pb.orbit hleC) _ j
    · rw [hnW]; exact auxWOf_degree_lt _ (powN_inj Pb.orbit hleW) _ _ j
  have hM : (canonM b Pb).Satisfies (sideMQ (trCanon δ b D hC hA (oP1 hpG hgen hR) χ) (axP1 δ b D hC Pb.orbit χ)) := by
    rw [etr]
    exact CanonGenP1.canonM_cellTr δ b hpG sz (cJ s f r) (chalsMJ8 δ) (pubsCOf δ b D hC Pb.orbit) (γV δ) (ρV δ)
      (zJ δ) (encR δ) (bigOf D) D.cells (mvF D) (mxF D) (fun _ => 0) (mhF D) χ hC hnC R.hcs R.hcell R.hch R.hnb
      R.hlen R.hrk rfl rfl
  have hW : (canonW b Pb).Satisfies (sideWQ (trCanon δ b D hC hA (oP1 hpG hgen hR) χ) (axP1 δ b D hC Pb.orbit χ)) := by
    rw [etr]
    exact canonW_walkTr δ b hpG sz (cJ s f r) (chalsMJ8 δ) (pubsWOf δ b D Pb.orbit) (γV δ) (ρV δ) (encR δ) D.cells
      D.reads (walk_pos D.cells D.reads) (kLW D) (vLW D) (kRW D) (vRW D) χ rfl hnW R.hsort R.hmem R.hlen R.hlen31
      R.hle rfl rfl
  refine ⟨⟨⟨hacc, ?_⟩, hC2side χ⟩, fun hne => ?_⟩
  · exact
    { hfrag := hc
      hPb := rfl
      hdeg := hdeg
      hC := hCside χ
      hM := hM
      hW := hW
      hV0 := rfl
      hApad := fun j hj => canon_trA δ b hpG hgen hc hA (oP1 hpG hgen hR) χ j hj
      hmsg := msgCanon_supp δ b D hC hA (oP1 hpG hgen hR) χ }
  · rw [etr]
    exact canon_dummy_idx δ b hpG sz (cJ s f r) (chalsMJ8 δ) (pubsWOf δ b D Pb.orbit) (γV δ) (ρV δ) (encR δ)
      D.cells D.reads (walk_pos D.cells D.reads) (kLW D) (vLW D) (kRW D) (vRW D) χ hnW hne
      (List.ne_nil_of_length_pos hC) rfl

end Complete

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1.szJ8_p1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1.htJ8_p1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1.pbOfO_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1.accepts_rt_swap
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1.accepts_pubs_zero
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1.complJ8_P1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1.accepts_canon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1.trCanon_congr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1.canon_complete
