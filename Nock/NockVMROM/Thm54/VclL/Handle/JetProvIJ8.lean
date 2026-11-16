/-
  Nock/NockVMROM/Thm54/VclL/Handle/JetProvIJ8.lean

  **The J chip's effective `TAG_jet` providers in
  IMPLICATION form, with NO subject obligation** (`hSubE`, hence the compute subject fact `hcomp`, removed).

  `SubJ8.jetProvOKE` needs `hSubE` (a call row's subject handle denotes) to run `jetChip_holds`.  In the
  implication form (`RecOKIJ8.PreI` on a jet key `[id, ck, cv, sk, sv, ek, ev, 3]` is `D (sk, sv) ≠ none`) the
  antecedent IS that fact for the call row the key is served by (the key's entries 3 / 4 are the row's
  `(kL, vL)`), so **`jetProvOKI`** is `jetProvOKE`'s proof with `hSubE _ hrc hkd _ hκ hfib` replaced by the
  antecedent.  The compute side supplies the antecedent at every tree node (`RowSemIJ8`: an `s11j` row's subject
  denotes).  New module, additive.
-/
import Nock.Jet.SubJ8
import Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.JetProvIJ8

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp Nock.Jet.ChipJ8 Nock.Jet.RapJetJ8
open Nock.Jet.RegJ8R Nock.Jet.PinJ8 Nock.Jet.FibreJ8 Nock.Jet.SubJ8
open Nock.Framework Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8 (PreI PreS)
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

noncomputable section

section Eff
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K} {lay : Fin n → PRow}
  {P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "RJ" => rowJ b nodes orbit chals pubs lay P
local notation "JP" => jProv b nodes orbit chals pubs lay P

/-- **`SubJ8.jetProvOKE` in implication form, without `hSubE`.** -/
theorem jetProvOKI (hp3 : 3 < p) {R : ℕ → Tpl} {regs ids : List ℕ}
    (hA : Accepted R regs ids (rowsJ b nodes orbit chals pubs lay P))
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX} (hD : DenOKX p D)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(R i).toTemplate p, compile p (R i)⟩ ∧ axPosB (R i) = true ∧
      (R i).WellTyped p)
    (hRd : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
      RecOK D Rg limbA ([r.w.vN.val, r.w.kL.val, r.w.vL.val, r.w.kR.val, r.w.vR.val], .x))
    (hReg : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .reg →
      D (r.w.kN.val, r.w.vN.val) = some (compile p (R r.pre.id)))
    (provO : List ((Fin 8 → K) × K)) :
    ServedJ8.ProvP (p := p) (K := K) (fun x => PreI D x → RecOK D Rg limbA x) .s
      (jProvE (δ := δ) (b := b) (nodes := nodes) (orbit := orbit) (chals := chals) (pubs := pubs)
        (lay := lay) (P := P) provO) := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hM : MemoryBB R (rowsJ b nodes orbit chals pubs lay P) (fun hh => D (hh.1.val, hh.2.val)) :=
    { den0 := fun v => by simp only [ZMod.val_zero]; exact hD.atom v.val
      gen := fun r hr hk => by
        obtain ⟨A, B, h1, h2, h3⟩ := hRd r hr hk
        unfold recB
        simp only [ZMod.val_one, h2, h3, h1]
        simp
      reg := hReg }
  have h1 : (1 : ℕ) < p := by omega
  have h2 : (2 : ℕ) < p := by omega
  have h3 : (3 : ℕ) < p := by omega
  have h0 : (0 : ℕ) < p := by omega
  intro q hqW l hl hlt hnk hante
  obtain ⟨hq, hq2⟩ := List.mem_filter.mp hqW
  change l.length ≤ 8 at hl
  change DenXJ8.natKey (p := p) (K := K) 8 l = q.1 at hnk
  obtain ⟨i, -, hq'⟩ := List.mem_flatMap.mp hq
  have hrc : RJ i ∈ rowsJ b nodes orbit chals pubs lay P := List.mem_ofFn.mpr ⟨i, rfl⟩
  rcases List.mem_append.mp hq' with hP | hJ
  · obtain ⟨κ', hκ', rfl⟩ := List.mem_map.mp hP
    rw [provKT_eq] at hκ'
    obtain ⟨κ1, hκ1, rfl⟩ := List.mem_map.mp hκ'
    obtain ⟨-, htag⟩ := tlF_shape (provK_shape _ κ1 hκ1)
    have h7ne : (tlF κ1).getD 7 0 ≠ 0 := by
      rcases htag with ht | ht <;> rw [ht]
      · simp
      · simpa using ne_cast h2 h0 (by norm_num)
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ := eight l (len8_of_tag hl hnk h7ne)
    have e7 := natKey_keyK hnk 7 (by norm_num)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at e7
    have hx7 : x7 < p := hlt x7 (by simp)
    rcases htag with ht | ht <;> rw [ht] at e7
    · obtain rfl := natCast_inj_lt hx7 h1 e7; simp [RecOK]
    · obtain rfl := natCast_inj_lt hx7 h2 e7; simp [RecOK]
  · obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hJ
    obtain ⟨h7, hlen, hkd, rfl⟩ := jet_tag _ κ hκ
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ :=
      eight l (len8_of_tag hl hnk (by rw [h7]; simpa using ne_cast h3 h0 (by norm_num)))
    have e : ∀ c (hc : c < 8), (([x0, x1, x2, x3, x4, x5, x6, x7].getD c 0 : ℕ) : ZMod p) =
        (keyJet.map (KE.ev (colOf (RJ i)))).getD c 0 := fun c hc => natKey_keyK hnk c hc
    have e0 := e 0 (by norm_num); have e1 := e 1 (by norm_num); have e2 := e 2 (by norm_num)
    have e3 := e 3 (by norm_num); have e4 := e 4 (by norm_num); have e5 := e 5 (by norm_num)
    have e6 := e 6 (by norm_num); have e7 := e 7 (by norm_num)
    simp only [List.getD_cons_succ, List.getD_cons_zero, keyJet, List.map_cons, List.map_nil, KE.ev,
      colOf, Col.id, Col.kN, Col.vN, Col.kL, Col.vL, Col.kR, Col.vR] at e0 e1 e2 e3 e4 e5 e6 e7
    have hlt' : ∀ x ∈ [x0, x1, x2, x3, x4, x5, x6, x7], x < p := hlt
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt'
    obtain ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩ := hlt'
    obtain rfl := natCast_inj_lt hx7 h3 e7
    have hpm := pre_mem hA hrc
    obtain ⟨c, i0, hc, hpre⟩ := layout_call hpm hkd
    have hi0 : i0 < p := by have := (hA.small _ hpm).1; rw [hpre] at this; exact this
    have hid : (RJ i).pre.id = i0 := by rw [hpre]; rfl
    rw [hid] at e0
    obtain rfl := natCast_inj_lt hx0 hi0 e0
    obtain rfl := val_of_cast hx1 e1; obtain rfl := val_of_cast hx2 e2
    obtain rfl := val_of_cast hx3 e3; obtain rfl := val_of_cast hx4 e4
    obtain rfl := val_of_cast hx5 e5; obtain rfl := val_of_cast hx6 e6
    have hreg := call_reg hA hrc hpre
    obtain ⟨hRg, hax, hT⟩ := hTpl x0 hreg
    have hpre' : D ((RJ i).w.kL.val, (RJ i).w.vL.val) ≠ none := by
      simpa only [PreI, PreS, if_pos, show ¬ (25 : ℕ) < 11 by norm_num, show ¬ (26 : ℕ) < 11 by norm_num,
        if_false, ite_false, reduceIte] using hante
    obtain ⟨S, hS⟩ := Option.ne_none_iff_exists'.mp hpre'
    obtain ⟨hcomp, E, hE, hsem, -⟩ := jetChip_holds R regs ids (rowsJ b nodes orbit chals pubs lay P)
      (fun hh => D (hh.1.val, hh.2.val)) hA hM c x0 hc hax hT (RJ i) hrc hpre S hS
    exact ⟨_, hRg, hcomp, S, E, hS, hE, hsem⟩

end Eff

end

end Nock.NockVMROM.Thm54.VclL.Handle.JetProvIJ8
