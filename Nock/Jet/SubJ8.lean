/-
  Nock/Jet/SubJ8.lean

  **`hSub` discharged — the J chip's `TAG_jet` provides are owed
  `RecOK` only where they are EFFECTIVE, and an effective provide is consumed by compute.**

  Two call rows with the same jet key and weights `m, −m`
  cancel; no consumer is owed and none exists, so `hSubW` (`m ≠ 0 ⇒ subject denotes`) is not
  derivable.  The identity controls the KEY FIBRE: a key whose total weight is nonzero is consumed
  (`FibreJ8.consumed_of_fibre`), and the non-effective providers drop out of every balance sum
  (`FibreJ8.sum_effP`).  So the provider obligation ranges over the EFFECTIVE providers.

  * `liftS`, `jProvE` / `provOE` (the J / other service providers whose lifted key fibre in the
    merged service list is nonzero), `liftS_effE` (`liftS (jProvE ++ provOE) = effP (liftS S)`:
    the effective list IS the J-share filter, so the merged balance and its IO event can be stated
    at `jProvE ++ provOE`), `balance_effE` (the balance sum is unchanged).
  * **`jetProvOKE`**: `ProvP RecOK.s jProvE`, with the subject obligation `hSubE` only on call rows
    whose jet key is effective.
  * **`hSubE_of_service`**: `hSubE` from the merged service balance outside its weighted IO event at
    the effective providers, and the COMPUTE side's subject fact `hcomp` (named: every `TAG_jet`
    record compute consumes names a subject handle that denotes).  An effective jet key is consumed
    (`consumed_of_fibre`); it is not a J in-chip consume (entry 7 is `3`, theirs `1 / 2`), so it is a
    compute consume.
  * **`jetProvOK_pin`**: `jetProvOKE` at `D = denK` with `hReg` from the pin (`PinJ8.hReg_of_pin`)
    and `hSubE` from the service balance (`hSubE_of_service`).
-/
import Nock.Jet.PinJ8
import Nock.Jet.FibreJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.Jet.SubJ8

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp Nock.Jet.ChipJ8 Nock.Jet.RapJetJ8
open Nock.Jet.RegJ8R Nock.Jet.PinJ8 Nock.Jet.FibreJ8
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

/-- The service providers lifted to `𝕂′` (the `bal_of_service` provider list). -/
def liftS (l : List ((Fin 8 → K) × K)) : List ((Fin 8 → 𝕂′) × 𝕂′) :=
  l.map fun q => (liftRec (L := 𝕂′) q.1, algebraMap K 𝕂′ q.2)

/-- Effective in the merged service list `S`: the lifted key's fibre weight in `liftS S` is `≠ 0`. -/
def effS (S : List ((Fin 8 → K) × K)) (q : (Fin 8 → K) × K) : Bool :=
  decide (fibreW (liftS (δ := δ) S) (liftRec (L := 𝕂′) q.1) ≠ 0)

/-- **The effective J service providers** (in the merged list `jProv ++ provO`). -/
def jProvE (provO : List ((Fin 8 → K) × K)) : List ((Fin 8 → K) × K) :=
  (JP).filter (effS (δ := δ) (JP ++ provO))

/-- The effective other service providers. -/
def provOE (provO : List ((Fin 8 → K) × K)) : List ((Fin 8 → K) × K) :=
  provO.filter (effS (δ := δ) (JP ++ provO))

/-- **The effective list is the J-share filter**: `liftS (jProvE ++ provOE) = effP (liftS S)`. -/
theorem liftS_effE (provO : List ((Fin 8 → K) × K)) :
    liftS (δ := δ) (jProvE (δ := δ) (b := b) (nodes := nodes) (orbit := orbit) (chals := chals) (pubs := pubs)
        (lay := lay) (P := P) provO ++ provOE (δ := δ) (b := b) (nodes := nodes) (orbit := orbit)
        (chals := chals) (pubs := pubs) (lay := lay) (P := P) provO) =
      effP (liftS (δ := δ) (JP ++ provO)) := by
  unfold effP
  rw [liftS, liftS, List.filter_map, List.filter_append, jProvE, provOE]
  rfl

/-- **The merged balance is unchanged at the effective providers.** -/
theorem balance_effE (provO : List ((Fin 8 → K) × K)) (f : (Fin 8 → 𝕂′) → 𝕂′) :
    ((liftS (δ := δ) (JP ++ provO)).map fun q => q.2 * f q.1).sum =
      ((liftS (δ := δ) (jProvE (δ := δ) (b := b) (nodes := nodes) (orbit := orbit) (chals := chals) (pubs := pubs)
        (lay := lay) (P := P) provO ++ provOE (δ := δ) (b := b) (nodes := nodes) (orbit := orbit)
        (chals := chals) (pubs := pubs) (lay := lay) (P := P) provO)).map fun q => q.2 * f q.1).sum := by
  rw [liftS_effE]; exact sum_effP f _

/-- **`JetProvOK` on the effective providers.**  As `RegJ8R.jetProvOKW`, with the subject obligation
`hSubE` only on call rows whose jet key is effective in the merged service list. -/
theorem jetProvOKE (hp3 : 3 < p) {R : ℕ → Tpl} {regs ids : List ℕ}
    (hA : Accepted R regs ids (rowsJ b nodes orbit chals pubs lay P))
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX} (hD : DenOKX p D)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(R i).toTemplate p, compile p (R i)⟩ ∧ axPosB (R i) = true ∧
      (R i).WellTyped p)
    (hRd : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
      RecOK D Rg limbA ([r.w.vN.val, r.w.kL.val, r.w.vL.val, r.w.kR.val, r.w.vR.val], .x))
    (hReg : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .reg →
      D (r.w.kN.val, r.w.vN.val) = some (compile p (R r.pre.id)))
    (provO : List ((Fin 8 → K) × K))
    (hSubE : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .call → ∀ κ ∈ keysOf ents3 r,
      fibreW (liftS (δ := δ) (JP ++ provO)) (liftRec (L := 𝕂′) (keyK (K := K) 8 κ)) ≠ 0 →
      ∃ S, D (r.w.kL.val, r.w.vL.val) = some S) :
    ServedJ8.ProvP (p := p) (K := K) (RecOK D Rg limbA) .s
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
  intro q hqW l hl hlt hnk
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
    have hfib : fibreW (liftS (δ := δ) (JP ++ provO)) (liftRec (L := 𝕂′) (keyK (K := K) 8 κ)) ≠ 0 := by
      simpa [effS] using hq2
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
    obtain ⟨S, hS⟩ := hSubE _ hrc hkd _ hκ hfib
    obtain ⟨hcomp, E, hE, hsem, -⟩ := jetChip_holds R regs ids (rowsJ b nodes orbit chals pubs lay P)
      (fun hh => D (hh.1.val, hh.2.val)) hA hM c x0 hc hax hT (RJ i) hrc hpre S hS
    exact ⟨_, hRg, hcomp, S, E, hS, hE, hsem⟩

/-- **`hSubE` from the merged service balance and the compute side's subject fact.**  Under the
merged service identity (`bal_of_service`'s `hG`), outside the weighted IO failure event of the J
and other consumers against the EFFECTIVE providers, every call row whose jet key is effective has
its key consumed; the consumer is not a J in-chip consume (tag `3` vs `1 / 2`), so it is one of the
other (compute) consumers `reqO`, and the compute side's fact `hcomp` (named) gives the subject. -/
theorem hSubE_of_service [CharP 𝕂′ p] (hp3 : 3 < p)
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    {R : ℕ → Tpl} {regs ids : List ℕ} (hA : Accepted R regs ids (rowsJ b nodes orbit chals pubs lay P))
    (reqO : List (Fin 8 → K)) (provO : List ((Fin 8 → K) × K))
    (hG : Quad.mk _ (pubs 0) (pubs 1) +
        (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hout : ((coinsJ δ chals).gamma, (coinsJ δ chals).pole) ∉
      IOFailureEventW ((reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)))
        (effP (liftS (δ := δ) (JP ++ provO))))
    {D : HX → Option Noun}
    (hcomp : ∀ c ∈ reqO, ∀ l : List ℕ, l.length = 8 → (∀ e ∈ l, e < p) →
      DenXJ8.natKey (p := p) (K := K) 8 l = c → l.getD 7 0 = 3 →
      ∃ S, D (l.getD 3 0, l.getD 4 0) = some S) :
    ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .call → ∀ κ ∈ keysOf ents3 r,
      fibreW (liftS (δ := δ) (JP ++ provO)) (liftRec (L := 𝕂′) (keyK (K := K) 8 κ)) ≠ 0 →
      ∃ S, D (r.w.kL.val, r.w.vL.val) = some S := by
  set reqs := (reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)) with hreqs
  set provs := liftS (δ := δ) (JP ++ provO) with hprovs
  have hts := jet_tagged_sum hsat hbind hinj hn hadj
  have hsum : (reqs.map fun r => (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ r)⁻¹).sum =
      (provs.map fun q => q.2 * (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ q.1)⁻¹).sum := by
    simp only [hreqs, hprovs, liftS, List.map_map, Function.comp_def, List.map_append, List.sum_append]
    have e1 := hts
    change (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum +
        ((jCons b nodes orbit chals pubs lay P).map fun c =>
          (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      ((jProv b nodes orbit chals pubs lay P).map fun q =>
          algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum +
        (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum
    rw [e1]
    linear_combination hG
  have hsumE : (reqs.map fun r => (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ r)⁻¹).sum =
      ((effP provs).map fun q => q.2 * (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ q.1)⁻¹).sum := by
    rw [hsum]; exact sum_effP (fun k => (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ k)⁻¹) provs
  have hdA := TeleC.den_ne_of_out reqs (effP provs) _ _ hout
  have hdB := ServedJ8.den_prov_ne_of_out reqs (effP provs) _ _ hout
  have hout' := hout
  rw [mem_IOFailureEventW_iff] at hout'
  push Not at hout'
  have hcons := consumed_of_fibre reqs (effP provs) ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩
    hdA hdB hsumE hout'.1 hout'.2.2
  have h1 : (1 : ℕ) < p := by omega
  have h2 : (2 : ℕ) < p := by omega
  have h3' : (3 : ℕ) < p := hp3
  have hinjK := (algebraMap (ZMod p) K).injective
  intro r hr hk κ hκ hfib
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  have hqS : (keyK (K := K) 8 κ, algebraMap (ZMod p) K (RJ i).w.m) ∈ JP ++ provO :=
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
      List.mem_append_right _ (List.mem_map_of_mem hκ)⟩)
  have hqP : (liftRec (L := 𝕂′) (keyK (K := K) 8 κ), algebraMap K 𝕂′ (algebraMap (ZMod p) K (RJ i).w.m)) ∈
      provs := by rw [hprovs, liftS]; exact List.mem_map.mpr ⟨_, hqS, rfl⟩
  have hqE := mem_effP.mpr ⟨hqP, hfib⟩
  have hfibE : fibreW (effP provs) (liftRec (L := 𝕂′) (keyK (K := K) 8 κ)) ≠ 0 := by
    rw [fibreW_effP _ hfib]; exact hfib
  have hin := hcons _ hqE hfibE
  obtain ⟨c, hc, hce⟩ := List.mem_map.mp hin
  have hck : c = keyK 8 κ := liftRec_inj hce
  obtain ⟨h7, hlen, hkd, hκe⟩ := jet_tag _ κ hκ
  rcases List.mem_append.mp hc with hcO | hcJ
  · have hpm := pre_mem hA hr
    have hid : (RJ i).pre.id < p := (hA.small _ hpm).1
    set l : List ℕ := [(RJ i).pre.id, (RJ i).w.kN.val, (RJ i).w.vN.val, (RJ i).w.kL.val, (RJ i).w.vL.val,
      (RJ i).w.kR.val, (RJ i).w.vR.val, 3] with hl
    have hnk : DenXJ8.natKey (p := p) (K := K) 8 l = keyK 8 κ := by
      rw [hκe]
      funext c
      fin_cases c <;>
        simp [hl, DenXJ8.natKey, keyK, keyJet, KE.ev, colOf, Col.id, Col.kN, Col.vN, Col.kL, Col.vL, Col.kR,
          Col.vR, ZMod.natCast_zmod_val]
    have hsmall : ∀ e ∈ l, e < p := by
      intro e he
      simp only [hl, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hid
      all_goals first | exact ZMod.val_lt _ | exact h3'
    obtain ⟨S, hS⟩ := hcomp c hcO l (by simp [hl]) hsmall (hck ▸ hnk) (by simp [hl])
    exact ⟨S, by simpa [hl] using hS⟩
  · exfalso
    obtain ⟨i', -, hc'⟩ := List.mem_flatMap.mp hcJ
    obtain ⟨κ', hκ', rfl⟩ := List.mem_map.mp hc'
    rw [consKT_eq] at hκ'
    obtain ⟨κ1, hκ1, rfl⟩ := List.mem_map.mp hκ'
    obtain ⟨-, htag⟩ := tlF_shape (consK_shape _ κ1 hκ1)
    have e7 : algebraMap (ZMod p) K ((tlF κ1).getD 7 0) = algebraMap (ZMod p) K (κ.getD 7 0) :=
      congrFun hck ⟨7, by norm_num⟩
    rw [h7] at e7
    have e7' := hinjK e7
    rcases htag with ht | ht <;> rw [ht] at e7'
    · exact ne_cast h1 h3' (by norm_num) e7'
    · exact ne_cast h2 h3' (by norm_num) e7'

/-! ## The in-chip balance at the effective providers (one IO event for the whole J share) -/

/-- **`inchip_served` at the effective providers**: the served half of the merged service balance
with the IO event taken at `effP (liftS (jProv ++ provO))` (the same event `hSubE_of_service`
uses), for any in-chip-shaped key among `reqO ++ jCons`. -/
theorem inchip_servedE [CharP 𝕂′ p] (hp3 : 3 < p)
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (reqO : List (Fin 8 → K)) (provO : List ((Fin 8 → K) × K))
    (hO7 : ∀ q ∈ provO, q.1 ⟨7, by norm_num⟩ = 0)
    (hG : Quad.mk _ (pubs 0) (pubs 1) +
        (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hout : ((coinsJ δ chals).gamma, (coinsJ δ chals).pole) ∉
      IOFailureEventW ((reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)))
        (effP (liftS (δ := δ) (JP ++ provO))))
    (hcount : (reqO ++ jCons b nodes orbit chals pubs lay P).length < p) :
    ∀ κ : List (ZMod p), ((∃ a b c d : ZMod p, κ = [((1 : ℕ) : ZMod p), a, b, c, d]) ∨
        ∃ a b c : ZMod p, κ = [((2 : ℕ) : ZMod p), a, b, c]) →
      keyK 8 (tlF κ) ∈ reqO ++ jCons b nodes orbit chals pubs lay P →
      ∃ r' ∈ rowsJ b nodes orbit chals pubs lay P, κ ∈ provK r' := by
  set reqs := (reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)) with hreqs
  set provs := liftS (δ := δ) (JP ++ provO) with hprovs
  have hts := jet_tagged_sum hsat hbind hinj hn hadj
  have hsum : (reqs.map fun r => (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ r)⁻¹).sum =
      (provs.map fun q => q.2 * (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ q.1)⁻¹).sum := by
    simp only [hreqs, hprovs, liftS, List.map_map, Function.comp_def, List.map_append, List.sum_append]
    have e1 := hts
    change (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum +
        ((jCons b nodes orbit chals pubs lay P).map fun c =>
          (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      ((jProv b nodes orbit chals pubs lay P).map fun q =>
          algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum +
        (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum
    rw [e1]
    linear_combination hG
  have hout' := hout
  rw [mem_IOFailureEventW_iff] at hout'
  push Not at hout'
  have hserved : ∀ r ∈ reqs, r ∈ provs.map Prod.fst := by
    intro r hr
    have := served_effective (p := p) reqs provs ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩
      (TeleC.den_ne_of_out reqs (effP provs) _ _ hout) (ServedJ8.den_prov_ne_of_out reqs (effP provs) _ _ hout)
      hsum (by simpa [hreqs] using hcount) hout'.1 hout'.2.2 r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp this
    exact List.mem_map_of_mem (List.mem_of_mem_filter hq)
  have h1 : (1 : ℕ) < p := by omega
  have h2 : (2 : ℕ) < p := by omega
  have h0 : (0 : ℕ) < p := by omega
  intro κ hshape hκm
  have hmem : liftRec (L := 𝕂′) (keyK (K := K) 8 (tlF κ)) ∈ reqs := List.mem_map_of_mem hκm
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hserved _ hmem)
  rw [hprovs, liftS] at hq
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  have hkey : q0.1 = keyK 8 (tlF κ) := liftRec_inj hqe
  obtain ⟨hlen, htag⟩ := tlF_shape hshape
  have h7 : q0.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((tlF κ).getD 7 0) := by rw [hkey]; rfl
  have hinjK := (algebraMap (ZMod p) K).injective
  rcases List.mem_append.mp hq0 with hJ | hO
  · obtain ⟨i', -, hq'⟩ := List.mem_flatMap.mp hJ
    rcases List.mem_append.mp hq' with hP | hJet
    · obtain ⟨κ', hκ', rfl⟩ := List.mem_map.mp hP
      rw [provKT_eq] at hκ'
      obtain ⟨κ1, hκ1, rfl⟩ := List.mem_map.mp hκ'
      have hs1 := provK_shape _ κ1 hκ1
      have e := keyK_inj (tlF_shape hs1).1 hlen hkey
      rw [tlF_inj (ne_cast h1 h2 (by norm_num)) hs1 hshape e] at hκ1
      exact ⟨RJ i', List.mem_ofFn.mpr ⟨i', rfl⟩, hκ1⟩
    · obtain ⟨κj, hκj, rfl⟩ := List.mem_map.mp hJet
      exfalso
      have hj7 := (jet_tag _ κj hκj).1
      have e7 : algebraMap (ZMod p) K (κj.getD 7 0) = algebraMap (ZMod p) K ((tlF κ).getD 7 0) := h7
      rw [hj7] at e7
      have e7' := hinjK e7
      rcases htag with ht | ht <;> rw [ht] at e7'
      · exact ne_cast (by omega) h1 (by norm_num) e7'
      · exact ne_cast (by omega) h2 (by norm_num) e7'
  · exfalso
    have := hO7 q0 hO
    rw [h7, show (0 : K) = algebraMap (ZMod p) K ((0 : ℕ) : ZMod p) by simp] at this
    have e7' := hinjK this
    rcases htag with ht | ht <;> rw [ht] at e7'
    · exact ne_cast h1 h0 (by norm_num) e7'
    · exact ne_cast h2 h0 (by norm_num) e7'

/-- **J-3b's `Accepted.bal` at the effective providers** (`bal_of_service` with the one event). -/
theorem bal_of_serviceE [CharP 𝕂′ p] (hp3 : 3 < p)
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (reqO : List (Fin 8 → K)) (provO : List ((Fin 8 → K) × K))
    (hO7 : ∀ q ∈ provO, q.1 ⟨7, by norm_num⟩ = 0)
    (hG : Quad.mk _ (pubs 0) (pubs 1) +
        (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hout : ((coinsJ δ chals).gamma, (coinsJ δ chals).pole) ∉
      IOFailureEventW ((reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)))
        (effP (liftS (δ := δ) (JP ++ provO))))
    (hcount : (reqO ++ jCons b nodes orbit chals pubs lay P).length < p) :
    ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, ∀ κ ∈ consK r,
      ∃ r' ∈ rowsJ b nodes orbit chals pubs lay P, κ ∈ provK r' := by
  intro r hr κ hκ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  refine inchip_servedE hp3 hsat hbind hinj hn hadj reqO provO hO7 hG hout hcount κ (consK_shape _ κ hκ)
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩))
  have : tlF κ ∈ consKT (RJ i) := by rw [consKT_eq]; exact List.mem_map_of_mem hκ
  exact List.mem_map_of_mem this

/-- **The pins are served** (one event). -/
theorem pin_servedE [CharP 𝕂′ p] (hp3 : 3 < p)
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (reqO : List (Fin 8 → K)) (provO : List ((Fin 8 → K) × K))
    (hO7 : ∀ q ∈ provO, q.1 ⟨7, by norm_num⟩ = 0)
    (hG : Quad.mk _ (pubs 0) (pubs 1) +
        (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hout : ((coinsJ δ chals).gamma, (coinsJ δ chals).pole) ∉
      IOFailureEventW ((reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)))
        (effP (liftS (δ := δ) (JP ++ provO))))
    (hcount : (reqO ++ jCons b nodes orbit chals pubs lay P).length < p)
    {regs : List ℕ} {idx : ℕ → ℕ} (hpin : pinCons (p := p) (K := K) regs idx ⊆ reqO) :
    ∀ id ∈ regs, ∃ r' ∈ rowsJ b nodes orbit chals pubs lay P, pinKey id (idx id) ∈ provK r' := by
  intro id hid
  exact inchip_servedE hp3 hsat hbind hinj hn hadj reqO provO hO7 hG hout hcount _ (pinKey_shape id (idx id))
    (List.mem_append_left _ (hpin (List.mem_map_of_mem hid)))

/-- **G-J1 and `hSub` closed together (option (b), effective providers).**  On an accepted
`jetChipJ8` trace realizing the public layout, under the merged service identity with the
verifier's pins among the other consumers, outside the ONE weighted IO event of the J share at the
effective providers, with `regs` nodup and `idx id < p` (public checks):
* the trace is J-3b `Accepted` (`bal_of_serviceE`);
* every effective J service provide is genuine at `D = denK`: `ProvP RecOK.s jProvE`, with `hReg`
  from the pin and the cell-side served claim keys (`hReg_of_pin`), and `hSubE` from the compute
  side's subject fact (`hSubE_of_service`).
Named: the cell table's facts (`TableAccepts2`, `AtomLeaves`, `hclaim` from `regClaims_provided`),
`hrk`, the census `hinjE`, `DenOKX`, the registry `hTpl`, the export reads `hRd`, and `hcomp`. -/
theorem jetProvOK_pin [CharP 𝕂′ p] (hq : 2 ^ 63 < p)
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    {R : ℕ → Tpl} {regs ids : List ℕ} (hlay : List.ofFn lay = layoutJ8 R regs ids)
    (hsmall : ∀ q ∈ layoutJ8 R regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 R regs ids).filterMap tvKey).Nodup)
    (reqO : List (Fin 8 → K)) (provO : List ((Fin 8 → K) × K))
    (hO7 : ∀ q ∈ provO, q.1 ⟨7, by norm_num⟩ = 0)
    (hG : Quad.mk _ (pubs 0) (pubs 1) +
        (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hout : ((coinsJ δ chals).gamma, (coinsJ δ chals).pole) ∉
      IOFailureEventW ((reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)))
        (effP (liftS (δ := δ) (JP ++ provO))))
    (hcount : (reqO ++ jCons b nodes orbit chals pubs lay P).length < p)
    (hnd : regs.Nodup) {idx : ℕ → ℕ} (hidx : ∀ id ∈ regs, idx id < p)
    (hpin : pinCons (p := p) (K := K) regs idx ⊆ reqO)
    {Kfp : Type} [Field Kfp] [Algebra (ZMod p) Kfp] {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b)) (hE : InlineAtoms p z E)
    {t : List (CellRow p Kfp)} {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (htab : TableAccepts2 z t vp) (hvp : AtomLeaves E vp ext) {rk : ℕ → ℕ × ℕ}
    (hclaim : ∀ id ∈ regs,
      (∃ c ∈ t, (E (compile p (R id)), (rk id).1, (rk id).2, idx id) = (c.p, c.b0.hi, c.b0.lo, c.b0.idx)) ∨
        (E (compile p (R id)), (rk id).1, (rk id).2, idx id) ∈ vp)
    (hrk : ∀ id ∈ regs, rk id ≠ (0, 0))
    (hinjE : ∀ id ∈ regs, ∀ d ∈ decodedNouns2 (t.map (·.b0)) ext,
      E (compile p (R id)) = E d → compile p (R id) = d)
    {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX} (hD : DenOKX p (denK (t.map (·.b0)) ext))
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(R i).toTemplate p, compile p (R i)⟩ ∧ axPosB (R i) = true ∧
      (R i).WellTyped p)
    (hRd : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
      RecOK (denK (t.map (·.b0)) ext) Rg limbA ([r.w.vN.val, r.w.kL.val, r.w.vL.val, r.w.kR.val, r.w.vR.val], .x))
    (hcomp : ∀ c ∈ reqO, ∀ l : List ℕ, l.length = 8 → (∀ e ∈ l, e < p) →
      DenXJ8.natKey (p := p) (K := K) 8 l = c → l.getD 7 0 = 3 →
      ∃ S, denK (t.map (·.b0)) ext (l.getD 3 0, l.getD 4 0) = some S) :
    Accepted R regs ids (rowsJ b nodes orbit chals pubs lay P) ∧
      ServedJ8.ProvP (p := p) (K := K) (RecOK (denK (t.map (·.b0)) ext) Rg limbA) .s
        (jProvE (δ := δ) (b := b) (nodes := nodes) (orbit := orbit) (chals := chals) (pubs := pubs)
          (lay := lay) (P := P) provO) := by
  have hp3 : 3 < p := by
    have : (3 : ℕ) < 2 ^ 63 := by norm_num
    omega
  have hA := accepted_of_sat hsat hbind hinj hlay hsmall huniq
    (bal_of_serviceE hp3 hsat hbind hinj hn hadj reqO provO hO7 hG hout hcount)
  have hpinS := pin_servedE hp3 hsat hbind hinj hn hadj reqO provO hO7 hG hout hcount hpin
  have hReg := hReg_of_pin hq hcons hE htab hvp hA hnd hidx hpinS hclaim hrk hinjE
  have hSubE := hSubE_of_service hp3 hsat hbind hinj hn hadj hA reqO provO hG hout hcomp
  exact ⟨hA, jetProvOKE hp3 hA hD hTpl hRd hReg provO hSubE⟩

end Eff

end

end Nock.Jet.SubJ8
