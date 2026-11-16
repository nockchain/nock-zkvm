/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/UniqueProvP1.lean

 **The read provenance `hprov` and the root bounds `hk1 hkn hkp` of `UniqueCloseP1.trace_unique_closed`.**

 * §1 the root bounds at `canonPb hpG (szOfClaim p) c`, unconditionally (no `P1SizeOK`): `szOfClaim` is either
 `szOf` of the canonical data (`kroots = krW ≥ 1`, `krW ≤ |walkRows|`, `|walkRows| ≤ 2^32` from the fit) or `sz1`
 (`kroots = nW = 1`); `p = Nock.Atoms.p > 2^33`. **`hk_canon`**.
 * §2 a consumed path request is served by a walk row: with the path balance `count = pw provs` and every provider a
 walk path record (`provs ⊆ walkPProvs`, the J-8 `.p` providers ARE `walkPProvs`, `AcceptsJ8.provsJ8`), a request
 `x` with `x 0 = a1`, `x 1 = a2` (`a1 a2 < p`) has a walk row `j` with `ridx = a1` and `2·pre + side = a2`; the
 BFS prefix bound (`a_lt`, `len ≤ 60`) gives `pre < 2^61`, so `pre = a2 / 2`. **`walk_row_of_req`**.
 * §3 **`hprov_of_cover`**: `hprov`'s form for any read set `Rd`, given that the walk's request list has the
 counts of a reference list `reqs0` covering `Rd` (`hcov`: every read `(σ, a)` is some request's first two
 coordinates). The reference list is where the run enters: `reqs0` is the honest trace's compute path requests
 (`UniqueAuxP1.reqsPW`), the count equality is `UniqueAuxP1.hreqW_canon` at the `r0C` agreement.
 * §4 `RdP1_fst_le`: the root serials of `RdP1 p c` are `≤ 2^31` under `P1SizeOK` (so `< p`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueProvP1

noncomputable section

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qW qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1 (AcceptsCanon2 two63_lt_ringChar)
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8_width)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1 (envB envB_eval)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (WT lbl_cols pF walkJ8_bfsRows)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1 (a_lt walkEnvFA_col)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1 (szOfClaim sz1 fact_rc RdP1 RdP1_of P1SizeOK P1SizeOK_of DC
  RdOf runP1)

/-! ## 1. The root bounds -/

section Roots
variable (p : ℕ) [Fact p.Prime]
attribute [local instance] fact_rc

/-- **The claim sizes' root count**: `1 ≤ kroots ≤ nW ≤ 2^32` (no size premise). -/
theorem roots_szOfClaim (c : P8PublicClaim) :
    1 ≤ (szOfClaim p c).kroots ∧ (szOfClaim p c).kroots ≤ (szOfClaim p c).nW ∧ (szOfClaim p c).nW ≤ 2 ^ 32 := by
  unfold szOfClaim
  split
  · next t r h =>
    split
    · next hfit =>
      exact ⟨GenWalk.one_le_krW _ _, GenWalk.krW_le_rows _ _,
        (le_max_right _ _).trans ((le_max_right _ _).trans hfit)⟩
    · exact ⟨le_rfl, le_rfl, by norm_num [sz1]⟩
  · exact ⟨le_rfl, le_rfl, by norm_num [sz1]⟩

/-- **`hk1 hkn hkp` of `trace_unique_closed`** at `Pb = canonPb hpG (szOfClaim p) c`. -/
theorem hk_canon (hpG : p = Nock.Atoms.p) (c : P8PublicClaim) :
    1 ≤ (canonPb hpG (szOfClaim p) c).kroots ∧ (canonPb hpG (szOfClaim p) c).kroots ≤ (canonPb hpG (szOfClaim p) c).nW ∧
      (canonPb hpG (szOfClaim p) c).kroots + (canonPb hpG (szOfClaim p) c).nW < p := by
  obtain ⟨h1, h2, h3⟩ := roots_szOfClaim p c
  have hp : 2 ^ 33 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  refine ⟨h1, h2, ?_⟩
  show (szOfClaim p c).kroots + (szOfClaim p c).nW < p
  omega

end Roots

/-! ## 2. A consumed path request is served by a walk row -/

section Serve
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K) [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Pb : PubJ8 p}

/-- The walk path records' environment is the trace's walk columns. -/
theorem wEF_trace (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) (j : Fin Pb.nW) {c : ℕ} (hc : c < 166) :
    (TeleH.wEF b Pb.nodesW Pb.orbitW chals pubs (qW δ b Pb tr chals pubs) j).trace c =
      (envB δ b Pb tr chals pubs j).trace c := by
  rw [envB_eval δ b Pb tr chals pubs hc j.isLt]
  exact envOfTrace_trace (qW δ b Pb tr chals pubs) _ _ _ _ (by rw [walkChipJ8_width]; exact hc)

/-- **A consumed path request is served by a walk row**: outside the walk event, with the path balance against
providers that are walk path records, a request whose first two coordinates are the naturals `a1 a2 < p` has a walk
row `j` with `ridx = a1` and `pre = a2 / 2`. -/
theorem walk_row_of_req [CharP K p] {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hq : 2 ^ 63 < ringChar (ZMod p))
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < ringChar (ZMod p))
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr))
    (reqs : List (Fin 5 → K)) (provs : List ((Fin 5 → K) × K))
    (hbal : ∀ x, (reqs.count x : K) = pw provs x)
    (hsup : ∀ q ∈ provs, q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))
    (hbud : reqs.length < p) {x : Fin 5 → K} (hx : x ∈ reqs) {a1 a2 : ℕ}
    (h1 : x 0 = (a1 : K)) (h2 : x 1 = (a2 : K)) (ha1 : a1 < p) (ha2 : a2 < p) :
    ∃ j < Pb.nW, natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) = a1 ∧
      natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.pre) = a2 / 2 := by
  set chals := chalsMJ8 δ χ with hchals
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp64 : 64 ≤ ringChar (ZMod p) := by
    have : (64 : ℕ) ≤ 2 ^ 63 := by norm_num
    omega
  obtain ⟨q, hqp, e⟩ := CountsP1.consumed_provided reqs provs hbal hbud hx
  have hw := hsup q hqp
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hw
  set E := TeleH.wEF b Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW) j with hE
  -- the prefix bound: `pre < 2^61` (BFS `a_lt`, `len ≤ 60`)
  have B := walkJ8_bfsRows δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW _ hA.hsatW hA.hbindW
    hA.hinjW hA.hadjW pF hk hkn hkp hq hout
  have L := lbl_cols δ b Pb tr chals M.pubsW j.isLt
  have hal := a_lt B j j.isLt
  have hpa : ((WT δ b Pb chals M.pubsW tr).lbl ((j : ℕ) + 1)).2.pre.val <
      2 ^ (((WT δ b Pb chals M.pubsW tr).lbl ((j : ℕ) + 1)).2.len.val + 1) := hal
  rw [L.2.2.1, L.2.2.2] at hpa
  have hlen := WalkJ8.walkJ8_len_le_60 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW
    (qW δ b Pb tr chals M.pubsW) pF hp64 hA.hsatW j j.isLt
  rw [walkEnvFA_col δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW _ j.isLt (Or.inl (by decide))
    (by decide)] at hlen
  have hlen' : natOf ((envB δ b Pb tr chals M.pubsW j).trace WChip.len) ≤ 60 := by
    rw [envB_eval δ b Pb tr chals M.pubsW (by decide) j.isLt]; exact hlen
  have hpre : natOf ((envB δ b Pb tr chals M.pubsW j).trace WChip.pre) < 2 ^ 61 :=
    lt_of_lt_of_le hpa (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- the record's coordinates
  have eR := wEF_trace δ b tr chals M.pubsW j (c := WChip.ridx) (by decide)
  have eP := wEF_trace δ b tr chals M.pubsW j (c := WChip.pre) (by decide)
  set v := natOf ((envB δ b Pb tr chals M.pubsW j).trace WChip.pre) with hv
  have hvc : ((v : ℕ) : ZMod p) = (envB δ b Pb tr chals M.pubsW j).trace WChip.pre := natOf_cast pF _
  have hridx : ∀ y : ZMod p, algebraMap (ZMod p) K y = (a1 : K) → y = E.trace WChip.ridx →
      natOf ((envB δ b Pb tr chals M.pubsW j).trace WChip.ridx) = a1 := by
    intro y hy hyE
    have := CountsP1.eq_natCast_of_algK hy
    rw [← eR, ← hyE, this]
    exact natOf_natCast pF (by rw [hrc]; exact ha1)
  have hpre2 : ∀ s : ℕ, s ≤ 1 → algebraMap (ZMod p) K (2 * E.trace WChip.pre + (s : ZMod p)) = (a2 : K) →
      v = a2 / 2 := by
    intro s hs hy
    have h0 := CountsP1.eq_natCast_of_algK hy
    rw [eP, ← hvc] at h0
    have h0' : (((2 * v + s : ℕ)) : ZMod p) = (a2 : ZMod p) := by push_cast; exact h0
    have := natCast_inj_lt (F := ZMod p) (by rw [hrc]; omega) (by rw [hrc]; exact ha2) h0'
    omega
  refine ⟨j, j.isLt, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · have e0 : ServeH.keyVec5 (K := K) WalkHC.recLH E 0 = (a1 : K) := by rw [← h1, ← e]
    have e1 : ServeH.keyVec5 (K := K) WalkHC.recLH E 1 = (a2 : K) := by rw [← h2, ← e]
    refine ⟨hridx _ e0 (by simp [ServeH.keyVec5, WalkHC.recLH, cv, CoeffExpr.eval]), hpre2 0 (by norm_num) ?_⟩
    rw [← e1]
    simp [ServeH.keyVec5, WalkHC.recLH, cv, CoeffExpr.eval]
  · have e0 : ServeH.keyVec5 (K := K) WalkHC.recRH E 0 = (a1 : K) := by rw [← h1, ← e]
    have e1 : ServeH.keyVec5 (K := K) WalkHC.recRH E 1 = (a2 : K) := by rw [← h2, ← e]
    refine ⟨hridx _ e0 (by simp [ServeH.keyVec5, WalkHC.recRH, cv, CoeffExpr.eval]), hpre2 1 le_rfl ?_⟩
    rw [← e1]
    simp [ServeH.keyVec5, WalkHC.recRH, cv, CoeffExpr.eval]

/-! ## 3. `hprov` from a covering request list -/

/-- **`hprov` from the walk balance and a cover of the reads**: the walk's consumer list `reqs` has the counts of a
reference list `reqs0` in which every read `(σ, a) ∈ Rd` is the first two coordinates of a request. -/
theorem hprov_of_cover [CharP K p] {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hq : 2 ^ 63 < ringChar (ZMod p))
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < ringChar (ZMod p))
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr))
    (reqs : List (Fin 5 → K)) (provs : List ((Fin 5 → K) × K))
    (hbal : ∀ x, (reqs.count x : K) = pw provs x)
    (hsup : ∀ q ∈ provs, q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))
    (hbud : reqs.length < p)
    (Rd : Finset (ℕ × ℕ)) (hRd : ∀ s ∈ Rd, s.1 < p ∧ s.2 < p)
    (reqs0 : List (Fin 5 → K)) (hcnt : ∀ x, reqs.count x = reqs0.count x)
    (hcov : ∀ s ∈ Rd, ∃ x ∈ reqs0, x 0 = (s.1 : K) ∧ x 1 = (s.2 : K)) :
    ∀ s ∈ Rd, ∃ j < Pb.nW, natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) = s.1 ∧
      natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.pre) = s.2 / 2 := by
  intro s hs
  obtain ⟨x, hx0, h1, h2⟩ := hcov s hs
  have hx : x ∈ reqs := List.count_pos_iff.mp (by rw [hcnt]; exact List.count_pos_iff.mpr hx0)
  exact walk_row_of_req δ b hA hq hk hkn hkp hout reqs provs hbal hsup hbud hx h1 h2 (hRd s hs).1 (hRd s hs).2

/-- **`hprov` and `hprov'` of `trace_unique_closed`** (its hypothesis forms: `noPath`, `hkp` at `p`), for two
`AcceptsCanon2` tuples outside their walk events, from the two path balances (providers the walk path records,
`hsup`, `hsup'`), one reference list `reqs0` covering `Rd` and the count equalities of both consumer lists with it. -/
theorem hprov_pair [CharP K p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {r : RowsJ8} {g : ℕ} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr))
    (hout' : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M'.pubsW tr'))
    (reqsW reqsW' : List (Fin 5 → K)) (provsW provsW' : List ((Fin 5 → K) × K))
    (hbalW : ∀ x, (reqsW.count x : K) = pw provsW x)
    (hsup : ∀ q ∈ provsW, q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))
    (hbalW' : ∀ x, (reqsW'.count x : K) = pw provsW' x)
    (hsup' : ∀ q ∈ provsW', q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
      (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW))
    (hbud : reqsW.length < p) (hbud' : reqsW'.length < p)
    (noPath : Prop) (Rd : Finset (ℕ × ℕ)) (hRd : ¬ noPath → ∀ s ∈ Rd, s.1 < p ∧ s.2 < p)
    (reqs0 : List (Fin 5 → K)) (hcnt : ∀ x, reqsW.count x = reqs0.count x)
    (hcnt' : ∀ x, reqsW'.count x = reqs0.count x)
    (hcov : ¬ noPath → ∀ s ∈ Rd, ∃ x ∈ reqs0, x 0 = (s.1 : K) ∧ x 1 = (s.2 : K)) :
    (¬ noPath → ∀ s ∈ Rd, ∃ j < Pb.nW,
      natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) = s.1 ∧
        natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.pre) = s.2 / 2) ∧
    (¬ noPath → ∀ s ∈ Rd, ∃ j < Pb.nW,
      natOf ((envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.ridx) = s.1 ∧
        natOf ((envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.pre) = s.2 / 2) := by
  have hq : 2 ^ 63 < ringChar (ZMod p) := two63_lt_ringChar hpG
  have hkp' : Pb.kroots + Pb.nW < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hkp
  exact ⟨fun hnp => hprov_of_cover δ b h.1.1 hq hk hkn hkp' hout reqsW provsW hbalW hsup hbud Rd (hRd hnp)
      reqs0 hcnt (hcov hnp),
    fun hnp => hprov_of_cover δ b h'.1.1 hq hk hkn hkp' hout' reqsW' provsW' hbalW' hsup' hbud' Rd (hRd hnp)
      reqs0 hcnt' (hcov hnp)⟩

end Serve

/-! ## 4. The root serials of `RdP1` -/

section RdBound
variable (p : ℕ) [Fact p.Prime]
attribute [local instance] fact_rc

/-- **The root serials of the claim's reads are `≤ 2^31`** under `P1SizeOK` (`cells.idxOf` is at most the cell
count, `Rows31`). -/
theorem RdP1_fst_le {c : P8PublicClaim} (hok : P1SizeOK p c) : ∀ s ∈ RdP1 p c, s.1 ≤ 2 ^ 31 := by
  intro s hs
  cases hrun : runP1 c with
  | none =>
    unfold P1SizeOK at hok
    split at hok
    · next t r h => rw [hrun] at h; cases h
    · exact hok.elim
  | some x =>
    obtain ⟨t, r⟩ := x
    have h31 := ((P1SizeOK_of p hrun).mp hok).1
    rw [RdP1_of p hrun] at hs
    unfold RdOf at hs
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
    have hC : (DC p hrun).cells.length ≤ 2 ^ 31 := h31 _ (by simp [ComplJ8Of.sizesJ8])
    exact (List.idxOf_le_length).trans hC

end RdBound

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueProvP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueProvP1.roots_szOfClaim
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueProvP1.hk_canon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueProvP1.wEF_trace
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueProvP1.walk_row_of_req
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueProvP1.hprov_of_cover
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueProvP1.hprov_pair
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueProvP1.RdP1_fst_le
