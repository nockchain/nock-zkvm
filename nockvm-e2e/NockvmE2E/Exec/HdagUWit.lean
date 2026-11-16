/-
  NockvmE2E/Exec/HdagUWit.lean   (non-vacuity: a Goldilocks `RapAirJ (ZMod p) KC` toy)

  One toy serves three checks: (i) every hypothesis of `hdagU_of_tie` proved (`w_hdagU`), (ii) `opsU_of_layout` instantiated (`w_opsU`),
  (iii) `hlink_regroup` at `KC` with the identity regroup (`w_hlink`).
  Toy: `summands := []`, `Holds := True`, one table, one column, chip `[.var 0 0]`, `ns = nsK = 1`, `d = 1` (so `nq = 0`), `r = 2`.
-/
import NockvmE2E.Exec.HdagU
import NockvmE2E.Exec.E2EInstGen
import NockvmE2E.Exec.J8Shape

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Polynomial

namespace NockvmE2E.Exec.HdagU
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.Tr NockvmE2E.Rap NockvmE2E.Deep NockvmE2E.J8
open NockvmE2E.Exec.E2ELR NockvmE2E.Exec.DagSem NockvmE2E.Succ Fri.Spec Domain

def wChip1 : Chip :=
  { id := "w1", shared := #[], cons := #[{ kind := 0, round := 0, deg := 1, e := .var 0 0 }],
    colRound := #[0], sharedK := #[], consK := #[false], baseCols := 1, width := 1 }

def wXI : ExecInst :=
  { NockvmE2E.Exec.J8Shape.toyShape with
    nD := 3, hN := 1, hGen := 2, hShift := 1, nc := 1, nq := 0, colKind := #[0], blockOf := #[0], pre := #[#[]], pubOf := #[],
    nCoins := #[0, 0], derived := #[],
    tabs := #[{ hN := 1, col0 := 0, nc := 1, npub := 0, pubBase := 0, chip := wChip1 }] }

abbrev Φw : CoinFrame := ⟨1, fun _ => 0⟩

noncomputable def wJ : RapAirJ (ZMod p) KC where
  Φ0 := Φw
  ι0 := Fin 1
  fι := inferInstance
  dι := inferInstance
  colRound0 := fun _ => 0
  hround := fun _ => by norm_num
  hcoin := fun _ => by show 0 < 2; norm_num
  pre := fun _ => none
  Msg := Unit
  Mcode := Unit
  fM := inferInstance
  dM := inferInstance
  dec := id
  Acc := fun _ _ _ => True
  Holds := True
  summands := []
  sound := fun _ _ _ _ _ => trivial
  eps := by simp [epsilonOf]
  oneRound := by intro s hs; simp at hs
  H := {1}
  T := 1
  Ht := fun _ => {1}
  hHt := fun _ => subset_rfl
  ωt := fun _ => zv wXI.hGen
  r := 2
  off := fun _ k => zv wXI.hGen ^ k.1
  hoff := fun _ _ => rfl
  tabC := fun _ => 0
  ns := 1
  tabS := fun _ => 0
  d := 1
  hd2 := Or.inr (fun _ => rfl)
  C := fun _ _ _ => MvPolynomial.X (0, 0)
  hdeg := fun _ _ _ => by simp
  hCreads := fun _ _ _ _ _ => rfl
  Pub := fun _ _ => True
  StmtOK := True
  acc_of := fun _ _ _ _ _ _ _ => trivial
  cap_ns := by norm_num
  cap_d := by norm_num
  cap_m := by simp
  cap_H := by simp

instance : NeZero wJ.r := ⟨by show (2 : ℕ) ≠ 0; norm_num⟩

noncomputable def wPR : PubRead wJ where
  pub := fun _ => false
  ppt := fun _ => 0
  rd := fun _ => ()
  gen := xr
  hrd := fun _ _ _ => rfl
  hCpub := fun _ _ _ _ _ => rfl


theorem w_hNH : (0 : ℕ) ≤ wJ.H.card := Nat.zero_le _
theorem w_hpd : ∀ j c, wJ.pre j = some c → c.natDegree ≤ wJ.H.card := by
  intro j c h; simp [wJ] at h

def wG : Regroup wJ.ns 1 where
  grp := fun _ => 0
  crd := fun _ => 0
  hinj := fun j j' _ _ => Fin.ext (by have := j.2; have := j'.2; simp [wJ] at *; omega)

noncomputable def wvTOf : Array (Array VF.K3) → wJ.ι0 × Fin wJ.r → KC := fun vT q => toKV (vT[q.1.1]!)[q.2.1]!

theorem wtab (t : Fin wXI.tabs.size) : wXI.tabs[t] = { hN := 1, col0 := 0, nc := 1, npub := 0, pubBase := 0, chip := wChip1 } := by
  obtain ⟨t, ht⟩ := t
  have : t = 0 := by simp [wXI] at ht; omega
  subst this; rfl

theorem wmem {t : TabInst} (ht : t ∈ wXI.tabs.toList) :
    t = { hN := 1, col0 := 0, nc := 1, npub := 0, pubBase := 0, chip := wChip1 } := by
  simpa [wXI] using ht

def wtX : Fin 1 → Fin wXI.tabs.size := fun _ => ⟨0, by simp [wXI]⟩
def wtJ : Fin wXI.tabs.size → Fin wJ.T := fun _ => ⟨0, Nat.one_pos⟩

theorem w_hns : 1 = (wXI.tabs.toList.map (·.chip.cons.size)).sum := by simp [wXI, wChip1]

theorem w_htabX : ∀ i : Fin 1, (wtX i).1 = (flatIdx (wXI.tabs.toList.map (·.chip.cons.size)) i.1).1 := by
  intro i
  have : i.1 = 0 := by omega
  simp [this, flatIdx, wXI, wChip1, wtX]

theorem w_hread : ∀ t ∈ wXI.tabs.toList, chipReadsLt t.chip (t.nc - t.npub) t.npub 19 = true := by
  intro t ht; rw [wmem ht]; simp [chipReadsLt, exReadsLt, wChip1]

theorem w_hcanon : ∀ t ∈ wXI.tabs.toList, chipCanon t.chip = true := by
  intro t ht; rw [wmem ht]; simp [chipCanon, exCanon, wChip1]

theorem w_hpreC : ∀ c : ℕ, ∀ x ∈ wXI.pre[c]!.toList, canon x := by
  intro c x hx
  have h1 : wXI.pre[c]! = #[] := by
    rcases Nat.lt_or_ge c 1 with h | h
    · obtain rfl : c = 0 := by omega
      rfl
    · rw [getElem!_neg _ _ (by simp [wXI]; omega)]; rfl
  simp [h1] at hx

theorem w_hS : canon wXI.hShift := by
  show canon (1 : UInt64)
  unfold canon; rw [p_lit]; decide

theorem w_hkind : ∀ (t : Fin wXI.tabs.size) c, c < wXI.tabs[t].nc - wXI.tabs[t].npub →
    wXI.colKind[wXI.tabs[t].col0 + c]! = 0 ∨ wXI.colKind[wXI.tabs[t].col0 + c]! = 1 := by
  intro t c hc
  rw [wtab t] at hc ⊢
  left
  have : c = 0 := by simp at hc; omega
  subst this; rfl

theorem w_hcur0 : ∀ (t : Fin wXI.tabs.size) c, c < wXI.tabs[t].nc - wXI.tabs[t].npub →
    wXI.colKind[wXI.tabs[t].col0 + c]! = 0 →
      wJ.pre ((fun _ _ => (0 : Fin 1)) t c) = none ∧ ∀ vT k, wvTOf vT ((fun _ _ => (0 : Fin 1)) t c, k) = toKV (vT[wXI.tabs[t].col0 + c]!)[k.1]! := by
  intro t c hc _
  rw [wtab t] at hc ⊢
  have : c = 0 := by simp at hc; omega
  subst this
  exact ⟨rfl, fun vT k => rfl⟩

theorem w_hcur1 : ∀ (t : Fin wXI.tabs.size) c, c < wXI.tabs[t].nc - wXI.tabs[t].npub →
    wXI.colKind[wXI.tabs[t].col0 + c]! = 1 →
      wJ.pre ((fun _ _ => (0 : Fin 1)) t c) = some (((List.range wXI.pre[wXI.tabs[t].col0 + c]!.size).map fun m =>
        Polynomial.monomial m (zv (wXI.pre[wXI.tabs[t].col0 + c]!)[m]!)).sum) := by
  intro t c hc hk
  rw [wtab t] at hc hk
  have : c = 0 := by simp at hc; omega
  subst this
  exact absurd hk (by decide)

theorem w_hpubJ : ∀ (t : Fin wXI.tabs.size) s vT, s < wXI.tabs[t].npub →
    wvTOf vT ((fun _ _ => (0 : Fin 1)) t s, 0) = toKV (vT[wXI.pubOf[wXI.tabs[t].pubBase + s]!]!)[0]! := by
  intro t s vT hs
  rw [wtab t] at hs
  simp at hs

theorem w_hdom : wJ.H = (Finset.range wXI.hN).image (fun i => zv wXI.hShift * zv wXI.hGen ^ i) := by
  show ({1} : Finset (ZMod p)) = _
  simp [wXI, zv]

theorem w_hdomt : ∀ t : Fin wXI.tabs.size, wJ.Ht (wtJ t) = (Finset.range wXI.tabs[t].hN).image (fun i => zv wXI.hShift * zv wXI.hGen ^ i) := by
  intro t; rw [wtab t]; exact w_hdom

theorem w_hinj : Set.InjOn (fun i => zv wXI.hShift * zv wXI.hGen ^ i) (Finset.range wXI.hN : Set ℕ) := by
  intro a ha b hb _
  simp [wXI] at ha hb; omega

theorem w_hslot : ∀ (c0 : Block (extFrame wJ.Φ0 2) KC 0) (c1 : Block (extFrame wJ.Φ0 2) KC 1)
    (c2 : Block (extFrame wJ.Φ0 2) KC 2) (c3 : Block (extFrame wJ.Φ0 2) KC 3), ∀ q < 19,
    toKV (slotsAt wXI ((fun _ => ([] : List ℕ)) c0) ((fun _ => ([] : List ℕ)) c1))[q]! =
      (fun (_ : Coins wJ.Φ0 KC) (_ : ℕ) => (0 : KC)) (restr 2 (chiOfBlocks c0 c1 c2 c3)) q := by
  intro c0 c1 c2 c3 q _
  have : slotsAt wXI [] [] = #[] := by
    simp [slotsAt, wXI, k3s]
  simp only [this]
  exact toKV_default

theorem w_htie : ∀ (i : Fin 1) (χ : Coins wJ.Φ0 KC) (v val : wJ.ι0 × Fin wJ.r → KC),
    ∑ j ∈ Finset.univ.filter (fun j : Fin wJ.ns => wG.grp j = i),
        (fun _ => (1 : KC)) (wG.crd j) * MvPolynomial.aeval val (wJ.C χ (wPR.rd (fun c => v (c, 0))) j) =
      (evalDagK wXI.tabs[wtX i].chip
        ⟨fun c => val ((fun _ _ => (0 : Fin 1)) (wtX i) c, 0),
         fun c => val ((fun _ _ => (0 : Fin 1)) (wtX i) c, ⟨1 % wJ.r, Nat.mod_lt _ (NeZero.pos _)⟩),
         fun s => coord0 (v ((fun _ _ => (0 : Fin 1)) (wtX i) s, 0)), (fun (_ : Coins wJ.Φ0 KC) (_ : ℕ) => (0 : KC)) χ,
         wXI.tabs[wtX i].chip.baseCols⟩)[(flatIdx (wXI.tabs.toList.map (·.chip.cons.size)) i.1).2]! := by
  intro i χ v val
  have hi : i = 0 := Fin.ext (by omega)
  subst hi
  have hu : ∀ j : Fin wJ.ns, j = ⟨0, Nat.one_pos⟩ := fun j => Fin.ext (by have := j.2; simp [wJ] at this; omega)
  have hm : (⟨0, Nat.one_pos⟩ : Fin wJ.ns) ∈ Finset.univ.filter (fun j : Fin wJ.ns => wG.grp j = 0) := by
    simp [wG]
  rw [Finset.sum_eq_single_of_mem _ hm (fun b _ hb => absurd (hu b) hb)]
  have hc : wXI.tabs[wtX 0] = { hN := 1, col0 := 0, nc := 1, npub := 0, pubBase := 0, chip := wChip1 } := wtab _
  rw [hc]
  have hf : flatIdx (wXI.tabs.toList.map (·.chip.cons.size)) 0 = (0, 0) := by
    simp [wXI, wChip1, flatIdx]
  simp [wJ, hf, evalDagK, memoK, evKC, wChip1]
  exact MvPolynomial.aeval_X _ _

theorem w_hle : ∀ t ∈ wXI.tabs.toList, t.hN ≤ wXI.hN := by
  intro t ht; rw [wmem ht]; simp [wXI]
theorem w_hcolB : ∀ t ∈ wXI.tabs.toList, t.col0 + t.nc ≤ wXI.nc := by
  intro t ht; rw [wmem ht]; simp [wXI]
theorem w_hpubB : ∀ t ∈ wXI.tabs.toList, t.pubBase + t.npub ≤ wXI.pubOf.size := by
  intro t ht; rw [wmem ht]; simp [wXI]
theorem w_hnpub : ∀ t ∈ wXI.tabs.toList, t.npub ≤ t.nc := by
  intro t ht; rw [wmem ht]; simp

set_option maxHeartbeats 1000000 in
/-- (i) **every hypothesis of `hdagU_of_tie` holds at the toy** (the conclusion is the `UniLinksN.hdagU` statement for the regrouped
`deepParamsJ`/`airJ` of `wJ`) -/
noncomputable def w_hdagU :=
  hdagU_of_tie wJ wPR NockvmE2E.Exec.DomIdx.ωT 0 0 w_hNH w_hpd wXI wG (fun _ => (1 : KC))
    (fun _ => ([] : List ℕ)) (fun _ => ([] : List ℕ)) wvTOf w_hns wtX wtJ (fun _ => rfl) w_htabX
    (fun _ _ => (0 : Fin 1)) (fun _ _ => (0 : Fin 1)) w_hread w_hcanon w_hpreC w_hS w_hle w_hcolB w_hpubB w_hnpub
    w_hkind w_hcur0 w_hcur1 w_hpubJ rfl rfl (fun _ _ => rfl) (fun (_ : Coins wJ.Φ0 KC) (_ : ℕ) => (0 : KC))
    w_hslot w_hdom w_hdomt w_hinj w_htie

/-! ## (ii) `opsU_of_layout` at the toy, (iii) `hlink_regroup` at `KC` -/

noncomputable abbrev wP := deepParamsJ wJ wPR NockvmE2E.Exec.DomIdx.ωT 0 0 w_hNH w_hpd
noncomputable abbrev wA := airJ wJ wPR NockvmE2E.Exec.DomIdx.ωT 0 0 w_hNH w_hpd

theorem wι0 (c : wJ.ι0) : c = (0 : Fin 1) := by
  have h : (show Fin 1 from c).1 < 1 := (show Fin 1 from c).2
  exact Fin.ext (by simp; omega)

set_option maxHeartbeats 1000000 in
noncomputable def w_opsU :=
  NockvmE2E.Exec.InstGen.opsU_of_layout wXI wP (rfl : wP.R = 2) (r := 2) wA (rfl : 2 = wXI.r) (rfl : wXI.nq = wP.nq)
    (fun c hc => by have : c = 0 := by simp [wXI] at hc; omega
                    subst this; decide)
    (Equiv.refl (Fin 1))
    (fun c => by rw [wι0 c]; rfl)
    (fun q => absurd q.2 (by simp [wP, deepParamsJ, wJ]))
    (fun c k ζ h => absurd h (by rw [wι0 c]; decide))
    (fun c k ζ _ => by simp [wA, airJ, wPR, wJ, psiV]) (m := 1) rfl

theorem w_hb : ∀ c : Fin 3 → ZMod p, (∀ k, (∀ j, wG.crd j ≠ k) → c k = 0) →
    ∑ k, algebraMap (ZMod p) KC (c k) * (fun _ => (1 : KC)) k = 0 → ∀ k, c k = 0 := by
  intro c h0 hs k
  have h1 : c 1 = 0 := h0 1 (fun j => by simp [wG])
  have h2 : c 2 = 0 := h0 2 (fun j => by simp [wG])
  have h3 : c 0 = 0 := by
    simp [Fin.sum_univ_three, h1, h2] at hs
    exact hs
  fin_cases k <;> simp [h1, h2, h3]

/-- (iii) the regroup at `KC` (identity regroup, `b = 1`): `hlink_regroup` instantiated -/
noncomputable def w_hlink :=
  hlink_regroup wJ wPR NockvmE2E.Exec.DomIdx.ωT 0 0 w_hNH w_hpd wG (fun _ => (1 : KC)) w_hb

end NockvmE2E.Exec.HdagU

#print axioms NockvmE2E.Exec.HdagU.w_hdagU
#print axioms NockvmE2E.Exec.HdagU.w_opsU
#print axioms NockvmE2E.Exec.HdagU.w_hlink
#print axioms NockvmE2E.Exec.HdagU.w_htie
