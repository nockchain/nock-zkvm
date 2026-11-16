/-
  NockvmE2E/Exec/HdagU.lean

  `hdagU_of_tie`: the `UniLinksN.hdagU` conclusion for the REGROUPED `deepParamsJ`/`airJ` at an abstract `J : RapAirJ (ZMod p) KC`,
  from the instance layout hypotheses and the evaluation-level tie `htie`.  Also the bridges left:
  `chipCanon_ExCan` (Bool -> Prop) and the canonicity of the `pubAt`/`curNxtAt`/slot environments.
-/
import NockvmE2E.Exec.DagSem
import NockvmE2E.J8.Regroup

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Polynomial

namespace NockvmE2E.Exec.HdagU
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.Tr NockvmE2E.Rap NockvmE2E.Deep NockvmE2E.J8
open NockvmE2E.Exec.E2ELR NockvmE2E.Exec.DagSem NockvmE2E.Succ Fri.Spec Domain

/-! ## 1. canonicity bridges -/

theorem canon_of_based (v : UInt64) (h : VF.based v.toNat = true) : canon v := by
  unfold canon; unfold VF.based at h
  have := of_decide_eq_true h
  rw [p_lit]; exact this

theorem exCanon_ExCan : ∀ e : Ex, exCanon e = true → ExCan e
  | .var _ _, _ => trivial
  | .cF v, h => canon_of_based v h
  | .add a b, h => by
    simp only [exCanon, Bool.and_eq_true] at h
    exact ⟨exCanon_ExCan a h.1, exCanon_ExCan b h.2⟩
  | .sub a b, h => by
    simp only [exCanon, Bool.and_eq_true] at h
    exact ⟨exCanon_ExCan a h.1, exCanon_ExCan b h.2⟩
  | .mul a b, h => by
    simp only [exCanon, Bool.and_eq_true] at h
    exact ⟨exCanon_ExCan a h.1, exCanon_ExCan b h.2⟩
  | .neg a, h => exCanon_ExCan a h
  | .pow a _, h => exCanon_ExCan a h
  | .extVar _ _, _ => trivial
  | .chal _, _ => trivial
  | .ref _, _ => trivial

/-- **`chipCanon_iff_ExCan`** (Bool -> Prop bridge; both directions are not needed, the forward one is the use) -/
theorem chipCanon_ExCan (ch : Chip) (h : chipCanon ch = true) :
    (∀ s ∈ ch.shared.toList, ExCan s) ∧ (∀ c ∈ ch.cons.toList, ExCan c.e) := by
  unfold chipCanon at h
  simp only [Bool.and_eq_true, Array.all_eq_true] at h
  refine ⟨fun s hs => ?_, fun c hc => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hs)
    exact exCanon_ExCan _ (h.1 i hi)
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hc)
    exact exCanon_ExCan _ (h.2 i hi)

theorem canon3_default : canon3 (default : VF.K3) := canon3_zero

theorem canon3_getA (a : Array VF.K3) (h : ∀ x ∈ a, canon3 x) (i : ℕ) : canon3 a[i]! := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi]; exact h _ (Array.getElem_mem hi)
  · rw [getElem!_neg a i hi]; exact canon3_default

theorem canon3_getAA (vT : Array (Array VF.K3)) (h : ∀ a ∈ vT, ∀ x ∈ a, canon3 x) (i k : ℕ) : canon3 (vT[i]!)[k]! := by
  by_cases hi : i < vT.size
  · rw [getElem!_pos vT i hi]; exact canon3_getA _ (h _ (Array.getElem_mem hi)) k
  · rw [getElem!_neg vT i hi]
    exact canon3_getA #[] (by simp) k

theorem canon_default : canon (default : UInt64) := canon3_zero.1

/-- `extract` read (in range of the extraction window) -/
theorem extract_get {α : Type} [Inhabited α] (a : Array α) (s e i : ℕ) (hi : i < e - s) :
    (a.extract s e)[i]! = a[s + i]! := by
  by_cases h : s + i < a.size
  · have h1 : i < (a.extract s e).size := by simp; omega
    rw [getElem!_pos _ i h1, getElem!_pos _ (s + i) h]
    simp [Array.getElem_extract]
  · have h1 : ¬ i < (a.extract s e).size := by simp; omega
    rw [getElem!_neg _ i h1, getElem!_neg _ (s + i) h]

theorem canon3_extract (a : Array VF.K3) (h : ∀ i : ℕ, canon3 a[i]!) (s e i : ℕ) : canon3 (a.extract s e)[i]! := by
  by_cases hi : i < e - s
  · rw [extract_get a s e i hi]; exact h _
  · have h1 : ¬ i < (a.extract s e).size := by simp; omega
    rw [getElem!_neg _ i h1]; exact canon3_default

theorem canon_extract (a : Array UInt64) (h : ∀ i : ℕ, canon a[i]!) (s e i : ℕ) : canon (a.extract s e)[i]! := by
  by_cases hi : i < e - s
  · rw [extract_get a s e i hi]; exact h _
  · have h1 : ¬ i < (a.extract s e).size := by simp; omega
    rw [getElem!_neg _ i h1]; exact canon_default

/-- every public value `pubAt` is canonical -/
theorem canon_pubAt (XI : ExecInst) (vT : Array (Array VF.K3)) (hvT : ∀ a ∈ vT, ∀ x ∈ a, canon3 x) (i : ℕ) :
    canon (pubAt XI vT)[i]! := by
  unfold pubAt
  by_cases hi : i < XI.pubOf.size
  · rw [getElem!_pos _ i (by simpa using hi)]
    simp only [Array.getElem_map]
    exact (canon3_getAA vT hvT _ 0).1
  · rw [getElem!_neg _ i (by simpa using hi)]; exact canon_default

/-- every entry of the `curNxtAt` arrays is canonical -/
theorem canon_curNxtAt (XI : ExecInst) (ζ : VF.K3) (vT : Array (Array VF.K3)) (hvT : ∀ a ∈ vT, ∀ x ∈ a, canon3 x)
    (hpre : ∀ c : ℕ, ∀ x ∈ XI.pre[c]!.toList, canon x) (c : ℕ) :
    canon3 (curNxtAt XI ζ vT).1[c]! ∧ canon3 (curNxtAt XI ζ vT).2[c]! := by
  have h := (curNxtAt_fold XI ζ vT XI.nc le_rfl).2.2 c
  rw [← curNxtAt_eq] at h
  rw [h.1, h.2]
  by_cases hc : c < XI.nc
  · simp only [hc, ite_true]
    constructor
    · unfold curVal
      split
      · exact canon3_getAA vT hvT _ 0
      · exact canon_hornerG _ _ (hpre c)
      · exact canon3_zero
    · unfold nxtVal
      split
      · split
        · exact canon3_getAA vT hvT _ 1
        · exact canon3_zero
      · exact canon_hornerG _ _ (hpre c)
      · exact canon3_zero
  · simp only [hc, ite_false]; exact ⟨canon3_zero, canon3_zero⟩

/-- `coord0` of a `KC` value -/
noncomputable def coord0 (y : KC) : ZMod p := (NockvmE2E.Exec.E2EResid.sK y).c0.toZ

theorem coord0_toKV (x : VF.K3) : coord0 (toKV x) = zv x.c0 := by
  have h : NockvmE2E.Exec.E2EResid.sK (toKV x) = t3 x := by
    apply Exec.K3.toK_injective
    rw [NockvmE2E.Exec.E2EResid.toK_sK, toKV_eq_toK]
  unfold coord0
  rw [h]
  simp only [t3]
  rw [Gold.ofU64_toZ]; rfl


/-! ## 2. the preprocessed polynomial evaluates as the Horner sum -/

theorem eval_prePoly (c : ℕ → UInt64) (n : ℕ) (y : KC) :
    eval y ((((List.range n).map fun m => Polynomial.monomial m (zv (c m))).sum).map (algebraMap (ZMod p) KC)) =
      ∑ m ∈ Finset.range n, psiV (c m) * y ^ m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Polynomial.map_add, eval_add, ih, Finset.sum_range_succ]
    simp [psiV, Polynomial.eval_monomial]

/-! ## 3. a table's constraint values in `KC` -/

theorem toKV_tabCvAt (XI : ExecInst) (slots : Array VF.K3) (ζ : VF.K3) (vT : Array (Array VF.K3)) (hC : CanonIn slots ζ vT)
    (hpre : ∀ c : ℕ, ∀ x ∈ XI.pre[c]!.toList, canon x) (t : TabInst) (hcan : chipCanon t.chip = true)
    (hread : chipReadsLt t.chip (t.nc - t.npub) t.npub 19 = true) (e' : KEnv) (hbc : e'.bc = t.chip.baseCols)
    (hc : ∀ i < t.nc - t.npub, toKV (curNxtAt XI ζ vT).1[t.col0 + i]! = e'.cur i)
    (hn : ∀ i < t.nc - t.npub, toKV (curNxtAt XI ζ vT).2[t.col0 + i]! = e'.next i)
    (hp : ∀ s < t.npub, zv (pubAt XI vT)[t.pubBase + s]! = e'.pub s)
    (hch : ∀ q < 19, toKV slots[q]! = e'.chal q) (l : ℕ) :
    toKV (tabCvAt XI slots ζ vT t)[l]! = (evalDagK t.chip e')[l]! := by
  obtain ⟨hsh, hcs⟩ := chipCanon_ExCan _ hcan
  have hcn := fun c => canon_curNxtAt XI ζ vT hC.2.2 hpre c
  have hE := toKV_evalDag t.chip
    { cur := (curNxtAt XI ζ vT).1.extract t.col0 (t.col0 + t.nc), next := (curNxtAt XI ζ vT).2.extract t.col0 (t.col0 + t.nc),
      pub := (pubAt XI vT).extract t.pubBase (t.pubBase + t.npub), chal := slots, bc := t.chip.baseCols }
    (fun i => canon3_extract _ (fun c => (hcn c).1) _ _ i) (fun i => canon3_extract _ (fun c => (hcn c).2) _ _ i)
    (fun i => canon_extract _ (canon_pubAt XI vT hC.2.2) _ _ i) (fun i => canon3_getA _ hC.1 i) hsh hcs l
  unfold tabCvAt
  rw [hE]
  rw [evalDagK_congr t.chip (t.nc - t.npub) t.npub 19 hread _ e' rfl hbc _ _ _ _]
  · intro i hi
    show toKV ((curNxtAt XI ζ vT).1.extract t.col0 (t.col0 + t.nc))[i]! = _
    rw [extract_get _ _ _ _ (by omega)]; exact hc i hi
  · intro i hi
    show toKV ((curNxtAt XI ζ vT).2.extract t.col0 (t.col0 + t.nc))[i]! = _
    rw [extract_get _ _ _ _ (by omega)]; exact hn i hi
  · intro s hs
    show zv ((pubAt XI vT).extract t.pubBase (t.pubBase + t.npub))[s]! = _
    rw [extract_get _ _ _ _ (by omega)]; exact hp s hs
  · intro q hq; exact hch q hq

/-! ## 3b. the opened-value function of `airJ.Cv`, abstracted (so that instance paths agree with `airJ`'s) -/

section GenCv
variable {B K : Type} [Field B] [Fintype B] [DecidableEq B] [NonBinaryField K] [Algebra B K] [Fintype K] [DecidableEq K] {n : ℕ}

noncomputable def valJ (J : RapAirJ B K) (y : K) (v : J.ι0 × Fin J.r → K) : J.ι0 × Fin J.r → K := fun p =>
  match J.pre p.1 with
  | some c => eval (y * algebraMap B K (J.off (J.tabC p.1) p.2)) (c.map (algebraMap B K))
  | none => v p

theorem regroup_Cv (J : RapAirJ B K) [NeZero J.r] (pr : PubRead J) (ω : SmoothCosetFftDomain n K) (δ : NNReal) (N : ℕ)
    (hNH : N ≤ J.H.card) (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card) {nsK : ℕ} (G : Regroup J.ns nsK)
    (gb : Fin 3 → K) (χ : Coins (extFrame J.Φ0 2) K) (y : K) (i : Fin nsK) (v : J.ι0 × Fin J.r → K) :
    ((airJ J pr ω δ N hNH hpd).regroup G gb).Cv χ y i v =
      ∑ j ∈ Finset.univ.filter (fun j => G.grp j = i), gb (G.crd j) *
        (MvPolynomial.aeval (valJ J y v) (J.C (restr 2 χ) (pr.rd fun c => v (c, 0)) j) *
          eval y ((Zout J.H (J.Ht (J.tabS j))).map (algebraMap B K))) := rfl
end GenCv

/-! ## 4. `hdagU` at an abstract `J` under the tie -/

section HD
variable {n : ℕ} (J : RapAirJ (ZMod p) KC) [NeZero J.r] (pr : PubRead J) (ω : SmoothCosetFftDomain n KC)
  (δ : NNReal) (N : ℕ) (hNH : N ≤ J.H.card) (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card)
  (XI : ExecInst) {nsK : ℕ} (G : Regroup J.ns nsK)

set_option maxHeartbeats 2000000 in
theorem hdagU_of_tie
    (gb : Fin 3 → KC)
    (e0 : Block (extFrame J.Φ0 2) KC 0 → List ℕ) (e1 : Block (extFrame J.Φ0 2) KC 1 → List ℕ)
    (vTOf : Array (Array VF.K3) → J.ι0 × Fin J.r → KC)
    (hns : nsK = (XI.tabs.toList.map (·.chip.cons.size)).sum)
    (tabX : Fin nsK → Fin XI.tabs.size) (tabJ : Fin XI.tabs.size → Fin J.T)
    (htabS : ∀ j, J.tabS j = tabJ (tabX (G.grp j)))
    (htabX : ∀ i : Fin nsK, (tabX i).1 = (flatIdx (XI.tabs.toList.map (·.chip.cons.size)) i.1).1)
    (colJ : Fin XI.tabs.size → ℕ → J.ι0) (pubJ : Fin XI.tabs.size → ℕ → J.ι0)
    -- instance shape facts (NEW w.r.t. the scratch: all `j8ShapeOk`-level, none needs π/FlatOk)
    (hread : ∀ t ∈ XI.tabs.toList, chipReadsLt t.chip (t.nc - t.npub) t.npub 19 = true)
    (hcanon : ∀ t ∈ XI.tabs.toList, chipCanon t.chip = true)
    (hpreC : ∀ c : ℕ, ∀ x ∈ XI.pre[c]!.toList, canon x)
    (hS : canon XI.hShift)
    (hle : ∀ t ∈ XI.tabs.toList, t.hN ≤ XI.hN)
    (hcolB : ∀ t ∈ XI.tabs.toList, t.col0 + t.nc ≤ XI.nc)
    (hpubB : ∀ t ∈ XI.tabs.toList, t.pubBase + t.npub ≤ XI.pubOf.size)
    (hnpub : ∀ t ∈ XI.tabs.toList, t.npub ≤ t.nc)
    (hkind : ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub →
      XI.colKind[XI.tabs[t].col0 + c]! = 0 ∨ XI.colKind[XI.tabs[t].col0 + c]! = 1)
    (hcur0 : ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub → XI.colKind[XI.tabs[t].col0 + c]! = 0 →
      J.pre (colJ t c) = none ∧ ∀ vT k, vTOf vT (colJ t c, k) = toKV (vT[XI.tabs[t].col0 + c]!)[k.1]!)
    (hcur1 : ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub → XI.colKind[XI.tabs[t].col0 + c]! = 1 →
      J.pre (colJ t c) = some (((List.range XI.pre[XI.tabs[t].col0 + c]!.size).map fun m =>
        Polynomial.monomial m (zv (XI.pre[XI.tabs[t].col0 + c]!)[m]!)).sum))
    (hpubJ : ∀ (t : Fin XI.tabs.size) s vT, s < XI.tabs[t].npub →
      vTOf vT (pubJ t s, 0) = toKV (vT[XI.pubOf[XI.tabs[t].pubBase + s]!]!)[0]!)
    (hr2 : XI.r = 2) (hJr : J.r = 2) (hoff : ∀ t (k : Fin J.r), J.off t k = zv XI.hGen ^ k.1)
    (chalK : Coins J.Φ0 KC → ℕ → KC)
    (hslot : ∀ c0 c1 c2 c3, ∀ q < 19, toKV (slotsAt XI (e0 c0) (e1 c1))[q]! = chalK (restr 2 (chiOfBlocks c0 c1 c2 c3)) q)
    (hdom : J.H = (Finset.range XI.hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i))
    (hdomt : ∀ t : Fin XI.tabs.size, J.Ht (tabJ t) = (Finset.range XI.tabs[t].hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i))
    (hinj : Set.InjOn (fun i => zv XI.hShift * zv XI.hGen ^ i) (Finset.range XI.hN : Set ℕ))
    (htie : ∀ (i : Fin nsK) (χ : Coins J.Φ0 KC) (v val : J.ι0 × Fin J.r → KC),
      ∑ j ∈ Finset.univ.filter (fun j => G.grp j = i),
          gb (G.crd j) * MvPolynomial.aeval val (J.C χ (pr.rd (fun c => v (c, 0))) j) =
        (evalDagK XI.tabs[tabX i].chip
          ⟨fun c => val (colJ (tabX i) c, 0), fun c => val (colJ (tabX i) c, ⟨1 % J.r, Nat.mod_lt _ (NeZero.pos _)⟩),
           fun s => coord0 (v (pubJ (tabX i) s, 0)), chalK χ, XI.tabs[tabX i].chip.baseCols⟩)[
          (flatIdx (XI.tabs.toList.map (·.chip.cons.size)) i.1).2]!) :
    ∀ (c0 : Block (extFrame J.Φ0 2) KC 0) (c1 : Block (extFrame J.Φ0 2) KC 1) (c2 : Block (extFrame J.Φ0 2) KC 2)
      (c3 : Block (extFrame J.Φ0 2) KC 3) (ζ : VF.K3) (vT : Array (Array VF.K3)),
      CanonIn (slotsAt XI (e0 c0) (e1 c1)) ζ vT →
      ∀ i : Fin ((deepParamsJ J pr ω δ N hNH hpd).regroup G gb).ns,
        (termsAt XI (slotsAt XI (e0 c0) (e1 c1)) ζ vT)[i.1]? =
          some (((airJ J pr ω δ N hNH hpd).regroup G gb).Cv (chiOfBlocks c0 c1 c2 c3) (toKV ζ) i (vTOf vT)) := by
  intro c0 c1 c2 c3 ζ vT hC i
  have hi' : i.1 < nsK := i.2
  have hi : i.1 < (XI.tabs.toList.map (·.chip.cons.size)).sum := hns ▸ hi'
  have htx := htabX (show Fin nsK from i)
  have hlt : (flatIdx (XI.tabs.toList.map (·.chip.cons.size)) i.1).1 < XI.tabs.size := htx ▸ (tabX (show Fin nsK from i)).2
  rw [termsAt_get? XI _ ζ vT i.1 hi hlt]
  have hTab : XI.tabs[(flatIdx (XI.tabs.toList.map (·.chip.cons.size)) i.1).1] = XI.tabs[tabX (show Fin nsK from i)] := by
    simp only [← htx]; rfl
  rw [hTab]
  set tx := tabX (show Fin nsK from i) with htxd
  set l := (flatIdx (XI.tabs.toList.map (·.chip.cons.size)) i.1).2 with hl
  have htmem : XI.tabs[tx] ∈ XI.tabs.toList := Array.getElem_mem_toList _
  have hmult := multOf_Zout XI XI.tabs[tx] ζ hC.2.1 hS J.H (J.Ht (tabJ tx)) hdom (hdomt tx) (hle _ htmem) hinj
  have hr : J.r = 2 := hJr
  have h1r : 1 % J.r = 1 := by rw [hr]
  -- the opened-value function of `airJ.Cv`
  set T : TabInst := XI.tabs[tx] with hTd
  have hTmem : T ∈ XI.tabs.toList := htmem
  let val : J.ι0 × Fin J.r → KC := valJ J (toKV ζ) (vTOf vT)
  have hcolle : ∀ c, c < T.nc - T.npub → T.col0 + c < XI.nc := fun c hc => by
    have := hcolB _ hTmem; have := hnpub _ hTmem; omega
  let E : KEnv := ⟨fun c => val (colJ tx c, 0), fun c => val (colJ tx c, ⟨1 % J.r, Nat.mod_lt _ (NeZero.pos _)⟩),
         fun s => coord0 (vTOf vT (pubJ tx s, 0)), chalK (restr 2 (chiOfBlocks c0 c1 c2 c3)), T.chip.baseCols⟩
  have hcg : ∀ c < T.nc - T.npub, toKV (curNxtAt XI ζ vT).1[T.col0 + c]! = E.cur c := by
    intro c hc
    have hlt := hcolle c hc
    rw [(curNxtAt_get XI ζ vT _ hlt).1]
    rcases hkind tx c hc with hk | hk
    · have hk' : XI.colKind[T.col0 + c]! = 0 := hk
      obtain ⟨hp0, hv0⟩ := hcur0 tx c hc hk
      have hv0' : vTOf vT (colJ tx c, 0) = toKV (vT[T.col0 + c]!)[0]! := hv0 vT 0
      have : val (colJ tx c, 0) = vTOf vT (colJ tx c, 0) := by simp only [val, valJ, hp0]
      have hcv : curVal XI ζ vT (T.col0 + c) = (vT[T.col0 + c]!)[0]! := by simp only [curVal, hk']
      rw [hcv]
      show _ = val (colJ tx c, 0)
      rw [this, hv0']
    · have hk' : XI.colKind[T.col0 + c]! = 1 := hk
      have hp1 : J.pre (colJ tx c) = some (((List.range XI.pre[T.col0 + c]!.size).map fun m =>
        Polynomial.monomial m (zv (XI.pre[T.col0 + c]!)[m]!)).sum) := hcur1 tx c hc hk
      have hcv : curVal XI ζ vT (T.col0 + c) = VF.K3.hornerG XI.pre[T.col0 + c]! ζ := by simp only [curVal, hk']
      rw [hcv, toKV_hornerG _ _ (hpreC _)]
      show _ = val (colJ tx c, 0)
      simp only [val, valJ, hp1]
      rw [eval_prePoly (fun m => (XI.pre[T.col0 + c]!)[m]!), hoff]
      simp
  have hng : ∀ c < T.nc - T.npub, toKV (curNxtAt XI ζ vT).2[T.col0 + c]! = E.next c := by
    intro c hc
    have hlt := hcolle c hc
    rw [(curNxtAt_get XI ζ vT _ hlt).2]
    rcases hkind tx c hc with hk | hk
    · have hk' : XI.colKind[T.col0 + c]! = 0 := hk
      obtain ⟨hp0, hv0⟩ := hcur0 tx c hc hk
      have hv0' : vTOf vT (colJ tx c, ⟨1 % J.r, Nat.mod_lt _ (NeZero.pos _)⟩) = toKV (vT[T.col0 + c]!)[1 % J.r]! :=
        hv0 vT _
      have : val (colJ tx c, ⟨1 % J.r, Nat.mod_lt _ (NeZero.pos _)⟩) = vTOf vT (colJ tx c, ⟨1 % J.r, Nat.mod_lt _ (NeZero.pos _)⟩) := by
        simp only [val, valJ, hp0]
      have hcv : nxtVal XI ζ vT (T.col0 + c) = (vT[T.col0 + c]!)[1]! := by simp [nxtVal, hk', hr2]
      rw [hcv]
      show _ = val _
      rw [this, hv0', h1r]
    · have hk' : XI.colKind[T.col0 + c]! = 1 := hk
      have hp1 : J.pre (colJ tx c) = some (((List.range XI.pre[T.col0 + c]!.size).map fun m =>
        Polynomial.monomial m (zv (XI.pre[T.col0 + c]!)[m]!)).sum) := hcur1 tx c hc hk
      have hcv : nxtVal XI ζ vT (T.col0 + c) = VF.K3.hornerG XI.pre[T.col0 + c]! (VF.K3.smul XI.hGen ζ) := by
        simp only [nxtVal, hk']
      rw [hcv, toKV_hornerG _ _ (hpreC _), toKV_smul]
      show _ = val _
      simp only [val, valJ, hp1]
      rw [eval_prePoly (fun m => (XI.pre[T.col0 + c]!)[m]!), hoff]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [h1r, pow_one, psiV]
      rw [mul_comm (toKV ζ)]
  have hpg : ∀ s < T.npub, zv (pubAt XI vT)[T.pubBase + s]! = E.pub s := by
    intro s hs
    have hlt : T.pubBase + s < XI.pubOf.size := by have := hpubB _ hTmem; omega
    have h1 : (XI.pubOf.map fun c => ((vT[c]!)[0]!).c0)[T.pubBase + s]! = ((vT[XI.pubOf[T.pubBase + s]!]!)[0]!).c0 := by
      rw [getElem!_pos _ _ (by simpa using hlt)]
      simp only [Array.getElem_map]
      rw [getElem!_pos XI.pubOf _ hlt]
    show _ = coord0 (vTOf vT (pubJ tx s, 0))
    rw [hpubJ tx s vT hs, coord0_toKV]
    unfold pubAt
    rw [h1]
  have hchg : ∀ q < 19, toKV (slotsAt XI (e0 c0) (e1 c1))[q]! = E.chal q := by
    intro q hq; exact hslot c0 c1 c2 c3 q hq
  have hcvK := toKV_tabCvAt XI (slotsAt XI (e0 c0) (e1 c1)) ζ vT hC hpreC T (hcanon _ hTmem) (hread _ hTmem) E rfl hcg hng hpg hchg l
  have ht := htie (show Fin nsK from i) (restr 2 (chiOfBlocks c0 c1 c2 c3)) (vTOf vT) val
  rw [regroup_Cv J pr ω δ N hNH hpd G gb _ _ (show Fin nsK from i)]
  congr 1
  rw [hmult, hcvK, ← ht, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hg : G.grp j = (show Fin nsK from i) := by
    have hj' : j ∈ Finset.univ.filter (fun j => G.grp j = (show Fin nsK from i)) := hj
    exact (Finset.mem_filter.mp hj').2
  rw [htabS j, hg, ← htxd]
  refine (mul_left_comm _ _ _).trans (congrArg (fun x => gb (G.crd j) * x) ?_)
  exact mul_comm (eval (toKV ζ) _) _

end HD
end NockvmE2E.Exec.HdagU

#print axioms NockvmE2E.Exec.HdagU.chipCanon_ExCan
#print axioms NockvmE2E.Exec.HdagU.canon_curNxtAt
#print axioms NockvmE2E.Exec.HdagU.canon_pubAt
#print axioms NockvmE2E.Exec.HdagU.coord0_toKV
#print axioms NockvmE2E.Exec.HdagU.toKV_tabCvAt
#print axioms NockvmE2E.Exec.HdagU.regroup_Cv
#print axioms NockvmE2E.Exec.HdagU.hdagU_of_tie
