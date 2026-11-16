import Nock.NockVMROM.Thm54.VclL.Handle.HonestCompTraceH
import Nock.NockVMROM.Thm54.VclL.Handle.CellTraceH

/-!
The honest compute trace satisfies the compute chip `computeChipVCLH`.  It proves that the pole
list and the honest fill depend only on the low trace columns (`polesOf_congr`, `notBadRow_congr`,
`honestFill_congr`), defines the closed-form walk columns of the honest trace (`wRows`, `wkCur`,
`wkSeed`, `wkLn`, `wkCnt`, `wkAcc`), shows that the nine compute-walk gates hold at the real chip
environment of every row (`walk_gates_real`), and concludes `computeChipVCLH_honest_sat`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk Nock.Reified Module
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC
open Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.Framework Nock.Framework.Reify Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.TraceGen ComputeTable Nock.NockVMROM.Thm54.SemanticStrategy
open scoped Polynomial

noncomputable section

section Transport
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]

/-- The pole list reads only columns `< 43` and the `γ` coin. -/
theorem polesOf_congr (eK1 eK2 : Env K) (e1 e2 : Env F) (h : ∀ c < 43, e1.trace c = e2.trace c)
    (hγ : eK1.chal chalGammaL = eK2.chal chalGammaL) : polesOf eK1 e1 = polesOf eK2 e2 := by
  unfold polesOf
  refine List.flatMap_congr (fun S hS => ?_)
  have hS' : S ∈ (slots : List (SlotSpec ℚ)) := hS
  have hmap : ∀ r : List ℕ, (∀ c ∈ r, c < 43) →
      (r.map fun i => algebraMap F K (e1.trace i)) = r.map fun i => algebraMap F K (e2.trace i) :=
    fun r hr => List.map_congr_left fun i hi => by rw [h i (hr i hi)]
  have hents : S.ents.map (fun x => rlcL (eK1.chal chalGammaL) 0 (x.rcd.map fun i => algebraMap F K (e1.trace i))) =
      S.ents.map (fun x => rlcL (eK2.chal chalGammaL) 0 (x.rcd.map fun i => algebraMap F K (e2.trace i))) :=
    List.map_congr_left fun x hx => by rw [hγ, hmap x.rcd (slots_read S hS' x hx).2]
  rw [hents]
  rcases hp : S.pair with _ | ⟨fl, a, bb⟩
  · simp
  · obtain ⟨-, ha, hb⟩ := slots_pair_read S hS' fl a bb hp
    simp only [hγ, hmap a ha, hmap bb hb]

theorem notBadRow_congr (eK1 eK2 : Env K) (e1 e2 : Env F) (h : ∀ c < 43, e1.trace c = e2.trace c)
    (hγ : eK1.chal chalGammaL = eK2.chal chalGammaL) (hρ : eK1.chal chalRhoL = eK2.chal chalRhoL)
    (hnb : NotBadRow eK1 e1) : NotBadRow eK2 e2 := by
  intro x hx
  rw [← polesOf_congr eK1 eK2 e1 e2 h hγ] at hx
  rw [← hρ]; exact hnb x hx

theorem honestFill_congr (b : Basis (Fin 3) F K) (e1 e2 : Env F) (h : ∀ c < 52, e1.trace c = e2.trace c)
    (hc : e1.chal = e2.chal) (hf : HonestFill b e1) : HonestFill b e2 := by
  intro S hS
  have hS' : S ∈ (slots : List (SlotSpec ℚ)) := hS
  have hAD := slotAD_congr S hS' (gE b e1) (gE b e2) e1 e2 (fun c hc => h c (by omega))
    (by simp [gE, Compute.TowerD.gatherEnv, hc]) (by simp [gE, Compute.TowerD.gatherEnv, hc])
  have hl : limbVal b e1.trace S.inv = limbVal b e2.trace S.inv := by
    unfold limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := k.isLt
    have hinv : S.inv = 43 ∨ S.inv = 46 ∨ S.inv = 49 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl | rfl <;>
        first | (left; rfl) | (right; left; rfl) | (right; right; rfl)
    rw [h _ (by omega)]
  rw [← hl, ← hAD.1, ← hAD.2]
  exact hf S hS

end Transport

section WalkReal
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Field Kg]

/-- The honest compute row `r` (`0`-based chip row): the hosted row of BFS node `r + 1`. -/
def wRows (W : List (NTree (GenComputeRow Kg))) : ℕ → RowN := fun r => rowAtW W (r + 1)

/-- The walk's honest columns (closed forms), as in `walkGatesH_honest`. -/
def wkCur (W : List (NTree (GenComputeRow Kg))) (γ : K) (cells : List Noun) : ℕ → K :=
  Walk.curCol (nodeValH (F := F) γ cells (Kg := Kg)) W
def wkSeed (W : List (NTree (GenComputeRow Kg))) (α γ : K) (cells : List Noun) : K :=
  wkCur (F := F) W γ cells 1 * α
def wkLn (α : K) : ℕ → K := lnClosed α
def wkCnt (W : List (NTree (GenComputeRow Kg))) (α : K) : ℕ → K := cntClosed (Walk.foCol W) α α
def wkAcc (W : List (NTree (GenComputeRow Kg))) (α γ : K) (cells : List Noun) : ℕ → K :=
  accClosed (wkCur (F := F) W γ cells) (Walk.chldCol (nodeValH (F := F) γ cells (Kg := Kg)) W) (Walk.foCol W) α
    (wkSeed (F := F) W α γ cells) α

end WalkReal


section WalkSat
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Field Kg]

/-- **The nine compute-walk gates hold at the real chip environment of every row** (`computeChipVCLH`'s `𝕂`
walk gates at the honest trace): the environment agrees with `walkGatesH_honest`'s closed-form environment
on every variable the gates read (§`HonestCongH`); at the last row the gates that read the next row are
scaled by `1 - isLast = 0`. -/
theorem walk_gates_real
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (h : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (cells : List Noun) (α γ : K) (hord : (bfsForest [airReorder t]).length ≤ orderOf α)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
    (hα : limbVal b chalV chalAlphaW = α) (hγ : limbVal b chalV chalGammaW = γ)
    (hpIC : limbVal b pubVal pubIC = α) (hpS : limbVal b pubVal pubSeed = wkSeed (F := F) (bfsForest [airReorder t]) α γ cells)
    (hpO : limbVal b pubVal pubOut = 0)
    (E : Env F) (r : ℕ) (hr : r < (bfsForest [airReorder t]).length)
    (hE0 : ∀ c, E.trace c = compTrace b cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
      chalV pubVal (wkLn α) (wkCnt (bfsForest [airReorder t]) α)
      (wkAcc (F := F) (bfsForest [airReorder t]) α γ cells) r c)
    (hEn : r + 1 < (bfsForest [airReorder t]).length → ∀ c, E.traceNext c =
      compTrace b cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
      chalV pubVal (wkLn α) (wkCnt (bfsForest [airReorder t]) α)
      (wkAcc (F := F) (bfsForest [airReorder t]) α γ cells) (r + 1) c)
    (hch : E.chal = chalV) (hpb : E.pub = pubVal) :
    ∀ g ∈ (walkGates : List (MixedExpr ℚ)), evalMQ g (gE b E) E = 0 := by
  intro g hg
  set W := bfsForest [airReorder t] with hW
  have hmain := walkGatesH_honest (F := F) h cells α γ hord (r + 1) (by omega) (by rw [← hW]; omega) g hg
  have hEt : E.trace = compTrace b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
      (wkAcc (F := F) W α γ cells) r := funext hE0
  -- agreement of the `𝕂` side
  have hKrd : ∀ p, wkOK p = true → (noNextB p = true ∨ r + 1 < W.length) →
      envRd (gE b E) p = envRd (walkEnvK (wkLn α) (wkCnt W α) (wkAcc (F := F) W α γ cells) α γ
        (wkSeed (F := F) W α γ cells) (r + 1)) p := by
    rintro ⟨k, c⟩ hp hn
    cases k
    · simp only [wkOK, Bool.or_eq_true, beq_iff_eq] at hp
      simp only [envRd, gE, Compute.TowerD.gatherEnv, hEt]
      rcases hp with ((hc | hc) | hc) | hc <;> subst hc
      · rw [limb_ln]; simp [walkEnvK, wLn]
      · rw [limb_cnt]; simp [walkEnvK, wLn, wCnt]
      · rw [limb_acc]; simp [walkEnvK, wLn, wCnt, wAcc]
      · rw [limb_inv]; simp [walkEnvK, wLn, wCnt, wAcc, wInv, wkLn, wkCnt, lnClosed, cntClosed]
    · have hlt : r + 1 < W.length := by
        rcases hn with hn | hn
        · simp [noNextB] at hn
        · exact hn
      simp only [wkOK, Bool.or_eq_true, beq_iff_eq] at hp
      have hEnt : E.traceNext = compTrace b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
          (wkAcc (F := F) W α γ cells) (r + 1) := funext (hEn hlt)
      simp only [envRd, gE, Compute.TowerD.gatherEnv, hEnt]
      rcases hp with (hc | hc) | hc <;> subst hc
      · rw [limb_ln]; simp [walkEnvK, wLn]
      · rw [limb_cnt]; simp [walkEnvK, wLn, wCnt]
      · rw [limb_acc]; simp [walkEnvK, wLn, wCnt, wAcc]
    · simp only [wkOK, Bool.or_eq_true, beq_iff_eq] at hp
      simp only [envRd, gE, Compute.TowerD.gatherEnv, hch]
      rcases hp with hc | hc <;> subst hc
      · rw [hα]; simp [walkEnvK, chalAlphaW]
      · rw [hγ]; simp [walkEnvK, chalAlphaW, chalGammaW]
    · simp only [wkOK, Bool.or_eq_true, beq_iff_eq] at hp
      simp only [envRd, gE, Compute.TowerD.gatherEnv, hpb]
      rcases hp with (hc | hc) | hc <;> subst hc
      · rw [hpIC]; simp [walkEnvK, pubIC]
      · rw [hpS]; simp [walkEnvK, pubIC, pubSeed]
      · rw [hpO]; simp [walkEnvK, pubIC, pubSeed, pubOut]
  -- agreement of the base side
  have hFrd : ∀ p, wfOK p = true → (noNextB p = true ∨ r + 1 < W.length) →
      envRd E p = envRd (walkEnvF (F := F) W cells (r + 1)) p := by
    rintro ⟨k, c⟩ hp hn
    cases k
    · simp only [wfOK, decide_eq_true_eq] at hp
      simp only [envRd, hEt]
      rw [compTrace_base b cells _ _ chalV pubVal _ _ _ r c hp]
      simp only [walkEnvF, wRows]
      have e1 : (fstF r : F) = if r + 1 = 1 then 1 else 0 := by simp [fstF]
      have e2 : (lstF W.length r : F) = if r + 1 = W.length then 1 else 0 := rfl
      rw [e1, e2]
    · have hlt : r + 1 < W.length := by
        rcases hn with hn | hn
        · simp [noNextB] at hn
        · exact hn
      simp only [wfOK, decide_eq_true_eq] at hp
      have hEnt : E.traceNext = compTrace b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
          (wkAcc (F := F) W α γ cells) (r + 1) := funext (hEn hlt)
      simp only [envRd, hEnt]
      rw [compTrace_base b cells _ _ chalV pubVal _ _ _ (r + 1) c hp]
      simp only [walkEnvF, wRows]
      have e1 : (fstF (r + 1) : F) = if r + 1 + 1 = 1 then 1 else 0 := by simp [fstF]
      have e2 : (lstF W.length (r + 1) : F) = if r + 1 + 1 = W.length then 1 else 0 := rfl
      rw [e1, e2]
    · simp [wfOK] at hp
    · simp [wfOK] at hp
  by_cases hlt : r + 1 < W.length
  · rw [← hmain]
    refine evalMQ_congr_rds g _ _ _ _ (fun p hp => hKrd p ?_ (Or.inr hlt)) (fun p hp => hFrd p ?_ (Or.inr hlt))
    · exact walk_readsK g hg p hp
    · exact walk_readsF g hg p hp
  · have hlast : r + 1 = W.length := by omega
    rcases walk_gate_shapeB g hg with ⟨hK, hF⟩ | hs
    · rw [← hmain]
      exact evalMQ_congr_rds g _ _ _ _ (fun p hp => hKrd p (walk_readsK g hg p hp) (Or.inl (hK p hp)))
        (fun p hp => hFrd p (walk_readsF g hg p hp) (Or.inl (hF p hp)))
    · obtain ⟨u, rfl⟩ := isScaleNL_eq g hs
      rw [evalMQ_scale]
      have h12 : evalQ (notLast (F := ℚ)) E = 0 := by
        simp only [notLast, evalQ_notC, lastCol, hEt]
        rw [compTrace_base b cells _ _ chalV pubVal _ _ _ r 12 (by omega)]
        simp [colVal, lstF, hlast]
      rw [h12]; simp

end WalkSat


section Rows
variable {F Kg : Type} [Field F] [Field Kg]

theorem rowAtW_eq (W : List (NTree (GenComputeRow Kg))) (r : ℕ) (hr : r < W.length) :
    rowAtW W (r + 1) = rowOfSkelH (W[r]'hr).label.skel := by
  unfold rowAtW
  simp [List.getElem?_eq_getElem hr]

theorem label_mem_bfsRows {t : NTree (GenComputeRow Kg)}
    (W : List (NTree (GenComputeRow Kg))) (hW : W = bfsForest [airReorder t]) (r : ℕ) (hr : r < W.length) :
    (W[r]'hr).label ∈ bfsRows (airReorder t) := by
  unfold bfsRows
  rw [← hW]
  exact List.mem_map.mpr ⟨_, List.getElem_mem hr, rfl⟩

end Rows

section Sat
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Field Kg]

open Classical in
/-- **`hcomp`: the honest compute trace is accepted by `computeChipVCLH`.**

The chip has `n = |W|` rows (`W = bfsForest [airReorder t]`, the walk of the run `hrun`), the row nodes are
injective and `ω`-adjacent, the trace is `compPoly` (the `rowOfSkelH` rows, the `fillTrace` slot inverses, the
prefix-sum accumulators, the closed-form walk columns).  Hypotheses (all verifier data or priced events, none
about the prover's messages):
* `hα hγ hpIC hpS hpO`: the coin / public readings of the walk (the seed `hpS` is the claim-label RLC);
* `hpub6`: the claim publics `0..5` are the root row's handles;
* `hρX hρP`: the twin terminals (the totals of the honest export / path records);
* `hat`: atoms below the characteristic (the run's own bound);
* `hnb`: the compute pole event does not occur (`poleRow_card`: at most `|polesOf|` coins per row);
* `hord`: the walk coin order (`walk_coin_order_few`). -/
theorem computeChipVCLH_honest_sat
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (cells : List Noun) (α γ : K) (hord : (bfsForest [airReorder t]).length ≤ orderOf α)
    {hh n : ℕ} (hn : 0 < n) (hN : n = (bfsForest [airReorder t]).length)
    (nodes : Fin n → F) (hinj : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 hh)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hα : limbVal b chalV chalAlphaW = α) (hγ : limbVal b chalV chalGammaW = γ)
    (hpIC : limbVal b pubVal pubIC = α)
    (hpS : limbVal b pubVal pubSeed = wkSeed (F := F) (bfsForest [airReorder t]) α γ cells)
    (hpO : limbVal b pubVal pubOut = 0)
    (hpub6 : ∀ i < 6, pubVal i = pubVec cells (rowAtW (bfsForest [airReorder t]) 1) i)
    (hρX : ∀ k : Fin 3, pubVal (pubRhoX + k) =
      coord b (accSumX b cells (wRows (bfsForest [airReorder t])) chalV n) k)
    (hρP : ∀ k : Fin 3, pubVal (pubRhoP + k) =
      coord b (accSumP b cells (wRows (bfsForest [airReorder t])) chalV n) k)
    (hat : ∀ g ∈ bfsRows (airReorder t),
      AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (hnb : ∀ r < n, NotBadRow (gE b (baseEnvC cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length chalV pubVal r))
      (baseEnvC cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length chalV pubVal r)) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit)
      (compPoly b cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length chalV pubVal (wkLn α)
        (wkCnt (bfsForest [airReorder t]) α) (wkAcc (F := F) (bfsForest [airReorder t]) α γ cells) nodes
        (computeChipVCLH hn nodes b chalV pubVal orbit).rap.w) := by
  set W := bfsForest [airReorder t] with hW
  set P := compPoly b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
    (wkAcc (F := F) W α γ cells) nodes (computeChipVCLH hn nodes b chalV pubVal orbit).rap.w with hP
  have hw70 : 70 ≤ (computeChipVCLH hn nodes b chalV pubVal orbit).rap.w := by
    show 70 ≤ widthH; decide
  have hE0 : ∀ i : Fin n, ∀ c, (Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal).trace c =
      compTrace b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α) (wkAcc (F := F) W α γ cells) (i : ℕ) c :=
    fun i c => compPoly_env_trace b cells (wRows W) W.length chalV pubVal _ _ _ nodes hinj hw70 orbit.ω i c
  have hEn : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), ∀ c,
      (Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal).traceNext c =
      compTrace b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α) (wkAcc (F := F) W α γ cells)
        ((i : ℕ) + 1) c :=
    fun i hi c => compPoly_env_next b cells (wRows W) W.length chalV pubVal _ _ _ nodes hinj hw70 orbit.ω i hi
      (hadj i hi) c
  have hlen : W.length = n := hN.symm
  have hrowSem : ∀ r (hr : r < W.length), (wRows W r).Sem := by
    intro r hr
    have hg := label_mem_bfsRows W hW r hr
    unfold wRows; rw [rowAtW_eq W r hr]
    exact rowOfSkelH_sem _ (run_rows_sem hrun _ hg)
  have hrowHost : ∀ r (hr : r < W.length), (wRows W r).op = 3 →
      (wRows W r).ftth = hdN (wRows W r).sf1 ∧ (wRows W r).fttt = tlN (wRows W r).sf1 := by
    intro r hr; unfold wRows; rw [rowAtW_eq W r hr]; exact rowOfSkelH_hosted _
  let envs : ℕ → Env F := fun j =>
    if h : j < n then Reify.envOfTrace P orbit.ω (nodes ⟨j, h⟩) chalV pubVal
    else ⟨fun _ => 0, fun _ => 0, chalV, pubVal⟩
  have henv : ∀ i : Fin n, envs i = Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal := by
    intro i; simp [envs, i.isLt]
  have henv_chal : ∀ j, (envs j).chal = chalV := by
    intro j; by_cases hj : j < n <;> simp [envs, hj, Reify.envOfTrace]
  have henv_pub : ∀ j, (envs j).pub = pubVal := by
    intro j; by_cases hj : j < n <;> simp [envs, hj, Reify.envOfTrace]
  have henvT : ∀ j (hj : j < n) c, (envs j).trace c =
      compTrace b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α) (wkAcc (F := F) W α γ cells) j c := by
    intro j hj c; rw [henv ⟨j, hj⟩]; exact hE0 ⟨j, hj⟩ c
  have henvN : ∀ j (hj : j + 1 < n) c, (envs j).traceNext c =
      compTrace b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α) (wkAcc (F := F) W α γ cells) (j + 1) c := by
    intro j hj c
    have hj' : j < n := by omega
    rw [henv ⟨j, hj'⟩]; exact hEn ⟨j, hj'⟩ hj c
  have hAt : ∀ j (hj : j < n), AtRow cells (wRows W j) (fstF j) (lstF W.length j) (envs j) := by
    intro j hj c hc
    rw [henvT j hj c]
    exact compTrace_base b cells _ _ chalV pubVal _ _ _ j c (by omega)
  have hFill : ∀ j (hj : j < n), HonestFill b (envs j) := by
    intro j hj
    obtain ⟨h1, h2, h3, h4, h5⟩ := honestFill_attainable b (baseEnvC cells (wRows W) W.length chalV pubVal j)
    refine honestFill_congr b _ _ (fun c hc => ?_) (by rw [h2, henv_chal]; rfl) h5
    rw [henvT j hj c, compTrace_fill b cells _ _ chalV pubVal _ _ _ j c hc]
    rfl
  have hNB : ∀ j (hj : j < n), NotBadRow (gE b (envs j)) (envs j) := by
    intro j hj
    refine notBadRow_congr _ _ (baseEnvC cells (wRows W) W.length chalV pubVal j) (envs j)
      (fun c hc => ?_) ?_ ?_ (hnb j hj)
    · rw [henvT j hj c, compTrace_base b cells _ _ chalV pubVal _ _ _ j c hc]; rfl
    · simp [gE, Compute.TowerD.gatherEnv, henv_chal, baseEnvC]
    · simp [gE, Compute.TowerD.gatherEnv, henv_chal, baseEnvC]
  have hTX : ∀ i ≤ n, ∑ j ∈ Finset.range i, termVal b (slotsX (F := F)) (envs j) =
      accSumX b cells (wRows W) chalV i := by
    intro i hi
    unfold accSumX
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hi
    rw [termValX_honest cells (wRows W j) (fstF j) (lstF W.length j) (envs j) b (hrowSem j (by omega))
      (hAt j hj') (hrowHost j (by omega)) (hFill j hj') (hNB j hj')]
    simp only [gE, Compute.TowerD.gatherEnv, henv_chal]
  have hTP : ∀ i ≤ n, ∑ j ∈ Finset.range i, termVal b (slotsP (F := F)) (envs j) =
      accSumP b cells (wRows W) chalV i := by
    intro i hi
    unfold accSumP
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hi
    rw [termValP_honest cells (wRows W j) (fstF j) (lstF W.length j) (envs j) b (hrowSem j (by omega))
      (hAt j hj') (hrowHost j (by omega)) (hFill j hj') (hNB j hj')]
    simp only [gE, Compute.TowerD.gatherEnv, henv_chal]
  have hbind : (computeChipVCLH hn nodes b chalV pubVal orbit).BindsPreprocessing P := by
    intro j
    fin_cases j
    · exact compPoly_first b cells (wRows W) W.length chalV pubVal _ _ _ nodes _ (by omega)
    · exact compPoly_last b cells (wRows W) W.length chalV pubVal _ _ _ nodes hn hlen _ (by omega)
  have h11 : ∀ j (hj : j < n), (envs j).trace 11 = if j = 0 then 1 else 0 := by
    intro j hj
    rw [henvT j hj, compTrace_base b cells _ _ chalV pubVal _ _ _ j 11 (by omega)]
    simp [colVal, fstF]
  have h12 : ∀ j (hj : j < n), (envs j).trace 12 = if j + 1 = W.length then 1 else 0 := by
    intro j hj
    rw [henvT j hj, compTrace_base b cells _ _ chalV pubVal _ _ _ j 12 (by omega)]
    simp [colVal, lstF]
  have hrx : rxTot b cells (wRows W) envs W.length = accSumX b cells (wRows W) chalV n := by
    unfold rxTot accSumX; rw [hlen]; simp only [gE, Compute.TowerD.gatherEnv, henv_chal]
  have hrp : rpTot b cells (wRows W) envs W.length = accSumP b cells (wRows W) chalV n := by
    unfold rpTot accSumP; rw [hlen]; simp only [gE, Compute.TowerD.gatherEnv, henv_chal]
  have hcoord : ∀ (i : ℕ) (hi : i < n) (base : ℕ) (x : K)
      (hl : limbVal b (compTrace b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
        (wkAcc (F := F) W α γ cells) i) base = x) (k : Fin 3),
      compTrace b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
        (wkAcc (F := F) W α γ cells) i (base + k) = coord b x k := by
    intro i hi base x hl k
    have := coord_limbVal b (compTrace b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
        (wkAcc (F := F) W α γ cells) i) base k
    rw [hl] at this; exact this.symm
  refine computeChipVCLH_sat_of_rows hn nodes b chalV pubVal orbit P hbind ?_ ?_
  · intro x hx g hg
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hiW : (i : ℕ) < W.length := by omega
    have hgm := label_mem_bfsRows W hW (i : ℕ) hiW
    have harith : ∀ g ∈ (arithGates : List (CoeffExpr ℚ)) ++ (eqGates : List (EqG ℚ)).map EqG.gate,
        evalQ g (Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal) = 0 := by
      intro g hmem
      have hroot : (fstF (i : ℕ) : F) = 0 ∨ ((rowOfSkelH (W[(i : ℕ)]'hiW).label.skel).s = (rowAtW W 1).s ∧
          (rowOfSkelH (W[(i : ℕ)]'hiW).label.skel).f = (rowAtW W 1).f ∧
          (rowOfSkelH (W[(i : ℕ)]'hiW).label.skel).e = (rowAtW W 1).e) := by
        by_cases h0 : (i : ℕ) = 0
        · right
          have hthis : rowOfSkelH (W[(i : ℕ)]'hiW).label.skel = rowAtW W 1 := by
            rw [← rowAtW_eq W (i : ℕ) hiW, h0]
          rw [hthis]; exact ⟨rfl, rfl, rfl⟩
        · left; simp [fstF, h0]
      have hb := honest_row_base_gatesH hrun hgm cells (fstF (i : ℕ)) (lstF W.length (i : ℕ)) (rowAtW W 1)
        (hat _ hgm) hroot g hmem
      rw [← rowAtW_eq W (i : ℕ) hiW] at hb
      rw [eval_mapC_cast] at hb
      rw [← hb]
      refine evalQ_congr_rds g _ _ (fun p hp => ?_)
      have hp' := arith_reads g hmem p hp
      rcases p with ⟨k, c⟩
      cases k
      · simp only [bsOK, decide_eq_true_eq] at hp'
        simp only [envRd, hEnv]
        rw [hE0 i c, compTrace_base b cells _ _ chalV pubVal _ _ _ (i : ℕ) c (by omega)]
        rfl
      · simp [bsOK] at hp'
      · simp [bsOK] at hp'
      · simp only [bsOK, decide_eq_true_eq] at hp'
        simp only [envRd, hEnv, Reify.envOfTrace]
        exact hpub6 c hp'
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact harith g (List.mem_append_left _ hg)
      · -- accumulator gates
        have hr := accGatesH_honest_rows b W.length (i : ℕ) hiW envs cells (wRows W) (fun j => fstF j)
          (fun j => lstF W.length j)
          (fun j hj => ⟨hrowSem j hj, hAt j (by omega), hrowHost j hj, hFill j (by omega), hNB j (by omega)⟩)
          (h11 _ i.isLt) (h12 _ i.isLt)
          (fun k => by
            rw [henvT _ (by omega), hTX _ (by omega)]
            exact hcoord (i : ℕ) i.isLt accX _ (limb_accX b cells _ _ chalV pubVal _ _ _ _) k)
          (fun hlt k => by
            rw [henvN _ (by omega), hTX _ (by omega)]
            exact hcoord ((i : ℕ) + 1) (by omega) accX _ (limb_accX b cells _ _ chalV pubVal _ _ _ _) k)
          (fun k => by
            rw [henvT _ (by omega), hTP _ (by omega)]
            exact hcoord (i : ℕ) i.isLt accP _ (limb_accP b cells _ _ chalV pubVal _ _ _ _) k)
          (fun hlt k => by
            rw [henvN _ (by omega), hTP _ (by omega)]
            exact hcoord ((i : ℕ) + 1) (by omega) accP _ (limb_accP b cells _ _ chalV pubVal _ _ _ _) k)
          (fun k => by rw [henv_pub, hrx]; exact hρX k)
          (fun k => by rw [henv_pub, hrp]; exact hρP k)
        have := hr (mapC (fun q : ℚ => (q : F)) g) (List.mem_map_of_mem hg)
        rwa [eval_mapC_cast, henv i] at this
    · exact harith g (List.mem_append_right _ hg)
  · intro x hx g hg
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hiW : (i : ℕ) < W.length := by omega
    rw [← henv i]
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hg
      exact slotGates_honest_row cells (wRows W (i : ℕ)) (fstF (i : ℕ)) (lstF W.length (i : ℕ)) (envs i) b
        (hrowSem _ hiW) (hAt _ i.isLt) (hFill _ i.isLt) (hNB _ i.isLt) S hS
    · rw [henv i]
      exact walk_gates_real hrun cells α γ hord b chalV pubVal hα hγ hpIC hpS hpO _ (i : ℕ) hiW
        (hE0 i) (fun hlt => hEn i (by have := hlen; rw [hW] at this; omega)) rfl rfl g hg

end Sat


end

end Nock.NockVMROM.Thm54.VclL.Handle
