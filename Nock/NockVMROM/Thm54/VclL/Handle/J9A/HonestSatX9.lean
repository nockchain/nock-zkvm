/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/HonestSatX9.lean

The J-9 A compute twin `computeChipVCLHX9` accepts the honest trace `polyX9` (`HonestTraceX9`: the base
  columns `colX9`, the slot inverse limbs, the accumulator prefix sums, the closed-form walk, in RAP column order
  through `invPermX9`) of a J-9 A tree `t9` (`W = bfsForest [t9]`, `n = |W|` rows).

  Generic form: the arithmetic / equality base gates of every row (`hbase`, at `hEnvX9` of the honest row, the
  form of `ComplJ9ACompRow.old_gates` / `s0B_gates` / `s10B_gates` / `s10S_gates`) and the walk label reads
  (`hrd : ReadsAt9`) are HYPOTHESES; every other gate (the six accumulators over the twin slots `slotsX9`, the
  four `𝕂′` slot pairs, the nine walk gates over 20 states) is proved here.  The route is
  `HonestTraceX9.computeChipVCLHX9_sat_of` (the converse of `computeChipVCLHX9_sat_twin`): every twin gate at
  `Env.viaPerm permX9 (envOfTrace P ω x …)` for every row node, plus the preprocessing binding.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HonestTraceX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.HonestSatX9

open Nock Nock.Noun Nock.Walk Nock.Jet Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC selS mapC mapM chalAlphaW chalGammaW pubIC pubSeed
  pubOut pubRhoX pubRhoP)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ (pubRhoXIm pubRhoPIm)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX (walkEnvKX)
open Nock.NockVMROM.Thm54.VclL.Handle (evalMQ eval_mapM_cast)
open Nock.NockVMROM.Thm54.VclL.HonestTraceX (okC okM envAt eval_okC eval_okM okC_mapC okM_mapM
  eval_mapC_castX okKs okKw okKc isNLX isNLX_eq walkV accSpec pubOfA accGatesX_map)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (colX9 hEnvX9 invPermX9)

noncomputable section

theorem r0_lt {c : ℕ} (hc : r0 c = true) : c < 137 := by rw [r0_iff] at hc; omega

/-- The honest walk accumulator column (closed form, seed `cur 1 · α`). -/
def accW9 {K : Type} [Field K] (nodeV : NTree LX9 → K) (W : List (NTree LX9)) (α : K) : ℕ → K :=
  accClosed (Walk.curCol nodeV W) (Walk.chldCol nodeV W) (Walk.foCol W) α (Walk.curCol nodeV W 1 * α) α

section Main
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

open Classical in
/-- **`computeChipVCLHX9` accepts the honest trace `polyX9` of a J-9 A tree** (generic form).

The chip has `n = |W|` rows, `W = bfsForest [t9]`; the row nodes are injective and `ω`-adjacent.  Hypotheses:
* `hbase`: at every chip row `j < n`, every arithmetic and every equality base gate of the twin vanishes at the
  honest environment `hEnvX9` of BFS row `j + 1` (first / last flags `fl1`, `llW`) — the conclusion form of
  `ComplJ9ACompRow.old_gates` / `s0B_gates` / `s10B_gates` / `s10S_gates`;
* `hrd`: the walk label reads of every BFS row are the tree's walk values for the node value `nodeV`
  (`ReadsAt9`, the twin of J-8's `reads_atX`);
* `hord`: the walk coin order `|W| ≤ orderOf α`;
* `hα hγ hpIC hpS hpO`: the walk coin / public readings (`hpS`: the seed `cur 1 · α`);
* `hρ`: the six accumulator terminals (publics `pubOfA a + k`) are the honest totals `accV9 … a n` — over the
  TWIN slots `slotsX9` (so they include the `TAG_ax` consumes of `s0B` / `s10B` on the service balance, the
  `s10S` limb consume, the new decode entries of `s0B` / `s10B` on the export balance);
* `hnb`: the slot pole event does not occur (`D ≠ 0 ∨ A = 0` per twin slot and row). -/
theorem computeChipVCLHX9_honest_sat
    (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (t9 : NTree LX9) (nodeV : NTree LX9 → K)
    (α γ : K) (hord : (bfsForest [t9]).length ≤ orderOf α)
    {hh n : ℕ} (hn : 0 < n) (hN : n = (bfsForest [t9]).length)
    (nodes : Fin n → F) (hinj : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 hh)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hα : limbVal b chalV chalAlphaW = α) (hγ : limbVal b chalV chalGammaW = γ)
    (hpIC : limbVal b pubVal pubIC = α)
    (hpS : limbVal b pubVal pubSeed = Walk.curCol nodeV (bfsForest [t9]) 1 * α)
    (hpO : limbVal b pubVal pubOut = 0)
    (hbase : ∀ j < n,
      (∀ g ∈ arithGatesX9, evalQX g (hEnvX9 H pd idOf (rowAt9 (bfsForest [t9]) (j + 1)) (fl1 (j + 1))
        (llW (bfsForest [t9]) (j + 1)) pubVal) = 0) ∧
      (∀ g ∈ (eqGatesX9 (F := ℚ)), evalQX g.gate (hEnvX9 H pd idOf (rowAt9 (bfsForest [t9]) (j + 1))
        (fl1 (j + 1)) (llW (bfsForest [t9]) (j + 1)) pubVal) = 0))
    (hrd : ReadsAt9 (F := F) H pd idOf (bfsForest [t9]) nodeV α γ)
    (hρ : ∀ a < 6, ∀ k : Fin 3, pubVal (pubOfA a + k) =
      coord b (accV9 b δ H pd idOf (bfsForest [t9]) chalV pubVal a n) k)
    (hnb : ∀ j < n, ∀ S ∈ slotsX9 (F := F),
      dVal b δ S (env0 H pd idOf (bfsForest [t9]) chalV pubVal j) ≠ 0 ∨
        aVal b δ S (env0 H pd idOf (bfsForest [t9]) chalV pubVal j) = 0) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit)
      (polyX9 b δ H pd idOf (bfsForest [t9]) chalV pubVal (lnClosed α)
        (cntClosed (Walk.foCol (bfsForest [t9])) α α) (accW9 nodeV (bfsForest [t9]) α) nodes
        (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w) := by
  set W := bfsForest [t9] with hW
  set ln : ℕ → K := lnClosed α with hln
  set cnt : ℕ → K := cntClosed (Walk.foCol W) α α with hcnt
  set acc : ℕ → K := accW9 nodeV W α with hacc
  set P := polyX9 b δ H pd idOf W chalV pubVal ln cnt acc nodes
    (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w with hP
  have hw : 137 ≤ (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w :=
    (computeChipVCLHX9_width hn nodes b δ chalV pubVal orbit).ge
  have hlen : W.length = n := hN.symm
  set tr := trX9 b δ H pd idOf W chalV pubVal ln cnt acc with htr
  let E : Fin n → Env F := fun i => Env.viaPerm permX9 (Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal)
  have hE0 : ∀ i : Fin n, ∀ c, c < 137 → (E i).trace c = tr (i : ℕ) c :=
    fun i c hc => polyX9_via_trace b δ H pd idOf W chalV pubVal ln cnt acc nodes hinj hw orbit.ω i c hc
  have hEn : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), ∀ c, c < 137 →
      (E i).traceNext c = tr ((i : ℕ) + 1) c :=
    fun i hi c hc =>
      polyX9_via_next b δ H pd idOf W chalV pubVal ln cnt acc nodes hinj hw orbit.ω i hi (hadj i hi) c hc
  let envs : ℕ → Env F := fun j => if h : j < n then E ⟨j, h⟩ else ⟨fun _ => 0, fun _ => 0, chalV, pubVal⟩
  have henv : ∀ i : Fin n, envs i = E i := by
    intro i; simp [envs, i.isLt]
  have henv_chal : ∀ j, (envs j).chal = chalV := by
    intro j; by_cases hj : j < n <;> simp [envs, E, hj, Env.viaPerm, Reify.envOfTrace]
  have henv_pub : ∀ j, (envs j).pub = pubVal := by
    intro j; by_cases hj : j < n <;> simp [envs, E, hj, Env.viaPerm, Reify.envOfTrace]
  have henvT : ∀ j (hj : j < n) c, c < 137 → (envs j).trace c = tr j c := by
    intro j hj c hc; rw [henv ⟨j, hj⟩]; exact hE0 ⟨j, hj⟩ c hc
  have henvN : ∀ j (hj : j + 1 < n) c, c < 137 → (envs j).traceNext c = tr (j + 1) c := by
    intro j hj c hc
    have hj' : j < n := by omega
    rw [henv ⟨j, hj'⟩]; exact hEn ⟨j, hj'⟩ hj c hc
  -- the accumulator terms at the real environments
  have hterm : ∀ a j, j < n → termVal b (slotsF9 (F := F) (accSpec a).1 (accSpec a).2) (envs j) =
      termVal b (slotsF9 (accSpec a).1 (accSpec a).2) (env1 b δ H pd idOf W chalV pubVal j) := by
    intro a j hj
    refine termVal_congr9 b _ _ _ _ fun c hc => ?_
    rw [henvT j hj c (by omega), htr, trX9_pre b δ H pd idOf W chalV pubVal ln cnt acc j c (by omega)]
    rfl
  have hsum : ∀ a i, i ≤ n → ∑ j ∈ Finset.range i,
      termVal b (slotsF9 (F := F) (accSpec a).1 (accSpec a).2) (envs j) =
        accV9 b δ H pd idOf W chalV pubVal a i := by
    intro a i hi
    unfold accV9
    refine Finset.sum_congr rfl fun j hj => ?_
    exact hterm a j (lt_of_lt_of_le (Finset.mem_range.mp hj) hi)
  -- the preprocessing binding
  have hbind : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).BindsPreprocessing P := by
    intro j
    fin_cases j
    · exact polyX9_first b δ H pd idOf W chalV pubVal ln cnt acc nodes _ (by omega)
    · exact polyX9_last b δ H pd idOf W chalV pubVal ln cnt acc nodes hn hlen _ (by omega)
  refine computeChipVCLHX9_sat_of hn nodes b δ chalV pubVal orbit P hbind fun x hx g hg => ?_
  have hx' : ∃ i, nodes i = x := by
    classical
    simpa [rowNodeSet] using hx
  obtain ⟨i, rfl⟩ := hx'
  have hin' : (i : ℕ) < n := i.isLt
  have hiW : (i : ℕ) < W.length := by omega
  show g.eval (E i) = 0
  rw [← henv i]
  -- base agreement of the real row environment on the round-0 columns
  have hbaseE : ∀ c, r0 c = true → (envs i).trace c =
      (hEnvX9 H pd idOf (rowAt9 W ((i : ℕ) + 1)) (fl1 ((i : ℕ) + 1)) (llW W ((i : ℕ) + 1)) pubVal).trace c := by
    intro c hc
    rw [henvT _ hin' c (r0_lt hc), htr, trX9_base b δ H pd idOf W chalV pubVal ln cnt acc _ c hc]
    rfl
  have hAE := hbase (i : ℕ) hin'
  simp only [gatesHX9, List.mem_append, List.mem_flatMap] at hg
  rcases hg with (hg | ⟨q, hq, hg⟩) | ⟨gw, hgw, hg⟩
  · -- base gates
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simp only [baseGatesHX9, List.mem_append] at hg'
    rcases hg' with (ha | hacc') | he
    · rw [eval_mapC_castX, evalQX_congr9 g' (List.all_eq_true.mp arith_ok9 g' ha) _ _ hbaseE
        (by rw [henv_pub]; rfl)]
      exact hAE.1 g' ha
    · obtain ⟨a, ha6, hga⟩ := accGatesHX9_mem hacc'
      have hmem : mapC (fun q : ℚ => (q : F)) g' ∈
          accGatesX (slotsF9 (F := F) (accSpec a).1 (accSpec a).2) (93 + 3 * a) (pubOfA a) := by
        rw [slotsF9, ← accGatesX_map]; exact List.mem_map_of_mem hga
      refine accGatesX_prefixK b _ (93 + 3 * a) (pubOfA a) n (i : ℕ) hin' envs
        (accV9 b δ H pd idOf W chalV pubVal a n) ?_ ?_ ?_ ?_ ?_ (hsum a n le_rfl) _ hmem
      · rw [henvT _ hin' 17 (by norm_num), htr,
          trX9_base b δ H pd idOf W chalV pubVal ln cnt acc _ 17 (by decide), baseT9_17]
      · rw [henvT _ hin' 18 (by norm_num), htr,
          trX9_base b δ H pd idOf W chalV pubVal ln cnt acc _ 18 (by decide), baseT9_18, hlen]
      · intro k
        rw [henvT _ hin' _ (by have := k.isLt; omega), htr,
          trX9_acc b δ H pd idOf W chalV pubVal ln cnt acc _ a ha6 k, hsum a _ hin'.le]
      · intro hlt k
        rw [henvN _ hlt _ (by have := k.isLt; omega), htr,
          trX9_acc b δ H pd idOf W chalV pubVal ln cnt acc _ a ha6 k, hsum a _ (by omega)]
      · intro k; rw [henv_pub]; exact hρ a ha6 k
    · obtain ⟨e, he', rfl⟩ := List.mem_map.mp he
      rw [eval_mapC_castX, evalQX_congr9 e.gate (List.all_eq_true.mp eq_ok9 e he') _ _ hbaseE
        (by rw [henv_pub]; rfl)]
      exact hAE.2 e he'
  · -- the four `𝕂′` slot pairs
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hq
    obtain ⟨sI, hs4, rfl, hinvS, hinvSi⟩ := slot_index9 hS
    have hcg := dVal_aVal_congr9 b δ hS (envs i) (env0 H pd idOf W chalV pubVal (i : ℕ))
      (fun c hc => by
        rw [henvT _ hin' c (r0_lt hc), htr, trX9_base b δ H pd idOf W chalV pubVal ln cnt acc _ c hc]; rfl)
      (by rw [henv_chal]; rfl)
    have l1 : limbVal b (envs i).trace (69 + 6 * sI) =
        Quad.re _ (invV9 b δ H pd idOf W chalV pubVal (i : ℕ) (slotAt9 sI)) :=
      (limbVal_congr b _ (tr (i : ℕ)) _ fun k => henvT _ hin' _ (by have := k.isLt; omega)).trans
        (limb_inv9 b δ H pd idOf W chalV pubVal ln cnt acc _ sI hs4)
    have l2 : limbVal b (envs i).trace (72 + 6 * sI) =
        Quad.im _ (invV9 b δ H pd idOf W chalV pubVal (i : ℕ) (slotAt9 sI)) :=
      (limbVal_congr b _ (tr (i : ℕ)) _ fun k => henvT _ hin' _ (by have := k.isLt; omega)).trans
        (limb_invIm9 b δ H pd idOf W chalV pubVal ln cnt acc _ sI hs4)
    refine slotGateQX_honest b δ (slotAt9 sI) (envs i) ?_ ?_ g hg
    · unfold invAt
      rw [hcg.1, hcg.2, hinvS, hinvSi, l1, l2, Quad.mk_re_im]
      rfl
    · rw [hcg.1, hcg.2]; exact hnb _ hin' _ hS
  · -- the compiled walk gates
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hgw
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    have hmain := walkGatesX9_honest (F := F) (K := K) (H := H) (pd := pd) (idOf := idOf) t9 nodeV α γ
      hord hrd ((i : ℕ) + 1) (by omega) (by rw [← hW]; omega) g0 hg0
    rw [← eval_mapM_cast] at hmain
    have limbW : ∀ w, w < 4 → limbVal b (envs i).trace (111 + 3 * w) = walkV ln cnt acc w ((i : ℕ) + 1) :=
      fun w hw4 => (limbVal_congr b _ (tr (i : ℕ)) _ fun k => henvT _ hin' _ (by have := k.isLt; omega)).trans
        (limb_walk9 b δ H pd idOf W chalV pubVal ln cnt acc _ w hw4)
    have hev : (mapM (fun q : ℚ => (q : F)) g0).eval (Compute.TowerD.gatherEnv b (envs i)) (envs i) = 0 := by
      have hKc : ∀ kk j, okKc kk j = true →
          envAt (Compute.TowerD.gatherEnv b (envs i)) kk j =
            envAt (walkEnvKX ln cnt acc α γ (Walk.curCol nodeV W 1 * α) ((i : ℕ) + 1)) kk j := by
        intro kk j hkk
        cases kk <;> simp only [okKc, okKw, Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true] at hkk
        · simp only [envAt, Compute.TowerD.gatherEnv]
          rcases hkk with ((rfl | rfl) | rfl) | rfl
          · rw [show (111 : ℕ) = 111 + 3 * 0 from rfl, limbW 0 (by norm_num)]
            simp [walkEnvKX, walkV, wLnX]
          · rw [show (114 : ℕ) = 111 + 3 * 1 from rfl, limbW 1 (by norm_num)]
            simp [walkEnvKX, walkV, wLnX, wCntX]
          · rw [show (117 : ℕ) = 111 + 3 * 2 from rfl, limbW 2 (by norm_num)]
            simp [walkEnvKX, walkV, wLnX, wCntX, wAccX]
          · rw [show (120 : ℕ) = 111 + 3 * 3 from rfl, limbW 3 (by norm_num)]
            simp [walkEnvKX, walkV, wLnX, wCntX, wAccX, wInvX]
        · simp only [envAt, Compute.TowerD.gatherEnv]
          rw [henv_chal]
          rcases hkk with rfl | rfl
          · rw [show (6 : ℕ) = chalAlphaW from rfl, hα]; simp [walkEnvKX, chalAlphaW]
          · rw [show (9 : ℕ) = chalGammaW from rfl, hγ]; simp [walkEnvKX, chalAlphaW, chalGammaW]
        · simp only [envAt, Compute.TowerD.gatherEnv]
          rw [henv_pub]
          rcases hkk with (rfl | rfl) | rfl
          · rw [show (6 : ℕ) = pubIC from rfl, hpIC]; simp [walkEnvKX, pubIC]
          · rw [show (9 : ℕ) = pubSeed from rfl, hpS]; simp [walkEnvKX, pubIC, pubSeed]
          · rw [show (12 : ℕ) = pubOut from rfl, hpO]; simp [walkEnvKX, pubIC, pubSeed, pubOut]
      have hFc : ∀ kk j, okFc9 kk j = true →
          envAt (envs i) kk j = envAt (walkEnvF9 (F := F) H pd idOf W ((i : ℕ) + 1)) kk j := by
        intro kk j hkk
        cases kk <;> simp only [okFc9, Bool.false_eq_true] at hkk
        simp only [envAt]
        rw [henvT _ hin' j (r0_lt hkk), htr, trX9_base b δ H pd idOf W chalV pubVal ln cnt acc _ j hkk]
        rfl
      by_cases hlt : (i : ℕ) + 1 < n
      · have limbWN : ∀ w, w < 4 →
            limbVal b (envs i).traceNext (111 + 3 * w) = walkV ln cnt acc w ((i : ℕ) + 1 + 1) :=
          fun w hw4 => (limbVal_congr b _ (tr ((i : ℕ) + 1)) _ fun k =>
            henvN _ hlt _ (by have := k.isLt; omega)).trans
            (limb_walk9 b δ H pd idOf W chalV pubVal ln cnt acc _ w hw4)
        rw [← hmain]
        refine eval_okM okKw okFw9 _ (by rw [okM_mapM]; exact List.all_eq_true.mp walk_ok9 g0 hg0) _ _ _ _
          (fun kk j hkk => ?_) (fun kk j hkk => ?_)
        · cases kk
          · exact hKc .traceCur j hkk
          · simp only [okKw, Bool.or_eq_true, beq_iff_eq] at hkk
            simp only [envAt, Compute.TowerD.gatherEnv]
            rcases hkk with (rfl | rfl) | rfl
            · rw [show (111 : ℕ) = 111 + 3 * 0 from rfl, limbWN 0 (by norm_num)]
              simp [walkEnvKX, walkV, wLnX]; rfl
            · rw [show (114 : ℕ) = 111 + 3 * 1 from rfl, limbWN 1 (by norm_num)]
              simp [walkEnvKX, walkV, wLnX, wCntX]; rfl
            · rw [show (117 : ℕ) = 111 + 3 * 2 from rfl, limbWN 2 (by norm_num)]
              simp [walkEnvKX, walkV, wLnX, wCntX, wAccX]; rfl
          · exact hKc .challenge j hkk
          · exact hKc .publicVal j hkk
        · cases kk
          · exact hFc .traceCur j hkk
          · simp only [okFw9] at hkk
            simp only [envAt]
            rw [henvN _ hlt j (r0_lt hkk), htr, trX9_base b δ H pd idOf W chalV pubVal ln cnt acc _ j hkk]
            rfl
          · simp [okFw9] at hkk
          · simp [okFw9] at hkk
      · have hlast : (i : ℕ) + 1 = W.length := by omega
        have hsh := List.all_eq_true.mp walk_shape9 g0 hg0
        simp only [Bool.or_eq_true] at hsh
        rcases hsh with hc | hnl
        · rw [← hmain]
          exact eval_okM okKc okFc9 _ (by rw [okM_mapM]; exact hc) _ _ _ _ hKc hFc
        · obtain ⟨u, rfl⟩ := isNLX_eq g0 hnl
          have h18 : (envs i).trace 18 = 1 := by
            rw [henvT _ hin' 18 (by norm_num), htr,
              trX9_base b δ H pd idOf W chalV pubVal ln cnt acc _ 18 (by decide), baseT9_18, if_pos hlast]
          simp only [mapM, mapC, MixedExpr.eval, CoeffExpr.eval, h18, Rat.cast_one, sub_self, map_zero,
            zero_mul]
    exact ((mixedCompile_zero_iff b col0Id (isCoordEnv_gather b _) _).mp hev) k

end Main

end

end Nock.NockVMROM.Thm54.VclL.HonestSatX9

section Axioms
open Nock.NockVMROM.Thm54.VclL.HonestSatX9
#print axioms computeChipVCLHX9_honest_sat
end Axioms
