/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHOrbJ.lean

  The J chip of `withOrb I o` for jet-calling runs (`I = recJ9AXJ Rt s f χe t r`).

  * §1-3 `toQ_*`, `jGen_col`, `jGen_pubs`, `jGen_interp`: the executable J table `GenJet.jGen` (`K6`) is, column by
    column, the honest `colJ` (`ChipJ8THonestRAP`), its publics (`K3.toK`) are `pubsRows` (= `ComplJ8Of.pubsJOf`);
  * §4 `jPort`, `jchip_at`: the J `ChipPort` and the chip at any exec chip input `q` with injective nodes, abstract in
    the row list (no `AcceptsJ9A` import in this part);
  * §5 `lay_layJ`, `j_at`: at `recJ9AXJ`, the `hJk` field of `AcceptsJ9A` at `mkPbA (withOrb I o) hv'`
    (present: `chipAt_of_cols_pubs`; absent: `Or.inr`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipPort
import Nock.V1J8.GenJet
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfMem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbJ

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (liftQ)
open Nock.Jet.ChipJ8 (CRow PRow keysOf entsX ents0T ents1T ents2T ents3 colOf)
open Nock.Jet.ChipJ8 (preCol jetPre)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsJJ8)
open Nock.Jet.ChipJ8T.HonestRAP (sT sX termJ layJ accT accX tN xN colJ roleV qv)
open Nock.Jet.RapJetJ8 (dJ dJX coinsJ coinsJX keyK)
open Nock.NockVMROM.Thm54.T0Tower (Quad)
open Nock.NockVMROM.Thm54.CoordinateCompiler (CoeffExpr)

noncomputable section

/-! ## 1. The bridges -/

section Br
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]

theorem toQ_fq (x : ZMod P) : K6.toQ (fq x) = liftQ (K := KC) deltaF x := by
  unfold fq
  rw [toQ_g6, Gold.toZ_ofZ]
  exact IsScalarTower.algebraMap_apply (ZMod P) KC KQ _

theorem toQ_dKey_gen (χe : CoinsE) (m : ℕ) (κ : List (ZMod P)) :
    K6.toQ (dKey χe m κ) =
      (FiniteIO.compress (⟨ComplJ8Bad.γH deltaF (toχ χe), ComplJ8Bad.ρH deltaF (toχ χe)⟩ :
        FiniteIO.IOCoins KQ) (BalanceQ.liftRec (L := KQ) (keyK (K := KC) m κ)))⁻¹ := by
  unfold dKey
  rw [K6.toQ_inv, toQ_compressE]
  refine congrArg (fun z => z⁻¹) ?_
  refine congrArg (FiniteIO.compress _) (funext fun c => ?_)
  rw [toQ_fq]
  rfl

theorem toQ_dKey8 (χe : CoinsE) (κ : List (ZMod P)) :
    K6.toQ (dKey χe 8 κ) = dJ deltaF (chalsJJ8 (toχ χe)) κ := by
  have h := (ComplJ8Bad.coinsJ_J8 (K := KC) deltaF (toχ χe)).1
  rw [toQ_dKey_gen]; unfold dJ; rw [h]

theorem toQ_dKey5 (χe : CoinsE) (κ : List (ZMod P)) :
    K6.toQ (dKey χe 5 κ) = dJX deltaF (chalsJJ8 (toχ χe)) κ := by
  have h := (ComplJ8Bad.coinsJ_J8 (K := KC) deltaF (toχ χe)).2
  rw [toQ_dKey_gen]; unfold dJX; rw [h]

theorem toQ_foldr_add : ∀ L : List K6, K6.toQ (L.foldr (· + ·) 0) = (L.map K6.toQ).sum
  | [] => by simp [K6.toQ_zero]
  | x :: l => by
    rw [List.foldr_cons, K6.toQ_add, toQ_foldr_add l]
    simp

theorem toQ_sTE (χe : CoinsE) (es : List (Nock.Jet.ChipJ8.Kd × List Nock.Jet.ChipJ8.KE)) (r : CRow (ZMod P)) :
    K6.toQ (sTE χe es r) = sT deltaF (chalsJJ8 (toχ χe)) es r := by
  unfold sTE sT
  rw [toQ_foldr_add, List.map_map]
  congr 1
  refine List.map_congr_left fun κ _ => ?_
  exact toQ_dKey8 χe κ

theorem toQ_sXE (χe : CoinsE) (r : CRow (ZMod P)) :
    K6.toQ (sXE χe r) = sX deltaF (chalsJJ8 (toχ χe)) r := by
  unfold sXE sX
  rw [toQ_foldr_add, List.map_map]
  congr 1
  refine List.map_congr_left fun κ _ => ?_
  exact toQ_dKey5 χe κ

theorem toQ_termE (χe : CoinsE) (r : CRow (ZMod P)) :
    K6.toQ (termE χe r) = termJ deltaF (chalsJJ8 (toχ χe)) r := by
  unfold termE termJ
  rw [K6.toQ_sub, K6.toQ_sub, K6.toQ_add, K6.toQ_mul, K6.toQ_mul, toQ_sTE, toQ_sTE, toQ_sTE, toQ_sTE, toQ_fq,
    toQ_fq]

/-! ## 2. The accumulators -/

theorem scanK6_eq (l : List K6) : scanK6 l = (List.scanl (· + ·) 0 l).tail := by
  have key : ∀ (l : List K6) (a : K6) (acc : List K6),
      (l.foldl (fun (st : List K6 × K6) x => (st.1 ++ [st.2 + x], st.2 + x)) (acc, a)).1 =
        acc ++ (List.scanl (· + ·) a l).tail := by
    intro l
    induction l with
    | nil => intro a acc; simp
    | cons x l ih =>
      intro a acc
      rw [List.foldl_cons, ih, List.scanl_cons, List.tail_cons]
      cases l <;> simp [List.scanl]
  unfold scanK6
  rw [key]; simp

theorem toQ_scanl_getD : ∀ (l : List K6) (a : K6) (i : ℕ), i < l.length →
    K6.toQ ((List.scanl (· + ·) a l).getD (i + 1) 0) =
      K6.toQ a + ∑ j ∈ Finset.range (i + 1), K6.toQ (l.getD j 0)
  | [], a, i, h => by simp at h
  | x :: t, a, 0, _ => by
    rw [List.scanl_cons, List.getD_cons_succ]
    cases t <;> simp [List.scanl_cons, K6.toQ_add]
  | x :: t, a, j + 1, h => by
    have ih := toQ_scanl_getD t (a + x) j (by simpa using h)
    rw [List.scanl_cons, List.getD_cons_succ, ih, K6.toQ_add]
    rw [Finset.sum_range_succ' _ (j + 1)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    abel

theorem toQ_scanK6_getD (l : List K6) (i : ℕ) (hi : i < l.length) :
    K6.toQ ((scanK6 l).getD i 0) = ∑ j ∈ Finset.range (i + 1), K6.toQ (l.getD j 0) := by
  rw [scanK6_eq]
  have := toQ_scanl_getD l 0 i hi
  rw [K6.toQ_zero, zero_add] at this
  rw [← this]
  have e : ∀ L : List K6, L.tail.getD i 0 = L.getD (i + 1) 0 := by
    intro L; cases L <;> simp
  rw [e]

theorem getLastD_scanl : ∀ (l : List K6) (a z : K6), (List.scanl (· + ·) a l).getLastD z = l.foldl (· + ·) a
  | [], a, z => by simp
  | x :: l, a, z => by
    rw [List.scanl_cons, List.getLastD_cons, getLastD_scanl l (a + x) a, List.foldl_cons]

theorem toQ_foldl_add' : ∀ (l : List K6) (a : K6), K6.toQ (l.foldl (· + ·) a) = K6.toQ a + (l.map K6.toQ).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, toQ_foldl_add' l, K6.toQ_add, List.map_cons, List.sum_cons]
    abel

theorem toQ_lastK6_scanK6 (l : List K6) : K6.toQ (lastK6 (scanK6 l)) = (l.map K6.toQ).sum := by
  unfold lastK6
  rw [scanK6_eq]
  cases l with
  | nil => simp [K6.toQ_zero]
  | cons x l =>
    rw [List.scanl_cons, List.tail_cons, getLastD_scanl, toQ_foldl_add', K6.toQ_add, K6.toQ_zero]
    simp

theorem list_sum_map_get {α β : Type} [AddCommMonoid β] (l : List α) (f : α → β) :
    (l.map f).sum = ∑ k : Fin l.length, f (l.get k) := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-! ## 3. The columns -/

theorem toQ_qvE (χe : CoinsE) {n : ℕ} (rows : Fin n → CRow (ZMod P)) (i : Fin n) (aT aX : K6)
    (hT : K6.toQ aT = accT deltaF (chalsJJ8 (toχ χe)) rows i)
    (hX : K6.toQ aX = accX deltaF (chalsJJ8 (toχ χe)) rows i) (s : ℕ) (hs : s < 7) :
    K6.toQ (qvE χe (rows i) aT aX s) = qv deltaF (chalsJJ8 (toχ χe)) rows s i := by
  interval_cases s
  · exact toQ_sTE χe _ _
  · exact toQ_sTE χe _ _
  · exact toQ_sTE χe _ _
  · exact toQ_sTE χe _ _
  · exact toQ_sXE χe _
  · exact hT
  · exact hX

theorem coordN_toK_J (x : K3) (m : ℕ) : coordN powerBasis3 (K3.toK x) m = limbZ x (m % 3) := by
  rw [coordN, coord_K _ _ (Nat.mod_lt _ (by norm_num))]

theorem jGen_row (χe : CoinsE) (rows : List (CRow (ZMod P))) (i : Fin rows.length) :
    (jGen χe rows).1.getD i #[] =
      Array.ofFn (n := 71) fun c => jColD χe rows.length i (rows.get i)
        ((scanK6 (rows.map (termE χe))).getD i 0) ((scanK6 (rows.map (sXE χe))).getD i 0) c := by
  unfold jGen
  simp [Array.getD_eq_getD_getElem?, List.getElem_zipIdx, i.2]

theorem jGen_col (χe : CoinsE) (rows : List (CRow (ZMod P))) (i : Fin rows.length) (c : ℕ) (hc : c < 71) :
    ((jGen χe rows).1.getD i #[]).getD c 0 =
      colJ deltaF powerBasis3 (chalsJJ8 (toχ χe)) rows.get c i := by
  rw [jGen_row]
  have hlen : (rows.map (termE χe)).length = rows.length := by simp
  have hT : K6.toQ ((scanK6 (rows.map (termE χe))).getD i 0) =
      accT deltaF (chalsJJ8 (toχ χe)) rows.get i := by
    rw [toQ_scanK6_getD _ _ (by simp)]
    unfold accT
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < rows.length := by have := Finset.mem_range.mp hj; have := i.2; omega
    rw [tN, dif_pos hj']
    simp [List.getD_eq_getElem?_getD, hj', toQ_termE]
  have hX : K6.toQ ((scanK6 (rows.map (sXE χe))).getD i 0) =
      accX deltaF (chalsJJ8 (toχ χe)) rows.get i := by
    rw [toQ_scanK6_getD _ _ (by simp)]
    unfold accX
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < rows.length := by have := Finset.mem_range.mp hj; have := i.2; omega
    rw [xN, dif_pos hj']
    simp [List.getD_eq_getElem?_getD, hj', toQ_sXE]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hc, dif_pos, Option.getD_some]
  unfold jColD colJ
  by_cases h18 : c < 18
  · simp only [h18, if_true]
    unfold jetPre layJ
    by_cases h11 : c = 11
    · subst h11
      simp [flag]
    · by_cases h12 : c = 12
      · subst h12
        have : ((i : ℕ) + 1 == rows.length) = ((i : ℕ) = rows.length - 1) := by
          have := i.2
          simp only [beq_iff_eq, eq_iff_iff]; omega
        simp [flag, this]
      · simp [h11, h12]
  · by_cases h29 : c < 29
    · simp [h18, h29]
    · simp only [h18, h29, if_false]
      have hs : (c - 29) / 3 / 2 < 7 := by omega
      have hq := toQ_qvE χe rows.get i _ _ hT hX ((c - 29) / 3 / 2) hs
      unfold roleV
      rw [← hq]
      split_ifs
      · rw [re_toQ, coordN_toK_J]
      · rw [im_toQ, coordN_toK_J]

/-- The J publics from a row list (`ComplJ8Of.pubsJOf` at `D.jrows`). -/
def pubsRows (chals : ℕ → KC) (rows : List (CRow (ZMod P))) : ℕ → KC := fun i =>
  if i < 2 then ComplJ8Of.pub2 deltaF (∑ k : Fin rows.length, termJ deltaF chals (rows.get k)) i
  else if i < 4 then ComplJ8Of.pub2 deltaF (∑ k : Fin rows.length, sX deltaF chals (rows.get k)) i else 0

theorem jGen_pubs (χe : CoinsE) (rows : List (CRow (ZMod P))) (j : ℕ) :
    K3.toK ((jGen χe rows).2 j) = pubsRows (chalsJJ8 (toχ χe)) rows j := by
  unfold pubsRows
  have hT : K6.toQ (lastK6 (scanK6 (rows.map (termE χe)))) =
      ∑ k : Fin rows.length, termJ deltaF (chalsJJ8 (toχ χe)) (rows.get k) := by
    rw [toQ_lastK6_scanK6, List.map_map, list_sum_map_get]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [toQ_termE]
  have hX : K6.toQ (lastK6 (scanK6 (rows.map (sXE χe)))) =
      ∑ k : Fin rows.length, sX deltaF (chalsJJ8 (toχ χe)) (rows.get k) := by
    rw [toQ_lastK6_scanK6, List.map_map, list_sum_map_get]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [toQ_sXE]
  unfold jGen
  simp only []
  by_cases h0 : j = 0
  · subst h0
    rw [← hT]
    simp only [ComplJ8Of.pub2]
    simp
    exact (re_toQ _).symm
  by_cases h1 : j = 1
  · subst h1
    rw [← hT]
    simp only [ComplJ8Of.pub2]
    simp
    exact (im_toQ _).symm
  by_cases h2 : j = 2
  · subst h2
    rw [← hX]
    simp only [ComplJ8Of.pub2]
    simp
    exact (re_toQ _).symm
  by_cases h3 : j = 3
  · subst h3
    rw [← hX]
    simp only [ComplJ8Of.pub2]
    simp
    exact (im_toQ _).symm
  have : ¬ j < 2 := by omega
  have : ¬ j < 4 := by omega
  simp [h0, h1, h2, h3, K3.toK_zero, *]

theorem pubsRows_zero (chals : ℕ → KC) (rows : List (CRow (ZMod P))) (h0 : rows.length = 0) (i : ℕ) :
    pubsRows chals rows i = 0 := by
  have hs : ∀ (g : Fin rows.length → Quad (algebraMap (ZMod P) KC deltaF)), ∑ k, g k = 0 := by
    intro g; exact Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
  have hz : Quad.re _ (0 : Quad (algebraMap (ZMod P) KC deltaF)) = 0 ∧
      Quad.im _ (0 : Quad (algebraMap (ZMod P) KC deltaF)) = 0 :=
    (Quad.mk_eq_zero_iff _ _ _).mp (Quad.mk_re_im _ 0)
  have hp2 : ∀ i, ComplJ8Of.pub2 deltaF (0 : Quad (algebraMap (ZMod P) KC deltaF)) i = 0 := by
    intro i
    unfold ComplJ8Of.pub2
    split_ifs
    · exact hz.1
    · exact hz.2
  unfold pubsRows
  rw [hs, hs]
  split_ifs
  · exact hp2 i
  · exact hp2 i
  · rfl

/-! ## 4. The J chip port -/

open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipPort (ChipPort chipAt_of_cols_pubs)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of (powN)
open Nock.Jet.ChipJ8 (jetChipJ8 baseGatesJ envOf)
open Polynomial

/-- Sat and binds of the J chip at the honest row layout. -/
def JOk {n : ℕ} (rows : Fin n → CRow (ZMod P)) {h : ℕ} (ν : Fin n → ZMod P)
    (O : StrictOrbitDomain (ZMod P) 3 h) (chals pubs : ℕ → KC) (T : Fin 71 → (ZMod P)[X]) : Prop :=
  (jetChipJ8 deltaF powerBasis3 ν O chals pubs (layJ rows)).rap.Satisfies
      (fun j => T (Fin.cast (Nock.Jet.ChipJ8.jetChipJ8_width deltaF powerBasis3 ν O chals pubs (layJ rows)) j)) ∧
    (jetChipJ8 deltaF powerBasis3 ν O chals pubs (layJ rows)).BindsPreprocessing
      (fun j => T (Fin.cast (Nock.Jet.ChipJ8.jetChipJ8_width deltaF powerBasis3 ν O chals pubs (layJ rows)) j))

/-- The J chip as a `ChipPort` over the row list `rows`. -/
def jPort (rows : List (CRow (ZMod P))) : ChipPort KC 71 where
  Ok := fun {n} _ ν {h} O chals pubs T => ∀ e : n = rows.length,
    JOk (fun i => rows.get (Fin.cast e i)) ν O chals pubs T

theorem interp_reidx {n m : ℕ} (e : n = m) (ν : Fin n → ZMod P) (μ : Fin m → ZMod P)
    (hνμ : ∀ i : Fin n, ν i = μ (Fin.cast e i)) (v : Fin n → ZMod P) (w : Fin m → ZMod P)
    (hvw : ∀ i : Fin n, v i = w (Fin.cast e i)) :
    Lagrange.interpolate Finset.univ ν v = Lagrange.interpolate Finset.univ μ w := by
  subst e
  obtain rfl : ν = μ := funext hνμ
  obtain rfl : v = w := funext hvw
  rfl

/-- **The J chip at an arbitrary injective orbit** (abstract in the row list). -/
theorem jchip_at (χe : CoinsE) (rows : List (CRow (ZMod P)))
    (hgate : ∀ x ∈ rows, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod P))), g.eval (envOf x) = 0)
    (hpole : ¬ ComplJ8Jet.JPole deltaF rows.get (chalsJJ8 (toχ χe)))
    (q : ChipIn) (hoq : OrbOK q) (hinj0 : Function.Injective (nodesOf q))
    (hadj0 : ∀ (i : Fin q.n) (hi : (i : ℕ) + 1 < q.n),
      nodesOf q ⟨(i : ℕ) + 1, hi⟩ = nodesOf q i * (mkOrbit q hoq).ω)
    (hn : q.n = rows.length) (lay : Fin q.n → PRow)
    (hlay : ∀ i : Fin q.n, lay i = (rows.get (Fin.cast hn i)).pre)
    (pubs : ℕ → KC) (hpubs : pubs = fun j => K3.toK ((jGen χe rows).2 j))
    (hcols : ∀ (j : ℕ) (i : Fin q.n), j < 71 → q.cols j i = ((jGen χe rows).1.getD (i : ℕ) #[]).getD j 0) :
    JGenJ8.JChipOK deltaF powerBasis3 (nodesOf q) (mkOrbit q hoq) (chalsJJ8 (toχ χe)) pubs lay
      (fun j => interpOf q (Fin.cast (Nock.Jet.ChipJ8.jetChipJ8_width deltaF powerBasis3 (nodesOf q)
        (mkOrbit q hoq) (chalsJJ8 (toχ χe)) pubs lay) j : Fin 71)) := by
  by_cases h0 : rows.length = 0
  · refine Or.inr ⟨by omega, ?_⟩
    have hz : ∀ i, pubs i = 0 := fun i => by
      rw [hpubs]
      show K3.toK ((jGen χe rows).2 i) = 0
      rw [jGen_pubs]
      exact pubsRows_zero _ rows h0 i
    exact ⟨hz 0, hz 1, hz 2, hz 3⟩
  · have hm : 0 < rows.length := Nat.pos_of_ne_zero h0
    have hnq : 0 < q.n := by omega
    have hpubsR : pubs = pubsRows (chalsJJ8 (toχ χe)) rows := by
      rw [hpubs]; funext j; exact jGen_pubs χe rows j
    have hrun : ∀ {h : ℕ} (O : StrictOrbitDomain (ZMod P) 3 h), Function.Injective (powN O rows.length) →
        (∀ (i : Fin rows.length) (hi : (i : ℕ) + 1 < rows.length),
          powN O rows.length ⟨(i : ℕ) + 1, hi⟩ = powN O rows.length i * O.ω) →
        (jPort rows).Ok hm (powN O rows.length) O (chalsJJ8 (toχ χe)) (pubsRows (chalsJJ8 (toχ χe)) rows)
          (ComplJ8Jet.trJ deltaF powerBasis3 (powN O rows.length) (chalsJJ8 (toχ χe)) rows.get) := by
      intro h O hinj hadj e
      have H := ComplJ8Jet.jOK_present_trJ deltaF powerBasis3 (powN O rows.length) O (chalsJJ8 (toχ χe))
        (pubsRows (chalsJJ8 (toχ χe)) rows) rows.get hinj hm hadj
        (fun i => hgate _ (List.get_mem _ _))
        hpole
        (by simp only [pubsRows]; exact ComplJ8Of.pub2_mk deltaF _)
        (by simp only [pubsRows]; exact ComplJ8Of.pub2_mk2 deltaF _ 2 (by norm_num))
      have H' := JGenJ8.present_of_pos H hm
      exact ⟨H'.1, H'.2.1⟩
    have hnodes : ∀ i : Fin q.n, nodesOf q i = powN (mkOrbit q hoq) rows.length (Fin.cast hn i) :=
      fun i => nodesOf_eq q i
    have hcolsT : (fun j : Fin 71 => interpOf q j) =
        ComplJ8Jet.trJ deltaF powerBasis3 (powN (mkOrbit q hoq) rows.length) (chalsJJ8 (toχ χe)) rows.get := by
      funext j
      unfold interpOf ComplJ8Jet.trJ Nock.Jet.ChipJ8T.HonestRAP.polyJ
      refine interp_reidx hn _ _ hnodes _ _ fun i => ?_
      exact (hcols j i j.2).trans (jGen_col χe rows (Fin.cast hn i) j j.2)
    have H := chipAt_of_cols_pubs (jPort rows) q hoq hnq hinj0 hm hn (chalsJJ8 (toχ χe))
      (fun {_} _ => pubsRows (chalsJJ8 (toχ χe)) rows)
      (fun {_} O => ComplJ8Jet.trJ deltaF powerBasis3 (powN O rows.length) (chalsJJ8 (toχ χe)) rows.get)
      hrun pubs hpubsR (fun j : Fin 71 => interpOf q j) hcolsT
    have H2 := H hn
    have hlayE : lay = Nock.Jet.ChipJ8T.HonestRAP.layJ (fun i : Fin q.n => rows.get (Fin.cast hn i)) :=
      funext hlay
    subst hlayE
    exact Or.inl ⟨H2.1, H2.2, hinj0, hnq, hadj0⟩

theorem lay_len {n : ℕ} (lay : Fin n → PRow) (rows : List (CRow (ZMod P)))
    (h : List.ofFn lay = rows.map CRow.pre) : n = rows.length := by
  have := congrArg List.length h
  simpa using this

theorem lay_pointwise {n : ℕ} (lay : Fin n → PRow) (rows : List (CRow (ZMod P)))
    (h : List.ofFn lay = rows.map CRow.pre) (hn : n = rows.length) :
    ∀ i : Fin n, lay i = (rows.get (Fin.cast hn i)).pre := by
  intro i
  have hi : (i : ℕ) < (List.ofFn lay).length := by simp
  have h1 := List.getElem_of_eq h hi
  simpa using h1

/-- **`jGen_interp`**: the interpolant of an exec J column `j < 71` at arbitrary nodes is `trJ`. -/
theorem jGen_interp (χe : CoinsE) (rows : List (CRow (ZMod P))) {n : ℕ} (hn : n = rows.length)
    (ν : Fin n → ZMod P) (j : Fin 71) :
    Lagrange.interpolate Finset.univ ν (fun i : Fin n => ((jGen χe rows).1.getD (i : ℕ) #[]).getD j 0) =
      ComplJ8Jet.trJ deltaF powerBasis3 ν (chalsJJ8 (toχ χe)) (fun i => rows.get (Fin.cast hn i)) j := by
  subst hn
  unfold ComplJ8Jet.trJ Nock.Jet.ChipJ8T.HonestRAP.polyJ
  exact congrArg (Lagrange.interpolate Finset.univ ν) (funext fun i => jGen_col χe rows i j j.2)

end Br

/-! ## 5. At `recJ9AXJ` -/

section Glue

open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun (recJ9AXJ lay_eqJ)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm reorb withOrb)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (qJ)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)

variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- The exec layout is the layout of the J rows. -/
theorem jlay_list (χe : CoinsE) :
    List.ofFn (recJ9AXJ Rt s f χe t r).lay = (j9aDataOf P Rg Rt hgen).jrows.map CRow.pre :=
  (lay_eqJ Rt hgen χe).trans (ComplJ8Jet.jrows_pre_run Rt hgen).symm

/-- The exec J row count is the row count of the data. -/
theorem jlen (χe : CoinsE) :
    (recJ9AXJ Rt s f χe t r).J.n = (j9aDataOf P Rg Rt hgen).jrows.length :=
  lay_len _ _ (jlay_list Rt hgen χe)

/-- **`lay_layJ`**: the verifier's layout at `withOrb I o` is `layJ` of the honest rows (pointwise = equal). -/
theorem lay_layJ (χe : CoinsE) (o : OrbJ9A) (hv' : ValidJ9A (withOrb (recJ9AXJ Rt s f χe t r) o)) :
    (mkPbA (withOrb (recJ9AXJ Rt s f χe t r) o) hv').lay =
      Nock.Jet.ChipJ8T.HonestRAP.layJ
        (fun i : Fin (recJ9AXJ Rt s f χe t r).J.n =>
          (j9aDataOf P Rg Rt hgen).jrows.get (Fin.cast (jlen Rt hgen χe) i)) :=
  funext (lay_pointwise _ _ (jlay_list Rt hgen χe) (jlen Rt hgen χe))

/-- **`jGen_pubs` at the run**: the exec `pubsJ` (`K3.toK`) is `ComplJ8Of.pubsJOf deltaF DA (toχ χe)`. -/
theorem jGen_pubs_DA (χe : CoinsE) (j : ℕ) :
    K3.toK ((recJ9AXJ Rt s f χe t r).M.pubsJ j) =
      ComplJ8Of.pubsJOf deltaF (j9aDataOf P Rg Rt hgen) (toχ χe) j :=
  jGen_pubs χe (j9aDataOf P Rg Rt hgen).jrows j

/-- **The `hJk` field of `AcceptsJ9A` at `withOrb I o`** (`I = recJ9AXJ`), present or absent. -/
theorem j_at (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate P, Nock.Jet.Autogen.compile P (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped P)
    (χe : CoinsE) (o : OrbJ9A) (ho : OrbAdm (recJ9AXJ Rt s f χe t r) o)
    (hv' : ValidJ9A (withOrb (recJ9AXJ Rt s f χe t r) o))
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    JGenJ8.JChipOK deltaF powerBasis3 (mkPbA (withOrb (recJ9AXJ Rt s f χe t r) o) hv').nodesJ
      (mkPbA (withOrb (recJ9AXJ Rt s f χe t r) o) hv').orbitJ
      (chalsJJ8 (toχ (withOrb (recJ9AXJ Rt s f χe t r) o).χ))
      (withOrb (recJ9AXJ Rt s f χe t r) o).toMsg.pubsJ (mkPbA (withOrb (recJ9AXJ Rt s f χe t r) o) hv').lay
      (qJ deltaF powerBasis3 (mkPbA (withOrb (recJ9AXJ Rt s f χe t r) o) hv').toPubJ8
        (withOrb (recJ9AXJ Rt s f χe t r) o).toTr.toJ8
        (chalsJJ8 (toχ (withOrb (recJ9AXJ Rt s f χe t r) o).χ))
        (withOrb (recJ9AXJ Rt s f χe t r) o).toMsg.pubsJ) := by
  have hp : 0 < P := (Fact.out : P.Prime).pos
  have hn := jlen Rt hgen χe
  have hlay := lay_pointwise _ _ (jlay_list Rt hgen χe) hn
  have hoq : OrbOK (reorb (recJ9AXJ Rt s f χe t r).J o.J) := ho.J.1
  obtain ⟨hinj0, hadj0⟩ := GenPortJ9AHOrbA.nodes_ok _ hoq ho.J.2
  have hpole0 := ComplJ8Bad.jNoPole deltaF (ComplJ8Jet.jKeysT (j9aDataOf P Rg Rt hgen).jrows.get)
    (ComplJ8Jet.jKeysX (j9aDataOf P Rg Rt hgen).jrows.get) (toχ χe)
    (fun e he => ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ _
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) e he)
  have hpole := ComplJ8Jet.notJPole_of_keys deltaF _ _ hpole0.1 hpole0.2
  exact jchip_at χe (j9aDataOf P Rg Rt hgen).jrows
    (fun x hx => ComplJ8Jet.jrows_gate_run Rt hgen hp hRt x hx) hpole
    (reorb (recJ9AXJ Rt s f χe t r).J o.J) hoq hinj0 hadj0 hn
    (mkPbA (withOrb (recJ9AXJ Rt s f χe t r) o) hv').lay hlay
    (withOrb (recJ9AXJ Rt s f χe t r) o).toMsg.pubsJ (funext fun j => rfl) (fun j i _ => rfl)

end Glue

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbJ

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbJ
#print axioms toQ_fq
#print axioms toQ_dKey_gen
#print axioms toQ_dKey8
#print axioms toQ_dKey5
#print axioms toQ_foldr_add
#print axioms toQ_sTE
#print axioms toQ_sXE
#print axioms toQ_termE
#print axioms scanK6_eq
#print axioms toQ_scanl_getD
#print axioms toQ_scanK6_getD
#print axioms getLastD_scanl
#print axioms toQ_foldl_add'
#print axioms toQ_lastK6_scanK6
#print axioms list_sum_map_get
#print axioms toQ_qvE
#print axioms coordN_toK_J
#print axioms jGen_row
#print axioms jGen_col
#print axioms jGen_pubs
#print axioms pubsRows_zero
#print axioms interp_reidx
#print axioms jchip_at
#print axioms lay_len
#print axioms lay_pointwise
#print axioms jGen_interp
#print axioms jlay_list
#print axioms jlen
#print axioms lay_layJ
#print axioms jGen_pubs_DA
#print axioms j_at
