/-
  NockvmE2E/Exec/DagSem.lean   (proof-only)

  The `KC` / `MvPolynomial` reading of the verifier's chip DAG (`evalDag`), its congruence in the environment, `multOf = eval Zout`,
  and the flat-index bookkeeping of `termsAt`/`curNxtAt` that the generic half of `hdagU` needs.
-/
import NockvmE2E.Exec.E2ELinksRap
import NockvmE2E.Exec.E2EResid
import NockvmE2E.J8.Deep

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial

namespace NockvmE2E.Exec.DagSem
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.Tr NockvmE2E.Rap NockvmE2E.Deep NockvmE2E.J8
open NockvmE2E.Exec.E2ELR

/-! ## A. the `KC` interpreter of a chip DAG (mirror of `evK`/`evalDag`, Dag.lean:26-44) -/

structure KEnv where
  cur : ℕ → KC
  next : ℕ → KC
  pub : ℕ → ZMod p
  chal : ℕ → KC
  bc : ℕ

noncomputable def extK (a : ℕ → KC) (bc e : ℕ) : KC := a (bc + 3 * e) + a (bc + 3 * e + 1) * xr + a (bc + 3 * e + 2) * xr ^ 2

noncomputable def evKC (env : KEnv) (memo : Array KC) : Ex → KC
  | .var 0 i => env.cur i
  | .var 1 i => env.next i
  | .var _ i => algebraMap (ZMod p) KC (env.pub i)
  | .cF v => psiV v
  | .add a b => evKC env memo a + evKC env memo b
  | .sub a b => evKC env memo a - evKC env memo b
  | .mul a b => evKC env memo a * evKC env memo b
  | .neg a => - evKC env memo a
  | .pow a n => evKC env memo a ^ n
  | .extVar 0 e => extK env.cur env.bc e
  | .extVar 1 e => extK env.next env.bc e
  | .extVar _ e => algebraMap (ZMod p) KC (env.pub (3 * e)) + algebraMap (ZMod p) KC (env.pub (3 * e + 1)) * xr +
      algebraMap (ZMod p) KC (env.pub (3 * e + 2)) * xr ^ 2
  | .chal i => env.chal i
  | .ref i => memo[i]!

noncomputable def memoK (sh : List Ex) (env : KEnv) : Array KC :=
  sh.foldl (fun (memo : Array KC) s => memo.push (evKC env memo s)) #[]

noncomputable def evalDagK (ch : Chip) (env : KEnv) : Array KC :=
  ch.cons.map fun c => evKC env (memoK ch.shared.toList env) c.e

/-- the `KC` reading of a verifier environment -/
noncomputable def KEnv.ofD (env : DEnv) : KEnv :=
  ⟨fun i => toKV env.cur[i]!, fun i => toKV env.next[i]!, fun i => zv env.pub[i]!, fun i => toKV env.chal[i]!, env.bc⟩

theorem default_KC : (default : KC) = 0 := rfl
theorem toKV_default : toKV (default : VF.K3) = 0 := by
  show toKV VF.K3.zero = 0
  exact toKV_zero

theorem toKV_gen : toKV VF.K3.gen = xr := by
  unfold toKV VF.K3.gen
  simp [zv_zero, zv_one]

theorem toKV_mk (a b c : UInt64) : toKV ⟨a, b, c⟩ = algebraMap (ZMod p) KC (zv a) + algebraMap (ZMod p) KC (zv b) * xr +
    algebraMap (ZMod p) KC (zv c) * xr ^ 2 := rfl

theorem toKV_extV (a : Array VF.K3) (ha : ∀ i : ℕ, canon3 a[i]!) (bc e : ℕ) :
    toKV (extV a bc e) = extK (fun i => toKV a[i]!) bc e := by
  unfold extV extK
  have h1 : canon3 (VF.K3.mul a[bc + 3 * e + 1]! VF.K3.gen) := canon3_mul _ _
  have h2 : canon3 (VF.K3.mul a[bc + 3 * e + 2]! (VF.K3.mul VF.K3.gen VF.K3.gen)) := canon3_mul _ _
  rw [toKV_add _ _ (canon3_add _ _ (ha _) h1) h2, toKV_add _ _ (ha _) h1, toKV_mul, toKV_mul, toKV_mul, toKV_gen]
  ring

/-- the paired memo invariant: a verifier memo `M` and a `KC` memo `MK` of equal size, `M` canonical, `toKV ∘ M = MK` -/
def MemoPair (M : Array VF.K3) (MK : Array KC) : Prop :=
  M.size = MK.size ∧ (∀ i : ℕ, canon3 M[i]!) ∧ ∀ i : ℕ, toKV M[i]! = MK[i]!

theorem MemoPair.empty : MemoPair #[] #[] := by
  refine ⟨rfl, fun i => ?_, fun i => ?_⟩
  · simp [getElem!_neg]; exact canon3_zero
  · simp [getElem!_neg]; exact toKV_default

theorem MemoPair.push {M : Array VF.K3} {MK : Array KC} (h : MemoPair M MK) (x : VF.K3) (y : KC) (hx : canon3 x)
    (hxy : toKV x = y) : MemoPair (M.push x) (MK.push y) := by
  obtain ⟨hs, hc, ht⟩ := h
  refine ⟨by simp [hs], canon_push _ _ hc hx, fun i => ?_⟩
  by_cases hi : i < M.size
  · have hi' : i < MK.size := hs ▸ hi
    rw [getElem!_pos (M.push x) i (by simpa using Nat.lt_succ_of_lt hi), getElem!_pos (MK.push y) i (by simpa using Nat.lt_succ_of_lt hi'),
      Array.getElem_push, Array.getElem_push]
    simp only [hi, hi', dite_true]
    rw [← getElem!_pos M i hi, ← getElem!_pos MK i hi']; exact ht i
  · by_cases hi2 : i = M.size
    · rw [hi2, getElem!_pos (M.push x) M.size (by simp), getElem!_pos (MK.push y) M.size (by simp [hs]), Array.getElem_push_eq]
      simp only [hs, Array.getElem_push_eq, hxy]
    · have h1 : ¬ i < (M.push x).size := by simp; omega
      have h2 : ¬ i < (MK.push y).size := by simp [← hs]; omega
      rw [getElem!_neg (M.push x) i h1, getElem!_neg (MK.push y) i h2]
      exact toKV_default

theorem toKV_evK (env : DEnv) (hcur : ∀ i : ℕ, canon3 env.cur[i]!) (hnext : ∀ i : ℕ, canon3 env.next[i]!)
    (hpub : ∀ i : ℕ, canon env.pub[i]!) (hchal : ∀ i : ℕ, canon3 env.chal[i]!) (M : Array VF.K3) (MK : Array KC)
    (hM : MemoPair M MK) : ∀ ex : Ex, ExCan ex → toKV (evK env M ex) = evKC (KEnv.ofD env) MK ex
  | .var k i, _ => by
    rcases k with _ | _ | k
    · rfl
    · rfl
    · simp only [evK, evKC, toKV_ofG]; rfl
  | .cF v, _ => by simp only [evK, evKC, toKV_ofG]
  | .add a b, hc => by
    have hE : EnvCan env M := ⟨hcur, hnext, hpub, hchal, hM.2.1⟩
    simp only [evK, evKC]
    rw [toKV_add _ _ (canon3_evK env M hE a hc.1) (canon3_evK env M hE b hc.2), toKV_evK env hcur hnext hpub hchal M MK hM a hc.1,
      toKV_evK env hcur hnext hpub hchal M MK hM b hc.2]
  | .sub a b, hc => by
    have hE : EnvCan env M := ⟨hcur, hnext, hpub, hchal, hM.2.1⟩
    simp only [evK, evKC]
    rw [toKV_sub _ _ (canon3_evK env M hE a hc.1) (canon3_evK env M hE b hc.2), toKV_evK env hcur hnext hpub hchal M MK hM a hc.1,
      toKV_evK env hcur hnext hpub hchal M MK hM b hc.2]
  | .mul a b, hc => by
    simp only [evK, evKC]
    rw [toKV_mul, toKV_evK env hcur hnext hpub hchal M MK hM a hc.1, toKV_evK env hcur hnext hpub hchal M MK hM b hc.2]
  | .neg a, hc => by
    have hE : EnvCan env M := ⟨hcur, hnext, hpub, hchal, hM.2.1⟩
    simp only [evK, evKC]
    rw [toKV_neg _ (canon3_evK env M hE a hc), toKV_evK env hcur hnext hpub hchal M MK hM a hc]
  | .pow a n, hc => by
    simp only [evK, evKC]
    rw [toKV_pow, toKV_evK env hcur hnext hpub hchal M MK hM a hc]
  | .extVar k e, _ => by
    rcases k with _ | _ | k
    · exact toKV_extV _ hcur _ _
    · exact toKV_extV _ hnext _ _
    · rfl
  | .chal i, _ => rfl
  | .ref i, _ => by simp only [evK, evKC]; exact hM.2.2 i

theorem memoPair_fold (env : DEnv) (hcur : ∀ i : ℕ, canon3 env.cur[i]!) (hnext : ∀ i : ℕ, canon3 env.next[i]!)
    (hpub : ∀ i : ℕ, canon env.pub[i]!) (hchal : ∀ i : ℕ, canon3 env.chal[i]!) :
    ∀ (l : List Ex) (M : Array VF.K3) (MK : Array KC), MemoPair M MK → (∀ s ∈ l, ExCan s) →
      MemoPair (l.foldl (fun (memo : Array VF.K3) s => memo.push (evK env memo s)) M)
        (l.foldl (fun (memo : Array KC) s => memo.push (evKC (KEnv.ofD env) memo s)) MK) := by
  intro l
  induction l with
  | nil => intro M MK h _; simpa using h
  | cons s l ih =>
    intro M MK h hl
    simp only [List.foldl_cons]
    refine ih _ _ (h.push _ _ (canon3_evK env M ⟨hcur, hnext, hpub, hchal, h.2.1⟩ s (hl s (by simp))) ?_)
      (fun t ht => hl t (List.mem_cons_of_mem _ ht))
    exact toKV_evK env hcur hnext hpub hchal M MK h s (hl s (by simp))

/-- **A2** `evalDag` ⇔ `evalDagK` under `toKV` (canonical inputs; `ExCan` = `chipCanon`'s Prop form, Sound.lean:477) -/
theorem toKV_evalDag (ch : Chip) (env : DEnv) (hcur : ∀ i : ℕ, canon3 env.cur[i]!) (hnext : ∀ i : ℕ, canon3 env.next[i]!)
    (hpub : ∀ i : ℕ, canon env.pub[i]!) (hchal : ∀ i : ℕ, canon3 env.chal[i]!)
    (hsh : ∀ s ∈ ch.shared.toList, ExCan s) (hcs : ∀ c ∈ ch.cons.toList, ExCan c.e) (j : ℕ) :
    toKV (evalDag ch env)[j]! = (evalDagK ch (KEnv.ofD env))[j]! := by
  have hm := memoPair_fold env hcur hnext hpub hchal ch.shared.toList (Array.mkEmpty ch.shared.size) #[]
    (by simpa using MemoPair.empty) hsh
  unfold evalDag evalDagK memoK
  by_cases hj : j < ch.cons.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos _ j (by simpa using hj), Array.getElem_map, Array.getElem_map]
    exact toKV_evK env hcur hnext hpub hchal _ _ hm _ (hcs _ (Array.getElem_mem_toList hj))
  · rw [getElem!_neg, getElem!_neg]
    · exact toKV_default
    all_goals simpa using hj

/-- **A3** congruence: two environments agreeing on every column/public/slot a chip may read give the same values
(`chipReadsLt` is the executable bound check proposed for `j8ShapeOk`) -/
def exReadsLt (w npub nch : ℕ) (bc : ℕ) : Ex → Bool
  | .var 0 i | .var 1 i => decide (i < w)
  | .var _ i => decide (i < npub)
  | .extVar 0 e | .extVar 1 e => decide (bc + 3 * e + 2 < w)
  | .extVar _ e => decide (3 * e + 2 < npub)
  | .chal i => decide (i < nch)
  | .add a b | .sub a b | .mul a b => exReadsLt w npub nch bc a && exReadsLt w npub nch bc b
  | .neg a | .pow a _ => exReadsLt w npub nch bc a
  | _ => true

def chipReadsLt (ch : Chip) (w npub nch : ℕ) : Bool :=
  ch.shared.all (exReadsLt w npub nch ch.baseCols) && ch.cons.all (fun c => exReadsLt w npub nch ch.baseCols c.e)

theorem evKC_congr (w npub nch bc : ℕ) (e e' : KEnv) (hbc : e.bc = bc) (hbc' : e'.bc = bc)
    (hc : ∀ i < w, e.cur i = e'.cur i) (hn : ∀ i < w, e.next i = e'.next i)
    (hp : ∀ i < npub, e.pub i = e'.pub i) (hch : ∀ i < nch, e.chal i = e'.chal i) (M : Array KC) :
    ∀ ex : Ex, exReadsLt w npub nch bc ex = true → evKC e M ex = evKC e' M ex
  | .var k i, h => by
    rcases k with _ | _ | k
    · exact hc i (by simpa [exReadsLt] using h)
    · exact hn i (by simpa [exReadsLt] using h)
    · simp only [evKC]; rw [hp i (by simpa [exReadsLt] using h)]
  | .cF v, _ => rfl
  | .add a b, h => by
    simp only [exReadsLt, Bool.and_eq_true] at h
    simp only [evKC]; rw [evKC_congr w npub nch bc e e' hbc hbc' hc hn hp hch M a h.1, evKC_congr w npub nch bc e e' hbc hbc' hc hn hp hch M b h.2]
  | .sub a b, h => by
    simp only [exReadsLt, Bool.and_eq_true] at h
    simp only [evKC]; rw [evKC_congr w npub nch bc e e' hbc hbc' hc hn hp hch M a h.1, evKC_congr w npub nch bc e e' hbc hbc' hc hn hp hch M b h.2]
  | .mul a b, h => by
    simp only [exReadsLt, Bool.and_eq_true] at h
    simp only [evKC]; rw [evKC_congr w npub nch bc e e' hbc hbc' hc hn hp hch M a h.1, evKC_congr w npub nch bc e e' hbc hbc' hc hn hp hch M b h.2]
  | .neg a, h => by
    simp only [exReadsLt] at h
    simp only [evKC]; rw [evKC_congr w npub nch bc e e' hbc hbc' hc hn hp hch M a h]
  | .pow a n, h => by
    simp only [exReadsLt] at h
    simp only [evKC]; rw [evKC_congr w npub nch bc e e' hbc hbc' hc hn hp hch M a h]
  | .extVar k i, h => by
    rcases k with _ | _ | k
    · have h' : bc + 3 * i + 2 < w := by simpa [exReadsLt] using h
      show extK e.cur e.bc i = extK e'.cur e'.bc i
      rw [hbc, hbc']; unfold extK
      rw [hc _ (by omega), hc (bc + 3 * i + 1) (by omega), hc (bc + 3 * i + 2) (by omega)]
    · have h' : bc + 3 * i + 2 < w := by simpa [exReadsLt] using h
      show extK e.next e.bc i = extK e'.next e'.bc i
      rw [hbc, hbc']; unfold extK
      rw [hn _ (by omega), hn (bc + 3 * i + 1) (by omega), hn (bc + 3 * i + 2) (by omega)]
    · have h' : 3 * i + 2 < npub := by simpa [exReadsLt] using h
      simp only [evKC]
      rw [hp _ (by omega), hp (3 * i + 1) (by omega), hp (3 * i + 2) (by omega)]
  | .chal i, h => hch i (by simpa [exReadsLt] using h)
  | .ref i, _ => rfl

theorem evalDagK_congr (ch : Chip) (w npub nch : ℕ) (hr : chipReadsLt ch w npub nch = true) (e e' : KEnv)
    (hbc : e.bc = ch.baseCols) (hbc' : e'.bc = ch.baseCols)
    (hc : ∀ i < w, e.cur i = e'.cur i) (hn : ∀ i < w, e.next i = e'.next i)
    (hp : ∀ i < npub, e.pub i = e'.pub i) (hch : ∀ i < nch, e.chal i = e'.chal i) :
    evalDagK ch e = evalDagK ch e' := by
  simp only [chipReadsLt, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at hr
  obtain ⟨hs, hcs⟩ := hr
  have hm : ∀ (l : List Ex) (M : Array KC), (∀ s ∈ l, exReadsLt w npub nch ch.baseCols s = true) →
      l.foldl (fun (memo : Array KC) s => memo.push (evKC e memo s)) M =
        l.foldl (fun (memo : Array KC) s => memo.push (evKC e' memo s)) M := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons s l ih =>
      intro M hl
      simp only [List.foldl_cons]
      rw [evKC_congr w npub nch ch.baseCols e e' hbc hbc' hc hn hp hch M s (hl s (by simp))]
      exact ih _ (fun t ht => hl t (List.mem_cons_of_mem _ ht))
  unfold evalDagK memoK
  rw [hm ch.shared.toList #[] (fun s hs' => hs s (Array.mem_toList_iff.mp hs'))]
  refine Array.map_congr_left ?_
  intro c hc'
  exact evKC_congr w npub nch ch.baseCols e e' hbc hbc' hc hn hp hch _ c.e (hcs c hc')

/-! ## B. `dagPoly` (the chip DAG as `MvPolynomial (ℕ × Fin 2) KC`, coins and publics as constants) -/

noncomputable def extP (o : Fin 2) (bc e : ℕ) : MvPolynomial (ℕ × Fin 2) KC :=
  MvPolynomial.X (bc + 3 * e, o) + MvPolynomial.X (bc + 3 * e + 1, o) * MvPolynomial.C xr +
    MvPolynomial.X (bc + 3 * e + 2, o) * MvPolynomial.C (xr ^ 2)

noncomputable def dpK (chal : ℕ → KC) (pub : ℕ → ZMod p) (bc : ℕ) (memo : Array (MvPolynomial (ℕ × Fin 2) KC)) :
    Ex → MvPolynomial (ℕ × Fin 2) KC
  | .var 0 i => MvPolynomial.X (i, 0)
  | .var 1 i => MvPolynomial.X (i, 1)
  | .var _ i => MvPolynomial.C (algebraMap (ZMod p) KC (pub i))
  | .cF v => MvPolynomial.C (psiV v)
  | .add a b => dpK chal pub bc memo a + dpK chal pub bc memo b
  | .sub a b => dpK chal pub bc memo a - dpK chal pub bc memo b
  | .mul a b => dpK chal pub bc memo a * dpK chal pub bc memo b
  | .neg a => - dpK chal pub bc memo a
  | .pow a n => dpK chal pub bc memo a ^ n
  | .extVar 0 e => extP 0 bc e
  | .extVar 1 e => extP 1 bc e
  | .extVar _ e => MvPolynomial.C (algebraMap (ZMod p) KC (pub (3 * e)) + algebraMap (ZMod p) KC (pub (3 * e + 1)) * xr +
      algebraMap (ZMod p) KC (pub (3 * e + 2)) * xr ^ 2)
  | .chal i => MvPolynomial.C (chal i)
  | .ref i => memo[i]!

noncomputable def dagPoly (ch : Chip) (chal : ℕ → KC) (pub : ℕ → ZMod p) : Array (MvPolynomial (ℕ × Fin 2) KC) :=
  let memo := ch.shared.toList.foldl (fun memo s => memo.push (dpK chal pub ch.baseCols memo s)) #[]
  ch.cons.map fun c => dpK chal pub ch.baseCols memo c.e

/-- the valuation of a (cur, next) pair -/
def valOf (env : KEnv) : ℕ × Fin 2 → KC := fun q => if q.2 = 0 then env.cur q.1 else env.next q.1

theorem aeval_dpK (env : KEnv) (bc : ℕ) (hbc : env.bc = bc) (PM : Array (MvPolynomial (ℕ × Fin 2) KC)) (MK : Array KC)
    (hs : PM.size = MK.size) (hm : ∀ i : ℕ, MvPolynomial.aeval (valOf env) PM[i]! = MK[i]!) :
    ∀ ex : Ex, MvPolynomial.aeval (valOf env) (dpK env.chal env.pub bc PM ex) = evKC env MK ex
  | .var k i => by
    rcases k with _ | _ | k
    · simp [dpK, evKC, valOf]
    · simp [dpK, evKC, valOf]
    · simp [dpK, evKC]
  | .cF v => by simp [dpK, evKC]
  | .add a b => by simp only [dpK, evKC, map_add, aeval_dpK env bc hbc PM MK hs hm a, aeval_dpK env bc hbc PM MK hs hm b]
  | .sub a b => by simp only [dpK, evKC, map_sub, aeval_dpK env bc hbc PM MK hs hm a, aeval_dpK env bc hbc PM MK hs hm b]
  | .mul a b => by simp only [dpK, evKC, map_mul, aeval_dpK env bc hbc PM MK hs hm a, aeval_dpK env bc hbc PM MK hs hm b]
  | .neg a => by simp only [dpK, evKC, map_neg, aeval_dpK env bc hbc PM MK hs hm a]
  | .pow a n => by simp only [dpK, evKC, map_pow, aeval_dpK env bc hbc PM MK hs hm a]
  | .extVar k e => by
    rcases k with _ | _ | k
    · simp [dpK, evKC, extP, extK, valOf, hbc]
    · simp [dpK, evKC, extP, extK, valOf, hbc]
    · simp [dpK, evKC]
  | .chal i => by simp [dpK, evKC]
  | .ref i => by simp only [dpK, evKC]; exact hm i

theorem aeval_dpK_fold (env : KEnv) (bc : ℕ) (hbc : env.bc = bc) :
    ∀ (l : List Ex) (PM : Array (MvPolynomial (ℕ × Fin 2) KC)) (MK : Array KC), PM.size = MK.size →
      (∀ i : ℕ, MvPolynomial.aeval (valOf env) PM[i]! = MK[i]!) →
      (l.foldl (fun memo s => memo.push (dpK env.chal env.pub bc memo s)) PM).size =
          (l.foldl (fun (memo : Array KC) s => memo.push (evKC env memo s)) MK).size ∧
        ∀ i : ℕ, MvPolynomial.aeval (valOf env) (l.foldl (fun memo s => memo.push (dpK env.chal env.pub bc memo s)) PM)[i]! =
          (l.foldl (fun (memo : Array KC) s => memo.push (evKC env memo s)) MK)[i]! := by
  intro l
  induction l with
  | nil => intro PM MK hs hm; exact ⟨hs, hm⟩
  | cons s l ih =>
    intro PM MK hs hm
    simp only [List.foldl_cons]
    refine ih _ _ (by simp [hs]) (fun i => ?_)
    have hv := aeval_dpK env bc hbc PM MK hs hm s
    by_cases hi : i < PM.size
    · have hi' : i < MK.size := hs ▸ hi
      rw [getElem!_pos (PM.push _) i (by simpa using Nat.lt_succ_of_lt hi), getElem!_pos (MK.push _) i (by simpa using Nat.lt_succ_of_lt hi'),
        Array.getElem_push, Array.getElem_push]
      simp only [hi, hi', dite_true]
      rw [← getElem!_pos PM i hi, ← getElem!_pos MK i hi']; exact hm i
    · by_cases hi2 : i = PM.size
      · rw [hi2, getElem!_pos (PM.push _) PM.size (by simp), getElem!_pos (MK.push _) PM.size (by simp [hs]), Array.getElem_push_eq]
        simp only [hs, Array.getElem_push_eq, hv]
      · rw [getElem!_neg (PM.push _) i (by simp; omega), getElem!_neg (MK.push _) i (by simp [← hs]; omega)]
        simp [default_KC]
        rfl

/-- **B** `aeval ∘ dagPoly = evalDagK` -/
theorem aeval_dagPoly (ch : Chip) (env : KEnv) (hbc : env.bc = ch.baseCols) (j : ℕ) :
    MvPolynomial.aeval (fun q : ℕ × Fin 2 => if q.2 = 0 then env.cur q.1 else env.next q.1)
      (dagPoly ch env.chal env.pub)[j]! = (evalDagK ch env)[j]! := by
  have hf := aeval_dpK_fold env ch.baseCols hbc ch.shared.toList #[] #[] rfl (fun i => by
    simp [getElem!_neg]; rfl)
  unfold dagPoly evalDagK memoK
  by_cases hj : j < ch.cons.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos _ j (by simpa using hj), Array.getElem_map, Array.getElem_map]
    exact aeval_dpK env ch.baseCols hbc _ _ hf.1 hf.2 _
  · rw [getElem!_neg, getElem!_neg]
    · simp [default_KC]; rfl
    all_goals simpa using hj

/-! ## D. `multOf = eval Zout` (toKV_multOf exists, Sound.lean:1296) -/

theorem multOf_Zout (XI : ExecInst) (t : TabInst) (zeta : VF.K3) (hz : canon3 zeta) (hS : canon XI.hShift)
    (H Ht : Finset (ZMod p))
    (hH : H = (Finset.range XI.hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i))
    (hHt : Ht = (Finset.range t.hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i))
    (hle : t.hN ≤ XI.hN)
    (hinj : Set.InjOn (fun i => zv XI.hShift * zv XI.hGen ^ i) (Finset.range XI.hN : Set ℕ)) :
    toKV (multOf XI zeta t) = eval (toKV zeta) ((Zout H Ht).map (algebraMap (ZMod p) KC)) := by
  classical
  set f : ℕ → ZMod p := fun i => zv XI.hShift * zv XI.hGen ^ i with hf
  have hdiff : H \ Ht = (Finset.Ico t.hN XI.hN).image f := by
    ext x
    simp only [hH, hHt, Finset.mem_sdiff, Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hn⟩
      refine ⟨i, ⟨?_, hi⟩, rfl⟩
      by_contra hlt
      exact hn ⟨i, by omega, rfl⟩
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨i, h2, rfl⟩, ?_⟩
      rintro ⟨j, hj, hji⟩
      have := hinj (show j ∈ (Finset.range XI.hN : Set ℕ) by simp; omega) (show i ∈ (Finset.range XI.hN : Set ℕ) by simp; omega) hji
      omega
  have hinj2 : Set.InjOn f (Finset.Ico t.hN XI.hN : Set ℕ) := fun a ha b hb e =>
    hinj (show a ∈ (Finset.range XI.hN : Set ℕ) by simp at ha ⊢; omega) (show b ∈ (Finset.range XI.hN : Set ℕ) by simp at hb ⊢; omega) e
  rw [toKV_multOf XI zeta hz hS t]
  unfold Zout
  rw [Polynomial.map_prod, eval_prod, hdiff, Finset.prod_image hinj2, Finset.prod_Ico_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X, eval_C]
  simp only [hf, map_mul, map_pow]
  rfl

/-! ## F0. `termsAt` read at a flat index -/

/-- flat index → (table, local constraint) over the table sizes (the `flatMap` of `termsK`) -/
def flatIdx : List ℕ → ℕ → ℕ × ℕ
  | [], i => (0, i)
  | s :: ss, i => if i < s then (0, i) else let q := flatIdx ss (i - s); (q.1 + 1, q.2)

theorem termsK_get? (αV : VF.K3) (cv : TabInst → Array VF.K3) (mult : TabInst → VF.K3) (hcv : ∀ t, (cv t).size = t.chip.cons.size) :
    ∀ (ts : List TabInst) (i : ℕ) (hi : i < (ts.map (·.chip.cons.size)).sum)
      (ht : (flatIdx (ts.map (·.chip.cons.size)) i).1 < ts.length),
      (termsK αV cv mult ts)[i]? =
        some (toKV (mult ts[(flatIdx (ts.map (·.chip.cons.size)) i).1]) *
          toKV (cv ts[(flatIdx (ts.map (·.chip.cons.size)) i).1])[(flatIdx (ts.map (·.chip.cons.size)) i).2]!)
  | [], i, hi, ht => by simp at hi
  | t :: ts, i, hi, ht => by
    by_cases h : i < t.chip.cons.size
    · have hl : (((cv t).toList.map toKV).map (toKV (mult t) * ·)).length = t.chip.cons.size := by simp [hcv]
      have hfi : flatIdx ((t :: ts).map (·.chip.cons.size)) i = (0, i) := by simp [flatIdx, h]
      simp only [termsK, List.flatMap_cons]
      rw [List.getElem?_append_left (by omega)]
      simp only [hfi, List.getElem_cons_zero]
      have hi' : i < (cv t).size := by rw [hcv]; exact h
      rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hi',
        getElem!_pos (cv t) i hi']
      rfl
    · have hfi : flatIdx ((t :: ts).map (·.chip.cons.size)) i =
          ((flatIdx (ts.map (·.chip.cons.size)) (i - t.chip.cons.size)).1 + 1, (flatIdx (ts.map (·.chip.cons.size)) (i - t.chip.cons.size)).2) := by
        simp [flatIdx, h]
      have hl : (((cv t).toList.map toKV).map (toKV (mult t) * ·)).length = t.chip.cons.size := by simp [hcv]
      have hi2 : i - t.chip.cons.size < (ts.map (·.chip.cons.size)).sum := by
        simp only [List.map_cons, List.sum_cons] at hi; omega
      have ht2 : (flatIdx (ts.map (·.chip.cons.size)) (i - t.chip.cons.size)).1 < ts.length := by
        rw [hfi] at ht; simpa using ht
      have ih := termsK_get? αV cv mult hcv ts (i - t.chip.cons.size) hi2 ht2
      simp only [termsK, List.flatMap_cons]
      rw [List.getElem?_append_right (by omega)]
      simp only [hfi, List.getElem_cons_succ]
      rw [hl]
      exact ih

/-- `termsAt` read at a flat index -/
theorem termsAt_get? (XI : ExecInst) (slots : Array VF.K3) (ζ : VF.K3) (vT : Array (Array VF.K3)) (i : ℕ)
    (hi : i < (XI.tabs.toList.map (·.chip.cons.size)).sum)
    (ht : (flatIdx (XI.tabs.toList.map (·.chip.cons.size)) i).1 < XI.tabs.size) :
    (termsAt XI slots ζ vT)[i]? =
      some (toKV (multOf XI ζ XI.tabs[(flatIdx (XI.tabs.toList.map (·.chip.cons.size)) i).1]) *
        toKV (tabCvAt XI slots ζ vT XI.tabs[(flatIdx (XI.tabs.toList.map (·.chip.cons.size)) i).1])[
          (flatIdx (XI.tabs.toList.map (·.chip.cons.size)) i).2]!) := by
  have hcv : ∀ t, (tabCvAt XI slots ζ vT t).size = t.chip.cons.size := by
    intro t; unfold tabCvAt evalDag; simp
  have := termsK_get? VF.K3.zero (tabCvAt XI slots ζ vT) (multOf XI ζ) hcv XI.tabs.toList i hi (by simpa using ht)
  unfold termsAt
  rw [this]
  simp only [Array.getElem_toList]

/-! ## `curNxtAt` read at a column -/

theorem set!_get {α : Type} [Inhabited α] (a : Array α) (i j : ℕ) (v : α) (h : i < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos _ j hj]
    simp [Array.set!]
    split_ifs <;> simp_all
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg _ j hj]
    have : i ≠ j := by omega
    simp [this]

/-- the `cur` value of column `c` -/
def curVal (XI : ExecInst) (ζ : VF.K3) (vT : Array (Array VF.K3)) (c : ℕ) : VF.K3 :=
  match XI.colKind[c]! with
  | 0 => (vT[c]!)[0]!
  | 1 => VF.K3.hornerG XI.pre[c]! ζ
  | _ => VF.K3.zero

/-- the `next` value of column `c` -/
def nxtVal (XI : ExecInst) (ζ : VF.K3) (vT : Array (Array VF.K3)) (c : ℕ) : VF.K3 :=
  match XI.colKind[c]! with
  | 0 => if XI.r ≥ 2 then (vT[c]!)[1]! else VF.K3.zero
  | 1 => VF.K3.hornerG XI.pre[c]! (VF.K3.smul XI.hGen ζ)
  | _ => VF.K3.zero

/-- the step of `curNxtAt`'s column fold (the lambda of E2ELinksRap.lean:38-41) -/
def curNxtStep (XI : ExecInst) (ζ : VF.K3) (vT : Array (Array VF.K3)) (st : Array VF.K3 × Array VF.K3) (c : ℕ) :
    Array VF.K3 × Array VF.K3 :=
  match XI.colKind[c]! with
  | 0 => (st.1.set! c (vT[c]!)[0]!, st.2.set! c (if XI.r ≥ 2 then (vT[c]!)[1]! else VF.K3.zero))
  | 1 => (st.1.set! c (VF.K3.hornerG XI.pre[c]! ζ), st.2.set! c (VF.K3.hornerG XI.pre[c]! (VF.K3.smul XI.hGen ζ)))
  | _ => st

theorem curNxtAt_eq (XI : ExecInst) (ζ : VF.K3) (vT : Array (Array VF.K3)) :
    curNxtAt XI ζ vT = (List.range XI.nc).foldl (curNxtStep XI ζ vT)
      (Array.replicate (XI.nc + XI.nq) VF.K3.zero, Array.replicate (XI.nc + XI.nq) VF.K3.zero) := rfl

theorem curNxtAt_fold (XI : ExecInst) (ζ : VF.K3) (vT : Array (Array VF.K3)) : ∀ m : ℕ, m ≤ XI.nc →
    ((List.range m).foldl (curNxtStep XI ζ vT)
      (Array.replicate (XI.nc + XI.nq) VF.K3.zero, Array.replicate (XI.nc + XI.nq) VF.K3.zero)).1.size = XI.nc + XI.nq ∧
    ((List.range m).foldl (curNxtStep XI ζ vT)
      (Array.replicate (XI.nc + XI.nq) VF.K3.zero, Array.replicate (XI.nc + XI.nq) VF.K3.zero)).2.size = XI.nc + XI.nq ∧
      ∀ c, ((List.range m).foldl (curNxtStep XI ζ vT)
        (Array.replicate (XI.nc + XI.nq) VF.K3.zero, Array.replicate (XI.nc + XI.nq) VF.K3.zero)).1[c]! =
          (if c < m then curVal XI ζ vT c else VF.K3.zero) ∧
        ((List.range m).foldl (curNxtStep XI ζ vT)
          (Array.replicate (XI.nc + XI.nq) VF.K3.zero, Array.replicate (XI.nc + XI.nq) VF.K3.zero)).2[c]! =
          (if c < m then nxtVal XI ζ vT c else VF.K3.zero) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨by simp, by simp, fun c => ⟨?_, ?_⟩⟩
    · simp only [List.range_zero, List.foldl_nil, Nat.not_lt_zero, ite_false]
      by_cases h : c < XI.nc + XI.nq
      · rw [getElem!_pos _ c (by simpa using h)]; simp
      · rw [getElem!_neg _ c (by simpa using h)]; rfl
    · simp only [List.range_zero, List.foldl_nil, Nat.not_lt_zero, ite_false]
      by_cases h : c < XI.nc + XI.nq
      · rw [getElem!_pos _ c (by simpa using h)]; simp
      · rw [getElem!_neg _ c (by simpa using h)]; rfl
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hst : (List.range m).foldl (curNxtStep XI ζ vT)
      (Array.replicate (XI.nc + XI.nq) VF.K3.zero, Array.replicate (XI.nc + XI.nq) VF.K3.zero) = st at h1 h2 h3
    have hz1 : st.1[m]! = VF.K3.zero := by rw [(h3 m).1]; simp
    have hz2 : st.2[m]! = VF.K3.zero := by rw [(h3 m).2]; simp
    unfold curNxtStep
    have hlt : m < XI.nc + XI.nq := by omega
    rcases hk : XI.colKind[m]! with _ | _ | k
    · simp only []
      refine ⟨by simp [h1], by simp [h2], fun c => ⟨?_, ?_⟩⟩
      · rw [set!_get _ _ _ _ (by omega), (h3 c).1]
        by_cases hcm : c = m
        · subst hcm; simp [curVal, hk]
        · have : ¬ m = c := fun h => hcm h.symm
          simp only [this, ite_false]
          by_cases hl : c < m
          · simp [hl, show c < m + 1 by omega]
          · simp [hl, show ¬ c < m + 1 by omega]
      · rw [set!_get _ _ _ _ (by omega), (h3 c).2]
        by_cases hcm : c = m
        · subst hcm; simp [nxtVal, hk]
        · have : ¬ m = c := fun h => hcm h.symm
          simp only [this, ite_false]
          by_cases hl : c < m
          · simp [hl, show c < m + 1 by omega]
          · simp [hl, show ¬ c < m + 1 by omega]
    · simp only []
      refine ⟨by simp [h1], by simp [h2], fun c => ⟨?_, ?_⟩⟩
      · rw [set!_get _ _ _ _ (by omega), (h3 c).1]
        by_cases hcm : c = m
        · subst hcm; simp [curVal, hk]
        · have : ¬ m = c := fun h => hcm h.symm
          simp only [this, ite_false]
          by_cases hl : c < m
          · simp [hl, show c < m + 1 by omega]
          · simp [hl, show ¬ c < m + 1 by omega]
      · rw [set!_get _ _ _ _ (by omega), (h3 c).2]
        by_cases hcm : c = m
        · subst hcm; simp [nxtVal, hk]
        · have : ¬ m = c := fun h => hcm h.symm
          simp only [this, ite_false]
          by_cases hl : c < m
          · simp [hl, show c < m + 1 by omega]
          · simp [hl, show ¬ c < m + 1 by omega]
    · simp only []
      refine ⟨h1, h2, fun c => ⟨?_, ?_⟩⟩
      · rw [(h3 c).1]
        by_cases hcm : c = m
        · subst hcm; simp [curVal, hk]
        · by_cases hl : c < m
          · simp [hl, show c < m + 1 by omega]
          · simp [hl, show ¬ c < m + 1 by omega]
      · rw [(h3 c).2]
        by_cases hcm : c = m
        · subst hcm; simp [nxtVal, hk]
        · by_cases hl : c < m
          · simp [hl, show c < m + 1 by omega]
          · simp [hl, show ¬ c < m + 1 by omega]

/-- **F1** `curNxtAt` read at a column `c < nc` -/
theorem curNxtAt_get (XI : ExecInst) (ζ : VF.K3) (vT : Array (Array VF.K3)) (c : ℕ) (hc : c < XI.nc) :
    (curNxtAt XI ζ vT).1[c]! = curVal XI ζ vT c ∧ (curNxtAt XI ζ vT).2[c]! = nxtVal XI ζ vT c := by
  have h := (curNxtAt_fold XI ζ vT XI.nc le_rfl).2.2 c
  rw [curNxtAt_eq]
  simpa [hc] using h

/-! ## `toKV` of the verifier's Horner evaluation -/

theorem toKV_hornerList (z : VF.K3) : ∀ l : List UInt64, (∀ x ∈ l, canon x) →
    toKV (l.foldr (fun c acc => VF.K3.add (VF.K3.mul acc z) (VF.K3.ofG c)) VF.K3.zero) =
      ∑ m ∈ Finset.range l.length, psiV l[m]! * toKV z ^ m
  | [], _ => by simp [toKV_zero]
  | c :: l, h => by
    have hl : ∀ x ∈ l, canon x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.foldr_cons, List.length_cons]
    rw [toKV_add _ _ (canon3_mul _ _) (canon3_ofG _ (h c (by simp))), toKV_mul, toKV_ofG, toKV_hornerList z l hl,
      Finset.sum_range_succ']
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, pow_zero, mul_one, pow_succ]
    rw [Finset.sum_mul, add_comm]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    ring

/-- **F2** `hornerG` of canonical coefficients is the `KC` power sum (no hypothesis on `z` is needed) -/
theorem toKV_hornerG (coef : Array UInt64) (z : VF.K3) (hcoef : ∀ x ∈ coef.toList, canon x) :
    toKV (VF.K3.hornerG coef z) = ∑ m ∈ Finset.range coef.size, psiV coef[m]! * toKV z ^ m := by
  unfold VF.K3.hornerG
  rw [toKV_hornerList z _ hcoef]
  simp only [Array.length_toList]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [getElem!_pos coef m hm, getElem!_pos coef.toList m (by simpa using hm)]
  simp

end NockvmE2E.Exec.DagSem

#print axioms NockvmE2E.Exec.DagSem.toKV_evalDag
#print axioms NockvmE2E.Exec.DagSem.evalDagK_congr
#print axioms NockvmE2E.Exec.DagSem.aeval_dagPoly
#print axioms NockvmE2E.Exec.DagSem.multOf_Zout
#print axioms NockvmE2E.Exec.DagSem.termsAt_get?
#print axioms NockvmE2E.Exec.DagSem.curNxtAt_get
#print axioms NockvmE2E.Exec.DagSem.toKV_hornerG
