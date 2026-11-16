/-
the tie at J-8.
Part 1: the generic algebra (J-8 coordinate gates at a `KC`-point vs the DAG semantics `evB/evM`).
-/
import NockvmE2E.J8.InstJ8
import NockvmE2E.Exec.HdagU
import NockvmE2E.Exec.DagSemV
import NockvmE2E.Emit.Tie
import NockvmE2E.Emit.TieLeaf
import NockvmE2E.Emit.TieMixed
import NockvmE2E.Emit.TieCompute
import NockvmE2E.Emit.TieR
import NockvmE2E.Emit.ChipsWalk
import NockvmE2E.Emit.ChipsTieR_atom
import NockvmE2E.Emit.ChipsTieR_cellKW
import NockvmE2E.Emit.ChipsTieR_jet
import NockvmE2E.Emit.ChipsTieR_compute
import NockvmE2E.Emit.ChipsTieR_walkAtom
import NockvmE2E.Emit.ChipsTieR_walkJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Polynomial

namespace NockvmE2E.J8.TieJ8

open NockvmE2E.Emit Nock.Emit
open Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open NockvmE2E.Exec NockvmE2E.Exec.DagSem
open NockvmE2E.J8.InstJ8 (truncP P)

/-- the coin field (nock's `KC`, defeq to the verifier's) -/
abbrev KN : Type := Nock.TraceGenExe.KC

/-! ## 1. `aeval` of a truncated reified base gate -/

/-- the coordinate-level point of a valuation `val` over the interface variables, with the chip's column map `e` -/
noncomputable def mkEnvA {w : ℕ} {ι : Type} (e : Fin w → ι) (val : ι × Fin 2 → KN) (cv pv : ℕ → ZMod P) : Env KN where
  trace n := if h : n < w then val (e ⟨n, h⟩, 0) else 0
  traceNext n := if h : n < w then val (e ⟨n, h⟩, 1) else 0
  chal n := algebraMap (ZMod P) KN (cv n)
  pub n := algebraMap (ZMod P) KN (pv n)

theorem aeval_trunc_coeffToMv {w : ℕ} {ι : Type} (e : Fin w → ι) (val : ι × Fin 2 → KN) (cv pv : ℕ → ZMod P)
    (u : CoeffExpr (ZMod P)) :
    MvPolynomial.aeval val (truncP e (coeffToMv (w := w) cv pv u)) = evalA (mkEnvA e val cv pv) u := by
  induction u with
  | const c => simp [coeffToMv, evalA]
  | var kind i =>
    cases kind
    · by_cases hi : i < w
      · simp [coeffToMv, evalA, mkEnvA, InstJ8.truncP, hi]
      · simp [coeffToMv, evalA, mkEnvA, InstJ8.truncP, hi]
    · by_cases hi : i < w
      · simp [coeffToMv, evalA, mkEnvA, InstJ8.truncP, hi]
      · simp [coeffToMv, evalA, mkEnvA, InstJ8.truncP, hi]
    · simp [coeffToMv, evalA, mkEnvA, InstJ8.truncP]
    · simp [coeffToMv, evalA, mkEnvA, InstJ8.truncP]
  | add a b iha ihb => simp only [coeffToMv, map_add, evalA, iha, ihb]
  | sub a b iha ihb => simp only [coeffToMv, map_sub, evalA, iha, ihb]
  | mul a b iha ihb => simp only [coeffToMv, map_mul, evalA, iha, ihb]
  | neg a iha => simp only [coeffToMv, map_neg, evalA, iha]
  | pow a n iha => simp only [coeffToMv, map_pow, evalA, iha]


/-! ## 2. the DAG semantics of a normalized / renamed gate -/

theorem ofGl_eq (c : Gl) : ofGl c = c := by
  unfold ofGl
  exact ZMod.natCast_zmod_val c

theorem evB_const (env : KEnv) (c : Gl) :
    evB env (.const c) = algebraMap (ZMod P) KN c := by
  show algebraMap (ZMod NockvmE2E.Exec.p) KC (ofGl c) = _
  rw [ofGl_eq]; rfl

theorem evM_powN (env : KEnv) (x : MixedExpr Gl) : ∀ n, evM env (powN x n) = evM env x ^ n
  | 0 => by simp [powN, evM]
  | n + 1 => by simp [powN, evM, evM_powN env x n, pow_succ]

theorem evM_norm (env : KEnv) : ∀ E : MixedExpr Gl, evM env (Nock.Emit.norm E) = evM env E
  | .Var k i => rfl
  | .Lift g => rfl
  | .Scale g u => by simp [Nock.Emit.norm, evM, evM_norm env u]
  | .Const c => rfl
  | .Add x y => by simp [Nock.Emit.norm, evM, evM_norm env x, evM_norm env y]
  | .Sub x y => by simp [Nock.Emit.norm, evM, evM_norm env x, evM_norm env y]
  | .Neg x => by simp [Nock.Emit.norm, evM, evM_norm env x]
  | .Mul x y => by simp [Nock.Emit.norm, evM, evM_norm env x, evM_norm env y]
  | .Pow x n => by simp [Nock.Emit.norm, evM, evM_powN, evM_norm env x]

/-! ## 3. leaf conditions and the evaluation tie of one gate -/

/-- the base leaves a gate may read -/
def okB (cB : VarKind → ℕ → Bool) : CoeffExpr Gl → Bool
  | .const _ => true
  | .var k i => cB k i
  | .add a b => okB cB a && okB cB b
  | .sub a b => okB cB a && okB cB b
  | .mul a b => okB cB a && okB cB b
  | .neg a => okB cB a
  | .pow a _ => okB cB a

/-- the leaves a `𝕂`-gate may read (`cK`: `𝕂`-leaves, `cB`: base leaves) -/
def okM (cK cB : VarKind → ℕ → Bool) : MixedExpr Gl → Bool
  | .Var k i => cK k i
  | .Lift g => okB cB g
  | .Scale g u => okB cB g && okM cK cB u
  | .Const _ => true
  | .Add x y => okM cK cB x && okM cK cB y
  | .Sub x y => okM cK cB x && okM cK cB y
  | .Neg x => okM cK cB x
  | .Mul x y => okM cK cB x && okM cK cB y
  | .Pow x _ => okM cK cB x

section Tie
variable (cK cB : VarKind → ℕ → Bool) (eA eK : Env KN) (env : KEnv)
  (hBc : ∀ n, cB .challenge n = false)
  (hBt : ∀ n, cB .traceCur n = true → eA.trace n = env.cur n)
  (hBn : ∀ n, cB .traceNext n = true → eA.traceNext n = env.next n)
  (hBp : ∀ n, cB .publicVal n = true → eA.pub n = algebraMap (ZMod NockvmE2E.Exec.p) KC (env.pub n))

include hBc hBt hBn hBp in
theorem evalA_eq_evB : ∀ g : CoeffExpr Gl, okB cB g = true → evalA eA g = evB env g
  | .const c, _ => (evB_const env c).symm
  | .var .traceCur i, h => hBt i h
  | .var .traceNext i, h => hBn i h
  | .var .challenge i, h => by simp [okB, hBc] at h
  | .var .publicVal i, h => hBp i h
  | .add a b, h => by
    simp only [okB, Bool.and_eq_true] at h
    simp only [evalA, evB, evalA_eq_evB a h.1, evalA_eq_evB b h.2] <;> rfl
  | .sub a b, h => by
    simp only [okB, Bool.and_eq_true] at h
    simp only [evalA, evB, evalA_eq_evB a h.1, evalA_eq_evB b h.2] <;> rfl
  | .mul a b, h => by
    simp only [okB, Bool.and_eq_true] at h
    simp only [evalA, evB, evalA_eq_evB a h.1, evalA_eq_evB b h.2] <;> rfl
  | .neg a, h => by
    simp only [okB] at h
    simp only [evalA, evB, evalA_eq_evB a h] <;> rfl
  | .pow a n, h => by
    simp only [okB] at h
    simp only [evalA, evB, evalA_eq_evB a h] <;> rfl

variable (fc fe fp : ℕ → ℕ)
  (hKt : ∀ i, cK .traceCur i = true → eK.trace i = extK env.cur env.bc (fe i))
  (hKn : ∀ i, cK .traceNext i = true → eK.traceNext i = extK env.next env.bc (fe i))
  (hKc : ∀ i, cK .challenge i = true → eK.chal i = env.chal (fc i))
  (hKp : ∀ i, cK .publicVal i = true → eK.pub i = pubK env (fp i))

include hBc hBt hBn hBp hKt hKn hKc hKp in
/-- **the evaluation tie of one `𝕂`-gate**: the J-8 side (`evalKK`, the unrenamed gate at the coordinate point) is the DAG side
(`evM` of the renamed normal form) -/
theorem evalKK_eq_evM : ∀ E : MixedExpr Gl, okM cK cB E = true →
    evalKK eK eA E = evM env (Nock.Emit.norm (renameM fc fe fp E))
  | .Var .traceCur i, h => by
    rw [evM_norm]; simp only [okM] at h; simp only [renameM, evM, evalKK]; exact hKt i h
  | .Var .traceNext i, h => by
    rw [evM_norm]; simp only [okM] at h; simp only [renameM, evM, evalKK]; exact hKn i h
  | .Var .challenge i, h => by
    rw [evM_norm]; simp only [okM] at h; simp only [renameM, evM, evalKK]; exact hKc i h
  | .Var .publicVal i, h => by
    rw [evM_norm]; simp only [okM] at h; simp only [renameM, evM, evalKK]; exact hKp i h
  | .Lift g, h => by
    rw [evM_norm]; simp only [okM] at h
    simp only [renameM, evM, evalKK]; exact evalA_eq_evB cB eA env hBc hBt hBn hBp g h <;> rfl
  | .Scale g u, h => by
    rw [evM_norm]; simp only [okM, Bool.and_eq_true] at h
    have ih := evalKK_eq_evM u h.2
    rw [evM_norm] at ih
    simp only [renameM, evM, evalKK, ih, evalA_eq_evB cB eA env hBc hBt hBn hBp g h.1] <;> rfl
  | .Const c, h => by
    rw [evM_norm]; simp [renameM, evM, evalKK] <;> rfl
  | .Add x y, h => by
    rw [evM_norm]; simp only [okM, Bool.and_eq_true] at h
    have i1 := evalKK_eq_evM x h.1; have i2 := evalKK_eq_evM y h.2
    rw [evM_norm] at i1 i2
    simp only [renameM, evM, evalKK, i1, i2] <;> rfl
  | .Sub x y, h => by
    rw [evM_norm]; simp only [okM, Bool.and_eq_true] at h
    have i1 := evalKK_eq_evM x h.1; have i2 := evalKK_eq_evM y h.2
    rw [evM_norm] at i1 i2
    simp only [renameM, evM, evalKK, i1, i2] <;> rfl
  | .Neg x, h => by
    rw [evM_norm]; simp only [okM] at h
    have i1 := evalKK_eq_evM x h
    rw [evM_norm] at i1
    simp only [renameM, evM, evalKK, i1] <;> rfl
  | .Mul x y, h => by
    rw [evM_norm]; simp only [okM, Bool.and_eq_true] at h
    have i1 := evalKK_eq_evM x h.1; have i2 := evalKK_eq_evM y h.2
    rw [evM_norm] at i1 i2
    simp only [renameM, evM, evalKK, i1, i2] <;> rfl
  | .Pow x n, h => by
    rw [evM_norm]; simp only [okM] at h
    have i1 := evalKK_eq_evM x h
    rw [evM_norm] at i1
    simp only [renameM, evM, evalKK, i1] <;> rfl

end Tie


/-! ## 4. the coordinate sum of a gate at a valuation -/

open Nock.TraceGenExe (powerBasis3) in
theorem pb3_apply (k : Fin 3) : powerBasis3 k = NockvmE2E.Exec.xr ^ (k : ℕ) := by
  rw [Nock.TraceGenExe.powerBasis3_apply]; rfl

theorem sum_xr (f : ℕ → NockvmE2E.Exec.KC) (bc e : ℕ) :
    ∑ k : Fin 3, NockvmE2E.Exec.xr ^ (k : ℕ) * f (bc + 3 * e + (k : ℕ)) = extK f bc e := by
  simp only [Fin.sum_univ_three, extK, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, Nat.add_zero]
  ring

open Nock.TraceGenExe (powerBasis3) in
theorem sum_pb3 (f : ℕ → KN) (bc e : ℕ) :
    ∑ k : Fin 3, powerBasis3 k * f (bc + 3 * e + (k : ℕ)) = extK f bc e := by
  rw [← sum_xr f bc e]
  exact Finset.sum_congr rfl fun k _ => by rw [pb3_apply]; rfl

open Nock.TraceGenExe (powerBasis3) in
/-- **the coordinate sum of an `okM` gate**: `Σ_k xr^k · (coordinate gate k)(val)` = the DAG value of the gate -/
theorem gate_tie {w : ℕ} {ι : Type} (e : Fin w → ι) (val : ι × Fin 2 → KN) (cv pv : ℕ → ZMod P)
    (col0 : VarKind → ℕ → ℕ) (cK cB : VarKind → ℕ → Bool) (env : KEnv) (fc fe fp : ℕ → ℕ)
    (hcur : ∀ n (hn : n < w), env.cur n = val (e ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < w), env.next n = val (e ⟨n, hn⟩, 1))
    (hBc : ∀ n, cB .challenge n = false)
    (hBt : ∀ n, cB .traceCur n = true → n < w) (hBn : ∀ n, cB .traceNext n = true → n < w)
    (hBp : ∀ n, cB .publicVal n = true → algebraMap (ZMod P) KN (pv n) = algebraMap (ZMod NockvmE2E.Exec.p) KC (env.pub n))
    (hKt : ∀ i, cK .traceCur i = true → col0 .traceCur i = env.bc + 3 * fe i ∧ env.bc + 3 * fe i + 2 < w)
    (hKn : ∀ i, cK .traceNext i = true → col0 .traceNext i = env.bc + 3 * fe i ∧ env.bc + 3 * fe i + 2 < w)
    (hKc : ∀ i, cK .challenge i = true →
      ∑ k : Fin 3, powerBasis3 k * algebraMap (ZMod P) KN (cv (col0 .challenge i + (k : ℕ))) = env.chal (fc i))
    (hKp : ∀ i, cK .publicVal i = true →
      ∑ k : Fin 3, powerBasis3 k * algebraMap (ZMod P) KN (pv (col0 .publicVal i + (k : ℕ))) = pubK env (fp i))
    (E : MixedExpr Gl) (hE : okM cK cB E = true) :
    ∑ k : Fin 3, powerBasis3 k * evalA (mkEnvA e val cv pv) (mixedCompile powerBasis3 col0 E k) =
      evM env (Nock.Emit.norm (renameM fc fe fp E)) := by
  set eA : Env KN := mkEnvA e val cv pv with heA
  let eK : Env KN := ⟨fun i => ∑ k : Fin 3, powerBasis3 k * eA.trace (col0 .traceCur i + (k : ℕ)),
    fun i => ∑ k : Fin 3, powerBasis3 k * eA.traceNext (col0 .traceNext i + (k : ℕ)),
    fun i => ∑ k : Fin 3, powerBasis3 k * eA.chal (col0 .challenge i + (k : ℕ)),
    fun i => ∑ k : Fin 3, powerBasis3 k * eA.pub (col0 .publicVal i + (k : ℕ))⟩
  have hco : IsCoordEnvA powerBasis3 col0 eK eA := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  rw [mixedCompile_evalA powerBasis3 col0 hco E]
  refine evalKK_eq_evM cK cB eA eK env ?_ ?_ ?_ ?_ fc fe fp ?_ ?_ ?_ ?_ E hE
  · exact hBc
  · intro n hn
    have := hBt n hn
    simp only [heA, mkEnvA, dif_pos this]; exact (hcur n this).symm
  · intro n hn
    have := hBn n hn
    simp only [heA, mkEnvA, dif_pos this]; exact (hnext n this).symm
  · intro n hn; exact hBp n hn
  · intro i hi
    obtain ⟨h1, h2⟩ := hKt i hi
    show ∑ k : Fin 3, powerBasis3 k * eA.trace (col0 .traceCur i + (k : ℕ)) = _
    rw [h1]; refine (Eq.trans ?_ (sum_pb3 env.cur env.bc (fe i)))
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : env.bc + 3 * fe i + (k : ℕ) < w := by have := k.2; omega
    simp only [heA, mkEnvA, dif_pos hk]
    rw [hcur _ hk]
  · intro i hi
    obtain ⟨h1, h2⟩ := hKn i hi
    show ∑ k : Fin 3, powerBasis3 k * eA.traceNext (col0 .traceNext i + (k : ℕ)) = _
    rw [h1]; refine (Eq.trans ?_ (sum_pb3 env.next env.bc (fe i)))
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : env.bc + 3 * fe i + (k : ℕ) < w := by have := k.2; omega
    simp only [heA, mkEnvA, dif_pos hk]
    rw [hnext _ hk]
  · intro i hi; exact hKc i hi
  · intro i hi; exact hKp i hi


/-! ## 5. routing: J-8 coordinate gate index  <->  (DAG gate, coordinate) -/

/-- a routing of `N` J-8 coordinate gates onto `nK` DAG gates, `mult ℓ ∈ {1,3}` coordinates each -/
structure Route where
  N : ℕ
  nK : ℕ
  route : ℕ → ℕ × ℕ
  jOf : ℕ → ℕ → ℕ
  mult : ℕ → ℕ
  h1 : ∀ j < N, (route j).1 < nK ∧ (route j).2 < mult (route j).1 ∧ jOf (route j).1 (route j).2 = j
  h2 : ∀ ℓ < nK, ∀ k < mult ℓ, jOf ℓ k < N ∧ route (jOf ℓ k) = (ℓ, k)
  hmult : ∀ ℓ, mult ℓ ≤ 3

/-- **the fiber sum**: the J-8 gates routed to the DAG gate `ℓ`, weighted by their coordinate -/
theorem fiber_sum (R : Route) (g : ℕ → KN) (F : ℕ → KN) (ℓ : ℕ) (hℓ : ℓ < R.nK) :
    ∑ j ∈ (Finset.range R.N).filter (fun j => (R.route j).1 = ℓ), g (R.route j).2 * F j =
      ∑ k ∈ Finset.range (R.mult ℓ), g k * F (R.jOf ℓ k) := by
  refine Finset.sum_nbij' (fun j => (R.route j).2) (fun k => R.jOf ℓ k) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨h1, h2, h3⟩ := R.h1 j hj.1
    rw [hj.2] at h2
    simpa using h2
  · intro k hk
    simp only [Finset.mem_range] at hk
    obtain ⟨h1, h2⟩ := R.h2 ℓ hℓ k hk
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨h1, by rw [h2]⟩
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    have := (R.h1 j hj.1).2.2
    rw [hj.2] at this; exact this
  · intro k hk
    simp only [Finset.mem_range] at hk
    have := (R.h2 ℓ hℓ k hk).2
    simp [this]
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    have := (R.h1 j hj.1).2.2
    rw [hj.2] at this
    rw [this]

/-- the non-compute routing: `nb` base gates, then `nm` `𝕂` gates (three coordinates each) -/
def ncRoute (nb nm : ℕ) : Route where
  N := nb + 3 * nm
  nK := nb + nm
  route l := if l < nb then (l, 0) else (nb + (l - nb) / 3, (l - nb) % 3)
  jOf ℓ k := if ℓ < nb then ℓ else nb + 3 * (ℓ - nb) + k
  mult ℓ := if ℓ < nb then 1 else 3
  h1 := by
    intro j hj
    refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> simp_all <;> omega
  h2 := by
    intro ℓ hℓ k hk
    skip
    refine ⟨?_, ?_⟩
    · split_ifs at hk ⊢ <;> omega
    · split_ifs at hk ⊢ <;> simp_all <;> omega
  hmult ℓ := by split_ifs <;> omega

/-- the compute routing: J-8 order `arith(na) | acc (3·nk1) | eq(ne) | 𝕂 gates (3·nk2)`, DAG order `arith | eq | acc | 𝕂 gates` -/
def cRoute (na ne nk1 nk2 : ℕ) : Route where
  N := na + 3 * nk1 + ne + 3 * nk2
  nK := na + ne + nk1 + nk2
  route l :=
    if l < na then (l, 0)
    else if l < na + 3 * nk1 then (na + ne + (l - na) / 3, (l - na) % 3)
    else if l < na + 3 * nk1 + ne then (na + (l - na - 3 * nk1), 0)
    else (na + ne + nk1 + (l - na - 3 * nk1 - ne) / 3, (l - na - 3 * nk1 - ne) % 3)
  jOf ℓ k :=
    if ℓ < na then ℓ
    else if ℓ < na + ne then ℓ + 3 * nk1
    else if ℓ < na + ne + nk1 then na + 3 * (ℓ - na - ne) + k
    else na + 3 * nk1 + ne + 3 * (ℓ - na - ne - nk1) + k
  mult ℓ := if ℓ < na + ne then 1 else 3
  h1 := by
    intro j hj
    refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> simp_all <;> omega
  h2 := by
    intro ℓ hℓ k hk
    skip
    refine ⟨?_, ?_⟩
    · split_ifs at hk ⊢ <;> omega
    · split_ifs at hk ⊢ <;> simp_all <;> omega
  hmult ℓ := by split_ifs <;> omega


/-! ## 6. the value-level tie of a chip's gate list -/

/-- the value of the `j`-th J-8 coordinate gate (`0` out of range) -/
noncomputable def Aof (ev : CoeffExpr Gl → KN) (L : List (CoeffExpr Gl)) (j : ℕ) : KN :=
  match L[j]? with | some g => ev g | none => 0

/-- the DAG gate values, as a function of the gate index -/
noncomputable def Vof {α : Type} [Zero α] (V : List α) (ℓ : ℕ) : α := V.getD ℓ 0

/-- the power-basis coefficient of coordinate `k` -/
noncomputable def cf (k : ℕ) : KN := NockvmE2E.Exec.xr ^ k

theorem flatMap3_get {α β : Type} (KG : List α) (f : α → Fin 3 → β) :
    ∀ (m : ℕ) (hm : m < KG.length) (k : Fin 3),
      (KG.flatMap (fun E => List.ofFn (f E)))[3 * m + (k : ℕ)]? = some (f KG[m] k) := by
  induction KG with
  | nil => intro m hm; simp at hm
  | cons E rest ih =>
    intro m hm k
    simp only [List.flatMap_cons]
    cases m with
    | zero =>
      have : (List.ofFn (f E)).length = 3 := by simp
      rw [List.getElem?_append_left (by simp)]
      simp
      fin_cases k <;> rfl
    | succ m =>
      have hl : (List.ofFn (f E)).length = 3 := by simp
      rw [List.getElem?_append_right (by rw [hl]; omega)]
      rw [hl]
      have : 3 * (m + 1) + (k : ℕ) - 3 = 3 * m + (k : ℕ) := by omega
      rw [this, ih m (by simpa using hm) k]
      simp

open Nock.TraceGenExe (powerBasis3) in
/-- **the value tie, non-compute chips** (base gates, then `𝕂` gates expanded in coordinates) -/
theorem nc_vals (col0 : VarKind → ℕ → ℕ) (ev : CoeffExpr Gl → KN) (base : List (CoeffExpr Gl)) (KG : List (MixedExpr Gl))
    (vB : CoeffExpr Gl → KN) (vK : MixedExpr Gl → KN)
    (hb : ∀ g ∈ base, ev g = vB g)
    (hk : ∀ E ∈ KG, ∑ k : Fin 3, powerBasis3 k * ev (mixedCompile powerBasis3 col0 E k) = vK E) :
    ∀ ℓ < (ncRoute base.length KG.length).nK,
      ∑ k ∈ Finset.range ((ncRoute base.length KG.length).mult ℓ), cf k *
          Aof ev (base ++ KG.flatMap (fun E => List.ofFn (mixedCompile powerBasis3 col0 E)))
            ((ncRoute base.length KG.length).jOf ℓ k) =
        Vof (base.map vB ++ KG.map vK) ℓ := by
  intro ℓ hℓ
  simp only [ncRoute] at hℓ ⊢
  by_cases h : ℓ < base.length
  · simp only [h, if_true, Finset.sum_range_one]
    have : (base ++ KG.flatMap (fun E => List.ofFn (mixedCompile powerBasis3 col0 E)))[ℓ]? = some base[ℓ] := by
      rw [List.getElem?_append_left h]; simp
    simp only [Aof, this, cf, pow_zero, one_mul, Vof]
    rw [hb _ (List.getElem_mem h)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
    rw [List.getElem?_map, List.getElem?_eq_getElem h]
    exact (one_mul (vB base[ℓ]) : _)
  · simp only [h, if_false]
    have hm : ℓ - base.length < KG.length := by omega
    have hA : ∀ k : Fin 3, (base ++ KG.flatMap (fun E => List.ofFn (mixedCompile powerBasis3 col0 E)))[base.length + 3 * (ℓ - base.length) + (k : ℕ)]? =
        some (mixedCompile powerBasis3 col0 KG[ℓ - base.length] k) := by
      intro k
      rw [List.getElem?_append_right (by omega)]
      have : base.length + 3 * (ℓ - base.length) + (k : ℕ) - base.length = 3 * (ℓ - base.length) + (k : ℕ) := by omega
      rw [this]
      exact flatMap3_get KG (fun E k => mixedCompile powerBasis3 col0 E k) _ hm k
    rw [Finset.sum_range (fun k => cf k * Aof ev _ (base.length + 3 * (ℓ - base.length) + k))]
    have : ∀ k : Fin 3, cf (k : ℕ) * Aof ev (base ++ KG.flatMap (fun E => List.ofFn (mixedCompile powerBasis3 col0 E)))
        (base.length + 3 * (ℓ - base.length) + (k : ℕ)) =
        powerBasis3 k * ev (mixedCompile powerBasis3 col0 KG[ℓ - base.length] k) := by
      intro k
      simp only [Aof, hA k, cf]
      rw [pb3_apply]
    rw [Finset.sum_congr rfl (fun k _ => this k), hk _ (List.getElem_mem hm)]
    simp only [Vof]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map]
    rw [List.getElem?_map, List.getElem?_eq_getElem hm]
    rfl


/-- the coordinate expansion of a list of `𝕂` gates -/
noncomputable def Kflat (col0 : VarKind → ℕ → ℕ) (KG : List (MixedExpr Gl)) : List (CoeffExpr Gl) :=
  KG.flatMap (fun E => List.ofFn (mixedCompile Nock.TraceGenExe.powerBasis3 col0 E))

theorem Kflat_length (col0 : VarKind → ℕ → ℕ) (KG : List (MixedExpr Gl)) : (Kflat col0 KG).length = 3 * KG.length := by
  induction KG with
  | nil => simp [Kflat]
  | cons E rest ih => simp only [Kflat, List.flatMap_cons, List.length_append, List.length_ofFn, List.length_cons] at ih ⊢; omega

theorem Kflat_get (col0 : VarKind → ℕ → ℕ) (KG : List (MixedExpr Gl)) (m : ℕ) (hm : m < KG.length) (k : Fin 3) :
    (Kflat col0 KG)[3 * m + (k : ℕ)]? = some (mixedCompile Nock.TraceGenExe.powerBasis3 col0 KG[m] k) :=
  flatMap3_get KG (fun E k => mixedCompile Nock.TraceGenExe.powerBasis3 col0 E k) m hm k

theorem Aof_congr {ev : CoeffExpr Gl → KN} {L L' : List (CoeffExpr Gl)} (h : L.map ev = L'.map ev) (j : ℕ) :
    Aof ev L j = Aof ev L' j := by
  have h1 : (L.map ev)[j]? = (L'.map ev)[j]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map] at h1
  unfold Aof
  cases hL : L[j]? <;> cases hL' : L'[j]? <;> simp_all

theorem app4_get {α : Type} (l1 l2 l3 l4 : List α) (i : ℕ) :
    (l1 ++ l2 ++ l3 ++ l4)[i]? =
      if i < l1.length then l1[i]? else if i < l1.length + l2.length then l2[i - l1.length]?
      else if i < l1.length + l2.length + l3.length then l3[i - l1.length - l2.length]?
      else l4[i - l1.length - l2.length - l3.length]? := by
  simp only [List.getElem?_append, List.length_append]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

open Nock.TraceGenExe (powerBasis3) in
/-- **the value tie, the compute chip**: J-8 order `arith | acc54 | eq | 𝕂 gates`, DAG order `arith | eq | acc18 | 𝕂 gates` -/
theorem c_vals (col0 : VarKind → ℕ → ℕ) (ev : CoeffExpr Gl → KN) (base1 eq acc : List (CoeffExpr Gl))
    (KG1 KG2 : List (MixedExpr Gl)) (vB : CoeffExpr Gl → KN) (vK : MixedExpr Gl → KN)
    (hb : ∀ g ∈ base1 ++ eq, ev g = vB g)
    (hk : ∀ E ∈ KG1 ++ KG2, ∑ k : Fin 3, powerBasis3 k * ev (mixedCompile powerBasis3 col0 E k) = vK E)
    (hacc : acc.map ev = (Kflat col0 KG1).map ev) :
    ∀ ℓ < (cRoute base1.length eq.length KG1.length KG2.length).nK,
      ∑ k ∈ Finset.range ((cRoute base1.length eq.length KG1.length KG2.length).mult ℓ), cf k *
          Aof ev (base1 ++ acc ++ eq ++ Kflat col0 KG2) ((cRoute base1.length eq.length KG1.length KG2.length).jOf ℓ k) =
        Vof (base1.map vB ++ eq.map vB ++ KG1.map vK ++ KG2.map vK) ℓ := by
  intro ℓ hℓ
  have hmap : (base1 ++ acc ++ eq ++ Kflat col0 KG2).map ev =
      (base1 ++ Kflat col0 KG1 ++ eq ++ Kflat col0 KG2).map ev := by
    simp only [List.map_append, hacc]
  simp only [Aof_congr hmap]
  have hk1 := Kflat_length col0 KG1
  have hk2 := Kflat_length col0 KG2
  simp only [cRoute] at hℓ ⊢
  -- the J-8 gate at index `j` and the DAG value at index `i`
  have hGL : ∀ j, (base1 ++ Kflat col0 KG1 ++ eq ++ Kflat col0 KG2)[j]? =
      if j < base1.length then base1[j]? else if j < base1.length + 3 * KG1.length then (Kflat col0 KG1)[j - base1.length]?
      else if j < base1.length + 3 * KG1.length + eq.length then eq[j - base1.length - 3 * KG1.length]?
      else (Kflat col0 KG2)[j - base1.length - 3 * KG1.length - eq.length]? := by
    intro j; rw [app4_get]; simp only [hk1]
  have hGV : ∀ i, Vof (base1.map vB ++ eq.map vB ++ KG1.map vK ++ KG2.map vK) i =
      (if i < base1.length then (base1.map vB)[i]? else if i < base1.length + eq.length then (eq.map vB)[i - base1.length]?
      else if i < base1.length + eq.length + KG1.length then (KG1.map vK)[i - base1.length - eq.length]?
      else (KG2.map vK)[i - base1.length - eq.length - KG1.length]?).getD 0 := by
    intro i
    simp only [Vof, List.getD_eq_getElem?_getD]
    rw [app4_get]; simp only [List.length_map]
  rw [hGV]
  by_cases h1 : ℓ < base1.length
  · simp only [h1, if_true, show ℓ < base1.length + eq.length by omega, Finset.sum_range_one, Aof, hGL, cf, pow_zero]
    rw [List.getElem?_map, List.getElem?_eq_getElem h1]
    simp only [Option.map_some, Option.getD_some]
    rw [hb _ (List.mem_append_left _ (List.getElem_mem h1))]
    exact (one_mul (vB base1[ℓ]) : _)
  by_cases h2 : ℓ < base1.length + eq.length
  · simp only [h1, h2, if_true, if_false, Finset.sum_range_one, Aof, hGL, cf, pow_zero]
    have hi : ℓ - base1.length < eq.length := by omega
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [show ℓ + 3 * KG1.length - base1.length - 3 * KG1.length = ℓ - base1.length by omega]
    rw [List.getElem?_map, List.getElem?_eq_getElem hi]
    simp only [Option.map_some, Option.getD_some]
    rw [hb _ (List.mem_append_right _ (List.getElem_mem hi))]
    exact (one_mul (vB eq[ℓ - base1.length]) : _)
  by_cases h3 : ℓ < base1.length + eq.length + KG1.length
  · simp only [h1, h2, h3, if_true, if_false]
    have hm : ℓ - base1.length - eq.length < KG1.length := by omega
    rw [Finset.sum_range (fun k => cf k * Aof ev _ (base1.length + 3 * (ℓ - base1.length - eq.length) + k))]
    have : ∀ k : Fin 3, cf (k : ℕ) * Aof ev (base1 ++ Kflat col0 KG1 ++ eq ++ Kflat col0 KG2)
        (base1.length + 3 * (ℓ - base1.length - eq.length) + (k : ℕ)) =
        powerBasis3 k * ev (mixedCompile powerBasis3 col0 KG1[ℓ - base1.length - eq.length] k) := by
      intro k
      have hk3 := k.2
      simp only [Aof, hGL]
      rw [if_neg (by omega), if_pos (by omega)]
      rw [show base1.length + 3 * (ℓ - base1.length - eq.length) + (k : ℕ) - base1.length =
        3 * (ℓ - base1.length - eq.length) + (k : ℕ) by omega, Kflat_get col0 KG1 _ hm k]
      simp only [cf]; rw [pb3_apply]
    rw [Finset.sum_congr rfl (fun k _ => this k), hk _ (List.mem_append_left _ (List.getElem_mem hm))]
    rw [List.getElem?_map, List.getElem?_eq_getElem hm]
    rfl
  · simp only [h1, h2, h3, if_false]
    have hm : ℓ - base1.length - eq.length - KG1.length < KG2.length := by omega
    rw [Finset.sum_range (fun k => cf k * Aof ev _
      (base1.length + 3 * KG1.length + eq.length + 3 * (ℓ - base1.length - eq.length - KG1.length) + k))]
    have : ∀ k : Fin 3, cf (k : ℕ) * Aof ev (base1 ++ Kflat col0 KG1 ++ eq ++ Kflat col0 KG2)
        (base1.length + 3 * KG1.length + eq.length + 3 * (ℓ - base1.length - eq.length - KG1.length) + (k : ℕ)) =
        powerBasis3 k * ev (mixedCompile powerBasis3 col0 KG2[ℓ - base1.length - eq.length - KG1.length] k) := by
      intro k
      have hk3 := k.2
      simp only [Aof, hGL]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [show base1.length + 3 * KG1.length + eq.length + 3 * (ℓ - base1.length - eq.length - KG1.length) + (k : ℕ)
          - base1.length - 3 * KG1.length - eq.length = 3 * (ℓ - base1.length - eq.length - KG1.length) + (k : ℕ) by omega,
        Kflat_get col0 KG2 _ hm k]
      simp only [cf]; rw [pb3_apply]
    rw [Finset.sum_congr rfl (fun k _ => this k), hk _ (List.mem_append_right _ (List.getElem_mem hm))]
    rw [List.getElem?_map, List.getElem?_eq_getElem hm]
    rfl


/-! ## 7. one chip: the J-8 expansion of a template against the DAG semantics -/

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (slotVal)
open Nock.TraceGenExe (powerBasis3)

theorem sum_slotVal (off : ℕ) (v : ℕ → KN) (i : ℕ) :
    ∑ k : Fin 3, powerBasis3 k * algebraMap (ZMod P) KN (slotVal powerBasis3 off v (off + 3 * i + (k : ℕ))) = v i := by
  have h := sum_coord_mul powerBasis3 (v i)
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : off ≤ off + 3 * i + (k : ℕ) := by omega
  have h2 : (off + 3 * i + (k : ℕ) - off) / 3 = i := by have := k.2; omega
  have h3 : (off + 3 * i + (k : ℕ) - off) % 3 = (k : ℕ) := by have := k.2; omega
  simp only [slotVal, h1, if_true, h2]
  rw [mul_comm]
  congr 3
  exact Fin.ext h3

/-- the chip value list of a template (base gates, then the renamed normalized `𝕂` gates) -/
noncomputable def tplVals (env : KEnv) (fc fe fp : ℕ → ℕ) (base : List (CoeffExpr Gl)) (KG : List (MixedExpr Gl)) :
    List NockvmE2E.Exec.KC :=
  base.map (evB env) ++ KG.map (fun E => evM env (Nock.Emit.norm (renameM fc fe fp E)))

theorem allGates_empty (T : ChipTemplate Gl) (hext : T.extTransition = []) (hd1 : T.extDeg1 = []) (hd3 : T.extDeg3 = [])
    (heq : T.equalityChecks = []) :
    T.allGates powerBasis3 = T.baseTransition ++ Kflat (T.col0 3) T.mixedTransition := by
  simp only [ChipTemplate.allGates, ChipTemplate.transitionGates, ChipTemplate.deg1Gates, ChipTemplate.deg3Gates,
    ChipTemplate.equalityGates, hext, hd1, hd3, heq, expandList, List.flatMap_nil, List.append_nil,
    mixedExpandList, Kflat, mixedCoordVec, List.ofFn_eq_map]
  rfl


/-- **the chip tie (non-compute families)**: for a template with only base and mixed gates, the J-8 coordinate gates at
the valuation `val` are the DAG values of the renamed gates -/
theorem nc_chip_tie (T : ChipTemplate Gl) (hext : T.extTransition = []) (hd1 : T.extDeg1 = []) (hd3 : T.extDeg3 = [])
    (heq : T.equalityChecks = []) {w : ℕ} {ι : Type} (e : Fin w → ι) (val : ι × Fin 2 → KN) (chals pubs : ℕ → KN)
    (cK cB : VarKind → ℕ → Bool) (fc : ℕ → ℕ) (env : KEnv) (len : ℕ)
    (hbc : env.bc = T.baseCols)
    (hcur : ∀ n (hn : n < w), env.cur n = val (e ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < w), env.next n = val (e ⟨n, hn⟩, 1))
    (hBc : ∀ n, cB .challenge n = false)
    (hBt : ∀ n, cB .traceCur n = true → n < w) (hBn : ∀ n, cB .traceNext n = true → n < w)
    (hBp : ∀ n, cB .publicVal n = false)
    (hKt : ∀ i, cK .traceCur i = true → T.baseCols + 3 * i + 2 < w)
    (hKn : ∀ i, cK .traceNext i = true → T.baseCols + 3 * i + 2 < w)
    (hKc : ∀ i, cK .challenge i = true → chals i = env.chal (fc i))
    (hKp : ∀ i, cK .publicVal i = true → pubs i = pubK env i)
    (okbase : ∀ g ∈ T.baseTransition, okB cB g = true) (okmix : ∀ E ∈ T.mixedTransition, okM cK cB E = true) :
    ∀ ℓ < (ncRoute T.baseTransition.length T.mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute T.baseTransition.length T.mixedTransition.length).mult ℓ), cf k *
          Aof (evalA (mkEnvA e val (slotVal powerBasis3 T.baseCols chals) (slotVal powerBasis3 T.baseCols pubs)))
            (T.allGates powerBasis3) ((ncRoute T.baseTransition.length T.mixedTransition.length).jOf ℓ k) =
        Vof (tplVals env fc id id T.baseTransition T.mixedTransition) ℓ := by
  rw [allGates_empty T hext hd1 hd3 heq]
  refine nc_vals (T.col0 3) _ T.baseTransition T.mixedTransition (evB env)
    (fun E => evM env (Nock.Emit.norm (renameM fc id id E))) ?_ ?_
  · intro g hg
    exact evalA_eq_evB cB _ env hBc
      (fun n hn => by have := hBt n hn; simp only [mkEnvA, dite_cond_eq_true (eq_true this)]; exact (hcur n this).symm)
      (fun n hn => by have := hBn n hn; simp only [mkEnvA, dite_cond_eq_true (eq_true this)]; exact (hnext n this).symm)
      (fun n hn => by simp [hBp n] at hn) g (okbase g hg)
  · intro E hE
    refine gate_tie e val (slotVal powerBasis3 T.baseCols chals) (slotVal powerBasis3 T.baseCols pubs) (T.col0 3) cK cB env fc id id
      hcur hnext hBc hBt hBn (fun n hn => by simp [hBp n] at hn) ?_ ?_ ?_ ?_ E (okmix E hE)
    · intro i hi; refine ⟨by simp [ChipTemplate.col0, hbc], by simp [hbc]; exact hKt i hi⟩
    · intro i hi; refine ⟨by simp [ChipTemplate.col0, hbc], by simp [hbc]; exact hKn i hi⟩
    · intro i hi
      have := sum_slotVal T.baseCols chals i
      simp only [ChipTemplate.col0]
      rw [this]; exact hKc i hi
    · intro i hi
      have := sum_slotVal T.baseCols pubs i
      simp only [ChipTemplate.col0]
      rw [this]; exact hKp i hi


/-- **the chip tie (compute family)**: generic over the gate lists, the column convention and the leaf maps -/
theorem c_chip_tie (col0 : VarKind → ℕ → ℕ) {w : ℕ} {ι : Type} (e : Fin w → ι) (val : ι × Fin 2 → KN) (cv pv : ℕ → ZMod P)
    (cK cB : VarKind → ℕ → Bool) (fc fe fp : ℕ → ℕ) (env : KEnv)
    (base1 eq acc : List (CoeffExpr Gl)) (KG1 KG2 : List (MixedExpr Gl))
    (hcur : ∀ n (hn : n < w), env.cur n = val (e ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < w), env.next n = val (e ⟨n, hn⟩, 1))
    (hBc : ∀ n, cB .challenge n = false)
    (hBt : ∀ n, cB .traceCur n = true → n < w) (hBn : ∀ n, cB .traceNext n = true → n < w)
    (hBp : ∀ n, cB .publicVal n = true → algebraMap (ZMod P) KN (pv n) = algebraMap (ZMod NockvmE2E.Exec.p) KC (env.pub n))
    (hKt : ∀ i, cK .traceCur i = true → col0 .traceCur i = env.bc + 3 * fe i ∧ env.bc + 3 * fe i + 2 < w)
    (hKn : ∀ i, cK .traceNext i = true → col0 .traceNext i = env.bc + 3 * fe i ∧ env.bc + 3 * fe i + 2 < w)
    (hKc : ∀ i, cK .challenge i = true →
      ∑ k : Fin 3, powerBasis3 k * algebraMap (ZMod P) KN (cv (col0 .challenge i + (k : ℕ))) = env.chal (fc i))
    (hKp : ∀ i, cK .publicVal i = true →
      ∑ k : Fin 3, powerBasis3 k * algebraMap (ZMod P) KN (pv (col0 .publicVal i + (k : ℕ))) = pubK env (fp i))
    (okbase : ∀ g ∈ base1 ++ eq, okB cB g = true) (okmix : ∀ E ∈ KG1 ++ KG2, okM cK cB E = true)
    (hacc : acc.map (evalA (mkEnvA e val cv pv)) = (Kflat col0 KG1).map (evalA (mkEnvA e val cv pv))) :
    ∀ ℓ < (cRoute base1.length eq.length KG1.length KG2.length).nK,
      ∑ k ∈ Finset.range ((cRoute base1.length eq.length KG1.length KG2.length).mult ℓ), cf k *
          Aof (evalA (mkEnvA e val cv pv)) (base1 ++ acc ++ eq ++ Kflat col0 KG2)
            ((cRoute base1.length eq.length KG1.length KG2.length).jOf ℓ k) =
        Vof (base1.map (evB env) ++ eq.map (evB env) ++
          KG1.map (fun E => evM env (Nock.Emit.norm (renameM fc fe fp E))) ++
          KG2.map (fun E => evM env (Nock.Emit.norm (renameM fc fe fp E)))) ℓ := by
  refine c_vals col0 _ base1 eq acc KG1 KG2 (evB env) (fun E => evM env (Nock.Emit.norm (renameM fc fe fp E))) ?_ ?_ hacc
  · intro g hg
    exact evalA_eq_evB cB _ env hBc
      (fun n hn => by have := hBt n hn; simp only [mkEnvA, dite_cond_eq_true (eq_true this)]; exact (hcur n this).symm)
      (fun n hn => by have := hBn n hn; simp only [mkEnvA, dite_cond_eq_true (eq_true this)]; exact (hnext n this).symm)
      (fun n hn => hBp n hn) g (okbase g hg)
  · intro E hE
    exact gate_tie e val cv pv col0 cK cB env fc fe fp hcur hnext hBc hBt hBn hBp hKt hKn hKc hKp E (okmix E hE)


/-! ## 8. the leaf conditions of the six chips (kernel checks on the template gate lists) -/


/-- memory-family `𝕂`-leaves: columns `bc + 3 i .. + 2 < w`, publics `i < len`, challenge leaves `chalOk` -/
def cKmem (bc w len : ℕ) (chalOk : ℕ → Bool) : VarKind → ℕ → Bool
  | .traceCur, i => decide (bc + 3 * i + 2 < w)
  | .traceNext, i => decide (bc + 3 * i + 2 < w)
  | .challenge, i => chalOk i
  | .publicVal, i => decide (i < len)

/-- base leaves of a chip of width `w`: trace columns only -/
def cBmem (w : ℕ) : VarKind → ℕ → Bool
  | .traceCur, n => decide (n < w)
  | .traceNext, n => decide (n < w)
  | _, _ => false

def chalM : ℕ → Bool := fun i => decide (i ≤ 36)
def chalA : ℕ → Bool := fun i => decide (i ≤ 38)
def chalV : ℕ → Bool := fun i => decide (i ≤ 36 ∧ i ≠ 2 ∧ i ≠ 3)
def chalJ : ℕ → Bool := fun i => decide (i < 8)

/-- compute-family `𝕂`-leaves (flat `col0Id` convention) -/
def cKc : VarKind → ℕ → Bool
  | .traceCur, r => decide (69 ≤ r ∧ (r - 69) % 3 = 0 ∧ r + 2 < 123)
  | .traceNext, r => decide (69 ≤ r ∧ (r - 69) % 3 = 0 ∧ r + 2 < 123)
  | .challenge, r => decide (r % 3 = 0 ∧ r < 18)
  | .publicVal, r => decide (r % 3 = 0 ∧ r + 2 < 33)

def cBc : VarKind → ℕ → Bool
  | .traceCur, n => decide (n < 123)
  | .traceNext, n => decide (n < 123)
  | .publicVal, n => decide (n < 33)
  | .challenge, _ => false

/-- the check of one memory-family template -/
def chkT (T : ChipTemplate Gl) (len : ℕ) (chalOk : ℕ → Bool) : Bool :=
  T.baseTransition.all (okB (cBmem (T.width 3))) &&
    T.mixedTransition.all (okM (cKmem T.baseCols (T.width 3) len chalOk) (cBmem (T.width 3)))

theorem chk_cell : chkT Nock.Emit.cellKWTemplate 6 chalM = true := by decide +kernel
theorem chk_atom : chkT Nock.Emit.atomTemplate 12 chalA = true := by decide +kernel
theorem chk_jet : chkT Nock.Emit.jetTemplate 4 chalJ = true := by decide +kernel
theorem chk_walkJ8 : ∀ k ∈ [1, 9, 25, 42, 48, 174],
    chkT (Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8.walkTemplateJ8 Nock.Emit.δ k) 8 chalM = true := by decide +kernel
theorem chk_walkV : ∀ k ∈ [1, 2],
    chkT (Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK.walkTemplateHQK Nock.Emit.δ k) 8 chalV = true := by decide +kernel

theorem chk_compute :
    (Nock.Emit.computeSpec0.base.all (okB cBc) && Nock.Emit.computeSpec0.mixed.all (okM cKc cBc)) = true := by decide +kernel


/-! ## 9. the J-8 challenge vectors against the slot maps of `TieLeaf` -/

open NockvmE2E.J8.InstJ8 (Φ0)
open Nock.TraceGenExe (deltaF)
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.T0Tower

/-- the coins as a function on `ℕ` (`0` outside the frame) -/
noncomputable def χf (χ : NockvmE2E.Rap.Coins Φ0 KN) (i : ℕ) : KN := if h : i < 19 then χ ⟨i, h⟩ else 0

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (chalsVCL) in
theorem chalsM_eq (χ : NockvmE2E.Rap.Coins Φ0 KN) (j : ℕ) (hj : j ≤ 36) : chalsMJ8 deltaF χ j = memVec (χf χ) j := by
  unfold chalsMJ8 memVec
  simp only [FrameVSQ.chalsVSQ, FrameVS.chalsVS, chalsVCL]
  have hG : CellH.hGam = 33 := rfl
  have hR : CellH.hRho = 34 := rfl
  simp only [hG, hR]
  by_cases h35 : j = 35
  · subst h35; simp [toVSQ, χf, FrameVSQ.cGamHi]; rfl
  by_cases h36 : j = 36
  · subst h36; simp [toVSQ, χf, FrameVSQ.cRhoHi]; rfl
  by_cases h33 : j = 33
  · subst h33; simp [toVSQ, χf, FrameVSQ.toVS, FrameVS.cGamH]; rfl
  by_cases h34 : j = 34
  · subst h34; simp [toVSQ, χf, FrameVSQ.toVS, FrameVS.cRhoH]; rfl
  simp only [h35, h36, h33, h34, if_false]
  by_cases h11 : j < 11
  · simp only [h11, dif_pos, if_true]
    simp [toVSQ, χf, FrameVSQ.toVS, FrameVS.toVCL, h11, show j < 19 by omega]; rfl
  · simp only [h11, dif_neg, if_false, not_false_eq_true]
    have h4 : (FrameVS.toVCL (FrameVSQ.toVS (toVSQ χ)) : Fin 11 → KN) (4 : Fin 11) = χf χ 4 := rfl
    have h6 : (FrameVS.toVCL (FrameVSQ.toVS (toVSQ χ)) : Fin 11 → KN) (6 : Fin 11) = χf χ 6 := rfl
    have h7 : algebraMap (ZMod Nock.Field.p) KN deltaF = 7 := by
      have : deltaF = (7 : ZMod Nock.Field.p) := rfl
      rw [this]; exact map_ofNat _ 7
    have key : ∀ (d : KN) (hd : d = 7) (re im : KN) (n : ℕ), Quad.mk d re im ^ n =
        Quad.mk d (NockvmE2E.Exec.DagSemV.qpow re im n).1 (NockvmE2E.Exec.DagSemV.qpow re im n).2 := by
      intro d hd re im n; subst hd; exact NockvmE2E.Emit.qpow_mk re im n
    rw [h4, h6, key _ h7 _ _ ((j - 11) / 2), key _ h7 _ _ ((j - 12) / 2)]
    simp only [↓reduceIte]
    split_ifs with hp
    · exact Quad.re_mk (algebraMap (ZMod Nock.Field.p) KN deltaF) _ _
    · exact Quad.im_mk (algebraMap (ZMod Nock.Field.p) KN deltaF) _ _


open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c2 c3)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)

theorem chalsA_eq (χ : NockvmE2E.Rap.Coins Φ0 KN) (j : ℕ) (hj : j ≤ 38) : chalsAJ8Z deltaF χ j = atomVec (χf χ) j := by
  unfold chalsAJ8Z chalsAJ8 atomVec
  by_cases h37 : j = 37
  · subst h37; simp [χf, c2]; rfl
  by_cases h38 : j = 38
  · subst h38; simp [χf, c3]; rfl
  by_cases h2 : j = 2
  · subst h2; simp [χf, FrameJ8.cY1]; rfl
  by_cases h3 : j = 3
  · subst h3; simp [χf, FrameJ8.cY2]; rfl
  simp only [h37, h38, h2, h3, if_false]
  exact chalsM_eq χ j (by omega)

theorem chalsV_eq (χ : NockvmE2E.Rap.Coins Φ0 KN) (j : ℕ) (hj : j ≤ 36) (h2 : j ≠ 2) (h3 : j ≠ 3) :
    chalsAJ8Z deltaF χ j = memVec (χf χ) j := by
  unfold chalsAJ8Z chalsAJ8
  simp only [show j ≠ 37 by omega, show j ≠ 38 by omega, h2, h3, if_false]
  exact chalsM_eq χ j hj

theorem chalsJ_eq (χ : NockvmE2E.Rap.Coins Φ0 KN) (j : ℕ) (hj : j < 8) : chalsJJ8 χ j = jetVec (χf χ) j := by
  unfold chalsJJ8 jetVec
  simp only [hj, if_true]
  have : j % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases hm : j % 4 <;> simp [hm, toVSQ, χf, FrameVSQ.cGamHi, FrameVSQ.cRhoHi] <;> rfl


open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ (coinHQ chalVHQ) in
theorem coinHQ_eq (χ : NockvmE2E.Rap.Coins Φ0 KN) (q : ℕ) (hq : q < 6) :
    coinHQ (toVSQ χ) q = χf χ ([11, 12, 13, 14, 15, 16].getD q 0) := by
  unfold coinHQ
  by_cases h4 : q < 4
  · simp only [h4, if_true, FrameVS.coinH]
    interval_cases q <;> simp [toVSQ, χf, FrameVSQ.toVS, FrameVS.cGamH, FrameVS.cRhoH, FrameVS.cAlphaW, FrameVS.cGamW] <;> rfl
  · by_cases h5 : q = 4
    · subst h5; simp [toVSQ, χf, FrameVSQ.cGamHi]; rfl
    · have : q = 5 := by omega
      subst this; simp [toVSQ, χf, FrameVSQ.cRhoHi]; rfl

open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ (coinHQ chalVHQ) in
theorem comp_chal (χ : NockvmE2E.Rap.Coins Φ0 KN) (E : ℕ → KN) (hE : SlotOK E (χf χ)) (r : ℕ) (hr3 : r % 3 = 0)
    (hr : r < 18) :
    ∑ k : Fin 3, powerBasis3 k * algebraMap (ZMod P) KN (chalVJ8 powerBasis3 χ (r + (k : ℕ))) = E (fX r) := by
  rw [fX_leaf hE r hr]
  have hq : r / 3 < 6 := by omega
  rw [← coinHQ_eq χ (r / 3) hq]
  rw [← sum_coord_mul powerBasis3 (coinHQ (toVSQ χ) (r / 3))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := k.2
  have h18 : r + (k : ℕ) < 18 := by omega
  have h1 : (r + (k : ℕ)) / 3 = r / 3 := by omega
  have h2 : (r + (k : ℕ)) % 3 = (k : ℕ) := by omega
  simp only [chalVJ8, chalVHQ, h18, if_true, h1]
  rw [mul_comm]
  congr 3
  exact Fin.ext h2


/-! ## 10. the J-8 constraints of the six tables as `Aof` of the template gate lists -/

open NockvmE2E.J8.InstJ8 (Datum DatumOK Msg consT sz Ι)

/-- the `j`-th constraint of table `t` as a function of the valuation (`0` out of range) -/
noncomputable def consAt (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (t : Fin 6) (val : Ι × Fin 2 → KN) (j : ℕ) : KN :=
  if h : j < InstJ8.sz d t then MvPolynomial.aeval val (InstJ8.consT d χ M t ⟨j, h⟩) else 0

/-- the column map of the cell table into the interface columns -/
def eCell (j : Fin (Nock.Emit.cellKWTemplate.width 3)) : Ι := Sum.inr (Sum.inl (Fin.cast (by decide) j))

theorem consAt_cell (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (j : ℕ) :
    consAt d χ M 1 val j = Aof (evalA (mkEnvA eCell val (slotVal powerBasis3 134 (chalsMJ8 deltaF χ))
      (slotVal powerBasis3 134 M.1.pubsC))) (Nock.Emit.cellKWTemplate.allGates powerBasis3) j := by
  unfold consAt Aof
  by_cases h : j < InstJ8.sz d 1
  · have h' : j < (Nock.Emit.cellKWTemplate.allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ ((Nock.Emit.cellKWTemplate.allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv eCell val _ _ _
  · have h' : ¬ j < (Nock.Emit.cellKWTemplate.allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]



abbrev tWalkJ8 (k : ℕ) : ChipTemplate Gl := WalkJ8.walkTemplateJ8 Nock.Emit.δ k
abbrev tWalkV (k : ℕ) : ChipTemplate Gl := CellTwinK.walkTemplateHQK Nock.Emit.δ k

def eWalk (k : ℕ) (j : Fin ((tWalkJ8 k).width 3)) : Ι := Sum.inr (Sum.inr (Sum.inl (Fin.cast rfl j)))
def eJet (j : Fin (Nock.Emit.jetTemplate.width 3)) : Ι := Sum.inr (Sum.inr (Sum.inr (Sum.inl (Fin.cast (by decide) j))))
def eAtom (j : Fin (Nock.Emit.atomTemplate.width 3)) : Ι := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Fin.cast (by decide) j)))))
def eWalkV (k : ℕ) (j : Fin ((tWalkV k).width 3)) : Ι := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Fin.cast rfl j)))))

theorem consAt_walk (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (j : ℕ) :
    consAt d χ M 2 val j = Aof (evalA (mkEnvA (eWalk d.Pb.kroots) val (slotVal powerBasis3 25 (chalsMJ8 deltaF χ))
      (slotVal powerBasis3 25 M.1.pubsW))) ((tWalkJ8 d.Pb.kroots).allGates powerBasis3) j := by
  unfold consAt Aof
  by_cases h : j < InstJ8.sz d 2
  · have h' : j < ((tWalkJ8 d.Pb.kroots).allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ (((tWalkJ8 d.Pb.kroots).allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv (eWalk d.Pb.kroots) val _ _ _
  · have h' : ¬ j < ((tWalkJ8 d.Pb.kroots).allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]

theorem consAt_jet (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (j : ℕ) :
    consAt d χ M 3 val j = Aof (evalA (mkEnvA eJet val (slotVal powerBasis3 29 (chalsJJ8 χ))
      (slotVal powerBasis3 29 M.1.pubsJ))) (Nock.Emit.jetTemplate.allGates powerBasis3) j := by
  unfold consAt Aof
  by_cases h : j < InstJ8.sz d 3
  · have h' : j < (Nock.Emit.jetTemplate.allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ ((Nock.Emit.jetTemplate.allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv eJet val _ _ _
  · have h' : ¬ j < (Nock.Emit.jetTemplate.allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]

theorem consAt_atom (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (j : ℕ) :
    consAt d χ M 4 val j = Aof (evalA (mkEnvA eAtom val (slotVal powerBasis3 205 (chalsAJ8Z deltaF χ))
      (slotVal powerBasis3 205 M.1.pubsA))) (Nock.Emit.atomTemplate.allGates powerBasis3) j := by
  unfold consAt Aof
  by_cases h : j < InstJ8.sz d 4
  · have h' : j < (Nock.Emit.atomTemplate.allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ ((Nock.Emit.atomTemplate.allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv eAtom val _ _ _
  · have h' : ¬ j < (Nock.Emit.atomTemplate.allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]

theorem consAt_walkV (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (j : ℕ) :
    consAt d χ M 5 val j = Aof (evalA (mkEnvA (eWalkV d.Pb.krootsV) val (slotVal powerBasis3 25 (chalsAJ8Z deltaF χ))
      (slotVal powerBasis3 25 M.1.pubsV))) ((tWalkV d.Pb.krootsV).allGates powerBasis3) j := by
  unfold consAt Aof
  by_cases h : j < InstJ8.sz d 5
  · have h' : j < ((tWalkV d.Pb.krootsV).allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ (((tWalkV d.Pb.krootsV).allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv (eWalkV d.Pb.krootsV) val _ _ _
  · have h' : ¬ j < ((tWalkV d.Pb.krootsV).allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]


def eComp (j : Fin 123) : Ι := Sum.inl j

theorem consAt_comp (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (j : ℕ) :
    consAt d χ M 0 val j = Aof (evalA (mkEnvA eComp val (chalVJ8 powerBasis3 χ) (InstJ8.xpF M.2)))
      (ChipHX.gatesHX powerBasis3 deltaF) j := by
  unfold consAt Aof
  by_cases h : j < InstJ8.sz d 0
  · have h' : j < (ChipHX.gatesHX powerBasis3 deltaF).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ ((ChipHX.gatesHX powerBasis3 deltaF).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv (w := 123) eComp val _ _ _
  · have h' : ¬ j < (ChipHX.gatesHX powerBasis3 deltaF).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]


/-! ## 11. the tie of each table -/

theorem bc_cell : Nock.Emit.cellKWTemplate.baseCols = 134 := by decide +kernel
theorem w_cell : Nock.Emit.cellKWTemplate.width 3 = 242 := by decide +kernel

/-- **the cell table**: the J-8 constraints routed to DAG gate `ℓ`, against the DAG value -/
theorem tie_cell (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (env : KEnv)
    (hbc : env.bc = 134)
    (hcur : ∀ n (hn : n < Nock.Emit.cellKWTemplate.width 3), env.cur n = val (eCell ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < Nock.Emit.cellKWTemplate.width 3), env.next n = val (eCell ⟨n, hn⟩, 1))
    (hE : SlotOK env.chal (χf χ)) (hpub : ∀ i < 6, M.1.pubsC i = pubK env i) :
    ∀ ℓ < (ncRoute Nock.Emit.cellKWTemplate.baseTransition.length Nock.Emit.cellKWTemplate.mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute Nock.Emit.cellKWTemplate.baseTransition.length
          Nock.Emit.cellKWTemplate.mixedTransition.length).mult ℓ),
        cf k * consAt d χ M 1 val ((ncRoute Nock.Emit.cellKWTemplate.baseTransition.length
          Nock.Emit.cellKWTemplate.mixedTransition.length).jOf ℓ k) =
      Vof (tplVals env Nock.Emit.fM id id Nock.Emit.cellKWTemplate.baseTransition Nock.Emit.cellKWTemplate.mixedTransition) ℓ := by
  intro ℓ hℓ
  simp only [consAt_cell, bc_cell]
  have := nc_chip_tie Nock.Emit.cellKWTemplate rfl rfl rfl rfl eCell val (chalsMJ8 deltaF χ) M.1.pubsC
    (cKmem Nock.Emit.cellKWTemplate.baseCols (Nock.Emit.cellKWTemplate.width 3) 6 chalM)
    (cBmem (Nock.Emit.cellKWTemplate.width 3)) Nock.Emit.fM env 6 (by rw [hbc, bc_cell]) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i ≤ 36 := by simpa [cKmem, chalM] using hi
      rw [chalsM_eq χ i hi', fM_leaf hE i hi'])
    (fun i hi => hpub i (by simpa [cKmem] using hi))
    (fun g hg => by
      have := chk_cell; simp only [chkT, Bool.and_eq_true, List.all_eq_true] at this; exact this.1 g hg)
    (fun E hE' => by
      have := chk_cell; simp only [chkT, Bool.and_eq_true, List.all_eq_true] at this; exact this.2 E hE') ℓ hℓ
  rw [bc_cell] at this
  exact this


/-- **the table tie, generic non-compute chip**: assembled from `nc_chip_tie` and the constraint-as-`Aof` identity -/
theorem tie_nc (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (t : Fin 6)
    (T : ChipTemplate Gl) (hext : T.extTransition = []) (hd1 : T.extDeg1 = []) (hd3 : T.extDeg3 = [])
    (heq : T.equalityChecks = []) {w : ℕ} (hw : T.width 3 = w) (e : Fin (T.width 3) → Ι) (chals pubs : ℕ → KN)
    (cKf : VarKind → ℕ → Bool) (cBf : VarKind → ℕ → Bool) (fc : ℕ → ℕ) (env : KEnv) (len : ℕ)
    (hcons : ∀ j, consAt d χ M t val j =
      Aof (evalA (mkEnvA e val (slotVal powerBasis3 T.baseCols chals) (slotVal powerBasis3 T.baseCols pubs)))
        (T.allGates powerBasis3) j)
    (hbc : env.bc = T.baseCols)
    (hcur : ∀ n (hn : n < T.width 3), env.cur n = val (e ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < T.width 3), env.next n = val (e ⟨n, hn⟩, 1))
    (hBc : ∀ n, cBf .challenge n = false)
    (hBt : ∀ n, cBf .traceCur n = true → n < T.width 3) (hBn : ∀ n, cBf .traceNext n = true → n < T.width 3)
    (hBp : ∀ n, cBf .publicVal n = false)
    (hKt : ∀ i, cKf .traceCur i = true → T.baseCols + 3 * i + 2 < T.width 3)
    (hKn : ∀ i, cKf .traceNext i = true → T.baseCols + 3 * i + 2 < T.width 3)
    (hKc : ∀ i, cKf .challenge i = true → chals i = env.chal (fc i))
    (hKp : ∀ i, cKf .publicVal i = true → pubs i = pubK env i)
    (okbase : ∀ g ∈ T.baseTransition, okB cBf g = true) (okmix : ∀ E ∈ T.mixedTransition, okM cKf cBf E = true) :
    ∀ ℓ < (ncRoute T.baseTransition.length T.mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute T.baseTransition.length T.mixedTransition.length).mult ℓ),
        cf k * consAt d χ M t val ((ncRoute T.baseTransition.length T.mixedTransition.length).jOf ℓ k) =
      Vof (tplVals env fc id id T.baseTransition T.mixedTransition) ℓ := by
  intro ℓ hℓ
  simp only [hcons]
  exact nc_chip_tie T hext hd1 hd3 heq e val chals pubs cKf cBf fc env len hbc hcur hnext hBc hBt hBn hBp hKt hKn hKc hKp
    okbase okmix ℓ hℓ

theorem chkT_all {T : ChipTemplate Gl} {len : ℕ} {chalOk : ℕ → Bool} (h : chkT T len chalOk = true) :
    (∀ g ∈ T.baseTransition, okB (cBmem (T.width 3)) g = true) ∧
    (∀ E ∈ T.mixedTransition, okM (cKmem T.baseCols (T.width 3) len chalOk) (cBmem (T.width 3)) E = true) := by
  simp only [chkT, Bool.and_eq_true, List.all_eq_true] at h
  exact h

theorem bc_walkJ8 (k : ℕ) : (tWalkJ8 k).baseCols = 25 := rfl
theorem bc_jet : Nock.Emit.jetTemplate.baseCols = 29 := by decide +kernel
theorem bc_atom : Nock.Emit.atomTemplate.baseCols = 205 := by decide +kernel
theorem bc_walkV (k : ℕ) : (tWalkV k).baseCols = 25 := rfl

/-- **the walk-J8 table** (numeral `kroots ∈ {1,9,25,42,48,174}`) -/
theorem tie_walk (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (env : KEnv)
    (hk : d.Pb.kroots ∈ [1, 9, 25, 42, 48, 174])
    (hbc : env.bc = 25)
    (hcur : ∀ n (hn : n < (tWalkJ8 d.Pb.kroots).width 3), env.cur n = val (eWalk d.Pb.kroots ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < (tWalkJ8 d.Pb.kroots).width 3), env.next n = val (eWalk d.Pb.kroots ⟨n, hn⟩, 1))
    (hE : SlotOK env.chal (χf χ)) (hpub : ∀ i < 8, M.1.pubsW i = pubK env i) :
    ∀ ℓ < (ncRoute (tWalkJ8 d.Pb.kroots).baseTransition.length (tWalkJ8 d.Pb.kroots).mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute (tWalkJ8 d.Pb.kroots).baseTransition.length
          (tWalkJ8 d.Pb.kroots).mixedTransition.length).mult ℓ),
        cf k * consAt d χ M 2 val ((ncRoute (tWalkJ8 d.Pb.kroots).baseTransition.length
          (tWalkJ8 d.Pb.kroots).mixedTransition.length).jOf ℓ k) =
      Vof (tplVals env Nock.Emit.fM id id (tWalkJ8 d.Pb.kroots).baseTransition (tWalkJ8 d.Pb.kroots).mixedTransition) ℓ := by
  have hchk := chkT_all (chk_walkJ8 d.Pb.kroots hk)
  refine tie_nc d χ M val 2 (tWalkJ8 d.Pb.kroots) rfl rfl rfl rfl rfl (eWalk d.Pb.kroots) (chalsMJ8 deltaF χ) M.1.pubsW
    (cKmem (tWalkJ8 d.Pb.kroots).baseCols ((tWalkJ8 d.Pb.kroots).width 3) 8 chalM)
    (cBmem ((tWalkJ8 d.Pb.kroots).width 3)) Nock.Emit.fM env 8 ?_ (by rw [hbc, bc_walkJ8]) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i ≤ 36 := by simpa [cKmem, chalM] using hi
      rw [chalsM_eq χ i hi', fM_leaf hE i hi'])
    (fun i hi => hpub i (by simpa [cKmem] using hi)) hchk.1 hchk.2
  · intro j; rw [bc_walkJ8]; exact consAt_walk d χ M val j

/-- **the jet table** -/
theorem tie_jet (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (env : KEnv)
    (hbc : env.bc = 29)
    (hcur : ∀ n (hn : n < Nock.Emit.jetTemplate.width 3), env.cur n = val (eJet ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < Nock.Emit.jetTemplate.width 3), env.next n = val (eJet ⟨n, hn⟩, 1))
    (hE : SlotOK env.chal (χf χ)) (hpub : ∀ i < 4, M.1.pubsJ i = pubK env i) :
    ∀ ℓ < (ncRoute Nock.Emit.jetTemplate.baseTransition.length Nock.Emit.jetTemplate.mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute Nock.Emit.jetTemplate.baseTransition.length
          Nock.Emit.jetTemplate.mixedTransition.length).mult ℓ),
        cf k * consAt d χ M 3 val ((ncRoute Nock.Emit.jetTemplate.baseTransition.length
          Nock.Emit.jetTemplate.mixedTransition.length).jOf ℓ k) =
      Vof (tplVals env Nock.Emit.fJ id id Nock.Emit.jetTemplate.baseTransition Nock.Emit.jetTemplate.mixedTransition) ℓ := by
  have hchk := chkT_all chk_jet
  refine tie_nc d χ M val 3 Nock.Emit.jetTemplate rfl rfl rfl rfl rfl eJet (chalsJJ8 χ) M.1.pubsJ
    (cKmem Nock.Emit.jetTemplate.baseCols (Nock.Emit.jetTemplate.width 3) 4 chalJ)
    (cBmem (Nock.Emit.jetTemplate.width 3)) Nock.Emit.fJ env 4 ?_ (by rw [hbc, bc_jet]) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i < 8 := by simpa [cKmem, chalJ] using hi
      rw [chalsJ_eq χ i hi', fJ_leaf hE i hi'])
    (fun i hi => hpub i (by simpa [cKmem] using hi)) hchk.1 hchk.2
  · intro j; rw [bc_jet]; exact consAt_jet d χ M val j

/-- **the atom table** -/
theorem tie_atom (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (env : KEnv)
    (hbc : env.bc = 205)
    (hcur : ∀ n (hn : n < Nock.Emit.atomTemplate.width 3), env.cur n = val (eAtom ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < Nock.Emit.atomTemplate.width 3), env.next n = val (eAtom ⟨n, hn⟩, 1))
    (hE : SlotOK env.chal (χf χ)) (hpub : ∀ i < 12, M.1.pubsA i = pubK env i) :
    ∀ ℓ < (ncRoute Nock.Emit.atomTemplate.baseTransition.length Nock.Emit.atomTemplate.mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute Nock.Emit.atomTemplate.baseTransition.length
          Nock.Emit.atomTemplate.mixedTransition.length).mult ℓ),
        cf k * consAt d χ M 4 val ((ncRoute Nock.Emit.atomTemplate.baseTransition.length
          Nock.Emit.atomTemplate.mixedTransition.length).jOf ℓ k) =
      Vof (tplVals env Nock.Emit.fA id id Nock.Emit.atomTemplate.baseTransition Nock.Emit.atomTemplate.mixedTransition) ℓ := by
  have hchk := chkT_all chk_atom
  refine tie_nc d χ M val 4 Nock.Emit.atomTemplate rfl rfl rfl rfl rfl eAtom (chalsAJ8Z deltaF χ) M.1.pubsA
    (cKmem Nock.Emit.atomTemplate.baseCols (Nock.Emit.atomTemplate.width 3) 12 chalA)
    (cBmem (Nock.Emit.atomTemplate.width 3)) Nock.Emit.fA env 12 ?_ (by rw [hbc, bc_atom]) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i ≤ 38 := by simpa [cKmem, chalA] using hi
      rw [chalsA_eq χ i hi', fA_leaf hE i hi'])
    (fun i hi => hpub i (by simpa [cKmem] using hi)) hchk.1 hchk.2
  · intro j; rw [bc_atom]; exact consAt_atom d χ M val j

/-- **the atom-walk table** (numeral `krootsV ∈ {1,2}`) -/
theorem tie_walkV (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (env : KEnv)
    (hk : d.Pb.krootsV ∈ [1, 2])
    (hbc : env.bc = 25)
    (hcur : ∀ n (hn : n < (tWalkV d.Pb.krootsV).width 3), env.cur n = val (eWalkV d.Pb.krootsV ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < (tWalkV d.Pb.krootsV).width 3), env.next n = val (eWalkV d.Pb.krootsV ⟨n, hn⟩, 1))
    (hE : SlotOK env.chal (χf χ)) (hpub : ∀ i < 8, M.1.pubsV i = pubK env i) :
    ∀ ℓ < (ncRoute (tWalkV d.Pb.krootsV).baseTransition.length (tWalkV d.Pb.krootsV).mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute (tWalkV d.Pb.krootsV).baseTransition.length
          (tWalkV d.Pb.krootsV).mixedTransition.length).mult ℓ),
        cf k * consAt d χ M 5 val ((ncRoute (tWalkV d.Pb.krootsV).baseTransition.length
          (tWalkV d.Pb.krootsV).mixedTransition.length).jOf ℓ k) =
      Vof (tplVals env Nock.Emit.fM id id (tWalkV d.Pb.krootsV).baseTransition (tWalkV d.Pb.krootsV).mixedTransition) ℓ := by
  have hchk := chkT_all (chk_walkV d.Pb.krootsV hk)
  refine tie_nc d χ M val 5 (tWalkV d.Pb.krootsV) rfl rfl rfl rfl rfl (eWalkV d.Pb.krootsV) (chalsAJ8Z deltaF χ) M.1.pubsV
    (cKmem (tWalkV d.Pb.krootsV).baseCols ((tWalkV d.Pb.krootsV).width 3) 8 chalV)
    (cBmem ((tWalkV d.Pb.krootsV).width 3)) Nock.Emit.fM env 8 ?_ (by rw [hbc, bc_walkV]) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i ≤ 36 ∧ i ≠ 2 ∧ i ≠ 3 := by simpa [cKmem, chalV] using hi
      rw [chalsV_eq χ i hi'.1 hi'.2.1 hi'.2.2, fM_leaf hE i hi'.1])
    (fun i hi => hpub i (by simpa [cKmem] using hi)) hchk.1 hchk.2
  · intro j; rw [bc_walkV]; exact consAt_walkV d χ M val j


/-! ## 12. the compute table -/

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD (col0Id)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (mapC)

/-- the compute chip's gate groups -/
noncomputable def cArith : List (CoeffExpr Gl) := (ChipHX.arithGatesX (F := ℚ)).map (mapC (fun q : ℚ => (q : Gl)))
noncomputable def cEq : List (CoeffExpr Gl) :=
  ((ChipHX.eqGatesX (F := ℚ)).map ChipH.EqG.gate).map (mapC (fun q : ℚ => (q : Gl)))
noncomputable def cAcc : List (MixedExpr Gl) := Nock.Emit.accKGatesHX (F := Gl)
noncomputable def cSlot : List (MixedExpr Gl) := (ChipHX.slotPairsX Gl Nock.Emit.δ).flatMap (fun q => [q.1, q.2])

theorem cK2_eq : Nock.Emit.computeSpec0.mixed = cAcc ++ (cSlot ++ ChipHX.walkGatesFX) := by
  simp only [Nock.Emit.computeSpec0, cSlot, cAcc, List.append_assoc]

theorem cBase_eq : Nock.Emit.computeSpec0.base = cArith ++ cEq := by
  simp only [Nock.Emit.computeSpec0, cArith, cEq, List.map_append]

theorem gatesHX_eq : ChipHX.gatesHX powerBasis3 Nock.Emit.δ =
    cArith ++ ChipHX.accGatesHX (F := Gl) ++ cEq ++ Kflat col0Id (cSlot ++ ChipHX.walkGatesFX) := by
  have h1 := Nock.Emit.computeBase_split
  have hq : ∀ q : MixedExpr Gl × MixedExpr Gl,
      Nock.NockVMROM.Thm54.VclL.Compute.TowerD.qGates powerBasis3 q = Kflat col0Id [q.1, q.2] := by
    intro q; simp [Nock.NockVMROM.Thm54.VclL.Compute.TowerD.qGates, Kflat]
  have hq' : Nock.NockVMROM.Thm54.VclL.Compute.TowerD.qGates powerBasis3 = fun q => Kflat col0Id [q.1, q.2] := funext hq
  simp only [ChipHX.gatesHX, h1, hq', Kflat, cSlot, List.flatMap_append, List.flatMap_assoc, cArith, cEq, List.append_assoc]

/-- the DAG value list of the compute chip -/
noncomputable def compVals (env : KEnv) : List NockvmE2E.Exec.KC :=
  cArith.map (evB env) ++ cEq.map (evB env) ++
    cAcc.map (fun E => evM env (Nock.Emit.norm (renameM Nock.Emit.fX Nock.Emit.feX Nock.Emit.fpX E))) ++
    (cSlot ++ ChipHX.walkGatesFX).map (fun E => evM env (Nock.Emit.norm (renameM Nock.Emit.fX Nock.Emit.feX Nock.Emit.fpX E)))

theorem sum_pub3' (env : KEnv) (f : ℕ → ZMod NockvmE2E.Exec.p) (hfg : ∀ s < 33, f s = env.pub s) (r : ℕ) (hr3 : r % 3 = 0)
    (hr : r + 2 < 33) :
    ∑ k : Fin 3, NockvmE2E.Exec.xr ^ (k : ℕ) * algebraMap (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC (f (r + (k : ℕ))) =
      pubK env (r / 3) := by
  simp only [Fin.sum_univ_three, pubK, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, Nat.add_zero]
  have e0 : 3 * (r / 3) = r := by omega
  rw [e0, hfg r (by omega), hfg (r + 1) (by omega), hfg (r + 2) (by omega)]
  ring

theorem sum_pub3 (env : KEnv) (f : ℕ → ZMod P) (hfg : ∀ s < 33, f s = env.pub s) (r : ℕ) (hr3 : r % 3 = 0)
    (hr : r + 2 < 33) :
    ∑ k : Fin 3, powerBasis3 k * algebraMap (ZMod P) KN (f (r + (k : ℕ))) = pubK env (r / 3) := by
  rw [← sum_pub3' env f hfg r hr3 hr]
  exact Finset.sum_congr rfl fun k _ => by rw [pb3_apply]; rfl

/-- **the compute table** -/
theorem tie_comp (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (env : KEnv)
    (hbc : env.bc = 69)
    (hcur : ∀ n (hn : n < 123), env.cur n = val (eComp ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < 123), env.next n = val (eComp ⟨n, hn⟩, 1))
    (hE : SlotOK env.chal (χf χ)) (hpub : ∀ s < 33, InstJ8.xpF M.2 s = env.pub s) :
    ∀ ℓ < (cRoute cArith.length cEq.length cAcc.length (cSlot ++ ChipHX.walkGatesFX).length).nK,
      ∑ k ∈ Finset.range ((cRoute cArith.length cEq.length cAcc.length
          (cSlot ++ ChipHX.walkGatesFX).length).mult ℓ),
        cf k * consAt d χ M 0 val ((cRoute cArith.length cEq.length cAcc.length
          (cSlot ++ ChipHX.walkGatesFX).length).jOf ℓ k) = Vof (compVals env) ℓ := by
  intro ℓ hℓ
  have hcons : ∀ j, consAt d χ M 0 val j = Aof (evalA (mkEnvA eComp val (chalVJ8 powerBasis3 χ) (InstJ8.xpF M.2)))
      (cArith ++ ChipHX.accGatesHX (F := Gl) ++ cEq ++ Kflat col0Id (cSlot ++ ChipHX.walkGatesFX)) j := by
    intro j; rw [consAt_comp, ← gatesHX_eq]; rfl
  have hok := chk_compute
  simp only [Bool.and_eq_true, List.all_eq_true, cBase_eq, cK2_eq, List.mem_append, List.forall_mem_append] at hok
  have hacc : (ChipHX.accGatesHX (F := Gl)).map (evalA (mkEnvA eComp val (chalVJ8 powerBasis3 χ) (InstJ8.xpF M.2))) =
      (Kflat col0Id cAcc).map (evalA (mkEnvA eComp val (chalVJ8 powerBasis3 χ) (InstJ8.xpF M.2))) :=
    NockvmE2E.Emit.accGatesHX_semA powerBasis3 _
  have e1 : ∑ k ∈ Finset.range ((cRoute cArith.length cEq.length cAcc.length
          (cSlot ++ ChipHX.walkGatesFX).length).mult ℓ),
        cf k * consAt d χ M 0 val ((cRoute cArith.length cEq.length cAcc.length
          (cSlot ++ ChipHX.walkGatesFX).length).jOf ℓ k)
      = ∑ k ∈ Finset.range ((cRoute cArith.length cEq.length cAcc.length
          (cSlot ++ ChipHX.walkGatesFX).length).mult ℓ),
        cf k * Aof (evalA (mkEnvA eComp val (chalVJ8 powerBasis3 χ) (InstJ8.xpF M.2)))
          (cArith ++ ChipHX.accGatesHX (F := Gl) ++ cEq ++ Kflat col0Id (cSlot ++ ChipHX.walkGatesFX))
          ((cRoute cArith.length cEq.length cAcc.length (cSlot ++ ChipHX.walkGatesFX).length).jOf ℓ k) :=
    Finset.sum_congr rfl (fun k _ => by rw [hcons])
  rw [e1]
  refine c_chip_tie col0Id (w := 123) eComp val (chalVJ8 powerBasis3 χ) (InstJ8.xpF M.2) cKc cBc Nock.Emit.fX
        Nock.Emit.feX Nock.Emit.fpX env cArith cEq (ChipHX.accGatesHX (F := Gl)) cAcc
        (cSlot ++ ChipHX.walkGatesFX)
        hcur hnext (fun n => rfl) (fun n hn => by simpa [cBc] using hn) (fun n hn => by simpa [cBc] using hn)
        (fun n hn => by
          have : n < 33 := by simpa [cBc] using hn
          rw [hpub n this]; rfl)
        (fun i hi => by
          simp only [cKc, decide_eq_true_eq] at hi
          simp only [col0Id, Nock.Emit.feX, hbc, if_pos hi.1]
          omega)
        (fun i hi => by
          simp only [cKc, decide_eq_true_eq] at hi
          simp only [col0Id, Nock.Emit.feX, hbc, if_pos hi.1]
          omega)
        (fun r hr => by
          simp only [cKc, decide_eq_true_eq] at hr
          exact comp_chal χ env.chal hE r hr.1 hr.2)
        (fun r hr => by
          simp only [cKc, decide_eq_true_eq] at hr
          exact sum_pub3 env (InstJ8.xpF M.2) hpub r hr.1 hr.2)
        ?_ ?_ hacc ℓ hℓ
  · intro g hg
    exact hok.1 g (List.mem_append.mp hg)
  · intro E hE'
    rcases List.mem_append.mp hE' with h | h
    · exact hok.2 E (Or.inl h)
    · rcases List.mem_append.mp h with h | h
      · exact hok.2 E (Or.inr (Or.inl h))
      · exact hok.2 E (Or.inr (Or.inr h))

/-! ## 13. hop 0 and the DAG value list of a loaded chip -/


/-- **hop 0** (named hypothesis; discharged by the exe-side literal check `J8Chips`): the loaded chip is the verifier chip
(`verifierChipT`) of the parse (`toEx`) of the emitted DAG document `D`, at the loader's `ders` / `cmeta`, with base-column count `bc` -/
def HopZero (ch : NockvmE2E.Exec.Tr.Chip) (D : DagGates) (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ)) (bc : ℕ) : Prop :=
  ∃ (ch0 : NockvmE2E.Exec.Tr.Chip) (sh cb ce cm c1 c3 cq : List Ex),
    D.defs.mapM toEx = some sh ∧ D.base.mapM toEx = some cb ∧ D.ext.mapM toEx = some ce ∧ D.mixed.mapM toEx = some cm ∧
    D.ext1.mapM toEx = some c1 ∧ D.ext3.mapM toEx = some c3 ∧ D.eqc.mapM toEx = some cq ∧
    ch0.shared = sh.toArray ∧ ch0.cons.toList.map (·.e) = cb ++ ce ++ cm ++ c1 ++ c3 ++ cq ∧
    ch.shared = (NockvmE2E.Exec.VC.verifierChipT ch0 ders cmeta).1.shared ∧
    ch.cons.map (·.e) = (NockvmE2E.Exec.VC.verifierChipT ch0 ders cmeta).1.cons.map (·.e) ∧ ch0.baseCols = bc

/-- **soundness of the `HopZero` weakening**: `evalDagK` reads only `shared` and the constraint expressions `cons.map (·.e)` -/
theorem evalDagK_congr_fields (a b : NockvmE2E.Exec.Tr.Chip) (hs : a.shared = b.shared) (hc : a.cons.map (·.e) = b.cons.map (·.e))
    (env : KEnv) : evalDagK a env = evalDagK b env := by
  have h : ∀ ch : NockvmE2E.Exec.Tr.Chip, evalDagK ch env =
      (ch.cons.map (·.e)).map (fun e => evKC env (memoK ch.shared.toList env) e) := by
    intro ch; simp [evalDagK, Array.map_map, Function.comp_def]
  rw [h a, h b, hs, hc]

/-- the DAG value list of decoded gates -/
noncomputable def dagVals (g : DGatesDec) (env : KEnv) : List NockvmE2E.Exec.KC :=
  g.base.map (evB env) ++ g.ext.map (evM env) ++ g.mixed.map (evM env) ++ g.ext1.map (evM env) ++ g.ext3.map (evM env) ++
    g.eqc.map (evB env)

/-- **the loaded chip's values are the decoded gates' values** (hop 0 + the emitter tie `evalDagK_toEx_of_decodeDag`) -/
theorem evalDagK_hop (ch : NockvmE2E.Exec.Tr.Chip) (D : DagGates) (g : DGatesDec) (hdec : decodeDagL D = some g)
    (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ)) (hop : HopZero ch D ders cmeta ch.baseCols) (env : KEnv) :
    (evalDagK ch env).toList = dagVals g {env with chal := NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal} := by
  obtain ⟨ch0, sh, cb, ce, cm, c1, c3, cq, hsh, hcb, hce, hcm, hc1, hc3, hcq, hsh', hcons, hs, hc, hbc⟩ := hop
  rw [evalDagK_congr_fields ch _ hs hc, NockvmE2E.Exec.DagSemV.evalDagK_verifierChipT]
  exact evalDagK_toEx_of_decodeDag D g hdec sh hsh cb ce cm c1 c3 cq hcb hce hcm hc1 hc3 hcq ch0 hsh' hcons _

theorem gates_nc (T : ChipTemplate Gl) (hext : T.extTransition = []) (hd1 : T.extDeg1 = []) (hd3 : T.extDeg3 = [])
    (heq : T.equalityChecks = []) (fc : ℕ → ℕ) :
    ((TSpec.ofTemplate T).rename fc id id).gates =
      ⟨T.baseTransition, [], T.mixedTransition.map (fun E => Nock.Emit.norm (renameM fc id id E)), [], [], []⟩ := by
  simp [TSpec.gates, TSpec.rename, TSpec.ofTemplate, hext, hd1, hd3, heq, List.map_map, Function.comp_def]

theorem dagVals_nc (T : ChipTemplate Gl) (hext : T.extTransition = []) (hd1 : T.extDeg1 = []) (hd3 : T.extDeg3 = [])
    (heq : T.equalityChecks = []) (fc : ℕ → ℕ) (env : KEnv) :
    dagVals (((TSpec.ofTemplate T).rename fc id id).gates) env = tplVals env fc id id T.baseTransition T.mixedTransition := by
  rw [gates_nc T hext hd1 hd3 heq fc]
  simp [dagVals, tplVals, List.map_map, Function.comp_def]

theorem dagVals_comp (env : KEnv) :
    dagVals (Nock.Emit.computeSpec.gates) env = compVals env := by
  have h1 := cBase_eq
  have h2 := cK2_eq
  simp only [Nock.Emit.computeSpec, Nock.Emit.TSpec.gates, Nock.Emit.TSpec.rename, h1, h2, dagVals, compVals, List.map_append,
    List.map_map, Function.comp_def, List.append_assoc]
  simp [Nock.Emit.computeSpec0]

/-! ## 14. the per-numeral document decodes (kernel) -/

theorem decR_walkJ8_at : ∀ k ∈ [1, 9, 25, 42, 48, 174],
    decodeDagR (emitDag (Nock.Emit.walkJ8SpecAt k)) = some (Nock.Emit.walkJ8SpecAt k).gates := by decide +kernel

theorem decR_walkV_at : ∀ k ∈ [1, 2],
    decodeDagR (emitDag (Nock.Emit.walkAtomSpecAt k)) = some (Nock.Emit.walkAtomSpecAt k).gates := by decide +kernel

/-! ## 15. the tie of each table against the LOADED chip -/

theorem dag_get (ch : NockvmE2E.Exec.Tr.Chip) (env : KEnv) (L : List NockvmE2E.Exec.KC) (h : (evalDagK ch env).toList = L) (ℓ : ℕ)
    (hℓ : ℓ < L.length) : (evalDagK ch env)[ℓ]! = Vof L ℓ := by
  have h1 : (evalDagK ch env).size = L.length := by rw [← h]; simp
  have hs : ℓ < (evalDagK ch env).size := by omega
  rw [getElem!_pos (evalDagK ch env) ℓ hs]
  subst h
  simp only [Vof, List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getElem?_eq_getElem hs]
  simp

theorem length_tplVals (env : KEnv) (fc fe fp : ℕ → ℕ) (base : List (CoeffExpr Gl)) (KG : List (MixedExpr Gl)) :
    (tplVals env fc fe fp base KG).length = (ncRoute base.length KG.length).nK := by
  simp only [tplVals, ncRoute, List.length_append, List.length_map]

section TieD
variable (d : Datum) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN)
  (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ)) (env : KEnv)

/-- `env` with the chip's slot semantics (`chalE`): the environment `evalDagK_verifierChipT` evaluates the emitted chip at -/
noncomputable def envE : KEnv := {env with chal := NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal}

theorem decL_of_decR {D : DagGates} {g : DGatesDec} (h : decodeDagR D = some g) : decodeDagL D = some g := by
  rw [← decodeDagR_eq]; exact h

/-- **cell table against the loaded chip** -/
theorem tieD_cell (ch : NockvmE2E.Exec.Tr.Chip) (hop : HopZero ch Nock.Emit.emit_cellKW ders cmeta ch.baseCols)
    (hbc : env.bc = 134) (hch : ch.baseCols = 134)
    (hcur : ∀ n (hn : n < Nock.Emit.cellKWTemplate.width 3), env.cur n = val (eCell ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < Nock.Emit.cellKWTemplate.width 3), env.next n = val (eCell ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 6, M.1.pubsC i = pubK env i) :
    ∀ ℓ < (ncRoute Nock.Emit.cellKWTemplate.baseTransition.length Nock.Emit.cellKWTemplate.mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute Nock.Emit.cellKWTemplate.baseTransition.length
          Nock.Emit.cellKWTemplate.mixedTransition.length).mult ℓ),
        cf k * consAt d χ M 1 val ((ncRoute Nock.Emit.cellKWTemplate.baseTransition.length
          Nock.Emit.cellKWTemplate.mixedTransition.length).jOf ℓ k) = (evalDagK ch env)[ℓ]! := by
  intro ℓ hℓ
  have hv := evalDagK_hop ch _ _ (decL_of_decR NockvmE2E.Emit.decR_cellKW) ders cmeta hop env
  rw [show Nock.Emit.cellKWSpec.gates = ((TSpec.ofTemplate Nock.Emit.cellKWTemplate).rename Nock.Emit.fM id id).gates from rfl,
    dagVals_nc Nock.Emit.cellKWTemplate rfl rfl rfl rfl Nock.Emit.fM] at hv
  rw [dag_get ch env _ hv ℓ (by rw [length_tplVals]; exact hℓ)]
  exact tie_cell d χ M val (envE ders cmeta env) hbc hcur hnext hE hpub ℓ hℓ

/-- **walk-J8 table against the loaded chip** -/
theorem tieD_walk (ch : NockvmE2E.Exec.Tr.Chip) (hk : d.Pb.kroots ∈ [1, 9, 25, 42, 48, 174])
    (hop : HopZero ch (emitDag (Nock.Emit.walkJ8SpecAt d.Pb.kroots)) ders cmeta ch.baseCols)
    (hbc : env.bc = 25)
    (hcur : ∀ n (hn : n < (tWalkJ8 d.Pb.kroots).width 3), env.cur n = val (eWalk d.Pb.kroots ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < (tWalkJ8 d.Pb.kroots).width 3), env.next n = val (eWalk d.Pb.kroots ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 8, M.1.pubsW i = pubK env i) :
    ∀ ℓ < (ncRoute (tWalkJ8 d.Pb.kroots).baseTransition.length (tWalkJ8 d.Pb.kroots).mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute (tWalkJ8 d.Pb.kroots).baseTransition.length
          (tWalkJ8 d.Pb.kroots).mixedTransition.length).mult ℓ),
        cf k * consAt d χ M 2 val ((ncRoute (tWalkJ8 d.Pb.kroots).baseTransition.length
          (tWalkJ8 d.Pb.kroots).mixedTransition.length).jOf ℓ k) = (evalDagK ch env)[ℓ]! := by
  intro ℓ hℓ
  have hv := evalDagK_hop ch _ _ (decL_of_decR (decR_walkJ8_at _ hk)) ders cmeta hop env
  rw [show (Nock.Emit.walkJ8SpecAt d.Pb.kroots).gates = ((TSpec.ofTemplate (tWalkJ8 d.Pb.kroots)).rename Nock.Emit.fM id id).gates
    from rfl, dagVals_nc (tWalkJ8 d.Pb.kroots) rfl rfl rfl rfl Nock.Emit.fM] at hv
  rw [dag_get ch env _ hv ℓ (by rw [length_tplVals]; exact hℓ)]
  exact tie_walk d χ M val (envE ders cmeta env) hk hbc hcur hnext hE hpub ℓ hℓ

/-- **jet table against the loaded chip** -/
theorem tieD_jet (ch : NockvmE2E.Exec.Tr.Chip) (hop : HopZero ch Nock.Emit.emit_jet ders cmeta ch.baseCols)
    (hbc : env.bc = 29)
    (hcur : ∀ n (hn : n < Nock.Emit.jetTemplate.width 3), env.cur n = val (eJet ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < Nock.Emit.jetTemplate.width 3), env.next n = val (eJet ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 4, M.1.pubsJ i = pubK env i) :
    ∀ ℓ < (ncRoute Nock.Emit.jetTemplate.baseTransition.length Nock.Emit.jetTemplate.mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute Nock.Emit.jetTemplate.baseTransition.length
          Nock.Emit.jetTemplate.mixedTransition.length).mult ℓ),
        cf k * consAt d χ M 3 val ((ncRoute Nock.Emit.jetTemplate.baseTransition.length
          Nock.Emit.jetTemplate.mixedTransition.length).jOf ℓ k) = (evalDagK ch env)[ℓ]! := by
  intro ℓ hℓ
  have hv := evalDagK_hop ch _ _ (decL_of_decR NockvmE2E.Emit.decR_jet) ders cmeta hop env
  rw [show Nock.Emit.jetSpec.gates = ((TSpec.ofTemplate Nock.Emit.jetTemplate).rename Nock.Emit.fJ id id).gates from rfl,
    dagVals_nc Nock.Emit.jetTemplate rfl rfl rfl rfl Nock.Emit.fJ] at hv
  rw [dag_get ch env _ hv ℓ (by rw [length_tplVals]; exact hℓ)]
  exact tie_jet d χ M val (envE ders cmeta env) hbc hcur hnext hE hpub ℓ hℓ

/-- **atom table against the loaded chip** -/
theorem tieD_atom (ch : NockvmE2E.Exec.Tr.Chip) (hop : HopZero ch Nock.Emit.emit_atom ders cmeta ch.baseCols)
    (hbc : env.bc = 205)
    (hcur : ∀ n (hn : n < Nock.Emit.atomTemplate.width 3), env.cur n = val (eAtom ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < Nock.Emit.atomTemplate.width 3), env.next n = val (eAtom ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 12, M.1.pubsA i = pubK env i) :
    ∀ ℓ < (ncRoute Nock.Emit.atomTemplate.baseTransition.length Nock.Emit.atomTemplate.mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute Nock.Emit.atomTemplate.baseTransition.length
          Nock.Emit.atomTemplate.mixedTransition.length).mult ℓ),
        cf k * consAt d χ M 4 val ((ncRoute Nock.Emit.atomTemplate.baseTransition.length
          Nock.Emit.atomTemplate.mixedTransition.length).jOf ℓ k) = (evalDagK ch env)[ℓ]! := by
  intro ℓ hℓ
  have hv := evalDagK_hop ch _ _ (decL_of_decR NockvmE2E.Emit.decR_atom) ders cmeta hop env
  rw [show Nock.Emit.atomSpec.gates = ((TSpec.ofTemplate Nock.Emit.atomTemplate).rename Nock.Emit.fA id id).gates from rfl,
    dagVals_nc Nock.Emit.atomTemplate rfl rfl rfl rfl Nock.Emit.fA] at hv
  rw [dag_get ch env _ hv ℓ (by rw [length_tplVals]; exact hℓ)]
  exact tie_atom d χ M val (envE ders cmeta env) hbc hcur hnext hE hpub ℓ hℓ

/-- **atom-walk table against the loaded chip** -/
theorem tieD_walkV (ch : NockvmE2E.Exec.Tr.Chip) (hk : d.Pb.krootsV ∈ [1, 2])
    (hop : HopZero ch (emitDag (Nock.Emit.walkAtomSpecAt d.Pb.krootsV)) ders cmeta ch.baseCols)
    (hbc : env.bc = 25)
    (hcur : ∀ n (hn : n < (tWalkV d.Pb.krootsV).width 3), env.cur n = val (eWalkV d.Pb.krootsV ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < (tWalkV d.Pb.krootsV).width 3), env.next n = val (eWalkV d.Pb.krootsV ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 8, M.1.pubsV i = pubK env i) :
    ∀ ℓ < (ncRoute (tWalkV d.Pb.krootsV).baseTransition.length (tWalkV d.Pb.krootsV).mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute (tWalkV d.Pb.krootsV).baseTransition.length
          (tWalkV d.Pb.krootsV).mixedTransition.length).mult ℓ),
        cf k * consAt d χ M 5 val ((ncRoute (tWalkV d.Pb.krootsV).baseTransition.length
          (tWalkV d.Pb.krootsV).mixedTransition.length).jOf ℓ k) = (evalDagK ch env)[ℓ]! := by
  intro ℓ hℓ
  have hv := evalDagK_hop ch _ _ (decL_of_decR (decR_walkV_at _ hk)) ders cmeta hop env
  rw [show (Nock.Emit.walkAtomSpecAt d.Pb.krootsV).gates = ((TSpec.ofTemplate (tWalkV d.Pb.krootsV)).rename Nock.Emit.fM id id).gates
    from rfl, dagVals_nc (tWalkV d.Pb.krootsV) rfl rfl rfl rfl Nock.Emit.fM] at hv
  rw [dag_get ch env _ hv ℓ (by rw [length_tplVals]; exact hℓ)]
  exact tie_walkV d χ M val (envE ders cmeta env) hk hbc hcur hnext hE hpub ℓ hℓ

/-- **compute table against the loaded chip** -/
theorem tieD_comp (ch : NockvmE2E.Exec.Tr.Chip) (hop : HopZero ch Nock.Emit.emit_compute ders cmeta ch.baseCols)
    (hbc : env.bc = 69)
    (hcur : ∀ n (hn : n < 123), env.cur n = val (eComp ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < 123), env.next n = val (eComp ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ s < 33, InstJ8.xpF M.2 s = env.pub s) :
    ∀ ℓ < (cRoute cArith.length cEq.length cAcc.length (cSlot ++ ChipHX.walkGatesFX).length).nK,
      ∑ k ∈ Finset.range ((cRoute cArith.length cEq.length cAcc.length (cSlot ++ ChipHX.walkGatesFX).length).mult ℓ),
        cf k * consAt d χ M 0 val ((cRoute cArith.length cEq.length cAcc.length
          (cSlot ++ ChipHX.walkGatesFX).length).jOf ℓ k) = (evalDagK ch env)[ℓ]! := by
  intro ℓ hℓ
  have hv := evalDagK_hop ch _ _ (decL_of_decR NockvmE2E.Emit.decR_compute) ders cmeta hop env
  rw [dagVals_comp] at hv
  have hlen : ∀ e : KEnv, (compVals e).length = (cRoute cArith.length cEq.length cAcc.length
      (cSlot ++ ChipHX.walkGatesFX).length).nK := by
    intro e; simp only [compVals, cRoute, List.length_append, List.length_map]
  rw [dag_get ch env _ hv ℓ (by rw [hlen]; exact hℓ)]
  exact tie_comp d χ M val (envE ders cmeta env) hbc hcur hnext hE hpub ℓ hℓ

end TieD

/-! ## 16. the global fiber: J-8 constraint index `j : Fin ns` <-> (table, local coordinate gate) -/

section Global
variable (sz : Fin 6 → ℕ)

/-- the local (within-table) index of a global J-8 constraint -/
def loc (j : Fin (∑ t : Fin 6, sz t)) : ℕ := ((finSigmaFinEquiv.symm j).2 : ℕ)

theorem loc_eq (j : Fin (∑ t : Fin 6, sz t)) : loc sz j = ((finSigmaFinEquiv.symm j).2 : ℕ) := rfl

theorem tabS_jglob (t : Fin 6) (l : Fin (sz t)) :
    (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨t, l⟩ : Fin (∑ t : Fin 6, sz t))).1 = t := by
  rw [Equiv.symm_apply_apply]

theorem loc_jglob (t : Fin 6) (l : Fin (sz t)) :
    loc sz (finSigmaFinEquiv ⟨t, l⟩) = l := by
  unfold loc; rw [Equiv.symm_apply_apply]

theorem fiber_global (rt : Fin 6 → Route) (hN : ∀ t, (rt t).N = sz t) (t : Fin 6) (ℓ : ℕ) (hℓ : ℓ < (rt t).nK)
    (F : Fin (∑ t : Fin 6, sz t) → KN) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (∑ t : Fin 6, sz t) =>
        (finSigmaFinEquiv.symm j).1 = t ∧ ((rt t).route (loc sz j)).1 = ℓ),
        cf ((rt t).route (loc sz j)).2 * F j =
      ∑ k ∈ Finset.range ((rt t).mult ℓ), cf k *
        (if h : (rt t).jOf ℓ k < sz t then F (finSigmaFinEquiv ⟨t, ⟨(rt t).jOf ℓ k, h⟩⟩) else 0) := by
  have hlt : ∀ k, k < (rt t).mult ℓ → (rt t).jOf ℓ k < sz t := fun k hk => by
    have := ((rt t).h2 ℓ hℓ k hk).1; rw [hN t] at this; exact this
  have hdec : ∀ j : Fin (∑ t : Fin 6, sz t), (finSigmaFinEquiv.symm j).1 = t →
      ∃ h : loc sz j < sz t, j = finSigmaFinEquiv ⟨t, ⟨loc sz j, h⟩⟩ := by
    intro j hj
    obtain ⟨⟨t', l'⟩, hjj⟩ : ∃ x, finSigmaFinEquiv.symm j = x := ⟨_, rfl⟩
    rw [hjj] at hj
    simp only at hj
    subst hj
    have hl : loc sz j = (l' : ℕ) := by unfold loc; rw [hjj]
    have hlt' : loc sz j < sz t' := by rw [hl]; exact l'.2
    refine ⟨hlt', ?_⟩
    have e1 : j = finSigmaFinEquiv ⟨t', l'⟩ := by rw [← hjj, Equiv.apply_symm_apply]
    have e2 : (⟨t', l'⟩ : Σ t, Fin (sz t)) = ⟨t', ⟨loc sz j, hlt'⟩⟩ := Sigma.ext rfl (heq_of_eq (Fin.ext hl.symm))
    rw [← e2]; exact e1
  refine Finset.sum_bij' (fun j _ => ((rt t).route (loc sz j)).2)
    (fun k hk => finSigmaFinEquiv ⟨t, ⟨(rt t).jOf ℓ k, hlt k (Finset.mem_range.mp hk)⟩⟩) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hl, _⟩ := hdec j hj.1
    have hl' : loc sz j < (rt t).N := by rw [hN]; exact hl
    have := ((rt t).h1 (loc sz j) hl').2.1
    rw [hj.2] at this
    exact Finset.mem_range.mpr this
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hk' := Finset.mem_range.mp hk
    refine ⟨by rw [Equiv.symm_apply_apply], ?_⟩
    rw [loc_jglob]
    exact congrArg Prod.fst ((rt t).h2 ℓ hℓ k hk').2
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hl, hjj⟩ := hdec j hj.1
    have hl' : loc sz j < (rt t).N := by rw [hN]; exact hl
    have h3 := ((rt t).h1 (loc sz j) hl').2.2
    rw [hj.2] at h3
    conv_rhs => rw [hjj]
    congr 2
    exact Fin.ext h3
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    show ((rt t).route (loc sz (finSigmaFinEquiv ⟨t, _⟩))).2 = k
    rw [loc_jglob]
    exact congrArg Prod.snd ((rt t).h2 ℓ hℓ k hk').2
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hl, hjj⟩ := hdec j hj.1
    have hl' : loc sz j < (rt t).N := by rw [hN]; exact hl
    have h3 := ((rt t).h1 (loc sz j) hl').2.2
    rw [hj.2] at h3
    have h4 : (rt t).jOf ℓ ((rt t).route (loc sz j)).2 < sz t := by rw [h3]; exact hl
    show cf _ * F j = cf _ * (if h : (rt t).jOf ℓ ((rt t).route (loc sz j)).2 < sz t then _ else 0)
    rw [dif_pos h4]
    congr 2
    conv_lhs => rw [hjj]
    congr 2
    exact Fin.ext h3.symm


section AevCfun
variable (d : Datum)

theorem aeval_consT_eq (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN)
    (σj : Σ t : Fin 6, Fin (InstJ8.sz d t)) :
    MvPolynomial.aeval val (InstJ8.consT d χ M σj.1 σj.2) = consAt d χ M σj.1 val (σj.2 : ℕ) := by
  unfold consAt
  rw [dif_pos σj.2.2]

/-- `aeval` of the global constraint is the local one -/
theorem aeval_Cfun (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (j : Fin (∑ t : Fin 6, InstJ8.sz d t)) :
    MvPolynomial.aeval val (InstJ8.Cfun d χ M j) =
      consAt d χ M ((finSigmaFinEquiv (n := InstJ8.sz d)).symm j).1 val (loc (InstJ8.sz d) j) :=
  aeval_consT_eq d χ M val ((finSigmaFinEquiv (n := InstJ8.sz d)).symm j)

end AevCfun

end Global

/-! ## 17. the routing of the six tables -/

theorem acc_len : (ChipHX.accGatesHX (F := Gl)).length = 3 * cAcc.length := by decide +kernel

/-- the routing of the six J-8 tables onto their DAG gates -/
noncomputable def rtJ8 (d : Datum) : Fin 6 → Route
  | 0 => cRoute cArith.length cEq.length cAcc.length (cSlot ++ ChipHX.walkGatesFX).length
  | 1 => ncRoute Nock.Emit.cellKWTemplate.baseTransition.length Nock.Emit.cellKWTemplate.mixedTransition.length
  | 2 => ncRoute (tWalkJ8 d.Pb.kroots).baseTransition.length (tWalkJ8 d.Pb.kroots).mixedTransition.length
  | 3 => ncRoute Nock.Emit.jetTemplate.baseTransition.length Nock.Emit.jetTemplate.mixedTransition.length
  | 4 => ncRoute Nock.Emit.atomTemplate.baseTransition.length Nock.Emit.atomTemplate.mixedTransition.length
  | 5 => ncRoute (tWalkV d.Pb.krootsV).baseTransition.length (tWalkV d.Pb.krootsV).mixedTransition.length

theorem len_nc (T : ChipTemplate Gl) (hext : T.extTransition = []) (hd1 : T.extDeg1 = []) (hd3 : T.extDeg3 = [])
    (heq : T.equalityChecks = []) :
    (T.allGates powerBasis3).length = (ncRoute T.baseTransition.length T.mixedTransition.length).N := by
  rw [allGates_empty T hext hd1 hd3 heq]
  simp only [List.length_append, Kflat_length, ncRoute]

/-- the sizes of the six tables are the route sizes -/
theorem rtJ8_N (d : Datum) (t : Fin 6) : (rtJ8 d t).N = InstJ8.sz d t := by
  fin_cases t
  · show (cRoute cArith.length cEq.length cAcc.length (cSlot ++ ChipHX.walkGatesFX).length).N =
      (ChipHX.gatesHX powerBasis3 deltaF).length
    rw [show (deltaF : Gl) = Nock.Emit.δ from rfl, gatesHX_eq]
    simp only [List.length_append, Kflat_length, cRoute, acc_len]
  · exact (len_nc Nock.Emit.cellKWTemplate rfl rfl rfl rfl).symm
  · exact (len_nc (tWalkJ8 d.Pb.kroots) rfl rfl rfl rfl).symm
  · exact (len_nc Nock.Emit.jetTemplate rfl rfl rfl rfl).symm
  · exact (len_nc Nock.Emit.atomTemplate rfl rfl rfl rfl).symm
  · exact (len_nc (tWalkV d.Pb.krootsV) rfl rfl rfl rfl).symm

end NockvmE2E.J8.TieJ8

#print axioms NockvmE2E.J8.TieJ8.chk_cell#print axioms NockvmE2E.J8.TieJ8.tieD_cell
#print axioms NockvmE2E.J8.TieJ8.tieD_walk
#print axioms NockvmE2E.J8.TieJ8.tieD_jet
#print axioms NockvmE2E.J8.TieJ8.tieD_atom
#print axioms NockvmE2E.J8.TieJ8.tieD_walkV
#print axioms NockvmE2E.J8.TieJ8.tieD_comp
#print axioms NockvmE2E.J8.TieJ8.fiber_global
#print axioms NockvmE2E.J8.TieJ8.aeval_Cfun
#print axioms NockvmE2E.J8.TieJ8.rtJ8_N
#print axioms NockvmE2E.J8.TieJ8.evalDagK_hop
#print axioms NockvmE2E.J8.TieJ8.decR_walkJ8_at
#print axioms NockvmE2E.J8.TieJ8.decR_walkV_at
