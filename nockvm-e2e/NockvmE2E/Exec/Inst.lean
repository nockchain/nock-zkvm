/-
  NockvmE2E/Exec/Inst.lean   (proof-only, not in the exe closure)

  The J-8 instance side of the sound direction, as far as it is pure field/domain algebra:
  * `smooth_pow`, `smoothDomain_pow`, `smoothDomain_apply`: every point of a `SmoothCosetFftDomain` satisfies `ω i ^ 2^n = c ^ 2^n`
    (feeds the verifier's check (v) `OffDom`), and `smoothDomain n i = 7 · ζ_n^i` (the verifier's `dShift · dGen^i`);
  * `toKV_inj` (injective on canonical limbs), `DomLink`, `hω_of_domLink`, `offDom_of_flatOk`: the verifier's power test (v) ⇒ no opening
    point is on the domain;
  * `decBlock` and the α/ζ/coin decoding of a challenge block;
  * `DeepLink`: the bundle of the remaining J-8-side hypotheses of `deepCheck_of_flatOk'`, each field documented.
  NOT done here (needs the audited J-8 round list `compiledRoundsK … msC` instantiated: ~40 arguments, `deepParamsJ` with `hNH`,
  `PointMaskData`, `OpenAll`).
-/
import NockvmE2E.Exec.Sound

set_option autoImplicit false

namespace NockvmE2E.Exec.Inst
open NockvmE2E.Exec NockvmE2E.Exec.VL NockvmE2E.Exec.V Domain

/-! ## the smooth domain -/

theorem smooth_pow {F : Type} [Field F] (n : ℕ) (ω : SmoothCosetFftDomain n F) (i : Fin (2 ^ n)) :
    ω i ^ 2 ^ n = ((ω.cosetGenerator : Fˣ) : F) ^ 2 ^ n := by
  have h1 : (Multiplicative.ofAdd i) ^ 2 ^ n = 1 := by
    have := pow_card_eq_one (G := Multiplicative (Fin (2 ^ n))) (x := Multiplicative.ofAdd i)
    simpa using this
  have h2 : (ω.subgroupDomain (Multiplicative.ofAdd i)) ^ 2 ^ n = 1 := by
    rw [← map_pow, h1, map_one]
  rw [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain, mul_pow]
  have h3 : ((ω.subgroupUnit i : Fˣ) : F) ^ 2 ^ n = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) h2
    simpa [CosetFftDomain.subgroupUnit] using this
  rw [h3, mul_one]

/-- every point of `smoothDomain n` satisfies `y^(2^n) = 7^(2^n)` -/
theorem smoothDomain_pow (n : ℕ) (hn : n ≤ 32) (i : Fin (2 ^ n)) :
    smoothDomain n hn i ^ 2 ^ n = (algebraMap (ZMod p) KC 7) ^ 2 ^ n := by
  rw [smooth_pow]
  rfl

theorem smoothDomain_apply (n : ℕ) (hn : n ≤ 32) (i : Fin (2 ^ n)) :
    smoothDomain n hn i = algebraMap (ZMod p) KC 7 * ((zeta n : KCˣ) : KC) ^ (i : ℕ) := rfl

/-! ## injectivity of `toKV` on canonical limbs -/

theorem canon_powAux : ∀ (f : ℕ) (b : UInt64) (k : ℕ) (r : UInt64), canon r → canon (VF.powAux f b k r) := by
  intro f
  induction f with
  | zero => intro b k r hr; simpa [VF.powAux] using hr
  | succ f ih =>
    intro b k r hr
    unfold VF.powAux
    by_cases h0 : (k == 0) = true
    · simpa [h0] using hr
    · simp only [h0, Bool.false_eq_true, ite_false]
      apply ih
      split
      · exact mul_lt _ _
      · exact hr

theorem canon_pow (a : UInt64) (e : ℕ) : canon (VF.pow a e) := canon_powAux _ _ _ _ Gold.one_lt

/-! ## domain link and `OffDom` -/

/-- the verifier's domain `dShift · dGen^i` is `smoothDomain nD`: `dShift = 7`, `dGen = ζ_nD` (J-8 instance data, hypotheses) -/
structure DomLink (XI : ExecInst) (hn : XI.nD ≤ 32) : Prop where
  dShift_eq : psiV XI.dShift = algebraMap (ZMod p) KC 7
  dGen_eq : psiV XI.dGen = ((zeta XI.nD : KCˣ) : KC)

theorem hω_of_domLink (XI : ExecInst) (hn : XI.nD ≤ 32) (L : DomLink XI hn) (i : Fin (2 ^ XI.nD)) :
    smoothDomain XI.nD hn i = psiV XI.dShift * psiV XI.dGen ^ (i : ℕ) := by
  rw [smoothDomain_apply, L.dShift_eq, L.dGen_eq]

/-- **`OffDom` from the verifier's check (v)**: if the verifier accepted, no opening point is a point of the domain. -/
theorem offDom_of_flatOk (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π)
    (hn : XI.nD ≤ 32) (L : DomLink XI hn) :
    ∀ pt ∈ (openPts XI (zetaOf XI FS z π)).toList, ∀ i : Fin (2 ^ XI.nD), smoothDomain XI.nD hn i ≠ toKV pt := by
  intro pt hpt i h
  have hv := flatOk_offdom XI H FS z π hok pt hpt
  have hne : pt.pow (2 ^ XI.nD) ≠ VF.K3.ofG (VF.pow XI.dShift (2 ^ XI.nD)) := by
    intro he
    have h1 : (pt.pow (2 ^ XI.nD) == VF.K3.ofG (VF.pow XI.dShift (2 ^ XI.nD))) = true := (K3_beq_iff _ _).mpr he
    simp [bne, h1] at hv
  apply hne
  apply toKV_inj _ _ (canon3_pow _ _) (canon3_ofG _ (canon_pow _ _))
  rw [toKV_pow, toKV_ofG, psiV_pow, L.dShift_eq, ← h, smoothDomain_pow]

/-! ## challenge blocks -/

/-- the coins of a challenge block: `n` consecutive `K3` of 3 limbs each, read in `KC` -/
noncomputable def decBlock (l : List ℕ) (n : ℕ) : Fin n → KC := fun i => toKV (VF.K3.ofLimbs (l.drop (3 * i.1)))

theorem toKV_k3s_get (l : List ℕ) (n : ℕ) (i : Fin n) : toKV (k3s l n)[i.1]! = decBlock l n i := by
  unfold k3s decBlock
  rw [getElem!_pos _ i.1 (by simp)]
  simp

/-- α and ζ are the (single) coins of the blocks after rounds 3 and 4 (`roundNl = 3`) -/
theorem alpha_eq_dec (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) :
    toKV (alphaOf XI FS z π) = decBlock (chalsOf XI FS z π)[3]! 1 0 := by
  simp [alphaOf, decBlock]

theorem zeta_eq_dec (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) :
    toKV (zetaOf XI FS z π) = decBlock (chalsOf XI FS z π)[4]! 1 0 := by
  simp [zetaOf, decBlock]

/-! ## the J-8-side hypothesis bundle of `deepCheck_of_flatOk'` -/

section DeepLink
open NockvmE2E.Deep NockvmE2E.Rap Polynomial
variable {Φ : CoinFrame} {ι β : Type} [Fintype KC] [DecidableEq KC] {colRound : ι → ℕ}

/-- Everything `deepCheck_of_flatOk'` needs from the J-8 instance that is NOT derivable from the verifier alone (each field is an
instance-data fact discharged per instance; none is about the proof `π` except through the decoded quantities):
* `hα`/`hζ`: the audited coins `α = χ P.a`, `ζ = χ P.z` are the decoded challenge blocks of rounds 3, 4 (`alpha_eq_dec`/`zeta_eq_dec`);
* `hlen`/`hdag`: the verifier's table terms `mult_t·cv_{t,i}` (concatenated over the tables, `termsOfK`) are the audited `A.Cv` (which carries `Zout`); the cross-toolchain data tie;
* `hH`/`hinj`: the audited trace domain `P.H` is `{hShift·hGen^i : i < hN}` (injectively);
* `he`/`hnq`/`hcw`: quotient chunks have 3 base columns each (`e = 3`), `nq` agrees, chunk weights `cw j = gen^(j%3)`;
* `hqlen`/`hQ`: the proof's `vQ` array has `nq` entries and decodes to the audited `vQ`. -/
structure DeepLink (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof)
    (P : DeepParams Φ KC ι β colRound) {r : ℕ} (A : AirShape P r) (χ : Coins Φ KC) (α ζ : KC)
    (vT : ι × Fin r → KC) (vQ : Fin P.nq → KC) : Prop where
  hα : toKV (alphaOf XI FS z π) = α
  hζ : toKV (zetaOf XI FS z π) = ζ
  hlen : (termsOfK XI FS z π).length = P.ns
  hdag : ∀ i : Fin (termsOfK XI FS z π).length, (termsOfK XI FS z π).get i = A.Cv χ ζ (Fin.cast hlen i) vT
  hH : P.H = (Finset.range XI.hN).image (fun i => psiV XI.hShift * psiV XI.hGen ^ i)
  hinj : Set.InjOn (fun i => psiV XI.hShift * psiV XI.hGen ^ i) (Finset.range XI.hN : Set ℕ)
  he : P.e = 3
  hnq : XI.nq = P.nq
  hqlen : π.vQ.size = P.nq
  hcw : ∀ j : Fin P.nq, toKV VF.K3.gen ^ (j.1 % 3) = P.cw j
  hQ : ∀ j : Fin P.nq, toKV π.vQ[j.1]! = vQ j

omit [Fintype KC] in
/-- **L10 core with the bundled J-8 link**: `FlatOk` + `AllCanon` + `DeepLink` ⇒ `DeepCheck` -/
theorem deepCheck_of_link (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof)
    (P : DeepParams Φ KC ι β colRound) {r : ℕ} (A : AirShape P r) (χ : Coins Φ KC) (α ζ : KC)
    (vT : ι × Fin r → KC) (vQ : Fin P.nq → KC) (hok : FlatOk XI H FS z π)
    (L : DeepLink XI H FS z π P A χ α ζ vT vQ) : DeepCheck P A χ α ζ vT vQ :=
  deepCheck_of_flatOk' XI H FS z π P A χ α ζ vT vQ hok L.hα L.hζ L.hlen L.hdag L.hH L.hinj L.he L.hnq L.hqlen L.hcw L.hQ

end DeepLink

/-! ## non-vacuity of the hypotheses that do not mention `P` (trivial instance `toyInst`, `hN = 1`) -/

example : Set.InjOn (fun i => psiV toyInst.hShift * psiV toyInst.hGen ^ i) (Finset.range toyInst.hN : Set ℕ) := by
  intro a ha b hb _
  simp [toyInst] at ha hb
  omega

/-- `DomLink` is satisfiable: `7` and `ζ_n` themselves (as the verifier's limbs) for `n ≤ 32` is the J-8 data; at the algebra level the
two equations are consistent (`psiV` of a canonical limb is the residue) -/
example : ∃ g : UInt64, canon g ∧ psiV g = algebraMap (ZMod p) KC 7 :=
  ⟨7, by unfold canon p; decide, by unfold psiV; exact congrArg (algebraMap (ZMod p) KC) zv_seven⟩

example (n : ℕ) (hn : n ≤ 32) (i : Fin (2 ^ n)) : smoothDomain n hn i ^ 2 ^ n = (algebraMap (ZMod p) KC 7) ^ 2 ^ n :=
  smoothDomain_pow n hn i

end NockvmE2E.Exec.Inst

#print axioms NockvmE2E.Exec.Inst.smoothDomain_pow
#print axioms NockvmE2E.Exec.Inst.smoothDomain_apply
#print axioms NockvmE2E.Exec.V.toKV_inj
#print axioms NockvmE2E.Exec.Inst.hω_of_domLink
#print axioms NockvmE2E.Exec.Inst.offDom_of_flatOk
#print axioms NockvmE2E.Exec.Inst.deepCheck_of_link
