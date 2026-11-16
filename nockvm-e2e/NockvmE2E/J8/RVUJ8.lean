/-
**`hRVU_J8`**, the public twin at J-8.

The verifier-side relation `PubJ8P` (Exec/SoundClosed.lean; `pubCheck_sound`'s conclusion plus `ComputeDerivedP`) is mapped to
nock's `PubP d χ M` (InstJ8: `PubEqJ8 ∧ hclI ∧ AbsentPubs ∧ DerivedOK`) at the message `Mof L pub` read off the verifier's
publics.  The ring `SP.Q = QuadraticAlgebra KC 7 0` embeds in nock's `Quad` by `φ` (a ring equivalence); the noun encoder
`PE.enc` is mapped to nock's `encZY` (the spec of nock's `encE`), not re-proved from scratch.
-/
import NockvmE2E.J8.InstJ8
import NockvmE2E.Exec.SoundClosed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial

namespace NockvmE2E.J8.RVUJ8

open NockvmE2E.Exec NockvmE2E.Exec.VL
open Nock.NockVMROM.Thm54.T0Tower (Quad)
open Nock.TraceGenExe (deltaF)
open NockvmE2E.J8.InstJ8 (P KQ')
open Nock.ComputeTable (FP)

attribute [local instance] Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinFact Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinAlg

/-! ## 1. `SP.Q ≃+* Quad` -/

/-- nock's concrete `KC` (the same type as the executable `Exec.KC`; the two differ only in the instance terms) -/
abbrev KN : Type := Nock.TraceGenExe.KC

/-- the identity `Exec.KC ≃ KN`, as a ring map (so that `rw`/`simp` see no instance mismatch) -/
noncomputable def cR : KC →+* KN := RingHom.id _

@[simp] theorem cR_apply (a : KC) : cR a = a := rfl

/-- nock's `δ`, inside `KN` -/
noncomputable abbrev δK : KN := algebraMap (ZMod P) KN deltaF

theorem δK_eq : δK = 7 := by
  show algebraMap (ZMod P) KN (7 : ZMod P) = 7
  exact map_ofNat _ 7

theorem mk_mul7 (a b c d : KN) : Quad.mk δK a b * Quad.mk δK c d = Quad.mk δK (a * c + 7 * (b * d)) (a * d + b * c) := by
  rw [Quad.mk_mul]; congr 1

theorem nonsq7 : ¬ IsSquare (7 : KN) := by
  have h : ¬ IsSquare δK := (Nock.TraceGenExe.deltaFact).out
  rwa [δK_eq] at h

instance factδ : Fact (¬ IsSquare δK) := Nock.TraceGenExe.deltaFact

/-- the ring map `a + b i ↦ a + b √δ` -/
noncomputable def φ : SP.Q →+* KQ' where
  toFun x := Quad.mk δK (cR x.re) (cR x.im)
  map_one' := by
    rw [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, map_one, map_zero]; exact Quad.mk_one' _
  map_zero' := by
    rw [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, map_zero]; exact Quad.mk_zero' _
  map_add' x y := by
    rw [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add, map_add, Quad.mk_add]
  map_mul' x y := by
    rw [mk_mul7, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    congr 1 <;> simp only [map_add, map_mul, map_zero, map_ofNat] <;> ring

theorem φ_mk (a b : KC) : φ (SP.qmk a b) = Quad.mk δK (cR a) (cR b) := rfl


theorem φ_injective : Function.Injective φ := by
  intro x y h
  have := (Quad.mk_eq_mk_iff δK _ _ _ _).1 h
  exact QuadraticAlgebra.ext this.1 this.2

theorem φ_surjective : Function.Surjective φ := by
  intro q
  refine ⟨SP.qmk (Quad.re (K := KN) δK q) (Quad.im (K := KN) δK q), ?_⟩
  exact Quad.mk_re_im δK q

/-- **`Q ≃+* Quad`** -/
noncomputable def φE : SP.Q ≃+* KQ' := RingEquiv.ofBijective φ ⟨φ_injective, φ_surjective⟩

theorem nonsq7C : ¬ IsSquare (7 : KC) := by
  intro h
  obtain ⟨r, hr⟩ := h
  exact nonsq7 ⟨cR r, by have := congrArg cR hr; rw [map_ofNat, map_mul] at this; exact this⟩

theorem φ_qinv (x : SP.Q) : φ (SP.qinv x) = (φ x)⁻¹ := by
  by_cases hx : x = 0
  · subst hx
    have : SP.qinv 0 = 0 := by
      apply QuadraticAlgebra.ext <;> simp [SP.qinv]
    rw [this, map_zero, inv_zero]
  · have hn : x.re * x.re - 7 * (x.im * x.im) ≠ 0 := by
      intro h0
      by_cases hi : x.im = 0
      · rw [hi] at h0
        have : x.re = 0 := by simpa using h0
        exact hx (QuadraticAlgebra.ext this hi)
      · apply nonsq7C
        refine ⟨x.re / x.im, ?_⟩
        have : (7 : KC) * (x.im * x.im) = x.re * x.re := by linear_combination -h0
        field_simp
        linear_combination this
    have h1 : x * SP.qinv x = 1 := by
      apply QuadraticAlgebra.ext
      · simp only [QuadraticAlgebra.re_mul, SP.qinv, QuadraticAlgebra.re_one]
        refine Eq.trans ?_ (mul_inv_cancel₀ hn)
        ring
      · simp only [QuadraticAlgebra.im_mul, SP.qinv, QuadraticAlgebra.im_one]
        ring
    have := congrArg φ h1
    rw [map_mul, map_one] at this
    exact (inv_eq_of_mul_eq_one_right this).symm

theorem φ_compress {m : ℕ} (γ ρ : SP.Q) (v : Fin m → SP.Q) :
    φ (SP.compressQ γ ρ v) =
      Nock.NockVMROM.Thm54.FiniteIO.compress (⟨φ γ, φ ρ⟩ : Nock.NockVMROM.Thm54.FiniteIO.IOCoins KQ') (fun c => φ (v c)) := by
  unfold SP.compressQ Nock.NockVMROM.Thm54.FiniteIO.compress Nock.Walk.rlc
  simp [map_add, map_sum, map_mul, map_pow]


/-! ## 2. The noun encoder twin: `PE.enc` against nock's `encZY` (the spec of `encE`) -/

/-- an executable `K6` as an element of nock's `Quad` -/
noncomputable def ψ (a : PE.K6) : KQ' := φ (SP.toQ6 a)

theorem ψ_add (a b : PE.K6) (ha : SP.canon6 a) (hb : SP.canon6 b) : ψ (PE.K6.add a b) = ψ a + ψ b := by
  unfold ψ; rw [SP.toQ6_add _ _ ha hb, map_add]

theorem ψ_mul (a b : PE.K6) : ψ (PE.K6.mul a b) = ψ a * ψ b := by
  unfold ψ; rw [SP.toQ6_mul, map_mul]

theorem ψ_inv0 (a : PE.K6) : ψ (PE.K6.inv0 a) = (ψ a)⁻¹ := by
  unfold ψ; rw [SP.toQ6_inv0, φ_qinv]

theorem ψ_zero : ψ PE.K6.zero = 0 := by unfold ψ; rw [SP.toQ6_zero, map_zero]

theorem cR_alg (x : ZMod P) : cR (algebraMap (ZMod NockvmE2E.Exec.p) KC x) = algebraMap (ZMod P) KN x :=
  congrArg (fun f : ZMod P →+* KN => f x)
    (RingHom.ext_zmod (cR.comp (algebraMap (ZMod NockvmE2E.Exec.p) KC)) (algebraMap (ZMod P) KN))

theorem emb_eq (x : ZMod P) :
    algebraMap Nock.Atoms.Fp KQ' x = algebraMap KN KQ' (algebraMap (ZMod P) KN x) :=
  congrArg (fun f : ZMod P →+* KQ' => f x)
    (RingHom.ext_zmod (algebraMap Nock.Atoms.Fp KQ') ((algebraMap KN KQ').comp (algebraMap (ZMod P) KN)))

theorem ψ_base (x : UInt64) : ψ (PE.K6.base x) = algebraMap Nock.Atoms.Fp KQ' (zv x) := by
  unfold ψ
  show Quad.mk δK (cR (toKV (VF.K3.ofG x))) (cR (toKV VF.K3.zero)) = _
  rw [toKV_ofG, toKV_zero, map_zero, Quad.mk_base]
  refine Eq.trans ?_ (emb_eq (zv x)).symm
  congr 1

theorem zv_ofNat (a : ℕ) (h : a < 18446744073709551616) : zv (UInt64.ofNat a) = (a : ZMod P) := by
  unfold zv
  rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64.size]; exact h)]
  rfl

theorem PN_eq : VF.PN = Nock.Atoms.p := by
  unfold VF.PN Nock.Atoms.p Nock.Field.p; norm_num

theorem limbsAux_digits : ∀ (f n : ℕ), n < 4294967296 ^ f → PE.limbsAux f n = Nat.digits 4294967296 n
  | 0, n, h => by
      have : n = 0 := by simpa using h
      subst this; simp [PE.limbsAux]
  | f + 1, n, h => by
      unfold PE.limbsAux
      by_cases h0 : n = 0
      · subst h0; simp
      · have h1 : n / 4294967296 < 4294967296 ^ f := by
          rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [Nat.pow_succ] at h; exact h
        rw [if_neg (by simpa using h0), limbsAux_digits f _ h1, Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero h0)]

theorem limbs32_eq (n : ℕ) : PE.limbs32 n = Nock.Atoms.limbs n := by
  unfold PE.limbs32 Nock.Atoms.limbs Nock.Atoms.B
  have hn : n < 4294967296 ^ (n.log2 / 32 + 2) := by
    have h1 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
    refine lt_of_lt_of_le h1 ?_
    rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [limbsAux_digits _ _ hn]
  norm_num

theorem aeval_limbPoly_cons (y : KQ') (a : ℕ) (l : List ℕ) :
    aeval y (Nock.Atoms.limbPoly (a :: l)) =
      algebraMap Nock.Atoms.Fp KQ' (a : Nock.Atoms.Fp) + y * aeval y (Nock.Atoms.limbPoly l) := by
  have e : Nock.Atoms.limbPoly (a :: l) = Polynomial.C (a : Nock.Atoms.Fp) + Polynomial.X * Nock.Atoms.limbPoly l := by
    simp [Nock.Atoms.limbPoly, Nock.Atoms.natPoly, Polynomial.map_add, Polynomial.map_mul]
  rw [e, map_add, map_mul, aeval_C, aeval_X]

theorem hornerL_spec (y : PE.K6) (hy : SP.canon6 y) :
    ∀ l : List ℕ, (∀ a ∈ l, a < 4294967296) →
      ψ (PE.hornerL y l) = aeval (ψ y) (Nock.Atoms.limbPoly l)
  | [], _ => by
      simp [PE.hornerL, ψ_zero, Nock.Atoms.limbPoly, Nock.Atoms.natPoly]
  | a :: l, h => by
      have ha : a < 4294967296 := h a (by simp)
      have hl : ∀ b ∈ l, b < 4294967296 := fun b hb => h b (by simp [hb])
      have hc : SP.canon6 (PE.K6.base (UInt64.ofNat a)) := SP.canon6_base _ (SP.canon_ofNat a (by unfold VF.PN; omega))
      unfold PE.hornerL
      rw [ψ_add _ _ hc (SP.canon6_mul _ _), ψ_mul, hornerL_spec y hy l hl, ψ_base,
        zv_ofNat a (by omega), aeval_limbPoly_cons]

theorem leafE_spec (y : PE.K6) (hy : SP.canon6 y) (n : ℕ) :
    ψ (PE.leafE y n) = Nock.Atoms.leafVal (ψ y) n := by
  unfold PE.leafE Nock.Atoms.leafVal Nock.Atoms.L
  by_cases h : n < VF.PN
  · have h' : n < Nock.Atoms.p := PN_eq ▸ h
    rw [if_pos h, if_pos h', ψ_base, zv_ofNat n (by unfold VF.PN at h; omega), aeval_C]
  · have h' : ¬ n < Nock.Atoms.p := PN_eq ▸ h
    have hlim : ∀ a ∈ PE.limbs32 n, a < 4294967296 := SP.limbsAux_lt _ _
    rw [if_neg h, if_neg h', hornerL_spec y hy _ hlim, limbs32_eq]

/-- the noun as prefix tokens -/
def toks : Nock.Noun → List PE.Tok
  | .atom n => [.atom n]
  | .cell a b => .cell :: (toks a ++ toks b)

/-- one `cell` step of the stack machine -/
def fpCons (z zinv : PE.K6) (a b : PE.Fp3) : PE.Fp3 :=
  ⟨PE.K6.mul a.size b.size,
   PE.K6.add (PE.K6.add (PE.K6.mul z a.dyck) (PE.K6.mul (PE.K6.mul a.size a.size) zinv))
     (PE.K6.mul (PE.K6.mul a.size a.size) b.dyck),
   PE.K6.add a.leaf (PE.K6.mul a.size b.leaf)⟩

/-- the fingerprint the stack machine computes -/
def fpOf (z zinv y : PE.K6) : Nock.Noun → PE.Fp3
  | .atom n => ⟨z, PE.K6.zero, PE.leafE y n⟩
  | .cell a b => fpCons z zinv (fpOf z zinv y a) (fpOf z zinv y b)

theorem run_toks (z zinv y : PE.K6) : ∀ (n : Nock.Noun) (s : List PE.Fp3),
    (toks n).reverse.foldl (PE.encStep z zinv y) (some s) = some (fpOf z zinv y n :: s)
  | .atom n, s => by simp [toks, PE.encStep, fpOf]
  | .cell a b, s => by
      simp only [toks, List.reverse_cons, List.reverse_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [run_toks z zinv y b, run_toks z zinv y a]
      simp [PE.encStep, fpOf, fpCons]

theorem enc_toks (z y : PE.K6) (n : Nock.Noun) : PE.enc z y (toks n) = some (fpOf z z.inv0 y n) := by
  unfold PE.enc
  rw [run_toks]

/-- the fingerprint in nock's `FP` -/
noncomputable def φFp (e : PE.Fp3) : FP KQ' := ⟨ψ e.size, ψ e.dyck, ψ e.leaf⟩

theorem fpOf_can (z y : PE.K6) (hz : SP.canon6 z) (hy : SP.canon6 y) (n : Nock.Noun) :
    SP.FpCan (fpOf z z.inv0 y n) :=
  SP.enc_can z y hz hy _ _ (enc_toks z y n)

theorem encZY_spec (z y : PE.K6) (hz : SP.canon6 z) (hy : SP.canon6 y) :
    ∀ n : Nock.Noun, φFp (fpOf z z.inv0 y n) = Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8.encZY (ψ z) (ψ y) n
  | .atom n => by
      show (⟨ψ z, ψ PE.K6.zero, ψ (PE.leafE y n)⟩ : FP KQ') = FP.atomFP _ _
      rw [ψ_zero, leafE_spec y hy]; rfl
  | .cell a b => by
      have ha := fpOf_can z y hz hy a
      have hb := fpOf_can z y hz hy b
      have iha := encZY_spec z y hz hy a
      have ihb := encZY_spec z y hz hy b
      show φFp (fpCons z z.inv0 (fpOf z z.inv0 y a) (fpOf z z.inv0 y b)) = FP.cons _ (Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8.encZY (ψ z) (ψ y) a)
        (Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8.encZY (ψ z) (ψ y) b)
      rw [← iha, ← ihb]
      unfold φFp FP.cons fpCons
      simp only []
      rw [ψ_add _ _ (SP.canon6_add _ _ (SP.canon6_mul _ _) (SP.canon6_mul _ _)) (SP.canon6_mul _ _),
        ψ_add _ _ (SP.canon6_mul _ _) (SP.canon6_mul _ _), ψ_add _ _ ha.2.2 (SP.canon6_mul _ _)]
      simp only [ψ_mul, ψ_inv0]


/-! ## 3. Records -/

open Nock.NockVMROM.Thm54.VclL.Handle in
theorem claimVec_spec (e : PE.Fp3) (idx hi lo : ℕ) (hidx : idx < 18446744073709551616) (hhi : hi < 18446744073709551616)
    (hlo : lo < 18446744073709551616) :
    (fun c : Fin 5 => ψ ((PE.claimVec e idx hi lo).getD c PE.K6.zero)) =
      ClaimVS.claimVec (F := ZMod P) (K := KN) deltaF (φFp e) (idx : ZMod P) (hi : ZMod P) (lo : ZMod P) := by
  funext c
  fin_cases c
  · rfl
  · rfl
  · rfl
  · show ψ ⟨VF.K3.ofG (UInt64.ofNat lo), VF.K3.ofG (UInt64.ofNat hi)⟩ = _
    show Quad.mk δK (cR (toKV (VF.K3.ofG (UInt64.ofNat lo)))) (cR (toKV (VF.K3.ofG (UInt64.ofNat hi)))) = _
    rw [toKV_ofG, toKV_ofG]
    refine Eq.trans (congrArg₂ (Quad.mk δK) (cR_alg (zv (UInt64.ofNat lo))) (cR_alg (zv (UInt64.ofNat hi)))) ?_
    rw [zv_ofNat _ hlo, zv_ofNat _ hhi]
    rfl
  · show ψ (PE.K6.base (UInt64.ofNat idx)) = _
    rw [ψ_base, zv_ofNat _ hidx, emb_eq, ← Quad.mk_base]
    rfl


theorem tlF_pinKey (id idx : ℕ) :
    Nock.Jet.RapJetJ8.tlF (Nock.Jet.PinJ8.pinKey (F := ZMod P) id idx) =
      [(id : ZMod P), 1, (idx : ZMod P), 0, 0, 0, 0, ((2 : ℕ) : ZMod P)] := by
  simp [Nock.Jet.RapJetJ8.tlF, Nock.Jet.PinJ8.pinKey]

theorem pinCons_spec (id idx : ℕ) (hid : id < 18446744073709551616) (hidx : idx < 18446744073709551616) :
    (fun c : Fin 8 => ψ ((PE.pinConsKey id idx).getD c PE.K6.zero)) =
      Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ.liftRec (L := KQ')
        (Nock.Jet.RapJetJ8.keyK (K := KN) 8 (Nock.Jet.RapJetJ8.tlF (Nock.Jet.PinJ8.pinKey (F := ZMod P) id idx))) := by
  rw [tlF_pinKey]
  have h1 : ∀ v : ℕ, v < 18446744073709551616 → ψ (PE.K6.base (UInt64.ofNat v)) = algebraMap KN KQ' (algebraMap (ZMod P) KN (v : ZMod P)) := by
    intro v hv
    rw [ψ_base, zv_ofNat _ hv, emb_eq]
  funext c
  fin_cases c
  · exact h1 id hid
  · exact h1 1 (by norm_num)
  · exact h1 idx hidx
  · exact h1 0 (by norm_num)
  · exact h1 0 (by norm_num)
  · exact h1 0 (by norm_num)
  · exact h1 0 (by norm_num)
  · exact h1 2 (by norm_num)


theorem mapM_cons_some {α β : Type} (f : α → Option β) (a : α) (l : List α) (r : List β)
    (h : (a :: l).mapM f = some r) : ∃ b rs, f a = some b ∧ l.mapM f = some rs ∧ r = b :: rs := by
  rw [List.mapM_cons] at h
  rcases hf : f a with _ | b0
  · simp [hf] at h
  rcases hl : l.mapM f with _ | r0
  · simp [hf, hl] at h
  simp only [hf, hl, bind, Option.bind, pure, Option.some.injEq] at h
  exact ⟨b0, r0, rfl, rfl, h.symm⟩

theorem claimRecS_cell (z y : PE.K6) (x : Array UInt64) (k : Fin 3) (a b : Nock.Noun) (hi lo : ℕ) (r : List PE.K6)
    (h : SP.claimRecS z y x ⟨k.val, toks (.cell a b), 0, hi, lo⟩ = some r) :
    SP.labelOf x (2 * k.val) = 1 ∧
      r = PE.claimVec (fpOf z z.inv0 y (.cell a b)) (SP.labelOf x (2 * k.val + 1)) hi lo := by
  unfold SP.claimRecS at h
  simp only [toks] at h
  have hk : ¬ (k.val > 2) := by omega
  by_cases hl : SP.labelOf x (2 * k.val) = 1
  · refine ⟨hl, ?_⟩
    simp only [hk, hl, decide_false, Bool.false_or, bne_self_eq_false, Bool.false_eq_true, if_false] at h
    rw [show (toks a ++ toks b) = toks a ++ toks b from rfl] at h
    have he := enc_toks z y (.cell a b)
    simp only [toks] at he
    rw [he] at h
    simp only [bind, Option.bind, pure, Option.some.injEq] at h
    exact h.symm
  · exfalso
    simp [hk, hl] at h


open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (rkC claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN claimH labelF hvalF ClaimMsgVS)

/-- the executable claim record of claim position `k` (`key = k`, rank halves of the noun; the serial is read from the labels) -/
def claimRec (nn : Fin 3 → Nock.Noun) (k : Fin 3) : PE.NounRec :=
  ⟨k.val, toks (nn k), 0, (rkC (nn k)).1, (rkC (nn k)).2⟩

theorem claimRecS_cell' (z y : PE.K6) (x : Array UInt64) (k : Fin 3) (n : Nock.Noun) (hc : isCellN n = true) (hi lo : ℕ)
    (r : List PE.K6) (h : SP.claimRecS z y x ⟨k.val, toks n, 0, hi, lo⟩ = some r) :
    SP.labelOf x (2 * k.val) = 1 ∧
      r = PE.claimVec (fpOf z z.inv0 y n) (SP.labelOf x (2 * k.val + 1)) hi lo := by
  cases n with
  | atom v => simp [isCellN] at hc
  | cell a b => exact claimRecS_cell z y x k a b hi lo r h

theorem claims_mapM (z y : PE.K6) (x : Array UInt64) (nn : Fin 3 → Nock.Noun) :
    ∀ (ks : List (Fin 3)), (∀ k ∈ ks, isCellN (nn k) = true) → ∀ r : List (List PE.K6),
      (ks.map (claimRec nn)).mapM (SP.claimRecS z y x) = some r →
      (∀ k ∈ ks, SP.labelOf x (2 * k.val) = 1) ∧
        r = ks.map (fun k => PE.claimVec (fpOf z z.inv0 y (nn k)) (SP.labelOf x (2 * k.val + 1)) (rkC (nn k)).1 (rkC (nn k)).2)
  | [], _, r, h => by
      simp only [List.map_nil, List.mapM_nil, pure, Option.some.injEq] at h
      subst h; simp
  | k :: ks, hk, r, h => by
      rw [List.map_cons] at h
      obtain ⟨b, rs, hb, hrs, rfl⟩ := mapM_cons_some _ _ _ _ h
      have h1 := claimRecS_cell' z y x k (nn k) (hk k (by simp)) _ _ b hb
      have h2 := claims_mapM z y x nn ks (fun k' hk' => hk k' (by simp [hk'])) rs hrs
      refine ⟨fun k' hk' => ?_, ?_⟩
      · rcases List.mem_cons.1 hk' with rfl | hk'
        · exact h1.1
        · exact h2.1 k' hk'
      · rw [List.map_cons, h1.2, h2.2]

theorem pins_mapM (z y : PE.K6) (nn : ℕ → Nock.Noun) (idx hi lo : ℕ → ℕ) :
    ∀ l : List ℕ, (l.map fun id => (⟨id, toks (nn id), idx id, hi id, lo id⟩ : PE.NounRec)).mapM (SP.pinRecS z y) =
      some (l.map fun id => PE.claimVec (fpOf z z.inv0 y (nn id)) (idx id) (hi id) (lo id))
  | [] => by simp
  | id :: l => by
      rw [List.map_cons, List.mapM_cons, pins_mapM z y nn idx hi lo l]
      simp [SP.pinRecS, enc_toks]


/-! ## 4. Coordinates of a verifier `K3` -/

/-- a canonical verifier `K3` as nock's executable `K3` -/
def n3 (x : VF.K3) (hx : canon3 x) : Nock.TraceGenExe.K3 := ⟨⟨x.c0, hx.1⟩, ⟨x.c1, hx.2.1⟩, ⟨x.c2, hx.2.2⟩⟩

theorem toKV_n3 (x : VF.K3) (hx : canon3 x) : toKV x = Nock.TraceGenExe.K3.toK (n3 x hx) := rfl

/-- **the coordinates of `toKV x` against nock's power basis are the limbs of `x`** -/
theorem coord_toKV (x : VF.K3) (hx : canon3 x) (k : Fin 3) :
    Nock.NockVMROM.Thm54.CoordinateBasis.coord Nock.TraceGenExe.powerBasis3 (toKV x) k = ![zv x.c0, zv x.c1, zv x.c2] k := by
  rw [toKV_n3 x hx, Nock.TraceGenExe.coord_powerBasis3_toK]
  rfl


/-! ## 5. The message and the public equations -/

open NockvmE2E.J8.InstJ8 (Datum DatumOK Msg StmtP PubP Φ0)
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')

/-- **the J-8 message read off the verifier's publics**: serials from the compute labels, `ρ`, `ρS` and the compute publics from
the compute slice, the five chip slices (K-values, zero-filled for an absent table by `slOf`) -/
noncomputable def Mof (L : PE.PubLayout) (pub : Array UInt64) : Msg :=
  (⟨fun k => ((SP.slOf L pub 0)[2 * k.val + 1]!.toNat, 0, 0),
    fun i => φ (SP.rhoOf (SP.slOf L pub 0) i), φ (SP.rhoSOf (SP.slOf L pub 0)),
    SP.pubK (SP.slOf L pub 1), SP.pubK (SP.slOf L pub 2), SP.pubK (SP.slOf L pub 3),
    SP.pubK (SP.slOf L pub 4), SP.pubK (SP.slOf L pub 5)⟩,
   fun j => (zv (SP.slOf L pub 0)[j.val]! : ZMod P))

/-- **the datum link** (instance data = the claim and the registry of the J-8 datum; a per-program `decide`/`rfl`): the verifier's
claim cells are the cell nouns of the claim, its pins the registry templates, its atoms the atom nouns of the claim -/
structure InpLink (d : Datum) (inp : PE.PubIn) : Prop where
  hcl : inp.claimCells = (claimCells d.c).map (claimRec (claimNoun d.c))
  hpin : inp.pins = d.Pb.regs.map (fun id => (⟨id, toks (Nock.Jet.Autogen.compile P (d.Pb.Rt id)), d.Pb.idx id,
    (d.Pb.rk id).1, (d.Pb.rk id).2⟩ : PE.NounRec))
  hat : inp.atoms = (List.finRange 3).filterMap (fun k => match claimNoun d.c k with
    | .atom v => some (k.val, v) | .cell _ _ => none)

theorem sum_map_φ {α : Type} (l : List α) (f : α → SP.Q) : φ (l.map f).sum = (l.map (fun a => φ (f a))).sum := by
  rw [map_list_sum, List.map_map]; rfl


theorem coinsOf_can (slots : Array VF.K3) (slotOf : Array ℕ) (hs : ∀ s ∈ slots, canon3 s) :
    ∀ i : ℕ, canon3 (SP.coinsOf slots slotOf)[i]! := by
  refine SP.canon_getBang canon3 SP.canon3_default _ ?_
  intro g hg
  unfold SP.coinsOf at hg
  rw [Array.mem_map] at hg
  obtain ⟨i, _, rfl⟩ := hg
  exact SP.canon_getBang canon3 SP.canon3_default slots hs _

theorem ringChar_P : ringChar (ZMod P) = P := ZMod.ringChar_zmod_n _

theorem P_lt : P < 18446744073709551616 := by
  show Nock.Field.p < _
  unfold Nock.Field.p; norm_num

open Nock.NockVMROM.Thm54.VclL.Handle in
theorem inv_comp {m : ℕ} (l : List (Fin m → SP.Q)) (γ ρ : SP.Q) :
    φ ((l.map fun r => SP.qinv (SP.compressQ γ ρ r)).sum) =
      ((l.map fun r c => φ (r c)).map fun v =>
        (Nock.NockVMROM.Thm54.FiniteIO.compress (⟨φ γ, φ ρ⟩ : Nock.NockVMROM.Thm54.FiniteIO.IOCoins KQ') v)⁻¹).sum := by
  rw [sum_map_φ, List.map_map]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply, φ_qinv, φ_compress]

theorem pinConsR_eq (regs : List ℕ) (idx : ℕ → ℕ) (h : ∀ id ∈ regs, id < 18446744073709551616 ∧ idx id < 18446744073709551616) :
    ((regs.map fun id => (SP.recQ (PE.pinConsKey id (idx id)) : Fin 8 → SP.Q)).map fun r c => φ (r c)) =
      (Nock.Jet.PinJ8.pinCons (p := P) (K := KN) regs idx).map
        fun r => Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ.liftRec (L := KQ') r := by
  unfold Nock.Jet.PinJ8.pinCons
  simp only [List.map_map]
  refine List.map_congr_left fun id hid => ?_
  exact pinCons_spec id (idx id) (h id hid).1 (h id hid).2

open Nock.NockVMROM.Thm54.VclL.Handle in
theorem claimRecs_eq (d : Datum) (hS : StmtP d) (z y : PE.K6) (hz : SP.canon6 z) (hy : SP.canon6 y)
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins FrameJ8.frameJ8 KN) (hzψ : ψ z = Quad.mk δK (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c2) (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c3))
    (hyψ : ψ y = Quad.mk δK (χ FrameJ8.cY1) (χ FrameJ8.cY2)) (x : Array UInt64) (hx : SP.ArrCan x) :
    ((claimCells d.c).map fun k => PE.claimVec (fpOf z z.inv0 y (claimNoun d.c k)) (SP.labelOf x (2 * k.val + 1))
        (rkC (claimNoun d.c k)).1 (rkC (claimNoun d.c k)).2).map (fun r => fun c : Fin 5 => φ (SP.recQ r c)) =
      AcceptsJ8P.claimRecsJ8 (K := KN) deltaF χ d.c (fun k => (x[2 * k.val + 1]!.toNat, 0, 0)) := by
  unfold AcceptsJ8P.claimRecsJ8
  rw [List.map_map]
  refine List.map_congr_left fun k hk => ?_
  have hcell : isCellN (claimNoun d.c k) = true := by
    unfold claimCells at hk
    exact (List.mem_filter.1 hk).2
  have hrk := hS.hclR k hcell
  have hlab : SP.labelOf x (2 * k.val + 1) < 18446744073709551616 := by
    have := hx (2 * k.val + 1)
    unfold SP.labelOf canon at *
    have h2 := P_lt
    have h3 : NockvmE2E.Exec.p = P := rfl
    omega
  have hhi : (rkC (claimNoun d.c k)).1 < 18446744073709551616 := lt_trans hrk P_lt
  have hlo : (rkC (claimNoun d.c k)).2 < 18446744073709551616 := by
    have : (rkC (claimNoun d.c k)).2 < 2 ^ 62 := Nat.mod_lt _ (by norm_num)
    omega
  have e1 := claimVec_spec (fpOf z z.inv0 y (claimNoun d.c k)) (SP.labelOf x (2 * k.val + 1)) _ _ hlab hhi hlo
  have e2 := encZY_spec z y hz hy (claimNoun d.c k)
  rw [hzψ, hyψ] at e2
  show (fun c : Fin 5 => ψ ((PE.claimVec _ _ _ _).getD c PE.K6.zero)) = _
  rw [e1, e2]
  rfl


open Nock.NockVMROM.Thm54.VclL.Handle in
theorem pinRecs_eq (d : Datum) (hS : StmtP d) (z y : PE.K6) (hz : SP.canon6 z) (hy : SP.canon6 y)
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins FrameJ8.frameJ8 KN)
    (hzψ : ψ z = Quad.mk δK (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c2) (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c3))
    (hyψ : ψ y = Quad.mk δK (χ FrameJ8.cY1) (χ FrameJ8.cY2)) :
    (d.Pb.regs.map fun id => PE.claimVec (fpOf z z.inv0 y (Nock.Jet.Autogen.compile P (d.Pb.Rt id))) (d.Pb.idx id)
        (d.Pb.rk id).1 (d.Pb.rk id).2).map (fun r => fun c : Fin 5 => φ (SP.recQ r c)) =
      AcceptsJ8P.pinRecsJ8 (K := KN) deltaF d.Pb χ := by
  unfold AcceptsJ8P.pinRecsJ8
  rw [List.map_map]
  refine List.map_congr_left fun id hid => ?_
  have hl := hS.hlt id hid
  rw [ringChar_P] at hl
  have hi : d.Pb.idx id < 18446744073709551616 := lt_trans hl.2.2 P_lt
  have hh : (d.Pb.rk id).1 < 18446744073709551616 := lt_trans hl.1 P_lt
  have hlo : (d.Pb.rk id).2 < 18446744073709551616 := lt_trans hl.2.1 P_lt
  have e1 := claimVec_spec (fpOf z z.inv0 y (Nock.Jet.Autogen.compile P (d.Pb.Rt id))) (d.Pb.idx id) _ _ hi hh hlo
  have e2 := encZY_spec z y hz hy (Nock.Jet.Autogen.compile P (d.Pb.Rt id))
  rw [hzψ, hyψ] at e2
  show (fun c : Fin 5 => ψ ((PE.claimVec _ _ _ _).getD c PE.K6.zero)) = _
  rw [e1, e2]

theorem pubEq_of_P (d : Datum) (hS : StmtP d) (inp : PE.PubIn) (hlink : InpLink d inp) (L : PE.PubLayout)
    (slotOf : Array ℕ) (slots : Array VF.K3) (pub : Array UInt64) (hs : ∀ s ∈ slots, canon3 s) (hp : ∀ g ∈ pub, canon g)
    (hids : ∀ id ∈ d.Pb.regs, id < P)
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins FrameJ8.frameJ8 KN) (hχ : ∀ i : Fin 19, χ i = toKV (SP.coinsOf slots slotOf)[i.val]!)
    (hP : NockvmE2E.Merkle.RapFriQ.PubJ8P inp L slotOf slots pub) :
    Nock.V1J8.PubEqJ8 deltaF Nock.TraceGenExe.powerBasis3 d.Pb d.c χ (Mof L pub).1 := by
  obtain ⟨⟨cr, pr, hcr, hpr, hrel⟩, -⟩ := hP
  have hc := coinsOf_can slots slotOf hs
  have hx : SP.ArrCan (SP.slOf L pub 0) := SP.slOf_can L pub hp 0
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrel
  have hz : SP.canon6 ⟨(SP.coinsOf slots slotOf)[2]!, (SP.coinsOf slots slotOf)[3]!⟩ := ⟨hc 2, hc 3⟩
  have hy : SP.canon6 ⟨(SP.coinsOf slots slotOf)[17]!, (SP.coinsOf slots slotOf)[18]!⟩ := ⟨hc 17, hc 18⟩
  have hzψ : ψ ⟨(SP.coinsOf slots slotOf)[2]!, (SP.coinsOf slots slotOf)[3]!⟩ =
      Quad.mk δK (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c2) (χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c3) := by
    have e2 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c2 = toKV (SP.coinsOf slots slotOf)[2]! := hχ ⟨2, (by norm_num : 2 < 19)⟩
    have e3 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c3 = toKV (SP.coinsOf slots slotOf)[3]! := hχ ⟨3, (by norm_num : 3 < 19)⟩
    rw [e2, e3]; rfl
  have hyψ : ψ ⟨(SP.coinsOf slots slotOf)[17]!, (SP.coinsOf slots slotOf)[18]!⟩ =
      Quad.mk δK (χ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.cY1) (χ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.cY2) := by
    have e2 : χ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.cY1 = toKV (SP.coinsOf slots slotOf)[17]! := hχ ⟨17, (by norm_num : 17 < 19)⟩
    have e3 : χ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.cY2 = toKV (SP.coinsOf slots slotOf)[18]! := hχ ⟨18, (by norm_num : 18 < 19)⟩
    rw [e2, e3]; rfl
  -- the records
  rw [hlink.hcl] at hcr
  have hcells : ∀ k ∈ claimCells d.c, isCellN (claimNoun d.c k) = true := fun k hk => by
    unfold claimCells at hk; exact (List.mem_filter.1 hk).2
  obtain ⟨-, hcr'⟩ := claims_mapM _ _ (SP.slOf L pub 0) (claimNoun d.c) (claimCells d.c) hcells cr hcr
  have hpm := pins_mapM ⟨(SP.coinsOf slots slotOf)[2]!, (SP.coinsOf slots slotOf)[3]!⟩
    ⟨(SP.coinsOf slots slotOf)[17]!, (SP.coinsOf slots slotOf)[18]!⟩ (fun id => Nock.Jet.Autogen.compile P (d.Pb.Rt id))
    d.Pb.idx (fun id => (d.Pb.rk id).1) (fun id => (d.Pb.rk id).2) d.Pb.regs
  rw [hlink.hpin] at hpr
  have hpr'' := Option.some.inj (hpr.symm.trans hpm)
  have hb : ∀ id ∈ d.Pb.regs, id < 18446744073709551616 ∧ d.Pb.idx id < 18446744073709551616 := fun id hid =>
    ⟨lt_trans (hids id hid) P_lt, by have := (hS.hlt id hid).2.2; rw [ringChar_P] at this; exact lt_trans this P_lt⟩
  have hg : FrameVSQ.gamHQ deltaF (FrameJ8.toVSQ χ) = φ (SP.qmk (toKV (SP.coinsOf slots slotOf)[11]!) (toKV (SP.coinsOf slots slotOf)[15]!)) := by
    have e2 : χ ⟨11, (by norm_num : 11 < 19)⟩ = toKV (SP.coinsOf slots slotOf)[11]! := hχ ⟨11, (by norm_num : 11 < 19)⟩
    have e3 : χ ⟨15, (by norm_num : 15 < 19)⟩ = toKV (SP.coinsOf slots slotOf)[15]! := hχ ⟨15, (by norm_num : 15 < 19)⟩
    show Quad.mk _ (χ ⟨11, _⟩) (χ ⟨15, _⟩) = _
    rw [e2, e3]; rfl
  have hr : FrameVSQ.rhoHQ deltaF (FrameJ8.toVSQ χ) = φ (SP.qmk (toKV (SP.coinsOf slots slotOf)[12]!) (toKV (SP.coinsOf slots slotOf)[16]!)) := by
    have e2 : χ ⟨12, (by norm_num : 12 < 19)⟩ = toKV (SP.coinsOf slots slotOf)[12]! := hχ ⟨12, (by norm_num : 12 < 19)⟩
    have e3 : χ ⟨16, (by norm_num : 16 < 19)⟩ = toKV (SP.coinsOf slots slotOf)[16]! := hχ ⟨16, (by norm_num : 16 < 19)⟩
    show Quad.mk _ (χ ⟨12, _⟩) (χ ⟨16, _⟩) = _
    rw [e2, e3]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, h6, h7, h8⟩
  · have e := congrArg φ h1
    rw [map_add, map_add, φ_mk, φ_mk, φ_mk] at e
    exact e
  · have e := congrArg φ h2
    rw [φ_mk] at e
    exact e
  · have hpc : (inp.pins.map fun q => (SP.recQ (PE.pinConsKey q.key q.idx) : Fin 8 → SP.Q)) =
        d.Pb.regs.map fun id => SP.recQ (PE.pinConsKey id (d.Pb.idx id)) := by
      rw [hlink.hpin, List.map_map]; rfl
    rw [hpc] at h3
    have e := congrArg φ h3
    rw [map_add, map_add, map_add, inv_comp, pinConsR_eq _ _ hb, List.map_map] at e
    rw [VerJ8.coinsCV_J8, hg, hr]
    exact e
  · have e4 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c4 = toKV (SP.coinsOf slots slotOf)[4]! := hχ ⟨4, (by norm_num : 4 < 19)⟩
    have e5 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c5 = toKV (SP.coinsOf slots slotOf)[5]! := hχ ⟨5, (by norm_num : 5 < 19)⟩
    have e6 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c6 = toKV (SP.coinsOf slots slotOf)[6]! := hχ ⟨6, (by norm_num : 6 < 19)⟩
    have e7 : χ Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.c7 = toKV (SP.coinsOf slots slotOf)[7]! := hχ ⟨7, (by norm_num : 7 < 19)⟩
    have hmap : ∀ (l : List (List PE.K6)), (l.map fun r => (SP.recQ r : Fin 5 → SP.Q)).map (fun r c => φ (r c)) =
        l.map (fun r => fun c : Fin 5 => φ (SP.recQ r c)) := by
      intro l; rw [List.map_map]; rfl
    have e := congrArg φ h4
    rw [map_add, inv_comp, List.map_append, hmap, hmap, hcr'] at e
    rw [hpr''] at e
    rw [claimRecs_eq d hS _ _ hz hy χ hzψ hyψ _ hx, pinRecs_eq d hS _ _ hz hy χ hzψ hyψ] at e
    rw [e4, e5, e6, e7]
    exact e
  · have e := congrArg φ h5
    rw [map_add, φ_mk, φ_mk, φ_mk] at e
    exact e


/-! ## 6. `DerivedOK`: the compute publics against `pubVJ8` -/

/-- `zv` as an element of nock's `ZMod P` (the same type; the two literals `p`, `P` differ syntactically) -/
abbrev zP (a : UInt64) : ZMod P := zv a

def mOf (x : Array UInt64) : ClaimMsgVS := fun k => (x[2 * k.val + 1]!.toNat, 0, 0)

noncomputable def ρOf (x : Array UInt64) : Fin 5 → KQ' := fun i => φ (SP.rhoOf x i)

noncomputable def ρSOf (x : Array UInt64) : KQ' := φ (SP.rhoSOf x)

theorem hk_facts (d : Datum) (hS : StmtP d) (x : Array UInt64)
    (hat : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v → x[2 * k.val]! = 0 ∧ x[2 * k.val + 1]! = UInt64.ofNat v)
    (hcl : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 1) (k : Fin 3) :
    zP x[2 * k.val]! = (if (claimH d.c (mOf x) k).1 then 1 else 0) ∧
      zP x[2 * k.val + 1]! = (((claimH d.c (mOf x) k).2 : ℕ) : ZMod P) := by
  unfold claimH
  rcases hn : claimNoun d.c k with v | ⟨a, b⟩
  · obtain ⟨h0, h1⟩ := hat k v hn
    have hv := hS.hclA k v hn
    simp only [claimHandle]
    refine ⟨?_, ?_⟩
    · rw [h0]; rfl
    · rw [h1]; exact zv_ofNat _ (lt_trans hv P_lt)
  · have hc : isCellN (claimNoun d.c k) = true := by rw [hn]; rfl
    have h1 := hcl k hc
    simp only [claimHandle]
    refine ⟨?_, rfl⟩
    unfold SP.labelOf at h1
    show ((x[2 * k.val]!).toNat : ZMod P) = _
    rw [h1]
    simp


theorem labelF_get (d : Datum) (hS : StmtP d) (x : Array UInt64)
    (hat : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v → x[2 * k.val]! = 0 ∧ x[2 * k.val + 1]! = UInt64.ofNat v)
    (hcl : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 1) :
    ∀ j < 6, (labelF (F := ZMod P) d.c (mOf x)).getD j 0 = zP x[j]! := by
  have h0 := hk_facts d hS x hat hcl 0
  have h1 := hk_facts d hS x hat hcl 1
  have h2 := hk_facts d hS x hat hcl 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, zero_add, mul_one, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2
  intro j hj
  unfold labelF hvalF
  interval_cases j
  · exact h0.1.symm
  · exact h0.2.symm
  · exact h1.1.symm
  · exact h1.2.symm
  · exact h2.1.symm
  · exact h2.2.symm


theorem labelF_list (d : Datum) (hS : StmtP d) (x : Array UInt64)
    (hat : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v → x[2 * k.val]! = 0 ∧ x[2 * k.val + 1]! = UInt64.ofNat v)
    (hcl : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 1) :
    labelF (F := ZMod P) d.c (mOf x) = List.ofFn (fun q : Fin 6 => zP x[q.val]!) := by
  apply List.ext_getElem
  · rw [FrameVS.labelF_length, List.length_ofFn]
  · intro n h1 h2
    have hn : n < 6 := by simpa [FrameVS.labelF_length] using h1
    have := labelF_get d hS x hat hcl n hn
    rw [List.getD_eq_getElem _ _ h1] at this
    rw [this, List.getElem_ofFn]

theorem seed_eq (d : Datum) (hS : StmtP d) (x : Array UInt64)
    (hat : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v → x[2 * k.val]! = 0 ∧ x[2 * k.val + 1]! = UInt64.ofNat v)
    (hcl : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 1)
    (c13 c14 : KN) :
    c13 * (((labelF (F := ZMod P) d.c (mOf x)).zipIdx.map fun p => c14 ^ p.2 * algebraMap (ZMod P) KN p.1).sum) =
      c13 * ∑ q : Fin 6, c14 ^ (q : ℕ) * algebraMap (ZMod P) KN (zP x[q.val]!) := by
  rw [labelF_list d hS x hat hcl]
  congr 1


theorem re_φ (a b : KC) : Quad.re δK (φ (SP.qmk a b)) = (a : KN) := Quad.re_mk _ _ _
theorem im_φ (a b : KC) : Quad.im δK (φ (SP.qmk a b)) = (b : KN) := Quad.im_mk _ _ _

theorem rhoOf3 (x : Array UInt64) : SP.rhoOf x 3 = SP.qmk (SP.pubK x 5) (SP.pubK x 7) := by simp [SP.rhoOf]
theorem rhoOf4 (x : Array UInt64) : SP.rhoOf x 4 = SP.qmk (SP.pubK x 6) (SP.pubK x 8) := by simp [SP.rhoOf]

/-- the coordinates of the `i`-th `K`-value of a canonical slice are its limbs `3i, 3i+1, 3i+2` -/
theorem coord_pubK (f : Array UInt64) (hf : SP.ArrCan f) (i : ℕ) (k : Fin 3) :
    Nock.NockVMROM.Thm54.CoordinateBasis.coord Nock.TraceGenExe.powerBasis3 (SP.pubK f i) k = zP f[3 * i + k.val]! := by
  have := coord_toKV ⟨f[3 * i]!, f[3 * i + 1]!, f[3 * i + 2]!⟩ ⟨hf _, hf _, hf _⟩ k
  refine this.trans ?_
  fin_cases k <;> rfl

theorem derived_of (d : Datum) (hS : StmtP d) (inp : PE.PubIn) (x : Array UInt64) (hx : SP.ArrCan x)
    (coins : Array VF.K3) (hder : SP.ComputeDerivedP inp coins x)
    (hat : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v → x[2 * k.val]! = 0 ∧ x[2 * k.val + 1]! = UInt64.ofNat v)
    (hcl : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → SP.labelOf x (2 * k.val) = 1)
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins FrameJ8.frameJ8 KN)
    (h13 : χ ⟨13, (by norm_num : 13 < 19)⟩ = toKV coins[13]!) (h14 : χ ⟨14, (by norm_num : 14 < 19)⟩ = toKV coins[14]!) :
    ∀ j : Fin 33, zP x[j.val]! = VerJ8.pubVJ8 deltaF Nock.TraceGenExe.powerBasis3 d.c (mOf x) (ρOf x) (ρSOf x) χ j.val := by
  obtain ⟨-, hα, hsd, h12, h13', h14', -⟩ := hder
  have hcx : ∀ a b c : ℕ, canon3 (⟨x[a]!, x[b]!, x[c]!⟩ : VF.K3) := fun a b c => ⟨hx a, hx b, hx c⟩
  have hseed : FrameVS.seedVS (F := ZMod P) d.c (mOf x) (FrameVSQ.toVS (FrameJ8.toVSQ χ)) = toKV ⟨x[9]!, x[10]!, x[11]!⟩ := by
    unfold FrameVS.seedVS
    refine (seed_eq d hS x hat hcl _ _).trans ?_
    show χ ⟨13, _⟩ * ∑ q : Fin 6, (χ ⟨14, _⟩) ^ (q : ℕ) * algebraMap (ZMod P) KN (zP x[q.val]!) = _
    rw [h13, h14, hsd]
    congr 1
  rintro ⟨j, hj⟩
  show zP x[j]! = _
  unfold VerJ8.pubVJ8 FrameVSQ.pubVHQ FrameVS.pubVH
  dsimp only
  have h27 : j < 27 ∨ 27 ≤ j := by omega
  rcases h27 with h27 | h27
  · rw [if_pos h27]
    by_cases h21 : j < 21
    · rw [if_pos h21]
      by_cases c1 : j < 6
      · rw [if_pos c1]; exact (labelF_get d hS x hat hcl j c1).symm
      rw [if_neg c1]
      by_cases c2 : j < 9
      · rw [dif_pos c2]
        show zP x[j]! = Nock.NockVMROM.Thm54.CoordinateBasis.coord _ (χ ⟨13, _⟩) _
        rw [h13, ← hα, coord_toKV _ (hcx 6 7 8)]
        interval_cases j <;> rfl
      rw [dif_neg c2]
      by_cases c3 : j < 12
      · rw [dif_pos c3, hseed, coord_toKV _ (hcx 9 10 11)]
        interval_cases j <;> rfl
      rw [dif_neg c3]
      by_cases c4 : j < 15
      · rw [if_pos c4]
        have hz0 : ∀ g : UInt64, g = 0 → zP g = 0 := fun g hg => by subst hg; rfl
        interval_cases j
        · exact hz0 _ h12
        · exact hz0 _ h13'
        · exact hz0 _ h14'
      rw [if_neg c4]
      have hr3 : ρOf x 3 = φ (SP.qmk (SP.pubK x 5) (SP.pubK x 7)) := by unfold ρOf; rw [rhoOf3]
      have hr4 : ρOf x 4 = φ (SP.qmk (SP.pubK x 6) (SP.pubK x 8)) := by unfold ρOf; rw [rhoOf4]
      by_cases c5 : j < 18
      · rw [dif_pos c5, hr3, re_φ, coord_pubK x hx 5]
        interval_cases j <;> rfl
      · rw [dif_neg c5, dif_pos h21, hr4, re_φ, coord_pubK x hx 6]
        interval_cases j <;> rfl
    · rw [if_neg h21]
      have hr3 : ρOf x 3 = φ (SP.qmk (SP.pubK x 5) (SP.pubK x 7)) := by unfold ρOf; rw [rhoOf3]
      have hr4 : ρOf x 4 = φ (SP.qmk (SP.pubK x 6) (SP.pubK x 8)) := by unfold ρOf; rw [rhoOf4]
      by_cases d1 : j < 24
      · rw [dif_pos d1, hr3, im_φ, coord_pubK x hx 7]
        interval_cases j <;> rfl
      · rw [dif_neg d1, dif_pos h27, hr4, im_φ, coord_pubK x hx 8]
        interval_cases j <;> rfl
  · rw [if_neg (by omega : ¬ j < 27)]
    have hrS : ρSOf x = φ (SP.qmk (SP.pubK x 9) (SP.pubK x 10)) := rfl
    by_cases e1 : j < 30
    · rw [dif_pos e1, hrS, re_φ, coord_pubK x hx 9]
      interval_cases j <;> rfl
    · rw [dif_neg e1, dif_pos (by omega : j < 33), hrS, im_φ, coord_pubK x hx 10]
      interval_cases j <;> rfl


/-! ## 7. `hRVU_J8` -/

theorem getBang_replicate (n j : ℕ) : (Array.replicate n (0 : UInt64))[j]! = 0 := by
  by_cases h : j < n
  · rw [getElem!_pos _ j (by simpa using h)]; simp
  · rw [getElem!_neg _ j (by simpa using h)]; rfl

theorem pubK_replicate (n i : ℕ) : SP.pubK (Array.replicate n 0) i = 0 := by
  unfold SP.pubK
  rw [getBang_replicate, getBang_replicate, getBang_replicate]
  exact toKV_zero

/-- **`hRVU_J8`: the public twin at J-8.**  The verifier-side public relation `PubJ8P` (at the instance data `inp`, the layout `L`,
the coin slots and the publics) gives nock's `Pub` of `J8 d hd` (`PubP d χ M`: the eight public equations, `hclI`, `AbsentPubs`,
`DerivedOK`) at the message `Mof L pub` and the coins `χ` of the slots.

Hypotheses (all instance-level or from `StmtP`): `StmtP d` (`hS`); the datum link `InpLink`; canonical slots and
publics; registry ids `< p` (`hids`: `StmtP` bounds `idx`, `rk` but not the ids); the coins are the slot coins (`hχ`, the `hslot` of
`hdagU_J`); an absent jet / atom-walk table has `present = false` in the layout (`hpJ`, `hpV`), so `slOf` zero-fills its publics. -/
theorem hRVU_J8 (d : Datum) (hS : StmtP d) (inp : PE.PubIn) (hlink : InpLink d inp) (L : PE.PubLayout)
    (slotOf : Array ℕ) (slots : Array VF.K3) (pub : Array UInt64) (hs : ∀ s ∈ slots, canon3 s) (hp : ∀ g ∈ pub, canon g)
    (hids : ∀ id ∈ d.Pb.regs, id < P)
    (hpJ : d.Pb.nJ = 0 → L.present[3]! = false) (hpV : d.Pb.krootsV = 0 → L.present[5]! = false)
    (χ : NockvmE2E.Rap.Coins Φ0 KN) (hχ : ∀ i : Fin 19, χ i = toKV (SP.coinsOf slots slotOf)[i.val]!)
    (hP : NockvmE2E.Merkle.RapFriQ.PubJ8P inp L slotOf slots pub) :
    PubP d χ (Mof L pub) := by
  have hP' := hP
  obtain ⟨⟨cr, pr, hcr, hpr, hrel⟩, hder⟩ := hP
  have hc := coinsOf_can slots slotOf hs
  have hx : SP.ArrCan (SP.slOf L pub 0) := SP.slOf_can L pub hp 0
  have hcells : ∀ k ∈ claimCells d.c, isCellN (claimNoun d.c k) = true := fun k hk => by
    unfold claimCells at hk; exact (List.mem_filter.1 hk).2
  have hcl : ∀ k : Fin 3, isCellN (claimNoun d.c k) = true → SP.labelOf (SP.slOf L pub 0) (2 * k.val) = 1 := by
    rw [hlink.hcl] at hcr
    obtain ⟨hl, -⟩ := claims_mapM _ _ (SP.slOf L pub 0) (claimNoun d.c) (claimCells d.c) hcells cr hcr
    intro k hk
    exact hl k (by unfold claimCells; exact List.mem_filter.2 ⟨List.mem_finRange k, hk⟩)
  have hat : ∀ k : Fin 3, ∀ v, claimNoun d.c k = .atom v →
      (SP.slOf L pub 0)[2 * k.val]! = 0 ∧ (SP.slOf L pub 0)[2 * k.val + 1]! = UInt64.ofNat v := by
    intro k v hk
    have hmem : (k.val, v) ∈ inp.atoms := by
      rw [hlink.hat]
      exact List.mem_filterMap.2 ⟨k, List.mem_finRange k, by simp [hk]⟩
    exact (hder.2.2.2.2.2.2 _ hmem).2
  refine ⟨pubEq_of_P d hS inp hlink L slotOf slots pub hs hp hids χ hχ hP', ?_, ?_, ?_⟩
  · intro k _
    exact hx (2 * k.val + 1)
  · refine ⟨fun hV => ?_, fun hJ => ?_⟩
    · have : SP.slOf L pub 5 = Array.replicate L.lens[5]! 0 := by
        unfold SP.slOf; rw [if_neg (by simp [hpV hV])]
      show SP.pubK (SP.slOf L pub 5) 0 = 0 ∧ SP.pubK (SP.slOf L pub 5) 1 = 0 ∧ SP.pubK (SP.slOf L pub 5) 4 = 0 ∧
        SP.pubK (SP.slOf L pub 5) (4 + 1) = 0 ∧ SP.pubK (SP.slOf L pub 5) 6 = 0 ∧ SP.pubK (SP.slOf L pub 5) (6 + 1) = 0
      rw [this]
      exact ⟨pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _⟩
    · have : SP.slOf L pub 3 = Array.replicate L.lens[3]! 0 := by
        unfold SP.slOf; rw [if_neg (by simp [hpJ hJ])]
      show SP.pubK (SP.slOf L pub 3) 0 = 0 ∧ SP.pubK (SP.slOf L pub 3) 1 = 0 ∧ SP.pubK (SP.slOf L pub 3) 2 = 0 ∧
        SP.pubK (SP.slOf L pub 3) 3 = 0
      rw [this]
      exact ⟨pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _, pubK_replicate _ _⟩
  · exact derived_of d hS inp _ hx _ hder hat hcl χ (hχ ⟨13, (by norm_num : 13 < 19)⟩) (hχ ⟨14, (by norm_num : 14 < 19)⟩)

/-! ## 8. Non-vacuity of the datum link on the real toy1 claim -/

/-- the toy1 claim of the J-8 fixture: subject `0`, formula `[1 0]`, result `0` -/
def toyClaim : Nock.NockVMROM.Thm54.P8PublicClaim := ⟨.atom 0, .cell (.atom 1) (.atom 0), .atom 0⟩

/-- **non-vacuity of `InpLink`**: the real toy1 `PubIn` of the verifier (`PE.toy1Claim`) is linked to every datum with the toy1 claim and
an empty registry (the claim cell `[1 0]` at position 1 with rank halves `(0, 1)`, the atoms at positions 0 and 2) -/
theorem inpLink_toy1 (d : Datum) (hc : d.c = toyClaim) (hr : d.Pb.regs = []) : InpLink d PE.toy1Claim := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [hr]; rfl
  · rw [hc]; rfl

end NockvmE2E.J8.RVUJ8

#print axioms NockvmE2E.J8.RVUJ8.inpLink_toy1
#print axioms NockvmE2E.J8.RVUJ8.φE
#print axioms NockvmE2E.J8.RVUJ8.φ_qinv
#print axioms NockvmE2E.J8.RVUJ8.φ_compress
#print axioms NockvmE2E.J8.RVUJ8.encZY_spec
#print axioms NockvmE2E.J8.RVUJ8.claimRecs_eq
#print axioms NockvmE2E.J8.RVUJ8.pinRecs_eq
#print axioms NockvmE2E.J8.RVUJ8.pubEq_of_P
#print axioms NockvmE2E.J8.RVUJ8.derived_of
#print axioms NockvmE2E.J8.RVUJ8.hRVU_J8
