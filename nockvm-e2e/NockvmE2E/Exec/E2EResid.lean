/-
  NockvmE2E/Exec/E2EResid.lean   (proof-only)

  Concrete decoders `dsmC` for the FRI mask and the codec/internal fields of `E2EMain.Resid`.
-/
import NockvmE2E.Exec.E2EMain

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.style.multiGoal false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.E2EResid

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort

/-- every element of `KC` is `toKV` of the `K3` of some limb list -/
theorem limbs_surj (y : KC) : ∃ x : List ℕ, (∀ v ∈ x, v < NockvmE2E.Exec.p) ∧ toKV (VF.K3.ofLimbs x) = y := by
  obtain ⟨s, hs⟩ := Exec.K3.toK_surjective y
  refine ⟨[s.c0.val.toNat, s.c1.val.toNat, s.c2.val.toNat], ?_, ?_⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact s.c0.lt
    · exact s.c1.lt
    · exact s.c2.lt
  rw [← hs]
  have h : ∀ a : Gold, zv (UInt64.ofNat a.val.toNat) = a.toZ := by
    intro a
    simp [zv, Gold.toZ, UInt64.ofNat_toNat]
  simp only [toKV, VF.K3.ofLimbs, List.getD_cons_zero, List.getD_cons_succ, h, Exec.K3.toK]


section Codec
open NockvmE2E.Merkle.Fri NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Exec.E2ELR

/-- a challenge codec for a round whose challenge type is `KC`: limbs of the `K3` -/
noncomputable def kcCodec (r : Round) (e : r.Challenge = KC) : CCodec r where
  encC c := Classical.choose (limbs_surj (cast e c))
  decC x := cast e.symm (toKV (VF.K3.ofLimbs x))
  decC_encC c := by
    show cast e.symm (toKV (VF.K3.ofLimbs (Classical.choose (limbs_surj (cast e c))))) = c
    rw [(Classical.choose_spec (limbs_surj (cast e c))).2]
    simp

theorem kcCodec_dec (r : Round) (e : r.Challenge = KC) (x : List ℕ) :
    cast e ((kcCodec r e).decC x) = toKV (VF.K3.ofLimbs x) := by
  simp [kcCodec]

variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC} (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]

theorem foldE (i : ℕ) (hi : i < k + 1) (hik : i < k) : ((friAlt (ω := ω) s d l).midRound i hi).Challenge = KC :=
  (congrArg (pSpec k (ω := ω) s l).«Type»
    (Fin.ext (by simp only [foldChallenge_val]; have := friLength (k := k); omega) :
      (⟨2 * i + 2, by have := friLength (k := k); omega⟩ : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) =
        (foldChallenge (ω := ω) s l ⟨i + 1, by omega⟩).val)).trans (foldChallenge_type s l _)

theorem queryE : ((friAlt (ω := ω) s d l).midRound k (Nat.lt_succ_self k)).Challenge = (Fin l → (ω.subdomain 0).toFinset) :=
  (congrArg (pSpec k (ω := ω) s l).«Type»
    (Fin.ext (by simp only [queryChallenge_val]) :
      (⟨2 * k + 2, by have := friLength (k := k); omega⟩ : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) =
        (queryChallenge (ω := ω) s l).val)).trans (queryChallenge_type s l)

/-- the query codec: the index (in `Fin (2^n)`) of each query point -/
noncomputable def qCodec : CCodec ((friAlt (ω := ω) s d l).midRound k (Nat.lt_succ_self k)) where
  encC c := List.ofFn (fun j : Fin l => ((ω.subdomain 0).equivToFinset.symm ((cast (queryE s d l) c) j)).val)
  decC x := cast (queryE s d l).symm
    (fun j : Fin l => (ω.subdomain 0).equivToFinset ⟨x[j.1]! % 2 ^ (n - 0), Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
  decC_encC c := by
    have h : (fun j : Fin l => (ω.subdomain 0).equivToFinset ⟨(List.ofFn (fun j : Fin l =>
        ((ω.subdomain 0).equivToFinset.symm ((cast (queryE s d l) c) j)).val))[j.1]! % 2 ^ (n - 0), Nat.mod_lt _ (Nat.two_pow_pos _)⟩) =
        cast (queryE s d l) c := by
      funext j
      have hj : (List.ofFn (fun j : Fin l => ((ω.subdomain 0).equivToFinset.symm ((cast (queryE s d l) c) j)).val))[j.1]! =
          ((ω.subdomain 0).equivToFinset.symm ((cast (queryE s d l) c) j)).val := by
        simp [List.getElem!_eq_getElem?_getD]
      refine (congrArg (ω.subdomain 0).equivToFinset
        (Fin.ext ?_ : _ = (ω.subdomain 0).equivToFinset.symm (cast (queryE s d l) c j))).trans
        (Equiv.apply_symm_apply _ _)
      show _ % _ = _
      rw [hj]
      exact Nat.mod_eq_of_lt (Fin.is_lt _)
    show cast (queryE s d l).symm _ = c
    rw [h]
    simp

/-- the final polynomial read from a flat limb list (`d` coefficients at most, each the `K3` of three consecutive limbs) -/
noncomputable def finPolyD (d : ℕ+) (m : List ℕ) : CompPoly.CPolynomial KC :=
  CompPoly.CPolynomial.ofFinCoeff (min (m.length / 3) d.val) (fun j => toKV (VF.K3.ofLimbs (m.drop (3 * j))))

theorem finPolyD_deg (d : ℕ+) (m : List ℕ) : (finPolyD d m).natDegree < d.val := by
  rw [CompPoly.CPolynomial.natDegree_toPoly]
  by_cases h0 : (finPolyD d m).toPoly = 0
  · rw [h0]; simp
  · have h1 := CompPoly.CPolynomial.degree_toPoly_ofFinCoeff_lt (min (m.length / 3) d.val)
      (fun j => toKV (VF.K3.ofLimbs (m.drop (3 * j))))
    have h2 : (min (m.length / 3) d.val : ℕ) ≤ d.val := min_le_right _ _
    refine (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (lt_of_lt_of_le h1 ?_)
    exact_mod_cast h2

/-- the decoder of the last round: query codec, final polynomial from limbs -/
noncomputable def lastRD : RDec ((friAlt (ω := ω) s d l).midRound k (Nat.lt_succ_self k)) where
  toCCodec := qCodec s d l
  decM m := ⟨cast (fri_msgType_final (ω := ω) s l k _ rfl).symm (finPolyD d m), fun hik => by
    simpa using finPolyD_deg d m⟩

theorem headE : ((friAlt (ω := ω) s d l).headRound).Challenge = KC :=
  (congrArg (pSpec k (ω := ω) s l).«Type»
    (Fin.ext (by simp only [foldChallenge_val]) :
      (⟨0, by have := friLength (k := k); omega⟩ : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) =
        (foldChallenge (ω := ω) s l ⟨0, by omega⟩).val)).trans (foldChallenge_type s l _)

/-- the decoder of the head round: the challenge `α₀` is the `K3` of the limbs; the message is `()`. -/
noncomputable def headRD : RDec ((friAlt (ω := ω) s d l).headRound) where
  toCCodec := kcCodec _ (headE s d l)
  decM _ := ()

variable (L : FriLeaves (ω := ω) s) (enc : KC ↪ DgJ8)

/-- the decoders of the merkle part of the FRI mask -/
noncomputable def dsFM : (i c : ℕ) → (h : i + c = k) → MDec (friMerkleMask s d l L DgJ8 enc i c h)
  | i, 0, h => by
      have hi : i = k := by omega
      subst hi
      exact (lastRD s d l, ())
  | i, c + 1, h => (kcCodec _ (foldE s d l i (by omega) (by omega)), dsFM i.succ c (by omega))

/-- **the concrete decoders of the FRI mask** -/
noncomputable def dsmC : MDec (friMask s d l L DgJ8 enc) := (headRD s d l, dsFM s d l L enc 0 k (Nat.zero_add k))

theorem codOK_dsFM : (c i : ℕ) → (h : i + c = k) →
    E2EFri.CodOK (ω := ω) s d l L DgJ8 enc (fun x => toKV (VF.K3.ofLimbs x)) i c h (dsFM s d l L enc i c h)
  | 0, i, h => trivial
  | c + 1, i, h => by
      refine ⟨fun x => ?_, codOK_dsFM c i.succ (by omega)⟩
      have := kcCodec_dec _ (foldE (ω := ω) s d l i (by omega) (by omega)) x
      refine (eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))).trans this

theorem hcod0_dsmC (x : List ℕ) :
    cast (foldChallenge_type (ω := ω) s l ⟨0, by omega⟩)
      (xp (a := ⟨0, by have := friLength (k := k); omega⟩) (b := (foldChallenge (ω := ω) s l ⟨0, by omega⟩).val)
        (Fin.ext (by simp only [foldChallenge_val])) ((dsmC s d l L enc).1.decC x)) = toKV (VF.K3.ofLimbs x) := by
  have := kcCodec_dec _ (headE (ω := ω) s d l) x
  refine (eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))).trans this

end Codec

theorem sndD_mdAppend {Yd : Type} [Finite Yd] [DecidableEq Yd] : (a b : MRounds Yd) → (da : MDec a) → (db : MDec b) →
    E2ELR.sndD a b (mdAppend a b da db) = db
  | [], _, _, _ => rfl
  | ⟨_, .clear⟩ :: a, b, (_, da), db => sndD_mdAppend a b da db
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (_, da), db => sndD_mdAppend a b da db

section Horner

theorem horner_partial (c : ℕ → KC) (n : ℕ) (y : KC) : (t : ℕ) → t ≤ n →
    (List.range' 0 t).foldl (fun acc i => acc * y + c (n - 1 - i)) 0 =
      ∑ i ∈ Finset.range t, c (n - 1 - i) * y ^ (t - 1 - i)
  | 0, _ => by simp
  | t + 1, ht => by
      rw [List.range'_concat, List.foldl_append, horner_partial c n y t (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, zero_add, one_mul, Nat.mul_zero]
      rw [Finset.sum_range_succ, Finset.sum_mul]
      have h1 : ∀ i ∈ Finset.range t, c (n - 1 - i) * y ^ (t - 1 - i) * y = c (n - 1 - i) * y ^ (t + 1 - 1 - i) := by
        intro i hi
        have := Finset.mem_range.mp hi
        rw [mul_assoc, ← pow_succ]
        congr 2
        omega
      rw [Finset.sum_congr rfl h1]
      simp

theorem hornerF_sum (c : ℕ → KC) (n : ℕ) (y : KC) : SF.hornerF c n y = ∑ j ∈ Finset.range n, c j * y ^ j := by
  unfold SF.hornerF
  rw [horner_partial c n y n le_rfl, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  have e1 : n - 1 - (n - 1 - i) = i := by omega
  rw [e1]

theorem eval_finPolyD (d : ℕ+) (m : List ℕ) (y : KC) :
    (finPolyD d m).eval y = ∑ j ∈ Finset.range (min (m.length / 3) d.val), toKV (VF.K3.ofLimbs (m.drop (3 * j))) * y ^ j := by
  unfold finPolyD CompPoly.CPolynomial.ofFinCoeff
  rw [CompPoly.CPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [CompPoly.CPolynomial.eval_monomial]

end Horner

section Flat

theorem ofLimbs_limbs (x : VF.K3) (r : List ℕ) : VF.K3.ofLimbs (VF.K3.limbs x ++ r) = x := by
  cases x
  simp [VF.K3.ofLimbs, VF.K3.limbs, UInt64.ofNat_toNat]

theorem ofLimbs_flat : (l : List VF.K3) → (j : ℕ) → j < l.length →
    VF.K3.ofLimbs ((l.flatMap VF.K3.limbs).drop (3 * j)) = l[j]!
  | [], j, h => by simp at h
  | x :: l, 0, h => by
      simpa [VF.K3.limbs, List.flatMap_cons] using ofLimbs_limbs x (l.flatMap VF.K3.limbs)
  | x :: l, j + 1, h => by
      have := ofLimbs_flat l j (by simpa using h)
      have e : (VF.K3.limbs x ++ l.flatMap VF.K3.limbs).drop (3 * (j + 1)) = (l.flatMap VF.K3.limbs).drop (3 * j) := by
        have : 3 * (j + 1) = (VF.K3.limbs x).length + 3 * j := by simp [VF.K3.limbs]; omega
        rw [this, List.drop_append]
        simp [VF.K3.limbs]
      simpa [List.flatMap_cons, e] using this

theorem length_flat (l : List VF.K3) : (l.flatMap VF.K3.limbs).length = 3 * l.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, VF.K3.limbs, ih]; omega

end Flat

section Msgs
open NockvmE2E.Merkle.Fri

/-- the messages along a path -/
def pathMsgs : (rounds : List Round) → (protocol rounds).tree.ExecutionPath → PublicMessages rounds
  | [], _ => PUnit.unit
  | _ :: rs, p => (p.1, pathMsgs rs p.2.2)

theorem pathMsgs_pathOf {Input : Type} (z : Input) : (rounds : List Round) → (g : (k : Key Input PUnit rounds) → k.Challenge) →
    (ms : PublicMessages rounds) → pathMsgs rounds (pathOf z rounds g ms) = ms
  | [], _, _ => rfl
  | _ :: rs, g, (m, ms) => by
      simp only [pathMsgs, pathOf]
      rw [pathMsgs_pathOf z rs _ ms]

variable {Yd : Type} [Finite Yd] [DecidableEq Yd] (dY : List ℕ → Yd) {Op : Type} [Finite Op] [DecidableEq Op]

/-- the messages of the suffix path -/
theorem pathMsgs_sndK : (a b : MRounds Yd) → (da : MDec a) → (db : MDec b) → (ω : Op) → (fm : List (List ℕ)) →
    (p : (protocol (compiledRoundsK Yd Op (a ++ b))).tree.ExecutionPath) →
    pathMsgs _ p = decMsgs _ (mDecs dY (a ++ b) (mdAppend a b da db) ω) fm →
    pathMsgs _ (MA.sndK Yd Op a b p) = decMsgs _ (mDecs dY b db ω) (fm.drop a.length)
  | [], b, da, db, ω, fm, p, h => by simpa [MA.sndK, mdAppend] using h
  | ⟨_, .clear⟩ :: a, b, (d, da), db, ω, fm, p, h => by
      have h2 := congrArg Prod.snd h
      have := pathMsgs_sndK a b da db ω fm.tail p.2.2 h2
      simpa [MA.sndK, List.drop_tail] using this
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (c, da), db, ω, fm, p, h => by
      have h2 := congrArg Prod.snd h
      have := pathMsgs_sndK a b da db ω fm.tail p.2.2 h2
      simpa [MA.sndK, List.drop_tail] using this


section FinP2
open NockvmE2E.Merkle.Fri NockvmE2E.Lift NockvmE2E.Lift.Alternating
variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC} (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (L : FriLeaves (ω := ω) s) (enc : KC ↪ DgJ8) (dY : List ℕ → DgJ8) {Op : Type} [Finite Op] [DecidableEq Op] (ω0 : Op)

theorem finPolyOf_dsFM : (c i : ℕ) → (h : i + c = k) →
    (q : (protocol (compiledRoundsK DgJ8 Op (friMerkleMask s d l L DgJ8 enc i c h))).tree.ExecutionPath) → (fm : List (List ℕ)) →
    pathMsgs _ q = decMsgs _ (mDecs dY _ (dsFM s d l L enc i c h) ω0) fm →
    E2EFri.finPolyOf (ω := ω) s d l L DgJ8 enc Op i c h q = finPolyD d (fm.getD c [])
  | 0, i, h, q, fm, hq => by
      have hi : i = k := by omega
      subst hi
      have h1 : q.1 = (lastRD s d l).decM (fm.headD []) := congrArg Prod.fst hq
      have h2 : q.1.1 = cast (fri_msgType_final (ω := ω) s l i _ rfl).symm (finPolyD d (fm.headD [])) := congrArg Subtype.val h1
      show cast _ (xp _ q.1.1) = _
      rw [h2]
      refine (eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _)))).trans ?_
      cases fm <;> rfl
  | c + 1, i, h, q, fm, hq => by
      have h2 := congrArg Prod.snd hq
      have := finPolyOf_dsFM c i.succ (by omega) q.2.2 fm.tail h2
      simpa [E2EFri.finPolyOf, List.getD_eq_getElem?_getD] using this

end FinP2
end Msgs

section Inst
open NockvmE2E.Exec.E2ELR NockvmE2E.Exec.Inst NockvmE2E.Merkle.Fri NockvmE2E.Lift NockvmE2E.Lift.Alternating

variable (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof) (hv : verifyFlat XI H FS zF π = true)

set_option hygiene false in
local notation "ωS" => smoothDomain XI.nD (nD_le_of_verify XI H FS zF π hv)
set_option hygiene false in
local notation "s1" => (fun _ : Fin (XI.k + 1) => (1 : ℕ+))

variable [∀ j, SampleableType ((pSpec XI.k (ω := ωS) s1 XI.l).Challenge j)]
variable (d : ℕ+) (enc : KC ↪ DgJ8) (L : Fri.FriLeaves (ω := ωS) s1) (Op : Type) [Finite Op] [DecidableEq Op]

theorem xs_last (v : ((friAlt (ω := ωS) s1 d XI.l).midRound XI.k (Nat.lt_succ_self XI.k)).Challenge) :
    cast (queryChallenge_type (ω := ωS) s1 XI.l)
      (xp (a := ⟨2 * XI.k + 2, by have := friLength (k := XI.k); omega⟩) (b := (queryChallenge (ω := ωS) s1 XI.l).val)
        (Fin.ext (by simp only [queryChallenge_val])) v) = cast (queryE (ω := ωS) s1 d XI.l) v :=
  eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))

theorem hX_dsFM (hD : DomLink XI (nD_le_of_verify XI H FS zF π hv)) : (c i : ℕ) → (h : i + c = XI.k) →
    (q : (protocol (compiledRoundsK DgJ8 Op (friMerkleMask s1 d XI.l L DgJ8 enc i c h))).tree.ExecutionPath) → (j : Fin XI.l) →
    (Fri.XsOf s1 d XI.l L DgJ8 enc Op i c h q j).val =
      homV.ψ XI.dShift * homV.ψ XI.dGen ^ ((lastEnc XI H FS zF π hv d DgJ8 enc L Op i c h (dsFM s1 d XI.l L enc i c h) q)[j.1]! % 2 ^ XI.nD)
  | 0, i, h, q, j => by
      have hi : i = XI.k := by omega
      subst hi
      have e1 : (Fri.XsOf s1 d XI.l L DgJ8 enc Op XI.k 0 h q j) = (cast (queryE (ω := ωS) s1 d XI.l) q.2.1) j := by
        have := xs_last XI H FS zF π hv d q.2.1
        exact congrFun this j
      have e2 : (lastEnc XI H FS zF π hv d DgJ8 enc L Op XI.k 0 h (dsFM s1 d XI.l L enc XI.k 0 h) q) =
          (qCodec (ω := ωS) s1 d XI.l).encC q.2.1 := rfl
      rw [e1, e2]
      set x := (cast (queryE (ω := ωS) s1 d XI.l) q.2.1) j with hx
      have hj : ((qCodec (ω := ωS) s1 d XI.l).encC q.2.1)[j.1]! =
          ((CosetFftDomain.subdomain ωS 0).equivToFinset.symm x).val := by
        simp [qCodec, List.getElem!_eq_getElem?_getD, hx]
      rw [hj]
      set idx := (CosetFftDomain.subdomain ωS 0).equivToFinset.symm x with hidx
      have h1 : x.val = ωS idx := by
        rw [← CosetFftDomainClass.subdomain_0_apply]
        exact (CosetFftDomain.equivToFinset_symm_apply (CosetFftDomain.subdomain ωS 0) x).symm
      rw [h1, Nat.mod_eq_of_lt (by simpa using idx.2)]
      exact hω_of_domLink XI _ hD idx
  | c + 1, i, h, q, j => hX_dsFM hD c i.succ (by omega) q.2.2 j

end Inst

section ValF
open NockvmE2E.Exec.SM NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.V

theorem selectedValueAt_valsOf {D : Type} (lv : ℕ → D) : {s : Skeleton} → (idx : SkeletonLeafIndex s) →
    (sel : LeafData Bool s) → (lo : ℕ) → (hs : sel.get idx = true) →
    selectedValueAt (valsOf lv s sel lo) idx hs = lv (lo + leafNum idx)
  | _, .ofLeaf, .leaf true, lo, hs => rfl
  | _, .ofLeaf, .leaf false, lo, hs => by simp [LeafData.get] at hs
  | .internal l r, .ofLeft a, .internal sl sr, lo, hs => by
      show selectedValueAt (valsOf lv l sl lo) a _ = lv (lo + leafNum a)
      exact selectedValueAt_valsOf lv a sl lo _
  | .internal l r, .ofRight a, .internal sl sr, lo, hs => by
      show selectedValueAt (valsOf lv r sr (lo + l.leafCount)) a _ = lv (lo + (l.leafCount + leafNum a))
      rw [selectedValueAt_valsOf lv a sr (lo + l.leafCount) _]
      congr 1; omega


theorem embed_tree_open (skels : List Skeleton) (h : NQuery skels → DgJ8) (j : Fin skels.length) (sp : TSpec) (hw : WfSpec sp)
    (hs : skels.get j = skelOf sp sp.total sp.total) (hsp1 : 1 ≤ sp.total) (sel : Array ℕ)
    (hsel : sel.toList.Pairwise (· < ·)) (leaf : ℕ → Dg5) (sibs : Array Dg5) (root : Dg5)
    (hcl : ∀ i, dgOk (leaf i) = true) (hsb : ∀ d ∈ sibs.toList, dgOk d = true)
    (hgo : goRoot (Hof skels h) sp j.1 sel leaf sibs 1 0 sp.total 0 = some (root, sibs.size)) :
    ∃ pr, mkOpeningD (ftreeOf sel leaf sibs.toList root) (skels.get j) =
      ⟨selOf (ftreeOf sel leaf sibs.toList root).isSel (skels.get j) 0,
        valsOf (ftreeOf sel leaf sibs.toList root).lv (skels.get j) (selOf (ftreeOf sel leaf sibs.toList root).isSel (skels.get j) 0) 0, pr⟩ := by
  obtain ⟨_, _, hg⟩ := goRootF_goSk (Hof skels h) sp hw j.1 sel leaf sibs sp.total 1 0 sp.total 0 root sibs.size hsp1
    le_rfl (Nat.zero_le _) hgo
  have hd : List.drop sibs.size sibs.toList = [] := by simp
  rw [List.drop_zero, hd, ← hs] at hg
  obtain ⟨hm1, hm2⟩ := goSk_map dgOf (fun d => dgOk d = true) (fun i l r => Hof skels h ([tagNode, j.1, i] ++ l ++ r))
    (fun i L R => dgOf (Hof skels h ([tagNode, j.1, i] ++ dgFlat L ++ dgFlat R)))
    (fun a b => decide (lb sel a < lb sel b)) (fun i => sel[lb sel i]? == some i) (fun i => leaf (lb sel i))
    (fun i => dgOf (leaf (lb sel i))) (fun i => ⟨hcl _, rfl⟩)
    (fun idx l r hl hr => ⟨dgOk_Hof _ _ _, by simp only [dgFlat_dgOf _ hl, dgFlat_dgOf _ hr]⟩)
    (skels.get j) 1 0 sibs.toList hsb
  rw [hg] at hm1
  simp only [Option.map_some, List.map_nil] at hm1
  obtain ⟨pr, hpr, hroot⟩ := goSk_sound
    (fun i L R => dgOf (Hof skels h ([tagNode, j.1, i] ++ dgFlat L ++ dgFlat R)))
    (fun a b => decide (lb sel a < lb sel b)) (fun i => sel[lb sel i]? == some i)
    (fun i => dgOf (leaf (lb sel i))) (hhas_lb sel hsel) (skels.get j) 1 0 (sibs.toList.map dgOf) (dgOf root) []
    hm1
  exact ⟨pr, mkOpeningD_eq (ftreeOf sel leaf sibs.toList root) (skels.get j) pr hpr⟩


theorem tree_open (XI : ExecInst) (FS : FSFn) (zF : List ℕ) (π : FlatProof) (skels : List Skeleton)
    (h : NQuery skels → DgJ8) (hok : FlatOk XI (Hof skels h) FS zF π) (hlen : skels.length = 4 + XI.k)
    (hsk : ∀ j (hj : j < skels.length), skels.get ⟨j, hj⟩ = skelFlat XI j) (j : Fin skels.length) (h4 : 4 ≤ j.1) :
    ∃ pr, mkOpeningD (ftree XI π j.1) (skels.get j) =
      ⟨selOf (ftree XI π j.1).isSel (skels.get j) 0,
        valsOf (ftree XI π j.1).lv (skels.get j) (selOf (ftree XI π j.1).isSel (skels.get j) 0) 0, pr⟩ := by
  have hj4 : j.1 < 4 + XI.k := hlen ▸ j.2
  have hne : ¬ (j.1 < 4 ∧ (blockLayout XI).1[j.1]! = 0) := fun hh => by omega
  have hc := flatOk_trees XI (Hof skels h) FS zF π hok j.1 (List.mem_range.mpr hj4)
  obtain ⟨_, hgo⟩ := treeCheck_root XI (Hof skels h) π _ _ _ j.1 hc hne
  have hsp : WfSpec (if j.1 < 4 then ragSpec (blockLayout XI).1[j.1]! (2 ^ (XI.nD - 1))
      else friSpec (2 ^ (XI.nD - (j.1 - 3)))) ∧
      1 ≤ (if j.1 < 4 then ragSpec (blockLayout XI).1[j.1]! (2 ^ (XI.nD - 1))
        else friSpec (2 ^ (XI.nD - (j.1 - 3)))).total := by
    have h4' : ¬ j.1 < 4 := by omega
    simp only [h4', ite_false]
    exact ⟨wf_friSpec _, by simp only [friSpec]; exact Nat.two_pow_pos _⟩
  have hlim := flatOk_limbs XI (Hof skels h) FS zF π hok
  have hcl : ∀ r, dgOk (if j.1 < 4 then [(π.vals[j.1]!)[r]!, 0, 0, 0, 0]
      else [(π.vals[j.1]!)[3 * r]!, (π.vals[j.1]!)[3 * r + 1]!, (π.vals[j.1]!)[3 * r + 2]!, 0, 0]) = true := by
    intro r
    have hz : NockvmE2E.Exec.VF.based 0 = true := by simp [NockvmE2E.Exec.VF.based, PN_eq]; exact (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
    split <;> simp [dgOk, NockvmE2E.Exec.VF.based, PN_eq, arr_get_lt (a := π.vals) hlim.2.2.2, hz] <;>
      exact (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
  exact embed_tree_open skels h j _ hsp.1 (hsk j.1 j.2) hsp.2 _ (selsOf_pw XI π j.1 hj4) _ _ _ hcl
    (sibs_ok (flatOk_allCanon XI _ FS zF π hok) j.1) (by simpa using hgo)


theorem open_val (XI : ExecInst) (FS : FSFn) (zF : List ℕ) (π : FlatProof) (skels : List Skeleton)
    (h : NQuery skels → DgJ8) (hok : FlatOk XI (Hof skels h) FS zF π) (hlen : skels.length = 4 + XI.k)
    (hsk : ∀ j (hj : j < skels.length), skels.get ⟨j, hj⟩ = skelFlat XI j) (j : Fin skels.length) (h4 : 4 ≤ j.1)
    (tr : FTree DgJ8) (htr : tr = ftree XI π j.1) (sk : Skeleton) (hs : sk = skels.get j) :
    ∀ t (ht : (mkOpeningD tr sk).selector.get t = true),
      selectedValueAt (mkOpeningD tr sk).values t ht = tr.lv (leafNum t) := by
  subst htr hs
  obtain ⟨pr, hpr⟩ := tree_open XI FS zF π skels h hok hlen hsk j h4
  intro t ht
  revert ht
  rw [hpr]
  intro ht
  exact (selectedValueAt_valsOf _ t _ 0 ht).trans (by rw [Nat.zero_add])


end ValF

section ValG
open NockvmE2E.Exec.SM NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Merkle.Fri NockvmE2E.Lift NockvmE2E.Lift.Alternating

variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC} (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (L : FriLeaves (ω := ω) s) (enc : KC ↪ DgJ8)

/-- `ValF` from the per-tree facts on the openings `mkOpeningD (ts.getD (b - i) _) (L.skel b)` -/
theorem valF_openAll (lv : ℕ → ℕ → KC) : (c i : ℕ) → (h : i + c = k) → (ts : List (FTree DgJ8)) →
    (∀ b (hb : b < k), i ≤ b → b < i + c → ∀ (o : BatchOpening DgJ8 (L.skel ⟨b, hb⟩)),
      o = mkOpeningD (ts.getD (b - i) ⟨fun _ => false, fun _ => default, [], default⟩) (L.skel ⟨b, hb⟩) →
      ∀ t (hs : o.selector.get t = true), selectedValueAt o.values t hs = enc (lv b (leafNum t))) →
    E2EFri.ValF (ω := ω) s d l L DgJ8 enc lv i c h (openAllOf _ ts)
  | 0, _, _, _, _ => trivial
  | c + 1, i, h, ts, hh => ⟨fun t ht => hh i (by omega) le_rfl (by omega) _
        (by simp only [Nat.sub_self]; cases ts <;> rfl) t ht,
      valF_openAll lv c i.succ (by omega) ts.tail (fun b hb h1 h2 o ho t ht => hh b hb (by omega) (by omega) o (by
        have e : ts.getD (b - i) ⟨fun _ => false, fun _ => default, [], default⟩ =
            ts.tail.getD (b - (i + 1)) ⟨fun _ => false, fun _ => default, [], default⟩ := by
          have e1 : b - i = (b - (i + 1)) + 1 := by omega
          rw [e1]; cases ts <;> simp
        rw [e]; exact ho) t ht)⟩

end ValG

/-- **the leaf-digest fact on the free embedding `enc`**: the digest of a canonical `K3` leaf `[a, b, c]` is `dgOf [a, b, c, 0, 0]`
(an instance fact: `enc` is a free `KC ↪ DgJ8` in `exec_e2e`; the embedded leaf digests are `dgOf [a,b,c,0,0]`) -/
def EncOK (enc : KC ↪ DgJ8) : Prop :=
  ∀ a b c : ℕ, a < NockvmE2E.Exec.p → b < NockvmE2E.Exec.p → c < NockvmE2E.Exec.p →
    enc (toKV (VF.K3.ofLimbs [a, b, c])) = dgOf [a, b, c, 0, 0]


/-- a concrete `enc : KC ↪ DgJ8` with `EncOK` (non-vacuity of the `EncOK` premise): the three residues of `y`, then two zeros -/
noncomputable def sK : KC → Exec.K3 := Function.surjInv Exec.K3.toK_surjective

theorem toK_sK (y : KC) : (sK y).toK = y := Function.surjInv_eq Exec.K3.toK_surjective y

noncomputable def encK : KC ↪ DgJ8 where
  toFun y := ![(sK y).c0.toZ, (sK y).c1.toZ, (sK y).c2.toZ, 0, 0]
  inj' := by
    intro y y' h
    have h0 : (sK y).c0.toZ = (sK y').c0.toZ := congrFun h 0
    have h1 : (sK y).c1.toZ = (sK y').c1.toZ := congrFun h 1
    have h2 : (sK y).c2.toZ = (sK y').c2.toZ := congrFun h 2
    have : sK y = sK y' := by
      cases hh : sK y with
      | mk a0 a1 a2 =>
        cases hh' : sK y' with
        | mk b0 b1 b2 =>
          rw [hh, hh'] at h0 h1 h2
          simp only [Exec.K3.mk.injEq]
          exact ⟨Gold.toZ_injective h0, Gold.toZ_injective h1, Gold.toZ_injective h2⟩
    rw [← toK_sK y, ← toK_sK y', this]

theorem encK_ok : EncOK encK := by
  intro a b c ha hb hc
  have hp64 : NockvmE2E.Exec.p < 18446744073709551616 := by rw [p_lit]; norm_num
  have ha64 : a < 18446744073709551616 := ha.trans hp64
  have hb64 : b < 18446744073709551616 := hb.trans hp64
  have hc64 : c < 18446744073709551616 := hc.trans hp64
  have hinj : sK (toKV (VF.K3.ofLimbs [a, b, c])) = t3 (VF.K3.ofLimbs [a, b, c]) := by
    apply Exec.K3.toK_injective
    rw [toK_sK, toKV_eq_toK]
  funext i
  show ![_, _, _, (0 : ZMod NockvmE2E.Exec.p), (0 : ZMod NockvmE2E.Exec.p)] i = _
  rw [hinj]
  fin_cases i <;> simp [t3, Gold.ofU64_toZ, VF.K3.ofLimbs, dgOf, Nat.mod_eq_of_lt ha64, Nat.mod_eq_of_lt hb64, Nat.mod_eq_of_lt hc64]

section Main2
open NockvmE2E.Exec.E2EMain
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM

variable (XI0 : ExecInst) (hn32 : (XI170 XI0).nD ≤ 32)

set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD hn32
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ (XI170 XI0).nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ (XI170 XI0).nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ (XI170 XI0).nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (enc : KC ↪ DgJ8)
  (md : PointMaskData P.colRoundX (Fin (2 ^ (XI170 XI0).nD)) B DgJ8) (L : Fri.FriLeaves (ω := ωS) s1)
variable (hdom : 2 ^ (∑ j, ((s1) j).val) * d.val ≤ 2 ^ (XI170 XI0).nD)

set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin 4 s1 d (XI170 XI0).l DgJ8 enc md L (S := KC)
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := KC) s1 d (XI170 XI0).l DgJ8 enc L

set_option hygiene false in
local notation "GG" => CoreDefinitions.univariatePowersGenerator KC m
set_option hygiene false in
local notation "OPN" => OpenAll DgJ8 (merkleSkels (MC))

/-- **`hPdec`** at the concrete decoders (needs `d.val = XI0.d`, the one instance fact linking the FRI degree bound to the verifier's) -/
theorem hPdec_dsm {Statement Salt : Type} (hd : d.val = XI0.d)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt)
    (da : MDec (RM)) (dsb : RDec (batchRound KC))
    (g : (dd : NQuery (merkleSkels (MC)) ⊕ Key (Statement × Salt) PUnit (compiledRoundsK DgJ8 (OPN) (MC))) →
      succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)
    (z : Statement × Salt) (π : FlatProof)
    (hacc : AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ
      (mdAppend (RM) (BM) da (dsb, dsmC s1 d (XI170 XI0).l L enc)) g z π) (y : KC) :
    (E2EFri.finPolyOf s1 d (XI170 XI0).l L DgJ8 enc (OPN) 0 (XI170 XI0).k (by omega)
      (MA.sndK DgJ8 (OPN) (RM) (BM) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L
        (mdAppend (RM) (BM) da (dsb, dsmC s1 d (XI170 XI0).l L enc)) z (fun k => g (.inr k)) π)).2.2.2.2).eval y =
      SF.hornerF (fun j => homV.φ π.pfinal[j]!) π.pfinal.size y := by
  classical
  have hok := (verifyFlat_iff (XI170 XI0) _ _ (encZ z) π).mp hacc
  have hr : π.roots.size = 4 + (XI170 XI0).k := by
    obtain ⟨_, _, _, _, h5, _⟩ := hok
    simp only [Bool.and_eq_true, beq_iff_eq] at h5
    exact h5.1.1
  have hsz : π.pfinal.size = XI0.d := by
    obtain ⟨_, _, _, _, _, h6, _⟩ := hok
    simp only [Bool.and_eq_true, beq_iff_eq] at h6
    exact h6.1.2
  set ds := mdAppend (RM) (BM) da (dsb, dsmC s1 d (XI170 XI0).l L enc) with hds
  set ω0 := openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π) with hω0
  set fm := (msgsOf (XI170 XI0) π).toList with hfm
  have hm1 : pathMsgs _ (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L ds z (fun k => g (.inr k)) π) =
      decMsgs _ (mDecs dgOf (MC) ds ω0) fm :=
    pathMsgs_pathOf z _ _ _
  have hm2 := pathMsgs_sndK dgOf (RM) (BM) da (dsb, dsmC s1 d (XI170 XI0).l L enc) ω0 fm _ hm1
  have hm3 := congrArg Prod.snd (congrArg Prod.snd hm2)
  have hf := finPolyOf_dsFM (ω := ωS) s1 d (XI170 XI0).l L enc dgOf ω0 (XI170 XI0).k 0 (Nat.zero_add _) _
    (((fm.drop (RM).length).tail).tail) hm3
  have h6 : (RM).length = 6 := rfl
  have hlast : ((fm.drop (RM).length).tail.tail).getD (XI170 XI0).k [] = π.pfinal.toList.flatMap VF.K3.limbs := by
    rw [h6]
    have e1 : ((fm.drop 6).tail).tail = fm.drop 8 := by simp [List.tail_drop]
    rw [e1, E2E.getD_drop']
    simp only [hfm, msgsOf]
    have hr' : π.roots.size = 4 + XI0.k := hr
    have ht : (List.take XI0.k (List.drop 4 π.roots.toList)).length = XI0.k := by
      simp [List.length_take, List.length_drop]; omega
    simp [List.getD_eq_getElem?_getD, hr]
    rw [show 8 + XI0.k = XI0.k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    simp only [List.getElem?_cons_succ]
    change (List.take XI0.k (List.drop 4 π.roots.toList) ++ [List.flatMap VF.K3.limbs π.pfinal.toList])[XI0.k]?.getD [] = _
    rw [List.getElem?_append_right (by omega), ht]
    simp
  rw [hf, hlast, eval_finPolyD, hornerF_sum, length_flat, Array.length_toList]
  have hmin : min (3 * π.pfinal.size / 3) d.val = π.pfinal.size := by
    rw [hd, ← hsz]; omega
  rw [hmin]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have := ofLimbs_flat π.pfinal.toList j (by simpa using hj')
  rw [this]
  have h3 : π.pfinal.toList[j]! = π.pfinal[j]! := by
    simp [getElem!_pos, hj']
  rw [h3]; rfl

/-- **the four internal fields at the concrete decoders** (`hX`, `hcod0`, `hcod`, `hPdec`); `hvalF` is `valF_dsm` below -/
theorem resid_codec4 {Statement Salt : Type} (hD : DomLink (XI170 XI0) hn32) (hd : d.val = XI0.d)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt)
    (da : MDec (RM)) (dsb : RDec (batchRound KC)) :
    (∀ g z π (hv : AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ
        (mdAppend (RM) (BM) da (dsb, dsmC s1 d (XI170 XI0).l L enc)) g z π),
      ∀ (q : (protocol (compiledRoundsK DgJ8 (OPN) (friMerkleMask s1 d (XI170 XI0).l L DgJ8 enc 0 (XI170 XI0).k (by omega)))).tree.ExecutionPath)
        (j : Fin (XI170 XI0).l), (XsOf s1 d (XI170 XI0).l L DgJ8 enc (OPN) 0 (XI170 XI0).k (by omega) q j).val =
          homV.ψ (XI170 XI0).dShift * homV.ψ (XI170 XI0).dGen ^ ((E2ELR.lastEnc (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g)
            (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsmC s1 d (XI170 XI0).l L enc)) g) (encZ z) π hv d DgJ8 enc L (OPN) 0 (XI170 XI0).k (by omega)
            (E2ELR.sndD (RM) (BM) (mdAppend (RM) (BM) da (dsb, dsmC s1 d (XI170 XI0).l L enc))).2.2 q)[j.1]! % 2 ^ (XI170 XI0).nD)) ∧
    (∀ x, cast (foldChallenge_type (ω := ωS) s1 (XI170 XI0).l ⟨0, by omega⟩)
      (xp (a := ⟨0, by have := friLength (k := (XI170 XI0).k); omega⟩) (b := (foldChallenge (ω := ωS) s1 (XI170 XI0).l ⟨0, by omega⟩).val)
        (Fin.ext (by simp only [foldChallenge_val])) ((dsmC s1 d (XI170 XI0).l L enc).1.decC x)) = toKV (VF.K3.ofLimbs x)) ∧
    E2EFri.CodOK s1 d (XI170 XI0).l L DgJ8 enc (fun x => toKV (VF.K3.ofLimbs x)) 0 (XI170 XI0).k (by omega) (dsmC s1 d (XI170 XI0).l L enc).2 ∧
    (∀ g z π, AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ
        (mdAppend (RM) (BM) da (dsb, dsmC s1 d (XI170 XI0).l L enc)) g z π →
      ∀ y, (E2EFri.finPolyOf s1 d (XI170 XI0).l L DgJ8 enc (OPN) 0 (XI170 XI0).k (by omega)
        (MA.sndK DgJ8 (OPN) (RM) (BM) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L
          (mdAppend (RM) (BM) da (dsb, dsmC s1 d (XI170 XI0).l L enc)) z (fun k => g (.inr k)) π)).2.2.2.2).eval y =
        SF.hornerF (fun j => homV.φ π.pfinal[j]!) π.pfinal.size y) := by
  refine ⟨fun g z π hv q j => ?_, hcod0_dsmC s1 d (XI170 XI0).l L enc, codOK_dsFM s1 d (XI170 XI0).l L enc _ _ _, fun g z π hacc y => hPdec_dsm XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L hd encZ decZ da dsb g z π hacc y⟩
  exact hX_dsFM (XI170 XI0) _ _ (encZ z) π hv d enc L (OPN) hD _ _ _ q j

/-- **`hvalF` at the embedded openings** (needs `EncOK enc`, the skeleton facts `hL`, `hmd` of `exec_e2e`) -/
theorem valF_inst {Statement Salt : Type}
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (ds : MDec (MC))
    (hEnc : EncOK enc) (encB : B ↪ DgJ8) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb (XI170 XI0) r))
    (hn1 : 1 ≤ (XI170 XI0).nD) (hmd : md = mdX (XI170 XI0) hn1 P.colRoundX rk encB) (hL : L = LX (XI170 XI0) hn32)
    (g : (dd : NQuery (merkleSkels (MC)) ⊕ Key (Statement × Salt) PUnit (compiledRoundsK DgJ8 (OPN) (MC))) →
      succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)
    (z : Statement × Salt) (π : FlatProof)
    (hacc : AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ ds g z π) :
    E2EFri.ValF s1 d (XI170 XI0).l L DgJ8 enc (E2EFri.lvK (XI170 XI0) π) 0 (XI170 XI0).k (by omega)
      (MA.sndOpen (RM) (BM) (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π))) := by
  have hok := (verifyFlat_iff (XI170 XI0) _ _ (encZ z) π).mp hacc
  have hlist := hsk_list (S := KC) (XI170 XI0) _ _ (encZ z) π hacc P A R0 Rest RestV e I0 I Ifin 4 d enc md L encB rk hmd hL rfl
  have hlen : (merkleSkels (MC)).length = 4 + (XI170 XI0).k := by rw [hlist]; simp
  have hsk : ∀ j (hj : j < (merkleSkels (MC)).length), (merkleSkels (MC)).get ⟨j, hj⟩ = skelFlat (XI170 XI0) j := by
    intro j hj; simp [hlist]
  have hlen4 : (merkleSkels (RM)).length = 4 := by
    show (merkleSkels (RapP.rapMerkleMask Φ KC md.toRapMaskData (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I Ifin 0 4)).length = 4
    rw [merkleSkels_rapMerkleMask (Φ := Φ) (K := KC)]; simp
  rw [E2E.sndOpen_openAllOf, hlen4]
  refine valF_openAll (ω := ωS) s1 d (XI170 XI0).l L enc _ _ _ _ _ ?_
  intro b hb _ _ o ho t hs
  have hj : 4 + b < (merkleSkels (MC)).length := by omega
  have hget : ((flatTrees (XI170 XI0) π).drop 4).getD (b - 0) ⟨fun _ => false, fun _ => default, [], default⟩ = ftree (XI170 XI0) π (4 + b) := by
    rw [Nat.sub_zero, ← ftree_getD (XI170 XI0) π (4 + b) (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm 4 b]
  have hsL : L.skel ⟨b, hb⟩ = (merkleSkels (MC)).get ⟨4 + b, hj⟩ := by
    rw [hsk]
    subst hL
    show skelOf _ _ _ = _
    simp only [skelFlat]
    have : ¬ 4 + b < 4 := by omega
    have e3 : 4 + b - 3 = b + 1 := by omega
    simp only [this, ite_false, e3]
    rfl
  have hv := open_val (XI170 XI0) _ _ π (merkleSkels (MC)) _ hok hlen hsk ⟨4 + b, hj⟩ (by simp)
    _ hget _ hsL
  subst ho
  rw [hv t hs, hget]
  have hlim := flatOk_limbs (XI170 XI0) _ _ (encZ z) π hok
  have hb : ∀ a r, (π.vals[a]!)[r]! < NockvmE2E.Exec.p := fun a r => arr_get_lt (a := π.vals) (fun v hv x hx => hlim.2.2.2 v hv x hx) a r
  have h4' : ¬ 4 + b < 4 := by omega
  show dgOf _ = enc (homV.φ (friAtV π.vals (4 + b) (lb (selsOf (XI170 XI0) π)[4 + b]! (leafNum t))))
  unfold friAtV
  rw [show homV.φ _ = toKV _ from rfl, hEnc _ _ _ (hb _ _) (hb _ _) (hb _ _)]
  simp [ftree, ftreeOf, h4']

/-- **the five codec/internal fields of `Resid`** (`hX`, `hcod0`, `hcod`, `hvalF`, `hPdec`; all but `hU`, `hW0`) at a decoder tuple `dsm` -/
structure ResidCodec {Statement Salt : Type} (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt)
    (da : MDec (RM)) (dsb : RDec (batchRound KC)) (dsm : MDec (friMask s1 d (XI170 XI0).l L DgJ8 enc)) : Prop where
  hX : ∀ g z π (hv : AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g z π),
    ∀ (q : (protocol (compiledRoundsK DgJ8 (OPN) (friMerkleMask s1 d (XI170 XI0).l L DgJ8 enc 0 (XI170 XI0).k (by omega)))).tree.ExecutionPath)
      (j : Fin (XI170 XI0).l), (XsOf s1 d (XI170 XI0).l L DgJ8 enc (OPN) 0 (XI170 XI0).k (by omega) q j).val =
        homV.ψ (XI170 XI0).dShift * homV.ψ (XI170 XI0).dGen ^ ((E2ELR.lastEnc (XI170 XI0) (HT XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L g)
          (FST XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L decZ (mdAppend (RM) (BM) da (dsb, dsm)) g) (encZ z) π hv d DgJ8 enc L (OPN) 0 (XI170 XI0).k (by omega)
          (E2ELR.sndD (RM) (BM) (mdAppend (RM) (BM) da (dsb, dsm))).2.2 q)[j.1]! % 2 ^ (XI170 XI0).nD)
  hcod0 : ∀ x, cast (foldChallenge_type (ω := ωS) s1 (XI170 XI0).l ⟨0, by omega⟩)
      (xp (a := ⟨0, by have := friLength (k := (XI170 XI0).k); omega⟩) (b := (foldChallenge (ω := ωS) s1 (XI170 XI0).l ⟨0, by omega⟩).val)
        (Fin.ext (by simp only [foldChallenge_val])) (dsm.1.decC x)) = toKV (VF.K3.ofLimbs x)
  hcod : E2EFri.CodOK s1 d (XI170 XI0).l L DgJ8 enc (fun x => toKV (VF.K3.ofLimbs x)) 0 (XI170 XI0).k (by omega) dsm.2
  hvalF : ∀ g z π, AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g z π →
    E2EFri.ValF s1 d (XI170 XI0).l L DgJ8 enc (E2EFri.lvK (XI170 XI0) π) 0 (XI170 XI0).k (by omega)
      (MA.sndOpen (RM) (BM) (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)))
  hPdec : ∀ g z π, AccF XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ (mdAppend (RM) (BM) da (dsb, dsm)) g z π →
    ∀ y, (E2EFri.finPolyOf s1 d (XI170 XI0).l L DgJ8 enc (OPN) 0 (XI170 XI0).k (by omega)
      (MA.sndK DgJ8 (OPN) (RM) (BM) (EP XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L (mdAppend (RM) (BM) da (dsb, dsm)) z (fun k => g (.inr k)) π)).2.2.2.2).eval y =
      hornerF (fun j => homV.φ π.pfinal[j]!) π.pfinal.size y

/-- **`resid_codec`**: the five fields at the concrete decoders `dsmC`, from the J-8 instance facts `DomLink`, `d = XI0.d`, `EncOK enc`, and the skeleton
facts `hL`, `hmd` that `exec_e2e` already carries -/
theorem resid_codec {Statement Salt : Type} (hD : DomLink (XI170 XI0) hn32) (hd : d.val = XI0.d) (hEnc : EncOK enc)
    (encB : B ↪ DgJ8) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb (XI170 XI0) r))
    (hn1 : 1 ≤ (XI170 XI0).nD) (hmd : md = mdX (XI170 XI0) hn1 P.colRoundX rk encB) (hL : L = LX (XI170 XI0) hn32)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt)
    (da : MDec (RM)) (dsb : RDec (batchRound KC)) :
    ResidCodec XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ da dsb (dsmC s1 d (XI170 XI0).l L enc) := by
  obtain ⟨hX, hc0, hc, hP⟩ := resid_codec4 XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L hD hd encZ decZ da dsb
  exact ⟨hX, hc0, hc, fun g z π hacc => valF_inst XI0 hn32 P A R0 Rest RestV e I0 I Ifin d enc md L encZ decZ _ hEnc encB rk hn1 hmd hL g z π hacc, hP⟩


end Main2

end NockvmE2E.Exec.E2EResid
#print axioms NockvmE2E.Exec.E2EResid.limbs_surj
#print axioms NockvmE2E.Exec.E2EResid.dsmC
#print axioms NockvmE2E.Exec.E2EResid.codOK_dsFM
#print axioms NockvmE2E.Exec.E2EResid.hcod0_dsmC
#print axioms NockvmE2E.Exec.E2EResid.hX_dsFM
#print axioms NockvmE2E.Exec.E2EResid.hPdec_dsm
#print axioms NockvmE2E.Exec.E2EResid.encK_ok
#print axioms NockvmE2E.Exec.E2EResid.valF_inst
#print axioms NockvmE2E.Exec.E2EResid.resid_codec4
#print axioms NockvmE2E.Exec.E2EResid.resid_codec
