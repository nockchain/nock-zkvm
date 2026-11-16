/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/BindAL.lean

  **The `hdr` ↔ `preg` binding.**

  The ALU's `hdr` rows consume the keyRg `(idc, kc, vc, 0,0,0,0, 7)` and the op record `(idc, opc, 0,…,0, 6)`
  (`aluRegReqsOf`); the only service providers with entry-`7` tag `7` or `6` are the ALU's `preg` rows
  (`aluRegProvsOf`; every other provider's tag is excluded by `h7O`, e.g. `keyRgAL_disjoint_J` for the J keys).  A
  `preg` row has `sP = 1`, so it is one of the first `|prims|` rows (`PregOK`), and the gates `sP·(idc − pId)`,
  `sP·(opc − pOp)` bind its `idc`, `opc` to that primitive's id and op code.  The primitive ids are distinct
  (`hndP`), so the `preg` row of an id is unique; the verifier's pin `pinRgP` `(id, 1, idxP id, …, 7)` is served by
  that row, which fixes its `(kc, vc) = (1, idxP id)`.  Hence (**`hdr_binding`**): every `hdr` row has an
  `(id, op) ∈ prims` with `idc = id`, `kc = 1`, `vc = idxP id` and `opc = primCode op`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSumAL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.BindAL

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZRead (ag_zero)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG CopyG Op keyVecL)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps (aluEF aluEK alu_rowGates)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (PregOK pinRgP pinRgVec)
open Nock.Atoms (Fp)
open Module
open scoped Polynomial

noncomputable section

section Bind
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)
  {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp} {chals pubs : ℕ → K}

local notation "CH" => aluSZChipJ9 δ b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL
local notation "QL" => qAL δ b Pb tr chals pubs
local notation "E0" => alE0 (K := K) δ b Pb tr

/-! ## 1. Reading the two keys -/

theorem keyRg_ent {e : Env Fp} (c : Fin 8) :
    keyVecL (K := K) 8 keyRgE e c = algebraMap Fp K (((keyRgE : List (CoeffExpr Fp)).getD c (.const 0)).eval e) :=
  rfl

theorem keyRg_inj {e e' : Env Fp} (h : keyVecL (K := K) 8 keyRgE e = keyVecL (K := K) 8 keyRgE e') :
    e.trace idc = e'.trace idc ∧ e.trace kc = e'.trace kc ∧ e.trace vc = e'.trace vc := by
  have h0 := (algebraMap Fp K).injective (congrFun h 0)
  have h1 := (algebraMap Fp K).injective (congrFun h 1)
  have h2 := (algebraMap Fp K).injective (congrFun h 2)
  simp [keyRgE, keyRgRE, reE, CoeffExpr.eval, cv] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem opRec_inj {e e' : Env Fp} (h : keyVecL (K := K) 8 opRecE e = keyVecL (K := K) 8 opRecE e') :
    e.trace idc = e'.trace idc ∧ e.trace opc = e'.trace opc := by
  have h0 := (algebraMap Fp K).injective (congrFun h 0)
  have h1 := (algebraMap Fp K).injective (congrFun h 1)
  simp [opRecE, opRecRE, reE, CoeffExpr.eval, cv] at h0 h1
  exact ⟨h0, h1⟩

theorem keyRg_pin {e : Env Fp} {id idx : ℕ} (h : keyVecL (K := K) 8 keyRgE e = pinRgVec (p := Nock.Atoms.p) (K := K) id idx) :
    e.trace idc = (id : Fp) ∧ e.trace kc = 1 ∧ e.trace vc = (idx : Fp) := by
  have h0 := (algebraMap Fp K).injective (congrFun h 0)
  have h1 := (algebraMap Fp K).injective (congrFun h 1)
  have h2 := (algebraMap Fp K).injective (congrFun h 2)
  simp [keyRgE, keyRgRE, reE, CoeffExpr.eval, cv, pinRgVec, Nock.Jet.RapJetJ8.keyK] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem keyRg7 (e : Env Fp) : keyVecL (K := K) 8 keyRgE e ⟨7, by norm_num⟩ = algebraMap Fp K ((7 : ℕ) : Fp) := by
  simp [keyVecL, keyRgE, keyRgRE, reE, CoeffExpr.eval, tagRgP]

theorem opRec7 (e : Env Fp) : keyVecL (K := K) 8 opRecE e ⟨7, by norm_num⟩ = algebraMap Fp K ((6 : ℕ) : Fp) := by
  simp [keyVecL, opRecE, opRecRE, reE, CoeffExpr.eval, tagOp]

theorem pin7 (id idx : ℕ) :
    pinRgVec (p := Nock.Atoms.p) (K := K) id idx ⟨7, by norm_num⟩ = algebraMap Fp K ((7 : ℕ) : Fp) := by
  simp [pinRgVec, Nock.Jet.RapJetJ8.keyK, tagRgP]

theorem cast67 : ((7 : ℕ) : Fp) ≠ ((6 : ℕ) : Fp) :=
  Nock.Jet.RapJetJ8.ne_cast (by norm_num [Nock.Atoms.p, Nock.Field.p]) (by norm_num [Nock.Atoms.p, Nock.Field.p])
    (by norm_num)

/-! ## 2. The `preg` rows -/

/-- Column `2 + k` of an ALU row is the verifier's `preg` polynomial `preL k`. -/
theorem pre_col (hbind : (CH).BindsPreprocessing QL) (k : Fin 3) (i : Fin Pb.nL) :
    (E0 i).trace (2 + k) = (Pb.preL k).eval (Pb.nodesL i) := by
  have h2 : QL ⟨2 + k, by rw [aluSZ_width_eq]; omega⟩ = Pb.preL k := by
    have := hbind ⟨2 + k, by show 2 + (k : ℕ) < 5; omega⟩
    refine this.trans ?_
    show preOf Pb.hnL Pb.nodesL Pb.preL ⟨2 + k, _⟩ = _
    simp only [preOf]
    rw [dif_neg (by omega), dif_neg (by omega)]
    congr 1; ext; simp
  show (Reify.envOfTrace (qAL δ b Pb tr (fun _ => (0 : K)) (fun _ => (0 : K))) Pb.orbitL.ω (Pb.nodesL i)
    (slotVal b 94 (fun _ => (0 : K))) (slotVal b 94 (fun _ => (0 : K)))).trace (2 + k) = _
  rw [envOfTrace_trace _ _ _ _ _ (by rw [aluSZ_width_eq]; omega)]
  exact congrArg (fun P => Polynomial.eval (Pb.nodesL i) P) h2

/-- **A `preg` row** (`sP ≠ 0`) is the row of a primitive: `i < |prims|`, `idc = id`, `opc = primCode op`. -/
theorem preg_row (hsat : (CH).rap.Satisfies QL) (hbind : (CH).BindsPreprocessing QL)
    (hpre : PregOK Pb.nodesL Pb.prims Pb.preL) (i : Fin Pb.nL) (hs : (E0 i).trace sP ≠ 0) :
    ∃ hi : (i : ℕ) < Pb.prims.length,
      (E0 i).trace idc = ((Pb.prims[(i : ℕ)]'hi).1 : Fp) ∧
        (E0 i).trace opc = ((primCode (Pb.prims[(i : ℕ)]'hi).2 : ℕ) : Fp) := by
  obtain ⟨h0, h1, h2⟩ := hpre.2 i
  have c0 := pre_col δ b hbind 0 i
  have c1 := pre_col δ b hbind 1 i
  have c2 := pre_col δ b hbind 2 i
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, add_zero] at c0 c1 c2
  have hi : (i : ℕ) < Pb.prims.length := by
    by_contra hc
    apply hs
    show (E0 i).trace 2 = 0
    rw [c0, h0, if_neg hc]
  refine ⟨hi, ?_, ?_⟩
  · have g := ag_zero (alu_rowGates b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat i)
      (AluSZOps.Rows.mem_hdr (a := ar (.mul (cv sP) (.sub (cv idc) (cv pId)))) (by simp [gHdr]))
    simp only [AG.gate, ar, CoeffExpr.eval, cv] at g
    have hs1 : (E0 i).trace sP = 1 := by show (E0 i).trace 2 = 1; rw [c0, h0, if_pos hi]
    have g' : (E0 i).trace idc = (E0 i).trace pId := by
      have := g; change (E0 i).trace sP * ((E0 i).trace idc - (E0 i).trace pId) = 0 at this
      rw [hs1, one_mul] at this; exact sub_eq_zero.mp this
    rw [g']
    show (E0 i).trace (2 + 1) = _
    rw [c1, h1, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
  · have g := ag_zero (alu_rowGates b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat i)
      (AluSZOps.Rows.mem_hdr (a := ar (.mul (cv sP) (.sub (cv opc) (cv pOp)))) (by simp [gHdr]))
    simp only [AG.gate, ar, CoeffExpr.eval, cv] at g
    have hs1 : (E0 i).trace sP = 1 := by show (E0 i).trace 2 = 1; rw [c0, h0, if_pos hi]
    have g' : (E0 i).trace opc = (E0 i).trace pOp := by
      have := g; change (E0 i).trace sP * ((E0 i).trace opc - (E0 i).trace pOp) = 0 at this
      rw [hs1, one_mul] at this; exact sub_eq_zero.mp this
    rw [g']
    show (E0 i).trace (2 + 2) = _
    rw [c2, h2, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

/-- **Uniqueness of the `preg` row of an id** (`hndP`, ids `< p`). -/
theorem preg_unique (hndP : (Pb.prims.map Prod.fst).Nodup) (hlt : ∀ q ∈ Pb.prims, q.1 < Nock.Atoms.p)
    {j j' : ℕ} (hj : j < Pb.prims.length) (hj' : j' < Pb.prims.length)
    (h : ((Pb.prims[j]'hj).1 : Fp) = ((Pb.prims[j']'hj').1 : Fp)) : j = j' := by
  have e : (Pb.prims[j]'hj).1 = (Pb.prims[j']'hj').1 := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt _ (List.getElem_mem hj)),
      Nat.mod_eq_of_lt (hlt _ (List.getElem_mem hj'))] at h
    exact h
  have e' : (Pb.prims.map Prod.fst)[j]'(by simpa using hj) = (Pb.prims.map Prod.fst)[j']'(by simpa using hj') := by
    simpa using e
  exact (List.Nodup.getElem_inj_iff hndP).mp e'

/-- A served key with entry-`7` tag `7` or `6` is a `preg` provide. -/
theorem served_reg {pO : List ((Fin 8 → K) × K)}
    (h7O : ∀ q ∈ pO, q.1 ⟨7, by norm_num⟩ ≠ algebraMap Fp K ((7 : ℕ) : Fp) ∧
      q.1 ⟨7, by norm_num⟩ ≠ algebraMap Fp K ((6 : ℕ) : Fp))
    {c : Fin 8 → K} (hc : c ∈ (aluRegProvsOf (K := K) δ b Pb tr ++ pO).map Prod.fst)
    (h7 : c ⟨7, by norm_num⟩ = algebraMap Fp K ((7 : ℕ) : Fp) ∨ c ⟨7, by norm_num⟩ = algebraMap Fp K ((6 : ℕ) : Fp)) :
    ∃ j : Fin Pb.nL, (E0 j).trace sP ≠ 0 ∧ (c = keyVecL 8 keyRgE (E0 j) ∨ c = keyVecL 8 opRecE (E0 j)) := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_append.mp hq with hR | hO
  · obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hR
    by_cases hz : (E0 j).trace sP * (E0 j).trace mP = 0
    · simp only [hz, if_true] at hj; simp at hj
    · simp only [hz, if_false, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
      refine ⟨j, left_ne_zero_of_mul hz, ?_⟩
      rcases hj with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  · exfalso
    obtain ⟨n7, n6⟩ := h7O q hO
    rcases h7 with h | h
    · exact n7 h
    · exact n6 h

/-! ## 3. The binding -/

/-- **`hdr_binding`**: every `hdr` row's keyRg and op record are those of the unique `preg` row of its id, whose
`(kc, vc)` the verifier pin fixes to `(1, idxP id)`. -/
theorem hdr_binding (hsat : (CH).rap.Satisfies QL) (hbind : (CH).BindsPreprocessing QL)
    (hpre : PregOK Pb.nodesL Pb.prims Pb.preL) (hndP : (Pb.prims.map Prod.fst).Nodup)
    (hlt : ∀ q ∈ Pb.prims, q.1 < Nock.Atoms.p)
    {pO : List ((Fin 8 → K) × K)}
    (h7O : ∀ q ∈ pO, q.1 ⟨7, by norm_num⟩ ≠ algebraMap Fp K ((7 : ℕ) : Fp) ∧
      q.1 ⟨7, by norm_num⟩ ≠ algebraMap Fp K ((6 : ℕ) : Fp))
    (hserv : ∀ c ∈ aluRegReqsOf (K := K) δ b Pb tr ++ pinRgP (p := Nock.Atoms.p) (K := K) Pb,
      c ∈ (aluRegProvsOf (K := K) δ b Pb tr ++ pO).map Prod.fst)
    (i : Fin Pb.nL) (hH : (E0 i).trace sH ≠ 0) :
    ∃ q ∈ Pb.prims, (E0 i).trace idc = (q.1 : Fp) ∧ (E0 i).trace kc = 1 ∧ (E0 i).trace vc = (Pb.idxP q.1 : Fp) ∧
      (E0 i).trace opc = ((primCode q.2 : ℕ) : Fp) := by
  have hmem : ∀ c ∈ [keyVecL (K := K) 8 keyRgE (E0 i), keyVecL (K := K) 8 opRecE (E0 i)],
      c ∈ aluRegReqsOf (K := K) δ b Pb tr ++ pinRgP (p := Nock.Atoms.p) (K := K) Pb := by
    intro c hc
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩)
    rw [if_neg hH]; exact hc
  have hne76 : algebraMap Fp K ((7 : ℕ) : Fp) ≠ algebraMap Fp K ((6 : ℕ) : Fp) :=
    fun e => cast67 ((algebraMap Fp K).injective e)
  -- the keyRg of row `i` is a `preg` row `j`'s keyRg
  obtain ⟨j, hsj, hRj⟩ := served_reg δ b h7O (hserv _ (hmem _ (by simp))) (Or.inl (keyRg7 (E0 i)))
  have hRj' : keyVecL (K := K) 8 keyRgE (E0 i) = keyVecL 8 keyRgE (E0 j) := by
    rcases hRj with h | h
    · exact h
    · exfalso; have := congrFun h ⟨7, by norm_num⟩; rw [keyRg7, opRec7] at this; exact hne76 this
  obtain ⟨hj, hidj, hopj⟩ := preg_row δ b hsat hbind hpre j hsj
  set q := Pb.prims[(j : ℕ)]'hj with hq
  have hqm : q ∈ Pb.prims := List.getElem_mem hj
  obtain ⟨ei, ek, ev⟩ := keyRg_inj hRj'
  -- the verifier pin of `q.1` is served by a `preg` row `j''`, which is `j`
  have hpinm : pinRgVec (p := Nock.Atoms.p) (K := K) q.1 (Pb.idxP q.1) ∈
      aluRegReqsOf (K := K) δ b Pb tr ++ pinRgP (p := Nock.Atoms.p) (K := K) Pb :=
    List.mem_append_right _ (List.mem_map.mpr ⟨q, hqm, rfl⟩)
  obtain ⟨j2, hsj2, hRj2⟩ := served_reg δ b h7O (hserv _ hpinm) (Or.inl (pin7 _ _))
  have hRj2' : keyVecL (K := K) 8 keyRgE (E0 j2) = pinRgVec (p := Nock.Atoms.p) (K := K) q.1 (Pb.idxP q.1) := by
    rcases hRj2 with h | h
    · exact h.symm
    · exfalso; have := congrFun h ⟨7, by norm_num⟩; rw [pin7, opRec7] at this; exact hne76 this
  obtain ⟨pi2, pk2, pv2⟩ := keyRg_pin hRj2'
  obtain ⟨hj2, hidj2, -⟩ := preg_row δ b hsat hbind hpre j2 hsj2
  have e2 : (j2 : ℕ) = j := preg_unique hndP (fun q hq => (hlt q hq)) hj2 hj (by rw [← hidj2, pi2])
  have ej : j2 = j := Fin.ext e2
  subst ej
  -- the op record of row `i` is a `preg` row `j3`'s, which is `j`
  obtain ⟨j3, hsj3, hOj3⟩ := served_reg δ b h7O (hserv _ (hmem _ (by simp))) (Or.inr (opRec7 (E0 i)))
  have hOj3' : keyVecL (K := K) 8 opRecE (E0 i) = keyVecL 8 opRecE (E0 j3) := by
    rcases hOj3 with h | h
    · exfalso; have := congrFun h ⟨7, by norm_num⟩; rw [opRec7, keyRg7] at this; exact hne76 this.symm
    · exact h
  obtain ⟨oi, oc⟩ := opRec_inj hOj3'
  obtain ⟨hj3, hidj3, hopj3⟩ := preg_row δ b hsat hbind hpre j3 hsj3
  have e3 : (j3 : ℕ) = j2 := preg_unique hndP (fun q hq => (hlt q hq)) hj3 hj (by rw [← hidj3, ← oi, ei, hidj])
  have ej3 : j3 = j2 := Fin.ext e3
  subst ej3
  refine ⟨q, hqm, by rw [ei, hidj], by rw [ek, pk2], by rw [ev, pv2], by rw [oc, hopj3]⟩

end Bind

end

end Nock.NockVMROM.Thm54.VclL.Handle.BindAL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.BindAL
#print axioms preg_row
#print axioms hdr_binding
end Axioms
