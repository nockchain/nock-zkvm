/-
the J-9 AL twin of `J9A/TieJ9A.lean §8-§9`: the tie of each of the NINE tables of
`consT9L` (`J9AL/InstJ9AL.lean`) against the loaded chip's DAG values.  Tables `0..7` are J-9 A's (`tieAt9` is reused unchanged through
`consAt9L_old`); table `8` is the ALU (`tieD9_alu`, a no-ext template: `tie_nc'`, `chk_alu`, `decR_alu`, `fL_leaf`).
Not zero-knowledge.
-/
import NockvmE2E.J9AL.InstJ9AL
import NockvmE2E.J9AL.TieAluJ9AL
import NockvmE2E.J9A.TieJ9A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.J9AL.TieJ9AL

open NockvmE2E.Emit Nock.Emit
open Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open NockvmE2E.Exec NockvmE2E.Exec.DagSem
open NockvmE2E.J8.TieJ8
open NockvmE2E.J9A.InstJ9A
open NockvmE2E.J9A.TieJ9A
open NockvmE2E.J9AL.InstJ9AL
open NockvmE2E.J9AL.TieAluJ9AL
open NockvmE2E.J8.InstJ8 (Φ0 truncP P)
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.T0Tower
open Nock.TraceGenExe (powerBasis3 deltaF)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (slotVal)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8

/-! ## 1. the constraint function of the nine tables -/

/-- the `j`-th constraint of table `t` of `consT9L` as a function of the valuation (`0` out of range) -/
noncomputable def consAt9L (d : Datum9AL) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9L) (t : Fin 9) (val : Ι9L × Fin 2 → KN) (j : ℕ) : KN :=
  if h : j < sz9L d t then MvPolynomial.aeval val (consT9L d χ M t ⟨j, h⟩) else 0

/-- **the reuse lemma**: on the eight old tables `consAt9L` is `consAt9` at the restricted valuation -/
theorem consAt9L_old (d : Datum9AL) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9L) (s : Fin 8) (val : Ι9L × Fin 2 → KN) (j : ℕ) :
    consAt9L d χ M s.castSucc val j = consAt9 d.toA χ M.toA s (val ∘ Prod.map Sum.inl id) j := by
  fin_cases s <;>
  · unfold consAt9L consAt9
    split_ifs with h1 h2 h2
    · exact MvPolynomial.aeval_rename _ _ _
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rfl

/-! ## 2. the ALU table: the template, the column map, the constraint as `Aof` -/

theorem w_alu : Nock.Emit.aluTemplate.width 3 = 196 := by decide +kernel

theorem bc_alu : Nock.Emit.aluTemplate.baseCols = 94 := AluSZChipJ9.aluTemplateSZ_baseCols _

def eAlu (j : Fin (Nock.Emit.aluTemplate.width 3)) : Ι9L := iL (Fin.cast w_alu j)

theorem consAt9L_alu (d : Datum9AL) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9L) (val : Ι9L × Fin 2 → KN) (j : ℕ) :
    consAt9L d χ M 8 val j = Aof (evalA (mkEnvA eAlu val (slotVal powerBasis3 94 (AluSZChipJ9.chalsALJ8 deltaF χ))
      (slotVal powerBasis3 94 M.1.pubsL))) (Nock.Emit.aluTemplate.allGates powerBasis3) j := by
  unfold consAt9L Aof
  by_cases h : j < sz9L d 8
  · have h' : j < (Nock.Emit.aluTemplate.allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ ((Nock.Emit.aluTemplate.allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv eAlu val _ _ _
  · have h' : ¬ j < (Nock.Emit.aluTemplate.allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]

/-! ## 3. the tie of the ALU against the loaded chip -/

section TieD9L
variable (d : Datum9AL) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9L) (val : Ι9L × Fin 2 → KN)
  (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ)) (env : KEnv) (ch : NockvmE2E.Exec.Tr.Chip)

theorem tieD9_alu (ch : NockvmE2E.Exec.Tr.Chip)
    (hop : HopZero ch (Nock.Emit.emit_alu) ders cmeta ch.baseCols)
    (hbc : env.bc = 94)
    (hcur : ∀ n (hn : n < (Nock.Emit.aluTemplate).width 3), env.cur n = val (eAlu ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < (Nock.Emit.aluTemplate).width 3), env.next n = val (eAlu ⟨n, hn⟩, 1))
    (hE : NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ))
    (hY : SlotY (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 6, M.1.pubsL i = pubK env i) :
    ∀ ℓ < (ncRoute (Nock.Emit.aluTemplate).baseTransition.length (Nock.Emit.aluTemplate).mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute (Nock.Emit.aluTemplate).baseTransition.length (Nock.Emit.aluTemplate).mixedTransition.length).mult ℓ),
        cf k * consAt9L d χ M 8 val ((ncRoute (Nock.Emit.aluTemplate).baseTransition.length (Nock.Emit.aluTemplate).mixedTransition.length).jOf ℓ k) =
      (evalDagK ch env)[ℓ]! := by
  have hchk := chkT_all (chk_alu)
  refine tieD_gen ch _ _ (decL_of_decR decR_alu) ders cmeta hop env _
    (by rw [show (Nock.Emit.aluSpec).gates = ((TSpec.ofTemplate (Nock.Emit.aluTemplate)).rename Nock.Emit.fL id id).gates from rfl]
        exact dagVals_nc _ rfl rfl rfl rfl _ _) _ (length_tplVals _ _ _ _ _ _) _ ?_
  refine tie_nc' (consAt9L d χ M 8 val) (Nock.Emit.aluTemplate) rfl rfl rfl rfl eAlu val (AluSZChipJ9.chalsALJ8 deltaF χ) (M.1.pubsL)
    (cKmem (Nock.Emit.aluTemplate).baseCols ((Nock.Emit.aluTemplate).width 3) 6 chalAL)
    (cBmem ((Nock.Emit.aluTemplate).width 3)) Nock.Emit.fL (envE ders cmeta env) 6
    (fun j => by rw [bc_alu]; exact consAt9L_alu d χ M val j)
    (by show env.bc = _; rw [bc_alu]; exact hbc) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i ≤ 38 ∨ (40 ≤ i ∧ i < 106) := by simpa [cKmem, chalAL] using hi
      exact (chalsAL_eq χ i (by omega) (by omega)).trans (fL_leaf hE hY i (by omega) (by omega)).symm)
    (fun i hi => hpub i (by simpa [cKmem] using hi)) hchk.1 hchk.2

end TieD9L

/-! ## 4. the routing of the nine tables, and the uniform tie -/

/-- the routing of the nine J-9 AL tables onto their DAG gates -/
noncomputable def rt9L (d : Datum9AL) : Fin 9 → Route
  | 0 => rt9 d.toA 0
  | 1 => rt9 d.toA 1
  | 2 => rt9 d.toA 2
  | 3 => rt9 d.toA 3
  | 4 => rt9 d.toA 4
  | 5 => rt9 d.toA 5
  | 6 => rt9 d.toA 6
  | 7 => rt9 d.toA 7
  | 8 => ncRoute Nock.Emit.aluTemplate.baseTransition.length Nock.Emit.aluTemplate.mixedTransition.length

theorem rt9L_old (d : Datum9AL) (s : Fin 8) : rt9L d s.castSucc = rt9 d.toA s := by fin_cases s <;> rfl

theorem rt9L_N (d : Datum9AL) (t : Fin 9) : (rt9L d t).N = sz9L d t := by
  fin_cases t
  · exact rt9_N d.toA 0
  · exact rt9_N d.toA 1
  · exact rt9_N d.toA 2
  · exact rt9_N d.toA 3
  · exact rt9_N d.toA 4
  · exact rt9_N d.toA 5
  · exact rt9_N d.toA 6
  · exact rt9_N d.toA 7
  · exact (len_nc9 Nock.Emit.aluTemplate rfl rfl rfl rfl).symm

/-- the loaded verifier chip's `ders` of table `t`: the ALU reads the `y`-power slots as well -/
def dersL (s : Fin 9) : Array NockvmE2E.Exec.Aux.Der :=
  if s = 8 then NockvmE2E.Exec.J8Chips.jDers ++ Nock.Emit.yDers else NockvmE2E.Exec.J8Chips.jDers

theorem dersL_eight : dersL 8 = Nock.Emit.aluDers := if_pos rfl

theorem dersL_ne (s : Fin 9) (h : s ≠ 8) : dersL s = NockvmE2E.Exec.J8Chips.jDers := if_neg h

/-- the emitted DAG document of table `s` -/
def DOf9L (d : Datum9AL) : Fin 9 → DagGates
  | 0 => DOf9 d.toA 0
  | 1 => DOf9 d.toA 1
  | 2 => DOf9 d.toA 2
  | 3 => DOf9 d.toA 3
  | 4 => DOf9 d.toA 4
  | 5 => DOf9 d.toA 5
  | 6 => DOf9 d.toA 6
  | 7 => DOf9 d.toA 7
  | 8 => Nock.Emit.emit_alu

theorem DOf9L_old (d : Datum9AL) (s : Fin 8) : DOf9L d s.castSucc = DOf9 d.toA s := by fin_cases s <;> rfl

def bcOf9L : Fin 9 → ℕ
  | 0 => bcOf9 0 | 1 => bcOf9 1 | 2 => bcOf9 2 | 3 => bcOf9 3 | 4 => bcOf9 4 | 5 => bcOf9 5 | 6 => bcOf9 6 | 7 => bcOf9 7
  | 8 => 94

theorem bcOf9L_old (s : Fin 8) : bcOf9L s.castSucc = bcOf9 s := by fin_cases s <;> rfl

def wOf9L : Fin 9 → ℕ
  | 0 => wOf9 0 | 1 => wOf9 1 | 2 => wOf9 2 | 3 => wOf9 3 | 4 => wOf9 4 | 5 => wOf9 5 | 6 => wOf9 6 | 7 => wOf9 7
  | 8 => 196

theorem wOf9L_old (s : Fin 8) : wOf9L s.castSucc = wOf9 s := by fin_cases s <;> rfl

/-- the interface column of local column `n` of table `s` (total: out of range wraps) -/
def colI9L : Fin 9 → ℕ → Ι9L
  | 0, n => Sum.inl (colI9 0 n)
  | 1, n => Sum.inl (colI9 1 n)
  | 2, n => Sum.inl (colI9 2 n)
  | 3, n => Sum.inl (colI9 3 n)
  | 4, n => Sum.inl (colI9 4 n)
  | 5, n => Sum.inl (colI9 5 n)
  | 6, n => Sum.inl (colI9 6 n)
  | 7, n => Sum.inl (colI9 7 n)
  | 8, n => iL ⟨n % 196, Nat.mod_lt _ (by norm_num)⟩

theorem colI9L_old (s : Fin 8) (n : ℕ) : colI9L s.castSucc n = Sum.inl (colI9 s n) := by fin_cases s <;> rfl

theorem tabΙ9L_colI9L (s : Fin 9) (n : ℕ) : tabΙ9L (colI9L s n) = s := by
  fin_cases s <;> first | rfl | exact congrArg Fin.castSucc (tabΙ9_colI9 _ n)

theorem eAlu_eq9L (j : Fin (Nock.Emit.aluTemplate.width 3)) : eAlu j = colI9L 8 j.1 :=
  congrArg iL (Fin.ext (Nat.mod_eq_of_lt (lt_of_lt_of_eq j.2 w_alu)).symm)

/-- what `pr.rd` must hand the chip of table `s` -/
def PubsOK9L (M : Msg9L) (env : KEnv) : Fin 9 → Prop
  | 0 => PubsOK9 M.toA env 0
  | 1 => PubsOK9 M.toA env 1
  | 2 => PubsOK9 M.toA env 2
  | 3 => PubsOK9 M.toA env 3
  | 4 => PubsOK9 M.toA env 4
  | 5 => PubsOK9 M.toA env 5
  | 6 => PubsOK9 M.toA env 6
  | 7 => PubsOK9 M.toA env 7
  | 8 => ∀ i < 6, M.1.pubsL i = pubK env i

theorem PubsOK9L_old (M : Msg9L) (env : KEnv) (s : Fin 8) : PubsOK9L M env s.castSucc = PubsOK9 M.toA env s := by
  fin_cases s <;> rfl

/-- the numerals the emitted chips exist for (the ALU has none) -/
def NumOK9L (d : Datum9AL) : Fin 9 → Prop
  | 0 => NumOK9 d.toA 0
  | 1 => NumOK9 d.toA 1
  | 2 => NumOK9 d.toA 2
  | 3 => NumOK9 d.toA 3
  | 4 => NumOK9 d.toA 4
  | 5 => NumOK9 d.toA 5
  | 6 => NumOK9 d.toA 6
  | 7 => NumOK9 d.toA 7
  | 8 => True

theorem NumOK9L_old (d : Datum9AL) (s : Fin 8) : NumOK9L d s.castSucc = NumOK9 d.toA s := by fin_cases s <;> rfl

/-- the tie of one table against its loaded chip -/
def TieAt9L (d : Datum9AL) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9L) (val : Ι9L × Fin 2 → KN) (env : KEnv)
    (ch : NockvmE2E.Exec.Tr.Chip) (s : Fin 9) : Prop :=
  ∀ ℓ < (rt9L d s).nK, ∑ k ∈ Finset.range ((rt9L d s).mult ℓ), cf k * consAt9L d χ M s val ((rt9L d s).jOf ℓ k) =
    (evalDagK ch env)[ℓ]!

set_option maxHeartbeats 1600000 in
/-- **the J-9 AL per-table tie, uniformly in the table** (twin of `tieAt9`): the old eight tables are `tieAt9` unchanged -/
theorem tieAt9L (d : Datum9AL) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9L) (val : Ι9L × Fin 2 → KN)
    (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ)) (env : KEnv) (ch : NockvmE2E.Exec.Tr.Chip) (s : Fin 9)
    (hnum : NumOK9L d s) (hop : HopZero ch (DOf9L d s) ders cmeta ch.baseCols) (hbe : env.bc = bcOf9L s)
    (hcur : ∀ n < wOf9L s, env.cur n = val (colI9L s n, 0)) (hnext : ∀ n < wOf9L s, env.next n = val (colI9L s n, 1))
    (hE : NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ))
    (hY : s = 8 → SlotY (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : PubsOK9L M env s) :
    TieAt9L d χ M val env ch s := by
  rcases Fin.eq_castSucc_or_eq_last s with ⟨s', rfl⟩ | rfl
  · rw [NumOK9L_old] at hnum
    rw [DOf9L_old] at hop
    rw [bcOf9L_old] at hbe
    rw [wOf9L_old] at hcur hnext
    rw [PubsOK9L_old] at hpub
    have h := tieAt9 d.toA χ M.toA (val ∘ Prod.map Sum.inl id) ders cmeta env ch s' hnum hop hbe
      (fun n hn => by rw [hcur n hn, colI9L_old]; rfl) (fun n hn => by rw [hnext n hn, colI9L_old]; rfl) hE hpub
    intro ℓ hℓ
    rw [rt9L_old] at hℓ ⊢
    simp only [consAt9L_old]
    exact h ℓ hℓ
  · have hop' : HopZero ch Nock.Emit.emit_alu ders cmeta ch.baseCols := hop
    exact tieD9_alu d χ M val ders cmeta env ch hop' hbe
      (fun n hn => by rw [eAlu_eq9L]; exact hcur n (by have := hn; rwa [w_alu] at this))
      (fun n hn => by rw [eAlu_eq9L]; exact hnext n (by have := hn; rwa [w_alu] at this)) hE (hY rfl) hpub

/-! ## 5. the global fiber (nine tables): twin of `fiber_global9` -/

section Global9L
variable (sz : Fin 9 → ℕ)

/-- the local (within-table) index of a global constraint -/
def loc9L (j : Fin (∑ t : Fin 9, sz t)) : ℕ := ((finSigmaFinEquiv.symm j).2 : ℕ)

theorem loc_eq9L (j : Fin (∑ t : Fin 9, sz t)) : loc9L sz j = ((finSigmaFinEquiv.symm j).2 : ℕ) := rfl

theorem tabS_jglob9L (t : Fin 9) (l : Fin (sz t)) :
    (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨t, l⟩ : Fin (∑ t : Fin 9, sz t))).1 = t := by
  rw [Equiv.symm_apply_apply]

theorem loc_jglob9L (t : Fin 9) (l : Fin (sz t)) :
    loc9L sz (finSigmaFinEquiv ⟨t, l⟩) = l := by
  unfold loc9L; rw [Equiv.symm_apply_apply]

theorem fiber_global9L (rt : Fin 9 → Route) (hN : ∀ t, (rt t).N = sz t) (t : Fin 9) (ℓ : ℕ) (hℓ : ℓ < (rt t).nK)
    (F : Fin (∑ t : Fin 9, sz t) → KN) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (∑ t : Fin 9, sz t) =>
        (finSigmaFinEquiv.symm j).1 = t ∧ ((rt t).route (loc9L sz j)).1 = ℓ),
        cf ((rt t).route (loc9L sz j)).2 * F j =
      ∑ k ∈ Finset.range ((rt t).mult ℓ), cf k *
        (if h : (rt t).jOf ℓ k < sz t then F (finSigmaFinEquiv ⟨t, ⟨(rt t).jOf ℓ k, h⟩⟩) else 0) := by
  have hlt : ∀ k, k < (rt t).mult ℓ → (rt t).jOf ℓ k < sz t := fun k hk => by
    have := ((rt t).h2 ℓ hℓ k hk).1; rw [hN t] at this; exact this
  have hdec : ∀ j : Fin (∑ t : Fin 9, sz t), (finSigmaFinEquiv.symm j).1 = t →
      ∃ h : loc9L sz j < sz t, j = finSigmaFinEquiv ⟨t, ⟨loc9L sz j, h⟩⟩ := by
    intro j hj
    obtain ⟨⟨t', l'⟩, hjj⟩ : ∃ x, finSigmaFinEquiv.symm j = x := ⟨_, rfl⟩
    rw [hjj] at hj
    simp only at hj
    subst hj
    have hl : loc9L sz j = (l' : ℕ) := by unfold loc9L; rw [hjj]
    have hlt' : loc9L sz j < sz t' := by rw [hl]; exact l'.2
    refine ⟨hlt', ?_⟩
    have e1 : j = finSigmaFinEquiv ⟨t', l'⟩ := by rw [← hjj, Equiv.apply_symm_apply]
    have e2 : (⟨t', l'⟩ : Σ t, Fin (sz t)) = ⟨t', ⟨loc9L sz j, hlt'⟩⟩ := Sigma.ext rfl (heq_of_eq (Fin.ext hl.symm))
    rw [← e2]; exact e1
  refine Finset.sum_bij' (fun j _ => ((rt t).route (loc9L sz j)).2)
    (fun k hk => finSigmaFinEquiv ⟨t, ⟨(rt t).jOf ℓ k, hlt k (Finset.mem_range.mp hk)⟩⟩) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hl, _⟩ := hdec j hj.1
    have hl' : loc9L sz j < (rt t).N := by rw [hN]; exact hl
    have := ((rt t).h1 (loc9L sz j) hl').2.1
    rw [hj.2] at this
    exact Finset.mem_range.mpr this
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hk' := Finset.mem_range.mp hk
    refine ⟨by rw [Equiv.symm_apply_apply], ?_⟩
    rw [loc_jglob9L]
    exact congrArg Prod.fst ((rt t).h2 ℓ hℓ k hk').2
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hl, hjj⟩ := hdec j hj.1
    have hl' : loc9L sz j < (rt t).N := by rw [hN]; exact hl
    have h3 := ((rt t).h1 (loc9L sz j) hl').2.2
    rw [hj.2] at h3
    conv_rhs => rw [hjj]
    congr 2
    exact Fin.ext h3
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    show ((rt t).route (loc9L sz (finSigmaFinEquiv ⟨t, _⟩))).2 = k
    rw [loc_jglob9L]
    exact congrArg Prod.snd ((rt t).h2 ℓ hℓ k hk').2
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hl, hjj⟩ := hdec j hj.1
    have hl' : loc9L sz j < (rt t).N := by rw [hN]; exact hl
    have h3 := ((rt t).h1 (loc9L sz j) hl').2.2
    rw [hj.2] at h3
    have h4 : (rt t).jOf ℓ ((rt t).route (loc9L sz j)).2 < sz t := by rw [h3]; exact hl
    show cf _ * F j = cf _ * (if h : (rt t).jOf ℓ ((rt t).route (loc9L sz j)).2 < sz t then _ else 0)
    rw [dif_pos h4]
    congr 2
    conv_lhs => rw [hjj]
    congr 2
    exact Fin.ext h3.symm

end Global9L

theorem aeval_consT9L_eq (d : Datum9AL) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9L) (val : Ι9L × Fin 2 → KN)
    (σj : Σ t : Fin 9, Fin (sz9L d t)) :
    MvPolynomial.aeval val (consT9L d χ M σj.1 σj.2) = consAt9L d χ M σj.1 val (σj.2 : ℕ) := by
  unfold consAt9L
  rw [dif_pos σj.2.2]

end NockvmE2E.J9AL.TieJ9AL

#print axioms NockvmE2E.J9AL.TieJ9AL.consAt9L_old
#print axioms NockvmE2E.J9AL.TieJ9AL.consAt9L_alu
#print axioms NockvmE2E.J9AL.TieJ9AL.tieD9_alu
#print axioms NockvmE2E.J9AL.TieJ9AL.rt9L_N
#print axioms NockvmE2E.J9AL.TieJ9AL.tabΙ9L_colI9L
#print axioms NockvmE2E.J9AL.TieJ9AL.tieAt9L
#print axioms NockvmE2E.J9AL.TieJ9AL.fiber_global9L
#print axioms NockvmE2E.J9AL.TieJ9AL.aeval_consT9L_eq
