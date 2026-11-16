/-
(generic part of the tie): `HtieG` from a per-table tie.  The twin of the re-indexing half of `TieJ8G.htie_J8`
(`gfilter`, `himg_of`, `TieJ8.fiber_global`) over an arbitrary bundle `InstG F J XI` (`dec` an equivalence, `rt` the routes):
`htieG_of` reduces `HtieG IG hsz npub tp hcap pr chalK` to the statement `TabTieG` about ONE table of `J` (the dec-indexed
constraint values of the table against the loaded chip's DAG value), which is the only part that depends on the chips (`tieAt9`).
-/
import NockvmE2E.Exec.E2EGen

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Polynomial

namespace NockvmE2E.Exec.E2EGenT

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.E2EGen NockvmE2E.Exec.ShapeF NockvmE2E.Exec.DagSem
open NockvmE2E.J8 NockvmE2E.Rap
open NockvmE2E.J8.TieJ8 (Route cf KN)
open NockvmE2E.J8.TieJ8G (sizes nsK sizes_length sizes_get flatIdx_off flatIdx_fst_lt flatIdx_snd_lt flatIdx_inv off_lt off_inj tabX
  gbJ gbJ_cf chalK)

/-- `cf` at the `Exec` field type (the two names of the field agree by unfolding only) -/
noncomputable def cfC (k : ℕ) : NockvmE2E.Exec.KC := cf k

theorem cfC_eq (k : ℕ) : cfC k = cf k := rfl

/-! ## 1. the fiber over a flat DAG gate -/

section Gfilter
variable {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI) (hsz : HSzG IG)

set_option maxRecDepth 8000 in
theorem gfilterG (i : Fin (nsK XI)) :
    (Finset.univ.filter fun j : Fin IG.R.ns' => (GflatG IG hsz).grp j = i) =
      Finset.univ.filter fun j : Fin IG.R.ns' => tkG IG j = tabX XI i ∧ (rOfG IG j).1 = (flatIdx (sizes XI) i.1).2 := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hi : i.1 < (sizes XI).sum := i.2
  have ht : (tkG IG j).1 < (sizes XI).length := by rw [sizes_length]; exact (tkG IG j).2
  have hfj := flatIdx_off (sizes XI) _ _ ht (by rw [sizes_get]; exact rOfG_lt_cons IG hsz j)
  constructor
  · intro h
    have h' : ((sizes XI).take (tkG IG j).1).sum + (rOfG IG j).1 = i.1 := congrArg Fin.val h
    rw [h'] at hfj
    have e1 : (tkG IG j).1 = (flatIdx (sizes XI) i.1).1 := (Prod.mk.inj hfj.symm).1
    exact ⟨Fin.ext e1, (Prod.mk.inj hfj.symm).2⟩
  · rintro ⟨h1, h2⟩
    apply Fin.ext
    show ((sizes XI).take (tkG IG j).1).sum + (rOfG IG j).1 = i.1
    have := flatIdx_inv (sizes XI) i.1 hi
    have h1' : (tkG IG j).1 = (flatIdx (sizes XI) i.1).1 := congrArg Fin.val h1
    rw [h1', h2]; exact this

/-- the image of the instance-side fiber under the restriction `ρ` is the dec-indexed fiber of `J` -/
theorem himgG (t' : Fin XI.tabs.size) (s : Fin J.T) (hsd : s = IG.σ t') (l : ℕ) :
    (Finset.univ.filter fun j : Fin IG.R.ns' => tkG IG j = t' ∧ (rOfG IG j).1 = l).image IG.R.ρ =
      Finset.univ.filter (fun j' : Fin J.ns => (IG.dec j').1 = s ∧ ((IG.rt s).route (IG.dec j').2).1 = l) := by
  have hsj : ∀ j : Fin IG.R.ns', tkG IG j = t' → sOfG IG j = s := by
    intro j hj
    rw [← sOfG_eq, hj, hsd]
  have hrj : ∀ j : Fin IG.R.ns', tkG IG j = t' → rOfG IG j = (IG.rt s).route ((IG.dec (IG.R.ρ j)).2 : ℕ) := by
    intro j hj
    unfold rOfG lOfG
    rw [hsj j hj]
  refine Finset.ext fun (j' : Fin J.ns) => ?_
  constructor
  · intro hm
    obtain ⟨j, hj, hjj⟩ := Finset.mem_image.mp hm
    have hj' := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [← hjj]; exact hsj j hj'.2.1
    · rw [← hjj, ← hrj j hj'.2.1]; exact hj'.2.2
  · intro hm
    obtain ⟨-, h1, h2⟩ := (Finset.mem_filter).mp hm
    obtain ⟨k, hk⟩ : ∃ k, IG.R.ρ k = j' := by
      obtain ⟨k, hk⟩ := IG.R.hρcov j' (Fin.cast IG.hT.symm t') (by
        rw [IG.hσR]
        simp only [Fin.cast_cast, Fin.cast_eq_self]
        rw [← hsd, ← IG.hdec]; exact h1.symm)
      exact ⟨k, hk⟩
    have hsk : sOfG IG k = s := by
      unfold sOfG; rw [hk]; exact h1
    have htk : tkG IG k = t' := IG.hσinj (by rw [sOfG_eq, hsk, hsd])
    refine Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htk, ?_⟩, hk⟩
    rw [hrj k htk, hk]; exact h2

end Gfilter

/-! ## 2. the fiber sum over a routed table (generic `dec`) -/

section Fiber
variable {T ns : ℕ} {nloc : Fin T → ℕ} (dec : Fin ns ≃ (Σ s : Fin T, Fin (nloc s))) (rt : Fin T → Route)

theorem fiber_globalG (hN : ∀ t, (rt t).N = nloc t) (t : Fin T) (ℓ : ℕ) (hℓ : ℓ < (rt t).nK) (Fv : Fin ns → NockvmE2E.Exec.KC) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin ns => (dec j).1 = t ∧ ((rt t).route ((dec j).2 : ℕ)).1 = ℓ),
        cfC ((rt t).route ((dec j).2 : ℕ)).2 * Fv j =
      ∑ k ∈ Finset.range ((rt t).mult ℓ), cfC k *
        (if h : (rt t).jOf ℓ k < nloc t then Fv (dec.symm ⟨t, ⟨(rt t).jOf ℓ k, h⟩⟩) else 0) := by
  have hlt : ∀ k, k < (rt t).mult ℓ → (rt t).jOf ℓ k < nloc t := fun k hk => by
    have := ((rt t).h2 ℓ hℓ k hk).1; rw [hN t] at this; exact this
  have hdec : ∀ j : Fin ns, (dec j).1 = t →
      ∃ h : ((dec j).2 : ℕ) < nloc t, j = dec.symm ⟨t, ⟨((dec j).2 : ℕ), h⟩⟩ := by
    intro j hj
    obtain ⟨⟨t', l'⟩, hjj⟩ : ∃ x, dec j = x := ⟨_, rfl⟩
    rw [hjj] at hj
    simp only at hj
    subst hj
    have hl : ((dec j).2 : ℕ) = (l' : ℕ) := by rw [hjj]
    have hlt' : ((dec j).2 : ℕ) < nloc t' := by rw [hl]; exact l'.2
    refine ⟨hlt', ?_⟩
    have e1 : j = dec.symm ⟨t', l'⟩ := by rw [← hjj, Equiv.symm_apply_apply]
    have e2 : (⟨t', l'⟩ : Σ t, Fin (nloc t)) = ⟨t', ⟨((dec j).2 : ℕ), hlt'⟩⟩ := Sigma.ext rfl (heq_of_eq (Fin.ext hl.symm))
    rw [← e2]; exact e1
  refine Finset.sum_bij' (fun j _ => ((rt t).route ((dec j).2 : ℕ)).2)
    (fun k hk => dec.symm ⟨t, ⟨(rt t).jOf ℓ k, hlt k (Finset.mem_range.mp hk)⟩⟩) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hl, _⟩ := hdec j hj.1
    have hl' : ((dec j).2 : ℕ) < (rt t).N := by rw [hN]; exact hl
    have := ((rt t).h1 ((dec j).2 : ℕ) hl').2.1
    rw [hj.2] at this
    exact Finset.mem_range.mpr this
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hk' := Finset.mem_range.mp hk
    refine ⟨by rw [Equiv.apply_symm_apply], ?_⟩
    rw [Equiv.apply_symm_apply]
    exact congrArg Prod.fst ((rt t).h2 ℓ hℓ k hk').2
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hl, hjj⟩ := hdec j hj.1
    have hl' : ((dec j).2 : ℕ) < (rt t).N := by rw [hN]; exact hl
    have h3 := ((rt t).h1 ((dec j).2 : ℕ) hl').2.2
    rw [hj.2] at h3
    conv_rhs => rw [hjj]
    congr 2
    exact Fin.ext h3
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    show ((rt t).route ((dec (dec.symm ⟨t, ⟨(rt t).jOf ℓ k, hlt k hk'⟩⟩)).2 : ℕ)).2 = k
    rw [Equiv.apply_symm_apply]
    exact congrArg Prod.snd ((rt t).h2 ℓ hℓ k hk').2
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hl, hjj⟩ := hdec j hj.1
    have hl' : ((dec j).2 : ℕ) < (rt t).N := by rw [hN]; exact hl
    have h3 := ((rt t).h1 ((dec j).2 : ℕ) hl').2.2
    rw [hj.2] at h3
    have h4 : (rt t).jOf ℓ ((rt t).route ((dec j).2 : ℕ)).2 < nloc t := by rw [h3]; exact hl
    show cfC _ * Fv j = cfC _ * (if h : (rt t).jOf ℓ ((rt t).route ((dec j).2 : ℕ)).2 < nloc t then _ else 0)
    rw [dif_pos h4]
    congr 2
    conv_lhs => rw [hjj]
    congr 2
    exact Fin.ext h3.symm

end Fiber

/-! ## 3. valuations -/

section Val
variable {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI)
  (npub : ℕ) (tp : Fin IG.Jm.T) (hcap : IG.Cap npub)

/-- the valuation of `J` induced by a valuation of the final interface (absent columns `0`) -/
noncomputable def valJ (val : (IG.JJ npub tp hcap).ι0 × Fin (IG.JJ npub tp hcap).r → NockvmE2E.Exec.KC) :
    J.ι0 × Fin J.r → NockvmE2E.Exec.KC :=
  fun q => @dite _ (IG.R.p q.1) (IG.R.dp q.1) (fun h => val (Sum.inl ⟨q.1, h⟩, q.2)) (fun _ => 0)

theorem valJ_apply (val : (IG.JJ npub tp hcap).ι0 × Fin (IG.JJ npub tp hcap).r → NockvmE2E.Exec.KC) (j : J.ι0) (h : IG.R.p j)
    (k : Fin J.r) : valJ IG npub tp hcap val (j, k) = val (Sum.inl ⟨j, h⟩, k) := dif_pos h

/-- `aeval` of a constraint of the final interface is `aeval` of the `J` constraint at the induced valuation -/
theorem aeval_JJ_C_G (χ : Coins J.Φ0 NockvmE2E.Exec.KC) (M : J.Msg) (j : Fin IG.R.ns')
    (val : (IG.JJ npub tp hcap).ι0 × Fin (IG.JJ npub tp hcap).r → NockvmE2E.Exec.KC) :
    MvPolynomial.aeval (R := ZMod NockvmE2E.Exec.p) val ((IG.JJ npub tp hcap).C χ M j) =
      MvPolynomial.aeval (valJ IG npub tp hcap val) (J.C χ M (IG.R.ρ j)) := by
  have h1 : MvPolynomial.aeval (R := ZMod NockvmE2E.Exec.p) val ((IG.JJ npub tp hcap).C χ M j) =
      MvPolynomial.aeval (R := ZMod NockvmE2E.Exec.p) (val ∘ Prod.map Sum.inl id) (IG.Jm.C χ M j) :=
    MvPolynomial.aeval_rename (Prod.map Sum.inl id) val _
  refine h1.trans ?_
  exact aeval_minusT_C (A := NockvmE2E.Exec.KC) J IG.R IG.hfree χ M j (fun q => val (Prod.map Sum.inl id q))

end Val

/-! ## 4. `HtieG` from the per-table tie -/

section Htie
variable {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI) (hsz : HSzG IG)
  (npub : ℕ) (tp : Fin IG.Jm.T) (hcap : IG.Cap npub) (pr : PubRead (IG.JJ npub tp hcap))
  (chalK : Coins (IG.JJ npub tp hcap).Φ0 NockvmE2E.Exec.KC → ℕ → NockvmE2E.Exec.KC)

/-- **the tie of one table**: the weighted dec-indexed constraint values of table `σ t'` at the DAG gate `l` of its chip are the chip's
DAG value (the content of `TieAt9`) -/
def TabTieG : Prop :=
  ∀ (t' : Fin XI.tabs.size) (l : ℕ), l < (IG.rt (IG.σ t')).nK →
    ∀ (χ : Coins (IG.JJ npub tp hcap).Φ0 NockvmE2E.Exec.KC)
      (v val : (IG.JJ npub tp hcap).ι0 × Fin (IG.JJ npub tp hcap).r → NockvmE2E.Exec.KC),
      ∑ k ∈ Finset.range ((IG.rt (IG.σ t')).mult l), cfC k *
          (if h : (IG.rt (IG.σ t')).jOf l k < IG.nloc (IG.σ t') then
            MvPolynomial.aeval (valJ IG npub tp hcap val)
              (J.C χ (pr.rd (fun c => v (c, 0))) (IG.dec.symm ⟨IG.σ t', ⟨(IG.rt (IG.σ t')).jOf l k, h⟩⟩))
          else 0) =
        (evalDagK XI.tabs[t'].chip
          ⟨fun c => val (colJG IG npub tp hcap t' c, 0),
           fun c => val (colJG IG npub tp hcap t' c, ⟨1 % (IG.JJ npub tp hcap).r, Nat.mod_lt _ (NeZero.pos _)⟩),
           fun s => HdagU.coord0 (v (pubJG IG npub tp hcap t' s, 0)), chalK χ, XI.tabs[t'].chip.baseCols⟩)[l]!

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem htieG_of (TT : TabTieG IG npub tp hcap pr chalK) : HtieG IG hsz npub tp hcap pr chalK := by
  intro i χ v val
  have hi : i.1 < (sizes XI).sum := i.2
  have hlt1 : (flatIdx (sizes XI) i.1).2 < XI.tabs[tabX XI i].chip.cons.size := by
    have h := flatIdx_snd_lt (sizes XI) i.1 hi
    have e := sizes_get XI (flatIdx (sizes XI) i.1).1 (flatIdx_fst_lt _ _ hi)
    exact lt_of_lt_of_eq h e
  set t' : Fin XI.tabs.size := tabX XI i with ht'e
  set l : ℕ := (flatIdx (sizes XI) i.1).2 with hle
  have hlt : l < (IG.rt (IG.σ t')).nK := by rw [← hsz t']; exact hlt1
  rw [gfilterG IG hsz i]
  set M : J.Msg := pr.rd (fun c => v (c, 0)) with hM
  set s : Fin J.T := IG.σ t' with hsdef
  set Fs : Finset (Fin IG.R.ns') :=
    Finset.univ.filter (fun j : Fin IG.R.ns' => tkG IG j = t' ∧ (rOfG IG j).1 = l) with hFs
  let Fg : Fin J.ns → NockvmE2E.Exec.KC := fun j' =>
    MvPolynomial.aeval (valJ IG npub tp hcap val) (J.C χ M j')
  have hsj : ∀ j ∈ Fs, sOfG IG j = s := by
    intro j hj
    have hj' : tkG IG j = t' := (Finset.mem_filter.mp hj).2.1
    rw [← sOfG_eq, hj']
  have hrj : ∀ j ∈ Fs, rOfG IG j = (IG.rt s).route ((IG.dec (IG.R.ρ j)).2 : ℕ) := by
    intro j hj
    unfold rOfG lOfG
    rw [hsj j hj]
  have hB : ∀ j ∈ Fs, gbJ ((GflatG IG hsz).crd j) *
      MvPolynomial.aeval val ((IG.JJ npub tp hcap).C χ M j) =
        cfC ((IG.rt s).route ((IG.dec (IG.R.ρ j)).2 : ℕ)).2 * Fg (IG.R.ρ j) := by
    intro j hj
    rw [aeval_JJ_C_G IG npub tp hcap χ M j val]
    have h1 : gbJ ((GflatG IG hsz).crd j) = cfC (rOfG IG j).2 := gbJ_cf _
    rw [h1, hrj j hj]
  rw [Finset.sum_congr rfl hB]
  have himg : Fs.image IG.R.ρ = _ := himgG IG t' s hsdef l
  have hsum := Finset.sum_image (s := Fs) (g := IG.R.ρ)
    (f := fun j' : Fin J.ns => cfC ((IG.rt s).route ((IG.dec j').2 : ℕ)).2 * Fg j')
    (fun a _ b _ h => IG.R.hρ h)
  refine hsum.symm.trans ((Finset.sum_congr himg (fun _ _ => rfl)).trans
    ((fiber_globalG IG.dec IG.rt IG.hrtN s l hlt Fg).trans ?_))
  exact TT t' l hlt χ v val

end Htie

end NockvmE2E.Exec.E2EGenT

#print axioms NockvmE2E.Exec.E2EGenT.gfilterG
#print axioms NockvmE2E.Exec.E2EGenT.himgG
#print axioms NockvmE2E.Exec.E2EGenT.fiber_globalG
#print axioms NockvmE2E.Exec.E2EGenT.aeval_JJ_C_G
#print axioms NockvmE2E.Exec.E2EGenT.htieG_of
