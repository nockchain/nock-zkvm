/-
  NockvmE2E/Exec/VKBindBridge.lean   (pcs, ; KERNEL-checked unless labelled)

  Part 1 (deterministic): `VKcoll` of HFixFri.lean, strengthened by the canonicity of the opened tree-0 limbs (`VKcollC`), IMPLIES the flat
  event `VKcollFlat` of VKBind.lean (`goRoot` accepts the spec root with a wrong opened leaf, well-formed opening).
  Why the canonicity is needed (finding): `VKcoll` alone is true (probability 1 for a query-making adversary) for an opening whose tree-0
  limbs are non-canonical (`honest leaf + p`): `Hof` reads limbs through `dgOf` (cast to `ZMod p`), so the verifier's recomputation hashes to the
  honest digests, while `vals[0][r] ≠ honestLeaf` as naturals.  `verifyFix'` rejects such proofs (`based` check), but `VKcoll` does not mention it.
-/
import NockvmE2E.Exec.VKBind
import NockvmE2E.Exec.HFixFri
import NockvmE2E.Exec.SoundFlatFri
import NockvmE2E.Exec.HFixNum
import NockvmE2E.Exec.J8Shape
import NockvmE2E.Exec.E2EEmbed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace NockvmE2E.Exec.VKBindBridge
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VKBind

/-- `VKcoll` together with the canonicity of the opened tree-0 limbs and frontier digests (what `verifyFix'` checks before the Merkle check) -/
def VKcollC (X0 : ExecInst) (vk : VK) (Hf : HFn) (πF : FixProof) : Prop :=
  VKcoll X0 vk Hf πF ∧ (πF.vals[0]!).all VF.based = true ∧ (πF.sibs[0]!).all dgOk = true

/-- the opening of tree 0 that `treeCheck` reads off the side proof -/
def openV (X0 : ExecInst) (πF : FixProof) : Array ℕ × (ℕ → Dg5) × Array Dg5 :=
  (treeSel (eraseX X0) (fixCols X0).size 0 πF.pos, fun r => [(πF.vals[0]!)[r]!, 0, 0, 0, 0], πF.sibs[0]!)

/-- the flat event of VKBind (`VKcollLazy` with the hash read off the cache replaced by an arbitrary flat hash `H`) -/
def VKcollFlat (XX : ExecInst) (H : HFn) (o : Array ℕ × (ℕ → Dg5) × Array Dg5) : Prop :=
  WfOpen o ∧ (∃ s', goRoot H (vkSp XX) 0 o.1 o.2.1 o.2.2 1 0 (vkSp XX).total 0 = some (specRoot XX H, s')) ∧
  WrongLeaf (hlSpec XX (fixCols XX).size (2 ^ (XX.nD - 1))) o 0 (vkSp XX).total

theorem VKcollLazy_eq_flat {YY : Type} (dg : YY → Dg5) (XX : ExecInst) (c : OracleSpec.QueryCache (HS YY))
    (o : Array ℕ × (ℕ → Dg5) × Array Dg5) : VKcollLazy dg XX c o ↔ VKcollFlat XX (Hc dg c) o := Iff.rfl


/-! ### the opening is well-formed: strictly sorted, in range, `lb` finds its own position -/

theorem treeSel_lt (XX : ExecInst) (F : ℕ) (hF : 0 < F) (pos : Array ℕ) :
    ∀ x ∈ (treeSel XX F 0 pos).toList, x < 2 * F * 2 ^ (XX.nD - 1) := by
  intro x hx
  have hF0 : (F == 0) = false := by simpa using Nat.pos_iff_ne_zero.mp hF
  unfold treeSel at hx
  simp only [show (0 : ℕ) < 4 from by decide, ite_true, hF0, Bool.false_eq_true, ite_false, Array.toList_flatMap,
    Array.toList_map, Array.toList_range, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨g, hg, a, ha, rfl⟩ := hx
  rw [mem_sortedDistinct] at hg
  simp only [Array.toList_map, List.mem_map] at hg
  obtain ⟨q, _, rfl⟩ := hg
  have hh : 0 < 2 ^ (XX.nD - 1) := Nat.two_pow_pos _
  have h1 : q % 2 ^ (XX.nD - 1) + 1 ≤ 2 ^ (XX.nD - 1) := Nat.mod_lt q hh
  calc (q % 2 ^ (XX.nD - 1)) * 2 * F + a < (q % 2 ^ (XX.nD - 1)) * 2 * F + 2 * F := by omega
    _ = (q % 2 ^ (XX.nD - 1) + 1) * (2 * F) := by ring
    _ ≤ 2 ^ (XX.nD - 1) * (2 * F) := Nat.mul_le_mul_right _ h1
    _ = 2 * F * 2 ^ (XX.nD - 1) := by ring

theorem strict_of_pw (a : Array ℕ) (h : a.toList.Pairwise (· < ·)) :
    ∀ i j, i < j → j < a.size → a[i]! < a[j]! := by
  intro i j hij hj
  have hi : i < a.size := lt_trans hij hj
  rw [List.pairwise_iff_getElem] at h
  have := h i j (by simpa using hi) (by simpa using hj) hij
  rw [getElem!_pos a i hi, getElem!_pos a j hj]
  simpa using this

theorem lb_self (a : Array ℕ) (hs : ∀ i j, i < j → j < a.size → a[i]! < a[j]!) (r : ℕ) (hr : r < a.size) :
    lb a a[r]! = r := by
  have hsorted : Sorted a := fun i j hij hj => by
    rcases Nat.eq_or_lt_of_le hij with rfl | h
    · exact le_rfl
    · exact (hs i j h hj).le
  obtain ⟨h1, h2, h3⟩ := lb_spec a hsorted a[r]!
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := h3 (lb a a[r]!) le_rfl (by omega)
    have := hs (lb a a[r]!) r hlt hr
    omega
  · have := h2 r hgt
    omega

/-! ### tree 0 of `treeCheck` is a `goRoot` acceptance -/

theorem ckE_bind_ok {α : Type} (b : Bool) (m : String) (f : Unit → Except String α) (a : α)
    (h : (ckE b m >>= f) = .ok a) : b = true ∧ f () = .ok a := by
  unfold ckE at h
  cases b
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simpa using h

theorem treeCheck_zero (XX : ExecInst) (H : HFn) (π : FlatProof) (W : Array ℕ) (half0 : ℕ) (sels : Array (Array ℕ))
    (hW : W[0]! ≠ 0) (h : treeCheck XX H π W half0 sels 0 = .ok ()) :
    ∃ s, goRoot H (ragSpec W[0]! half0) 0 sels[0]! (fun r => [(π.vals[0]!)[r]!, 0, 0, 0, 0]) (π.sibs[0]!.toList.toArray) 1 0
        (ragSpec W[0]! half0).total 0 = some (π.roots[0]!, s) ∧ s = π.sibs[0]!.size ∧ π.vals[0]!.size = sels[0]!.size := by
  have hW' : (W[0]! == 0) = false := by simpa using hW
  unfold treeCheck at h
  simp only [hW', Bool.and_false, ite_false, Nat.zero_lt_succ] at h
  simp only [↓reduceIte, Bool.false_eq_true] at h
  obtain ⟨hsz, h⟩ := ckE_bind_ok _ _ _ _ h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rename_i root s hgo
    obtain ⟨h1, h2⟩ := ckE_bind_ok _ _ _ _ h
    unfold ckE at h2
    split at h2
    · rename_i hr
      refine ⟨s, ?_, by simpa using h1, by simpa using hsz⟩
      rw [hgo]
      simp only [beq_iff_eq] at hr
      rw [hr]
    · simp [throw, throwThe, MonadExceptOf.throw] at h2

theorem VKcollC_flat (XX : ExecInst) (H : HFn) (πF : FixProof) (h : VKcollC XX (vkSpec XX H) H πF) :
    VKcollFlat XX H (openV XX πF) := by
  obtain ⟨⟨hchk, r, hr, hne⟩, hbased, hdg⟩ := h
  have hF := fixCols_size_pos XX
  have hW : (#[(fixCols XX).size, 0, 0, 0] : Array ℕ)[0]! ≠ 0 := by simpa using Nat.pos_iff_ne_zero.mp hF
  obtain ⟨s, hgo, hs, hsz⟩ := treeCheck_zero _ _ _ _ _ _ hW hchk
  simp [fixAdapt, vkSpec] at hgo hs hr hne
  have hE : eraseXS XX = eraseX XX := rfl
  have hnD : (eraseX XX).nD = XX.nD := rfl
  simp only [hE, hnD] at hgo hne hr
  have hpw := treeSel_pw (eraseX XX) (fixCols XX).size 0 πF.pos
  have hst := strict_of_pw _ hpw
  have hsorted : Sorted (treeSel (eraseX XX) (fixCols XX).size 0 πF.pos) := fun i j hij hj => by
    rcases Nat.eq_or_lt_of_le hij with rfl | h
    · exact le_rfl
    · exact (hst i j h hj).le
  have hlt := treeSel_lt (eraseX XX) _ hF πF.pos
  rw [hnD] at hlt
  refine ⟨⟨hsorted, fun _ => rfl, ?_⟩, ⟨s, ?_⟩, ?_⟩
  · intro s' sib hsib
    have hm : sib ∈ πF.sibs[0]! := Array.mem_of_getElem? hsib
    have := (Array.all_eq_true_iff_forall_mem.1 hdg) sib hm
    simp only [dgOk, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  · exact hgo
  · have hmem : (treeSel (eraseX XX) (fixCols XX).size 0 πF.pos)[r]! ∈ (treeSel (eraseX XX) (fixCols XX).size 0 πF.pos).toList := by
      rw [getElem!_pos _ r hr]; exact Array.mem_toList_iff.mpr (Array.getElem_mem hr)
    refine ⟨(treeSel (eraseX XX) (fixCols XX).size 0 πF.pos)[r]!, Nat.zero_le _, ?_, ?_, ?_⟩
    · rw [vkSp_total]; have := hlt _ hmem; omega
    · show (treeSel (eraseX XX) (fixCols XX).size 0 πF.pos)[lb (treeSel (eraseX XX) (fixCols XX).size 0 πF.pos) _]? = _
      rw [lb_self _ hst r hr, Array.getElem?_eq_getElem hr, getElem!_pos _ r hr]
    · show [(πF.vals[0]!)[lb (treeSel (eraseX XX) (fixCols XX).size 0 πF.pos) _]!, 0, 0, 0, 0] ≠ _
      rw [lb_self _ hst r hr]
      intro heq
      apply hne
      simpa [hlSpec, honestLeaf] using heq

/-! ### the numeric hypotheses of `exec_e2e_J8V''_numbers` -/

/-- `|DgJ8| = p^5` -/
theorem card_DgJ8 : Nat.card NockvmE2E.Exec.E2E.DgJ8 = NockvmE2E.Exec.p ^ 5 := by
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_fun, ZMod.card]

theorem goldilocks_eq_p : NockvmE2E.Succ.Numbers.goldilocks = NockvmE2E.Exec.p := rfl

/-- `|DgJ8| >= p^4` (the `hDg` of `epsfix_numbers`) -/
theorem DgJ8_ge : NockvmE2E.Succ.Numbers.goldilocks ^ 4 ≤ Nat.card NockvmE2E.Exec.E2E.DgJ8 := by
  rw [card_DgJ8, goldilocks_eq_p]
  have hp : 1 ≤ NockvmE2E.Exec.p := (Fact.out : Nat.Prime NockvmE2E.Exec.p).one_lt.le
  exact Nat.pow_le_pow_right hp (by norm_num)

/-- `k <= 61` (the side-proof layer count `XI.k`), from the J-8 shape: `nD = k + 7 <= 32` -/
theorem k_le_25 {XI : ExecInst} (h : J8Shape.j8ShapeOk XI = true) : XI.k ≤ 25 := by
  have h32 := J8Shape.hn32_of_shape h
  unfold J8Shape.j8ShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  omega

/-- the VK tree has `F * 2^nD` leaves, at most `F * 2^32` under the J-8 shape: `T <= 2^40` is the per-instance check `F * 2^nD <= 2^39`
(`F = #fixCols` is not bounded by the shape) -/
theorem vk_total_le {XI : ExecInst} (h : J8Shape.j8ShapeOk XI = true) :
    (vkSp XI).total ≤ (fixCols XI).size * 2 ^ 32 := by
  have h32 := J8Shape.hn32_of_shape h
  have h1 := J8Shape.hn1_of_shape h
  rw [vkSp_total]
  have : 2 * 2 ^ (XI.nD - 1) ≤ 2 ^ 32 := by
    have : 2 * 2 ^ (XI.nD - 1) = 2 ^ XI.nD := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; exact Nat.pow_le_pow_right (by norm_num) h32
  calc 2 * (fixCols XI).size * 2 ^ (XI.nD - 1) = (fixCols XI).size * (2 * 2 ^ (XI.nD - 1)) := by ring
    _ ≤ (fixCols XI).size * 2 ^ 32 := Nat.mul_le_mul_left _ this

/-! ### PROBE (kernel fact): `VKcoll` alone is not a hash collision

Every flat hash that reads limbs mod `p` (`Hof` does: `dgOf` casts into `ZMod p`) gives the same digests to an opening whose tree-0 leaf is
`honest + p`.  So `VKcoll` holds for such an opening, with a non-canonical limb, while every flat hash input maps to the same `NQuery`. -/

/-- limbwise equality mod `p` -/
def EqP (x y : List ℕ) : Prop := x.map (· % NockvmE2E.Exec.p) = y.map (· % NockvmE2E.Exec.p)

/-- a flat hash that ignores multiples of `p` in the limbs after the 3-entry header -/
def ModP (H : HFn) : Prop := ∀ x y : List ℕ, x.take 3 = y.take 3 → EqP (x.drop 3) (y.drop 3) → H x = H y

theorem node_eqv (a b c : ℕ) (l r l' r' : Dg5) (hl : EqP l l') (hr : EqP r r') :
    ([a, b, c] ++ l ++ r).take 3 = ([a, b, c] ++ l' ++ r').take 3 ∧ EqP (([a, b, c] ++ l ++ r).drop 3) (([a, b, c] ++ l' ++ r').drop 3) := by
  unfold EqP at *
  refine ⟨by simp, ?_⟩
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero, List.map_append, hl, hr]

theorem goRootF_congr (H : HFn) (hH : ModP H) (sp : TSpec) (j : ℕ) (sel : Array ℕ) (leaf leaf' : ℕ → Dg5) (sibs : Array Dg5)
    (hleaf : ∀ r, EqP (leaf r) (leaf' r)) :
    ∀ (f idx lo cnt s : ℕ),
      (goRootF H sp j sel leaf sibs f idx lo cnt s = none ∧ goRootF H sp j sel leaf' sibs f idx lo cnt s = none) ∨
      ∃ d d' s', goRootF H sp j sel leaf sibs f idx lo cnt s = some (d, s') ∧ goRootF H sp j sel leaf' sibs f idx lo cnt s = some (d', s') ∧
        EqP d d' ∧ (cnt ≠ 1 → d = d') := by
  intro f
  induction f with
  | zero => intro idx lo cnt s; left; simp [goRootF]
  | succ f ih =>
    intro idx lo cnt s
    simp only [goRootF]
    by_cases h1 : cnt == 1
    · simp only [h1, ite_true]
      by_cases hs : sel[lb sel lo]? == some lo
      · right; exact ⟨leaf (lb sel lo), leaf' (lb sel lo), s, by simp [hs], by simp [hs], hleaf _, fun h => absurd (by simpa using h1) h⟩
      · left; simp [hs]
    · simp only [h1, Bool.false_eq_true, ite_false]
      by_cases hg : (sp.split cnt == 0 || decide (sp.split cnt ≥ cnt)) = true
      · left; simp [hg]
      · simp only [hg, Bool.false_eq_true, ite_false]
        have hne : cnt ≠ 1 := by simpa using h1
        by_cases hB : lb sel (lo + sp.split cnt) > lb sel lo <;> by_cases hC : lb sel (lo + cnt) > lb sel (lo + sp.split cnt)
        · simp only [hB, hC, decide_true, Bool.and_self, ite_true, Option.bind_eq_bind]
          rcases ih (2 * idx) lo (sp.split cnt) s with ⟨a1, a2⟩ | ⟨d, d', s1, a1, a2, aE, -⟩
          · left; simp [a1, a2]
          rcases ih (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1 with ⟨b1, b2⟩ | ⟨e, e', s2, b1, b2, bE, -⟩
          · left; simp [a1, a2, b1, b2]
          right
          have hn := node_eqv tagNode j idx d e d' e' aE bE
          refine ⟨_, _, s2, by simp [a1, b1], by simp [a2, b2], ?_, fun _ => hH _ _ hn.1 hn.2⟩
          have := hH _ _ hn.1 hn.2
          rw [this]; rfl
        · simp only [hB, hC, decide_true, decide_false, Bool.and_false, Bool.false_eq_true, ite_false, ite_true]
          rcases hs : sibs[s]? with _ | sib
          · left; simp
          rcases ih (2 * idx) lo (sp.split cnt) (s + 1) with ⟨a1, a2⟩ | ⟨d, d', s1, a1, a2, aE, -⟩
          · left; simp [a1, a2]
          right
          have hn := node_eqv tagNode j idx d sib d' sib aE rfl
          refine ⟨_, _, s1, by simp [a1], by simp [a2], ?_, fun _ => hH _ _ hn.1 hn.2⟩
          have := hH _ _ hn.1 hn.2
          rw [this]; rfl
        · simp only [hB, hC, decide_true, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, ite_true]
          rcases hs : sibs[s]? with _ | sib
          · left; simp
          rcases ih (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1) with ⟨a1, a2⟩ | ⟨d, d', s1, a1, a2, aE, -⟩
          · left; simp [a1, a2]
          right
          have hn := node_eqv tagNode j idx sib d sib d' rfl aE
          refine ⟨_, _, s1, by simp [a1], by simp [a2], ?_, fun _ => hH _ _ hn.1 hn.2⟩
          have := hH _ _ hn.1 hn.2
          rw [this]; rfl
        · left; simp [hB, hC]


theorem dgOf_congr (l l' : List ℕ) (h : EqP l l') : NockvmE2E.Exec.E2E.dgOf l = NockvmE2E.Exec.E2E.dgOf l' := by
  funext i
  have h2 : l.getD i.1 0 % NockvmE2E.Exec.p = l'.getD i.1 0 % NockvmE2E.Exec.p := by
    have := congrArg (fun m => m.getD i.1 0) h
    simp only [EqP, List.getD_eq_getElem?_getD, List.getElem?_map] at this
    cases hl : l[i.1]? <;> cases hl' : l'[i.1]? <;> simp_all
  simp only [NockvmE2E.Exec.E2E.dgOf]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h2

/-- `Hof` reads limbs mod `p` (so it is `ModP`): the digests of `x` and of `x` with a limb shifted by `p` coincide -/
theorem Hof_ModP (skels : List BinaryTree.Skeleton) (h : NockvmE2E.Exec.E2E.NQuery skels → NockvmE2E.Exec.E2E.DgJ8) :
    ModP (NockvmE2E.Exec.E2E.Hof skels h) := by
  intro x y h3 hE
  rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c, rx⟩⟩⟩ <;> rcases y with _ | ⟨a', _ | ⟨b', _ | ⟨c', ry⟩⟩⟩ <;> simp at h3 <;>
    first | rfl | skip
  all_goals (try obtain ⟨rfl, rfl⟩ := h3)
  all_goals (try obtain ⟨rfl, rfl, rfl⟩ := h3)
  all_goals first | rfl | skip
  simp only [List.drop_succ_cons, List.drop_zero] at hE
  have e1 : EqP (rx.take 5) (ry.take 5) := by unfold EqP at *; rw [List.map_take, List.map_take, hE]
  have e2 : EqP (rx.drop 5) (ry.drop 5) := by unfold EqP at *; rw [List.map_drop, List.map_drop, hE]
  simp only [NockvmE2E.Exec.E2E.Hof, NockvmE2E.Exec.E2E.decQ, dgOf_congr _ _ e1, dgOf_congr _ _ e2]


theorem treeCheck_zero_intro (XX : ExecInst) (H : HFn) (π : FlatProof) (W : Array ℕ) (half0 : ℕ) (sels : Array (Array ℕ))
    (hW : W[0]! ≠ 0) (hsz : π.vals[0]!.size = sels[0]!.size) (s : ℕ)
    (hgo : goRoot H (ragSpec W[0]! half0) 0 sels[0]! (fun r => [(π.vals[0]!)[r]!, 0, 0, 0, 0]) (π.sibs[0]!.toList.toArray) 1 0
        (ragSpec W[0]! half0).total 0 = some (π.roots[0]!, s)) (hs : s = π.sibs[0]!.size) :
    treeCheck XX H π W half0 sels 0 = .ok () := by
  have hW' : (W[0]! == 0) = false := by simpa using hW
  unfold treeCheck
  simp only [hW', Bool.and_false, ite_false, Nat.zero_lt_succ]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [hgo]
  simp [ckE, hsz, hs]

/-- **PROBE (kernel fact; no probability)**: let `H` read limbs mod `p` (`ModP H`; `Hof` does, `Hof_ModP`) and let `πF` pass the tree-0 check of `VKcoll`
with an honest opened leaf at position `r`.  Then the proof `πF'` that differs only by `vals[0][r] + p` also passes the check, differs from the honest leaf, and has a
NON-CANONICAL limb: `VKcoll` holds although every hash input of the recomputation has the same digest as the honest one (inputs equal limbwise mod `p`;
under `Hof` they are the same `NQuery`, no table collision) -/
theorem vkcoll_not_collision (XX : ExecInst) (H : HFn) (hH : ModP H) (πF πF' : FixProof) (r : ℕ)
    (hchk : VKcoll XX (vkSpec XX H) H πF)
    (hr : r < (treeSel (eraseX XX) (fixCols XX).size 0 πF.pos).size)
    (hhon : (πF.vals[0]!)[r]! = honestLeaf XX (fixCols XX).size (2 ^ (XX.nD - 1)) (treeSel (eraseX XX) (fixCols XX).size 0 πF.pos)[r]!)
    (hv : πF'.vals[0]! = (πF.vals[0]!).set! r ((πF.vals[0]!)[r]! + NockvmE2E.Exec.p)) (hsib : πF'.sibs[0]! = πF.sibs[0]!)
    (hpos : πF'.pos = πF.pos) (hrr : r < πF.vals[0]!.size) :
    VKcoll XX (vkSpec XX H) H πF' ∧ ¬ ((πF'.vals[0]!).all VF.based = true) := by
  have hp : 0 < NockvmE2E.Exec.p := (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
  have hF := fixCols_size_pos XX
  have hE : eraseXS XX = eraseX XX := rfl
  have hnD : (eraseX XX).nD = XX.nD := rfl
  obtain ⟨hc, -⟩ := hchk
  have hW : (#[(fixCols XX).size, 0, 0, 0] : Array ℕ)[0]! ≠ 0 := by simpa using Nat.pos_iff_ne_zero.mp hF
  obtain ⟨s, hgo, hs, hsz⟩ := treeCheck_zero _ _ _ _ _ _ hW hc
  have hsz' : r < (πF.vals[0]!.set! r ((πF.vals[0]!)[r]! + NockvmE2E.Exec.p)).size := by simpa [Array.size_set!] using hrr
  have hnb : ¬ ((πF'.vals[0]!).all VF.based = true) := by
    intro hb
    rw [hv] at hb
    have e := Array.getElem!_set!_self (πF.vals[0]!) r ((πF.vals[0]!)[r]! + NockvmE2E.Exec.p) hrr
    rw [getElem!_pos _ r hsz'] at e
    have hm := Array.getElem_mem hsz'
    rw [e] at hm
    have := (Array.all_eq_true_iff_forall_mem.1 hb) _ hm
    have hPN := NockvmE2E.Exec.E2E.PN_eq
    simp only [VF.based, decide_eq_true_eq] at this
    omega
  have e : (πF'.vals[0]!)[r]! = (πF.vals[0]!)[r]! + NockvmE2E.Exec.p := by
    rw [hv]; exact Array.getElem!_set!_self _ r _ hrr
  refine ⟨⟨?_, r, ?_, ?_⟩, hnb⟩
  · have hleaf : ∀ r' : ℕ, EqP [(πF.vals[0]!)[r']!, 0, 0, 0, 0] [(πF'.vals[0]!)[r']!, 0, 0, 0, 0] := by
      intro r'
      unfold EqP
      by_cases h : r' = r
      · subst h; simp [e, Nat.add_mod_right]
      · have : (πF'.vals[0]!)[r']! = (πF.vals[0]!)[r']! := by
          rw [hv]; exact Array.getElem!_set!_ne _ _ _ _ (Ne.symm h)
        simp [this]
    refine treeCheck_zero_intro _ _ _ _ _ _ hW ?_ s ?_ ?_
    · simp [fixAdapt, vkSpec, hpos, hv, Array.size_set!] at hsz ⊢
      exact hsz
    · simp [fixAdapt, vkSpec, hpos, hsib] at hgo ⊢
      have hcg := goRootF_congr H hH (ragSpec (fixCols XX).size (2 ^ ((eraseXS XX).nD - 1))) 0
        (treeSel (eraseXS XX) (fixCols XX).size 0 πF.pos) (fun r' : ℕ => [(πF.vals[0]!)[r']!, 0, 0, 0, 0])
        (fun r' : ℕ => [(πF'.vals[0]!)[r']!, 0, 0, 0, 0]) πF.sibs[0]! hleaf
        (ragSpec (fixCols XX).size (2 ^ ((eraseXS XX).nD - 1))).total 1 0
        (ragSpec (fixCols XX).size (2 ^ ((eraseXS XX).nD - 1))).total 0
      unfold goRoot at hgo ⊢
      have hne : (ragSpec (fixCols XX).size (2 ^ ((eraseXS XX).nD - 1))).total ≠ 1 := by
        simp only [ragSpec]
        have : 1 ≤ 2 ^ ((eraseXS XX).nD - 1) := Nat.one_le_two_pow
        intro h; nlinarith
      rcases hcg with ⟨h1, -⟩ | ⟨d, d', s', h1, h2, -, h3⟩
      · rw [h1] at hgo; simp at hgo
      · rw [h1] at hgo
        rw [h2]
        have := h3 hne
        simp only [Option.some.injEq, Prod.mk.injEq] at hgo ⊢
        obtain ⟨hd, hs'⟩ := hgo
        subst this; exact ⟨hd.symm ▸ rfl, hs'⟩
    · simpa [fixAdapt, hsib] using hs
  · simpa [vkSpec, hpos, hE, hnD] using hr
  · simp only [vkSpec, hpos, hE, hnD, e]
    rw [hhon] at *
    omega

/-- the probe at the J-8 hash: `H = Hof skels h` for any table `h` on node queries -/
theorem vkcoll_not_collision_Hof (skels : List BinaryTree.Skeleton) (h : NockvmE2E.Exec.E2E.NQuery skels → NockvmE2E.Exec.E2E.DgJ8)
    (XX : ExecInst) (πF πF' : FixProof) (r : ℕ)
    (hchk : VKcoll XX (vkSpec XX (NockvmE2E.Exec.E2E.Hof skels h)) (NockvmE2E.Exec.E2E.Hof skels h) πF)
    (hr : r < (treeSel (eraseX XX) (fixCols XX).size 0 πF.pos).size)
    (hhon : (πF.vals[0]!)[r]! = honestLeaf XX (fixCols XX).size (2 ^ (XX.nD - 1)) (treeSel (eraseX XX) (fixCols XX).size 0 πF.pos)[r]!)
    (hv : πF'.vals[0]! = (πF.vals[0]!).set! r ((πF.vals[0]!)[r]! + NockvmE2E.Exec.p)) (hsib : πF'.sibs[0]! = πF.sibs[0]!)
    (hpos : πF'.pos = πF.pos) (hrr : r < πF.vals[0]!.size) :
    VKcoll XX (vkSpec XX (NockvmE2E.Exec.E2E.Hof skels h)) (NockvmE2E.Exec.E2E.Hof skels h) πF' ∧ ¬ ((πF'.vals[0]!).all VF.based = true) :=
  vkcoll_not_collision XX _ (Hof_ModP skels h) πF πF' r hchk hr hhon hv hsib hpos hrr

end NockvmE2E.Exec.VKBindBridge

#print axioms NockvmE2E.Exec.VKBindBridge.VKcollC_flat
#print axioms NockvmE2E.Exec.VKBindBridge.DgJ8_ge
#print axioms NockvmE2E.Exec.VKBindBridge.k_le_25
#print axioms NockvmE2E.Exec.VKBindBridge.vk_total_le
#print axioms NockvmE2E.Exec.VKBindBridge.Hof_ModP
#print axioms NockvmE2E.Exec.VKBindBridge.goRootF_congr
#print axioms NockvmE2E.Exec.VKBindBridge.vkcoll_not_collision
#print axioms NockvmE2E.Exec.VKBindBridge.vkcoll_not_collision_Hof
