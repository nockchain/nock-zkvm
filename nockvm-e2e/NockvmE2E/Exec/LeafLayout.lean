/-
  NockvmE2E/Exec/LeafLayout.lean   (HCOV Brief A, ; proof-only, no XI)

  Generic leaf numbering of a `Skeleton` (`leafNum`, `leafEquiv`), the selector link `selOf_get`, the RAP and FRI
  leaf permutations of the flat verifier (`ragPerm`, `friPerm`), and `layoutPointMd`: a `PointMaskData`
  with arbitrary skeletons and leaf numbering, blocks of width 0 empty (adapted from `boundedPointMd`).
-/
import NockvmE2E.Exec.SoundMerkle
import NockvmE2E.Merkle.RapFriQueryOnly

open BinaryTree

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.Layout

open NockvmE2E.Rap NockvmE2E.Merkle NockvmE2E.Merkle.RapFriQ

/-! ### A. Leaf numbering (DFS: the right child starts after the left leaves) -/

/-- the DFS number of a leaf -/
def leafNum : {s : Skeleton} → SkeletonLeafIndex s → ℕ
  | _, .ofLeaf => 0
  | _, .ofLeft a => leafNum a
  | .internal l _, .ofRight a => l.leafCount + leafNum a

/-- the leaf with a given DFS number (junk above the leaf count) -/
def leafOf : (s : Skeleton) → ℕ → SkeletonLeafIndex s
  | .leaf, _ => .ofLeaf
  | .internal l r, t => if t < l.leafCount then .ofLeft (leafOf l t) else .ofRight (leafOf r (t - l.leafCount))

theorem leafNum_lt : ∀ {s : Skeleton} (i : SkeletonLeafIndex s), leafNum i < s.leafCount
  | _, .ofLeaf => by simp [leafNum, Skeleton.leafCount]
  | _, .ofLeft a => by
      have := leafNum_lt a; simp only [leafNum, Skeleton.leafCount]; omega
  | .internal l r, .ofRight a => by
      have := leafNum_lt a; simp only [leafNum, Skeleton.leafCount]; omega

theorem leafNum_leafOf : ∀ (s : Skeleton) (t : ℕ), t < s.leafCount → leafNum (leafOf s t) = t
  | .leaf, t, h => by simp [Skeleton.leafCount] at h; simp [leafOf, leafNum, h]
  | .internal l r, t, h => by
      unfold leafOf
      split_ifs with h1
      · exact leafNum_leafOf l t h1
      · have : t - l.leafCount < r.leafCount := by simp only [Skeleton.leafCount] at h; omega
        have := leafNum_leafOf r _ this
        simp only [leafNum]; omega

theorem leafOf_leafNum : ∀ {s : Skeleton} (i : SkeletonLeafIndex s), leafOf s (leafNum i) = i
  | _, .ofLeaf => rfl
  | .internal l r, .ofLeft a => by
      have := leafNum_lt a
      simp [leafNum, leafOf, this, leafOf_leafNum a]
  | .internal l r, .ofRight a => by
      simp [leafNum, leafOf, leafOf_leafNum a]

/-- the numbering as an equivalence with `Fin leafCount` -/
def leafEquiv (s : Skeleton) : SkeletonLeafIndex s ≃ Fin s.leafCount where
  toFun i := ⟨leafNum i, leafNum_lt i⟩
  invFun t := leafOf s t.val
  left_inv i := leafOf_leafNum i
  right_inv t := Fin.ext (leafNum_leafOf s t.val t.isLt)

theorem leafNum_symm (s : Skeleton) (t : Fin s.leafCount) : leafNum ((leafEquiv s).symm t) = t.val :=
  leafNum_leafOf s t.val t.isLt

theorem leafEquiv_val {s : Skeleton} (i : SkeletonLeafIndex s) : ((leafEquiv s) i).val = leafNum i := rfl

/-- the dense selector read at a leaf is the predicate at its number -/
theorem selOf_get (isSel : ℕ → Bool) : ∀ (s : Skeleton) (lo : ℕ) (i : SkeletonLeafIndex s),
    (SM.selOf isSel s lo).get i = isSel (lo + leafNum i)
  | .leaf, lo, .ofLeaf => by simp [SM.selOf, leafNum]
  | .internal l r, lo, .ofLeft a => by
      simp only [SM.selOf, LeafData.get, leafNum]; exact selOf_get isSel l lo a
  | .internal l r, lo, .ofRight a => by
      simp only [SM.selOf, LeafData.get, leafNum]
      rw [selOf_get isSel r (lo + l.leafCount) a]; congr 1; omega

/-! ### Leaf permutations of the flat verifier -/

/-- RAP block of `h` groups of `2W` leaves: `(column rank ρ, point x) ↦ (x % h) * 2W + (x / h) * W + ρ` -/
def ragPerm (W h : ℕ) : Fin W × Fin (2 * h) ≃ Fin (h * 2 * W) :=
  (((Equiv.prodCongr (Equiv.refl (Fin W)) finProdFinEquiv.symm).trans (Equiv.prodComm _ _)).trans
    ((Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl (Fin W))).trans (Equiv.prodAssoc _ _ _))).trans
    ((Equiv.prodCongr (Equiv.refl (Fin h)) finProdFinEquiv).trans (finProdFinEquiv.trans (finCongr (by ring))))

theorem ragPerm_val {W h : ℕ} (ρ : Fin W) (x : Fin (2 * h)) :
    (ragPerm W h (ρ, x)).val = (x.val % h) * 2 * W + (x.val / h) * W + ρ.val := by
  simp [ragPerm, finProdFinEquiv, Fin.divNat, Fin.modNat]
  ring

/-- FRI tree over `2h` points: point `u ↦ leaf 2 * (u % h) + u / h` (the pair `{u, u + h}` is adjacent) -/
def friPerm (h : ℕ) : Fin (2 * h) ≃ Fin (2 * h) :=
  (finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv)).trans (finCongr (by ring))

theorem friPerm_val {h : ℕ} (u : Fin (2 * h)) : (friPerm h u).val = 2 * (u.val % h) + u.val / h := by
  simp [friPerm, finProdFinEquiv, Fin.divNat, Fin.modNat]
  ring

/-! ### `layoutPointMd`: arbitrary skeletons, blocks of width 0 empty -/

/-- leaf data over a one-point type is unique, for every skeleton -/
def leafDataUnit : (s : Skeleton) → Unique (LeafData PUnit s)
  | .leaf => ⟨⟨.leaf PUnit.unit⟩, fun x => by cases x with | leaf a => rfl⟩
  | .internal l r =>
      haveI := leafDataUnit l
      haveI := leafDataUnit r
      ⟨⟨.internal default default⟩, fun x => by
        cases x with | internal a b => congr 1 <;> exact Subsingleton.elim _ _⟩

/-- leaf type of block `r`: `F` when the block has width, else a point -/
abbrev FBlk (F : Type) (Wd : ℕ → ℕ) (r : ℕ) : Type := if 0 < Wd r then F else PUnit

theorem cast_get_leafCast {A B : Type} (h : A = B) {s : Skeleton} (x : LeafData A s) (i : SkeletonLeafIndex s) :
    cast h (x.get i) = (cast (congrArg (fun T => LeafData T s) h) x).get i := by
  subst h; rfl

/-- block `r`: (column, position) ↦ leaf through `E`, as leaf data -/
noncomputable def blockEqL {κ : Type} (colR : κ → ℕ) (Pt F : Type) (r : ℕ) (s : Skeleton)
    (E : {c : κ // colR c = r} × Pt ≃ SkeletonLeafIndex s) :
    Cols colR (Pt → F) r ≃ LeafData F s :=
  (Equiv.curry _ _ _).symm.trans ((Equiv.arrowCongr E (Equiv.refl F)).trans
    (LeafData.equivIndexFun s).symm)

theorem blockEqL_get {κ : Type} (colR : κ → ℕ) (Pt F : Type) (r : ℕ) (s : Skeleton)
    (E : {c : κ // colR c = r} × Pt ≃ SkeletonLeafIndex s) (w : Cols colR (Pt → F) r)
    (c : {c : κ // colR c = r}) (x : Pt) :
    (blockEqL colR Pt F r s E w).get (E (c, x)) = w c x := by
  show (LeafData.ofFun _ _).get _ = _
  rw [LeafData.get_ofFun]
  simp [Equiv.arrowCongr, Equiv.curry]

/-- **A `PointMaskData` with block skeletons `sk r` and leaf numbering `E r`**, blocks of width `0` empty
(`Wd r = 0 → ` no column in block `r`, leaf type one point). Adapted from `boundedPointMd`. -/
noncomputable def layoutPointMd {κ Pt F Dg : Type} (colR : κ → ℕ) (Wd : ℕ → ℕ) (sk : ℕ → Skeleton)
    (E : ∀ r, 0 < Wd r → ({c : κ // colR c = r} × Pt ≃ SkeletonLeafIndex (sk r)))
    (hemp : ∀ r, Wd r = 0 → IsEmpty {c : κ // colR c = r}) (ne : Nonempty F) (enc : F ↪ Dg) :
    PointMaskData colR Pt F Dg where
  skel := sk
  FB r := FBlk F Wd r
  words r :=
    if h : 0 < Wd r then
      (blockEqL colR Pt F r (sk r) (E r h)).trans
        (Equiv.cast (congrArg (fun T => LeafData T (sk r)) (if_pos h).symm))
    else
      haveI : Unique (LeafData (FBlk F Wd r) (sk r)) := by
        rw [FBlk, if_neg h]; exact leafDataUnit _
      haveI : IsEmpty {c : κ // colR c = r} := hemp r (by omega)
      haveI : Unique (Cols colR (Pt → F) r) := ⟨⟨isEmptyElim⟩, fun f => funext fun c => isEmptyElim c⟩
      Equiv.ofUnique _ _
  ne r := by
    by_cases h : 0 < Wd r
    · rw [FBlk, if_pos h]; exact ne
    · rw [FBlk, if_neg h]; exact ⟨PUnit.unit⟩
  enc r := by
    by_cases h : 0 < Wd r
    · have e : FBlk F Wd r = F := if_pos h
      exact (Equiv.cast e).toEmbedding.trans enc
    · have e : FBlk F Wd r = PUnit := if_neg h
      exact (Equiv.cast e).toEmbedding.trans ⟨fun _ => enc ne.some, fun a b _ => Subsingleton.elim a b⟩
  hF r c := if_pos (by
    by_contra h
    exact (hemp r (by omega)).false c)
  pos r cx := if h : 0 < Wd r then E r h cx else ((hemp r (by omega)).false cx.1).elim
  get_pos r w c x := by
    have h : 0 < Wd r := by
      by_contra h
      exact (hemp r (by omega)).false c
    simp only [dif_pos h, Equiv.trans_apply, Equiv.cast_apply]
    rw [← cast_get_leafCast (if_pos h).symm, cast_cast, ← blockEqL_get colR Pt F r (sk r) (E r h) w c x]
    exact cast_eq _ _

theorem layoutPointMd_pos {κ Pt F Dg : Type} (colR : κ → ℕ) (Wd : ℕ → ℕ) (sk : ℕ → Skeleton)
    (E : ∀ r, 0 < Wd r → ({c : κ // colR c = r} × Pt ≃ SkeletonLeafIndex (sk r)))
    (hemp : ∀ r, Wd r = 0 → IsEmpty {c : κ // colR c = r}) (ne : Nonempty F) (enc : F ↪ Dg)
    (r : ℕ) (h : 0 < Wd r) (cx : {c : κ // colR c = r} × Pt) :
    (layoutPointMd colR Wd sk E hemp ne enc).pos r cx = E r h cx := by
  simp [layoutPointMd, dif_pos h]

theorem layoutPointMd_skel {κ Pt F Dg : Type} (colR : κ → ℕ) (Wd : ℕ → ℕ) (sk : ℕ → Skeleton)
    (E : ∀ r, 0 < Wd r → ({c : κ // colR c = r} × Pt ≃ SkeletonLeafIndex (sk r)))
    (hemp : ∀ r, Wd r = 0 → IsEmpty {c : κ // colR c = r}) (ne : Nonempty F) (enc : F ↪ Dg) :
    (layoutPointMd colR Wd sk E hemp ne enc).skel = sk := rfl

/-! ### Non-vacuity -/

section NonVac
open NockvmE2E.Exec.V (ragSpec)

/-- `selOf_get` on the real RAP skeleton `skelOf (ragSpec 1 2) 4 4`: the leaf numbered 2 is selected -/
example : (SM.selOf (fun t => t == 2) (SM.skelOf (ragSpec 1 2) 4 4) 0).get
    ((leafEquiv _).symm ⟨2, by decide⟩) = true := by
  rw [selOf_get, leafNum_symm]; decide

example : (SM.skelOf (ragSpec 1 2) 4 4).leafCount = 4 := by decide

example : (ragPerm 1 2 (0, 3)).val = 3 := by decide
example : (ragPerm 2 2 (1, 3)).val = 1 * 2 * 2 + 1 * 2 + 1 := by decide
example : (friPerm 2 1).val = 2 := by decide
example : (friPerm 2 3).val = 3 := by decide

/-- two blocks over `Bool`: block `0` has one column and two points on a 2-leaf tree, block `1` is empty -/
def toyW (r : ℕ) : ℕ := if r = 0 then 1 else 0

theorem toy_hemp (r : ℕ) (h : toyW r = 0) : IsEmpty {c : Fin 1 // (fun _ : Fin 1 => 0) c = r} :=
  ⟨fun ⟨c, hc⟩ => by simp [toyW] at h; simp at hc; omega⟩

noncomputable def toyE (r : ℕ) (h : 0 < toyW r) :
    {c : Fin 1 // (fun _ : Fin 1 => 0) c = r} × Fin 2 ≃ SkeletonLeafIndex (Skeleton.perfect 1) :=
  (Fintype.equivOfCardEq (β := Fin (Skeleton.perfect 1).leafCount) (by
    have : r = 0 := by by_contra hr; simp [toyW, hr] at h
    subst this; decide)).trans (leafEquiv _).symm

noncomputable def toyMd : PointMaskData (fun _ : Fin 1 => 0) (Fin 2) Bool Bool :=
  layoutPointMd (fun _ : Fin 1 => 0) toyW (fun _ => Skeleton.perfect 1) toyE toy_hemp ⟨true⟩
    (Function.Embedding.refl Bool)

example : toyMd.FB 0 = Bool := rfl
example : toyMd.FB 1 = PUnit := rfl
example : toyMd.skel 1 = Skeleton.perfect 1 := rfl
example (x : Fin 2) : leafNum (toyMd.pos 0 (⟨0, rfl⟩, x)) < 2 := by
  have := leafNum_lt (toyMd.pos 0 (⟨0, rfl⟩, x))
  have h2 : (toyMd.skel 0).leafCount = 2 := by show (Skeleton.perfect 1).leafCount = 2; decide
  omega
end NonVac

#print axioms leafEquiv
#print axioms leafNum_symm
#print axioms selOf_get
#print axioms ragPerm_val
#print axioms friPerm_val
#print axioms layoutPointMd
#print axioms layoutPointMd_pos
#print axioms toyMd

end NockvmE2E.Exec.Layout
