/-
  NockvmE2E/Exec/PubExeG.lean   (executed, Mathlib-free, TOTAL)

  The table-count / table-length generic form of `PE.pubCheck` (Exec/PubExe.lean, untouched): the shape part of the check
  (layout arity, lengths, slices in range, 19 coin slots) is parametrised by the number of tables `n` and the per-table public
  lengths `lens`; the arithmetic part is a `chk` over the 19 frame-ordered coins and the `n` slices.
  * `pubCheck_eq_G`: `PE.pubCheck = pubCheckG 6 tabLens chk6` (the J-8 instance, `rfl`);
  * `pubCheckG_sound`: the generic soundness (shape and the `chk` of the slices), for any relation `R` that `chk` implies.
-/
import NockvmE2E.Exec.PubExe
set_option autoImplicit false

namespace NockvmE2E.Exec.PE
open NockvmE2E.Exec.VF

/-- table `t`'s publics slice: absent tables read as zeros (S4-RESULT step 3) -/
def sliceG (L : PubLayout) (pub : Array G) (t : Nat) : Array G :=
  if L.present[t]! then pub.extract L.bases[t]! (L.bases[t]! + L.lens[t]!) else Array.replicate L.lens[t]! 0

/-- the shape conditions of `pubCheck`, over `n` tables of lengths `lens` -/
def shapeOkG (n : Nat) (lens : Array Nat) (L : PubLayout) (slotOf : Array Nat) (slots : Array K3) (pub : Array G) : Bool :=
  L.bases.size == n && L.lens.size == n && L.present.size == n && L.lens == lens &&
    (List.range n).all (fun t => !L.present[t]! || L.bases[t]! + L.lens[t]! ≤ pub.size) &&
    slotOf.size ≥ 19 && (List.range 19).all (fun i => slotOf[i]! < slots.size)

/-- the 19 frame coins as read from the verifier's coin slots -/
def coins19 (slotOf : Array Nat) (slots : Array K3) : Array K3 :=
  (List.range 19).toArray.map fun i => slots[slotOf[i]!]!

/-- the generic verifier public check: `n` tables of lengths `lens`, the arithmetic `chk` on (coins, slices) -/
def pubCheckG (n : Nat) (lens : Array Nat) (chk : PubIn → Array K3 → Array (Array G) → Bool)
    (inp : PubIn) (L : PubLayout) (slotOf : Array Nat) : Array K3 → Array G → Bool :=
  fun slots pub =>
    shapeOkG n lens L slotOf slots pub && chk inp (coins19 slotOf slots) ((List.range n).toArray.map (sliceG L pub))

/-- the J-8 arithmetic part: `checkPubEq` over the six slices -/
def chk6 (inp : PubIn) (co : Array K3) (ps : Array (Array G)) : Bool :=
  checkPubEq inp co ⟨ps[0]!, ps[1]!, ps[2]!, ps[3]!, ps[4]!, ps[5]!⟩

/-- **J-8 is recovered**: `pubCheck = pubCheckG 6 tabLens chk6` -/
theorem pubCheck_eq_G (inp : PubIn) (L : PubLayout) (slotOf : Array Nat) :
    pubCheck inp L slotOf = pubCheckG 6 tabLens chk6 inp L slotOf := by
  funext slots pub
  have e : ((List.range 6).toArray.map (sliceG L pub)) =
      #[sliceG L pub 0, sliceG L pub 1, sliceG L pub 2, sliceG L pub 3, sliceG L pub 4, sliceG L pub 5] := by
    simp [List.range_succ]
  unfold pubCheck pubCheckG chk6 shapeOkG coins19
  rw [e]
  rfl

/-- generic soundness: a true check gives the shape conditions and every relation implied by `chk` on the slices -/
theorem pubCheckG_sound (n : Nat) (lens : Array Nat) (chk : PubIn → Array K3 → Array (Array G) → Bool)
    (R : PubIn → Array K3 → Array (Array G) → Prop) (hR : ∀ inp co ps, chk inp co ps = true → R inp co ps)
    (inp : PubIn) (L : PubLayout) (slotOf : Array Nat) (slots : Array K3) (pub : Array G)
    (h : pubCheckG n lens chk inp L slotOf slots pub = true) :
    shapeOkG n lens L slotOf slots pub = true ∧ R inp (coins19 slotOf slots) ((List.range n).toArray.map (sliceG L pub)) := by
  unfold pubCheckG at h
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, hR _ _ _ h.2⟩

end NockvmE2E.Exec.PE
