/-
  NockvmE2E/Exec/ZBind.lean   (S1; executed, Mathlib-free)

  Binds the public input into the Fiat-Shamir key.  `zHdr p = tagZ :: encPub p` is a fixed prefix of the statement list `z` (the first element of every FS key
  of `verifyOnlineE'`); `zBind p z` checks the prefix.  `encPub` is injective and prefix-free (`encPub_inj`), every limb is a canonical Goldilocks element
  (`encPub_based`: nat fields are split into base-`PN` digits with continue flags, so no length limb can exceed `PN`).  No hash, so no collision assumption.
  STILL NON-ADAPTIVE as a theorem: this file only makes the executed verifier enforce the binding.  Not zero-knowledge.
-/
import NockvmE2E.Exec.PubExe
set_option autoImplicit false

namespace NockvmE2E.Exec.ZBind
open NockvmE2E.Exec.VF NockvmE2E.Exec.PE

/-- prefix-free coding predicate -/
def Pf {α : Type} (f : α → List Nat) : Prop := ∀ a b s t, f a ++ s = f b ++ t → a = b ∧ s = t

/-- base-`PN` digits, least significant first; `0 ↦ []` -/
def lmb (n : Nat) : List Nat := if h : n = 0 then [] else n % PN :: lmb (n / PN)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by unfold PN; decide)

def fromL : List Nat → Nat
  | [] => 0
  | d :: t => d + PN * fromL t

theorem fromL_lmb (n : Nat) : fromL (lmb n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold lmb
    by_cases h : n = 0
    · simp [h, fromL]
    · rw [dif_neg h]
      have hlt : n / PN < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by unfold PN; decide)
      simp only [fromL, ih _ hlt]
      exact Nat.mod_add_div n PN

theorem lmb_based (n : Nat) : ∀ d ∈ lmb n, d < PN := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold lmb
    by_cases h : n = 0
    · simp [h]
    · rw [dif_neg h]
      have hlt : n / PN < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by unfold PN; decide)
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact Nat.mod_lt _ (by unfold PN; decide)
      · exact ih _ hlt d hd

/-- self-delimiting list code: continue flag `1`, element, ..., end flag `0` -/
def encL {α : Type} (f : α → List Nat) : List α → List Nat
  | [] => [0]
  | x :: xs => 1 :: (f x ++ encL f xs)

theorem pf_list {α : Type} {f : α → List Nat} (hf : Pf f) : Pf (encL f) := by
  intro xs
  induction xs with
  | nil =>
    intro ys s t h
    cases ys with
    | nil => simp only [encL, List.cons_append, List.nil_append, List.cons.injEq, true_and] at h; exact ⟨rfl, h⟩
    | cons y ys => simp [encL] at h
  | cons x xs ih =>
    intro ys s t h
    cases ys with
    | nil => simp [encL] at h
    | cons y ys =>
      simp only [encL, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := hf _ _ _ _ h
      obtain ⟨rfl, h3⟩ := ih _ _ _ h2
      exact ⟨rfl, h3⟩

theorem encL_based {α : Type} {f : α → List Nat} (xs : List α) (hf : ∀ x ∈ xs, ∀ y ∈ f x, y < PN) : ∀ y ∈ encL f xs, y < PN := by
  induction xs with
  | nil => intro y hy; simp [encL] at hy; subst hy; unfold PN; decide
  | cons x xs ih =>
    intro y hy
    simp only [encL, List.mem_cons, List.mem_append] at hy
    rcases hy with rfl | hy | hy
    · unfold PN; decide
    · exact hf x (List.mem_cons_self ..) y hy
    · exact ih (fun x' hx' => hf x' (List.mem_cons_of_mem _ hx')) y hy

def encNat (n : Nat) : List Nat := encL (fun d => [d]) (lmb n)

theorem pf_dig : Pf (fun d : Nat => [d]) := by
  intro a b s t h; simp only [List.singleton_append, List.cons.injEq] at h; exact ⟨h.1, h.2⟩

theorem pf_nat : Pf encNat := by
  intro a b s t h
  obtain ⟨h1, h2⟩ := pf_list pf_dig _ _ _ _ h
  refine ⟨?_, h2⟩
  rw [← fromL_lmb a, ← fromL_lmb b, h1]

theorem encNat_based (n : Nat) : ∀ y ∈ encNat n, y < PN :=
  encL_based _ (fun d hd y hy => by simp only [List.mem_singleton] at hy; subst hy; exact lmb_based n y hd)

def encTok : Tok → List Nat
  | .cell => [0]
  | .atom n => 1 :: encNat n

theorem pf_tok : Pf encTok := by
  intro a b s t h
  cases a <;> cases b
  · simp only [encTok, List.singleton_append, List.cons.injEq, true_and] at h; exact ⟨rfl, h⟩
  · simp [encTok] at h
  · simp [encTok] at h
  · simp only [encTok, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨h1, h2⟩ := pf_nat _ _ _ _ h
    subst h1; exact ⟨rfl, h2⟩

theorem encTok_based (t : Tok) : ∀ y ∈ encTok t, y < PN := by
  cases t with
  | cell => intro y hy; simp [encTok] at hy; subst hy; unfold PN; decide
  | atom n =>
    intro y hy
    simp only [encTok, List.mem_cons] at hy
    rcases hy with rfl | hy
    · unfold PN; decide
    · exact encNat_based n y hy

def encNR (r : NounRec) : List Nat :=
  encNat r.key ++ (encL encTok r.noun ++ (encNat r.idx ++ (encNat r.hi ++ encNat r.lo)))

theorem pf_nr : Pf encNR := by
  intro a b s t h
  cases a with | mk k n i hi lo => cases b with | mk k' n' i' hi' lo' =>
  simp only [encNR, List.append_assoc] at h
  obtain ⟨e, h1⟩ := pf_nat _ _ _ _ h
  cases e
  obtain ⟨e, h2⟩ := pf_list pf_tok _ _ _ _ h1
  cases e
  obtain ⟨e, h3⟩ := pf_nat _ _ _ _ h2
  cases e
  obtain ⟨e, h4⟩ := pf_nat _ _ _ _ h3
  cases e
  obtain ⟨e, h5⟩ := pf_nat _ _ _ _ h4
  cases e
  exact ⟨rfl, h5⟩

theorem encNR_based (r : NounRec) : ∀ y ∈ encNR r, y < PN := by
  intro y hy
  simp only [encNR, List.mem_append] at hy
  rcases hy with hy | hy | hy | hy | hy
  · exact encNat_based _ y hy
  · exact encL_based _ (fun x _ => encTok_based x) y hy
  · exact encNat_based _ y hy
  · exact encNat_based _ y hy
  · exact encNat_based _ y hy

def encAtom (a : Nat × Nat) : List Nat := encNat a.1 ++ encNat a.2

theorem pf_atom : Pf encAtom := by
  intro a b s t h
  obtain ⟨k, v⟩ := a; obtain ⟨k', v'⟩ := b
  simp only [encAtom, List.append_assoc] at h
  obtain ⟨e, h1⟩ := pf_nat _ _ _ _ h
  cases e
  obtain ⟨e, h2⟩ := pf_nat _ _ _ _ h1
  cases e
  exact ⟨rfl, h2⟩

def encPrim (r : PrimRec) : List Nat :=
  encNat r.id ++ (encNat r.code ++ (encNat r.idx ++ (encNat r.hi ++ encNat r.lo)))

theorem pf_prim : Pf encPrim := by
  intro a b s t h
  cases a with | mk k n i hi lo => cases b with | mk k' n' i' hi' lo' =>
  simp only [encPrim, List.append_assoc] at h
  obtain ⟨e, h1⟩ := pf_nat _ _ _ _ h
  cases e
  obtain ⟨e, h2⟩ := pf_nat _ _ _ _ h1
  cases e
  obtain ⟨e, h3⟩ := pf_nat _ _ _ _ h2
  cases e
  obtain ⟨e, h4⟩ := pf_nat _ _ _ _ h3
  cases e
  obtain ⟨e, h5⟩ := pf_nat _ _ _ _ h4
  cases e
  exact ⟨rfl, h5⟩

/-- the canonical, injective, prefix-free encoding of the public input (claim cells, pins, atoms, prims, calls) -/
def encPub (p : PubIn) : List Nat :=
  encL encNR p.claimCells ++ (encL encNR p.pins ++ (encL encAtom p.atoms ++ (encL encPrim p.prims ++ encL encNat p.calls)))

/-- domain tag `"ZB"` -/
def tagZ : Nat := 0x5A42

def zHdr (p : PubIn) : List Nat := tagZ :: encPub p

/-- `z` starts with the header of `p` -/
def zBind (p : PubIn) (z : List Nat) : Bool := z.take (zHdr p).length == zHdr p

theorem encPub_pf : Pf encPub := by
  intro a b s t h
  cases a with | mk c1 p1 a1 r1 k1 => cases b with | mk c2 p2 a2 r2 k2 =>
  simp only [encPub, List.append_assoc] at h
  obtain ⟨e, h1⟩ := pf_list pf_nr _ _ _ _ h
  cases e
  obtain ⟨e, h2⟩ := pf_list pf_nr _ _ _ _ h1
  cases e
  obtain ⟨e, h3⟩ := pf_list pf_atom _ _ _ _ h2
  cases e
  obtain ⟨e, h4⟩ := pf_list pf_prim _ _ _ _ h3
  cases e
  obtain ⟨e, h5⟩ := pf_list pf_nat _ _ _ _ h4
  cases e
  exact ⟨rfl, h5⟩

/-- `encPub` is injective (and prefix-free) -/
theorem encPub_inj {p q : PubIn} (h : encPub p = encPub q) : p = q := by
  have := encPub_pf p q [] [] (by simpa using h)
  exact this.1

theorem encPub_based (p : PubIn) : ∀ y ∈ encPub p, y < PN := by
  intro y hy
  simp only [encPub, List.mem_append] at hy
  rcases hy with hy | hy | hy | hy | hy
  · exact encL_based _ (fun x _ => encNR_based x) y hy
  · exact encL_based _ (fun x _ => encNR_based x) y hy
  · exact encL_based _ (fun x _ => by
      intro y hy; simp only [encAtom, List.mem_append] at hy
      rcases hy with hy | hy <;> exact encNat_based _ y hy) y hy
  · exact encL_based _ (fun x _ => by
      intro y hy; simp only [encPrim, List.mem_append] at hy
      rcases hy with hy | hy | hy | hy | hy <;> exact encNat_based _ y hy) y hy
  · exact encL_based _ (fun x _ => encNat_based x) y hy

theorem zHdr_based (p : PubIn) : ∀ y ∈ zHdr p, y < PN := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · unfold tagZ PN; decide
  · exact encPub_based p y hy

/-- the acceptance witness: the honest `z = zHdr p ++ s` passes the binding check -/
theorem zBind_hdr (p : PubIn) (s : List Nat) : zBind p (zHdr p ++ s) = true := by
  simp [zBind, List.take_left']

theorem zBind_iff (p : PubIn) (z : List Nat) : zBind p z = true ↔ ∃ s, z = zHdr p ++ s := by
  constructor
  · intro h
    refine ⟨z.drop (zHdr p).length, ?_⟩
    have h' : z.take (zHdr p).length = zHdr p := by simpa [zBind] using h
    have := List.take_append_drop (zHdr p).length z
    rw [h'] at this
    exact this.symm
  · intro hs
    obtain ⟨s, hs⟩ := hs
    subst hs
    exact zBind_hdr p s

/-- the binding determines the public input -/
theorem zBind_inj {p q : PubIn} {z : List Nat} (hp : zBind p z = true) (hq : zBind q z = true) : p = q := by
  obtain ⟨s, hs⟩ := (zBind_iff p z).1 hp
  obtain ⟨t, ht⟩ := (zBind_iff q z).1 hq
  have h := hs.symm.trans ht
  simp only [zHdr, List.cons_append, List.cons.injEq, true_and] at h
  exact (encPub_pf p q s t h).1

end NockvmE2E.Exec.ZBind

