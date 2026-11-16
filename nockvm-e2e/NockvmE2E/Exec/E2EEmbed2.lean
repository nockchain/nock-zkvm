/-
  NockvmE2E/Exec/E2EEmbed2.lean   (proof-only)

  The J-8 wiring of the embed of `E2EEmbed.lean`: `selF_openAll`, `fstOpen`/`sndOpen` of `openAllOf`, the skeleton list of the
  combined mask (`hsk`) and the full `SelLinkC` assembly, the merkle messages of the embedded flat messages, the verifier's
  challenges vs `fs_chal_dec`, and a kernel `goRoot`-acceptance example.
-/
import NockvmE2E.Exec.E2EEmbed

open BinaryTree InductiveMerkleTree OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.E2E

open NockvmE2E.Merkle NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.Emb

/-! ## 1. splitting `openAllOf` along a mask append -/

section Split
open NockvmE2E.Merkle.MA

variable {D : Type} [Inhabited D]

/-- the first mask's openings of `openAllOf` over the appended mask are `openAllOf` over the first mask -/
theorem fstOpen_openAllOf : (a b : MRounds D) → (ts : List (FTree D)) →
    fstOpen a b (openAllOf (merkleSkels (a ++ b)) ts) = openAllOf (merkleSkels a) ts
  | [], _, _ => rfl
  | ⟨_, .clear⟩ :: a, b, ts => fstOpen_openAllOf a b ts
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, ts => by
      show (_, fstOpen a b (openAllOf (merkleSkels (a ++ b)) ts.tail)) = (_, openAllOf (merkleSkels a) ts.tail)
      rw [fstOpen_openAllOf a b ts.tail]

/-- the second mask's openings: `openAllOf` over the second mask on the trees after the first mask's merkle rounds -/
theorem sndOpen_openAllOf : (a b : MRounds D) → (ts : List (FTree D)) →
    sndOpen a b (openAllOf (merkleSkels (a ++ b)) ts) = openAllOf (merkleSkels b) (ts.drop (merkleSkels a).length)
  | [], _, _ => rfl
  | ⟨_, .clear⟩ :: a, b, ts => sndOpen_openAllOf a b ts
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, ts => by
      show sndOpen a b (openAllOf (merkleSkels (a ++ b)) ts.tail) = openAllOf (merkleSkels b) (ts.drop ((merkleSkels a).length + 1))
      rw [sndOpen_openAllOf a b ts.tail]
      cases ts <;> simp

theorem merkleSkels_append : (a b : MRounds D) → merkleSkels (a ++ b) = merkleSkels a ++ merkleSkels b
  | [], _ => rfl
  | ⟨_, .clear⟩ :: a, b => merkleSkels_append a b
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b => by
      show _ :: merkleSkels (a ++ b) = _ :: (merkleSkels a ++ merkleSkels b)
      rw [merkleSkels_append a b]

end Split

/-! ## 2. `selF_openAll`, the FRI twin of `selR_openAll` -/

section SelFri
open NockvmE2E.Exec.SM NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout Fri.Spec Domain

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (L : Fri.FriLeaves (ω := ω) s) (enc : F ↪ DgJ8)

/-- the FRI trees `i, i+1, ..`: tree `b` is good for `Q` (it opens every leaf `Q b` marks) -/
theorem selF_openAll (Q : ℕ → ℕ → Prop) : (c i : ℕ) → (h : i + c = k) → (ts : List (FTree DgJ8)) →
    (∀ b (hb : b < k), i ≤ b → b < i + c → ∀ t, Q b (leafNum t) →
      (mkOpeningD (ts.getD (b - i) ⟨fun _ => false, fun _ => default, [], default⟩) (L.skel ⟨b, by omega⟩)).selector.get t = true) →
    SelF s d l L DgJ8 enc Q i c h (openAllOf _ ts)
  | 0, _, _, _, _ => trivial
  | c + 1, i, h, ts, hh => ⟨fun t ht => by
        have := hh i (by omega) le_rfl (by omega) t ht
        cases ts <;> simpa using this,
      selF_openAll Q c i.succ (by omega) ts.tail (fun b hb h1 h2 t ht => by
        have := hh b hb (by omega) (by omega) t ht
        have e : b - i = (b - (i + 1)) + 1 := by omega
        rw [e] at this
        cases ts <;> simpa using this)⟩

end SelFri

/-! ## 3. the skeleton list of the combined mask -/

section SkelList
open NockvmE2E.Exec.Cover NockvmE2E.Merkle.RapP NockvmE2E.Rap Fri.Spec Domain

section R
variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] [SampleableType K]
  {ι β F : Type} {colRound : ι → ℕ} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  (md : RapMaskData colRound (β := β) F DgJ8) (Mfin : Type) [DecidableEq Mfin] [Finite Mfin]
  (I : (r : ℕ) → OracleInterface (Cols colRound β r)) (Ifin : OracleInterface Mfin)

theorem merkleSkels_rapMerkleMask : (k r : ℕ) →
    merkleSkels (rapMerkleMask Φ K md Mfin I Ifin r k) = (List.range k).map (fun i => md.skel (r + i))
  | 0, _ => rfl
  | k + 1, r => by
      rw [List.range_succ_eq_map]
      show md.skel r :: merkleSkels (rapMerkleMask Φ K md Mfin I Ifin r.succ k) = _
      rw [merkleSkels_rapMerkleMask k r.succ, List.map_cons, List.map_map]
      refine congrArg₂ _ rfl (List.map_congr_left fun i _ => ?_)
      simp only [Function.comp, Nat.succ_eq_add_one]
      congr 1; omega
end R

section Fr
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (L : Fri.FriLeaves (ω := ω) s) (enc : F ↪ DgJ8)

theorem merkleSkels_friMerkleMask (skF : ℕ → Skeleton) (hS : ∀ m : Fin k, L.skel m = skF m.1) :
    (c i : ℕ) → (h : i + c = k) →
    merkleSkels (Fri.friMerkleMask s d l L DgJ8 enc i c h) = (List.range c).map (fun j => skF (i + j))
  | 0, _, _ => rfl
  | c + 1, i, h => by
      rw [List.range_succ_eq_map]
      show L.skel ⟨i, by omega⟩ :: merkleSkels (Fri.friMerkleMask s d l L DgJ8 enc i.succ c (by omega)) = _
      rw [merkleSkels_friMerkleMask skF hS c i.succ (by omega), List.map_cons, List.map_map, hS]
      refine congrArg₂ _ rfl (List.map_congr_left fun j _ => ?_)
      simp only [Function.comp, Nat.succ_eq_add_one]
      congr 1; omega
end Fr

end SkelList

/-! ## 3b. the merkle messages of the embedded flat messages -/

section MsgsM
open NockvmE2E.Merkle.RapP NockvmE2E.Rap NockvmE2E.Exec.V Fri.Spec Domain

section R2
variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] [SampleableType K]
  {ι β F Dg : Type} {colRound : ι → ℕ} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] [Finite Dg] [DecidableEq Dg]
  (dY : List ℕ → Dg) (md : RapMaskData colRound (β := β) F Dg) (Mfin : Type) [DecidableEq Mfin] [Finite Mfin]
  (I : (r : ℕ) → OracleInterface (Cols colRound β r)) (Ifin : OracleInterface Mfin)

theorem merkleMsgs_rapMerkleMask : (c r : ℕ) → (fm : List (List ℕ)) →
    merkleMsgs dY (rapMerkleMask Φ K md Mfin I Ifin r c) fm = (List.range c).map (fun j => dY (fm.getD j []))
  | 0, _, _ => rfl
  | c + 1, r, fm => by
      rw [List.range_succ_eq_map]
      show dY (fm.headD []) :: merkleMsgs dY (rapMerkleMask Φ K md Mfin I Ifin r.succ c) fm.tail = _
      rw [merkleMsgs_rapMerkleMask c r.succ fm.tail, List.map_cons, List.map_map]
      refine congrArg₂ _ ?_ (List.map_congr_left fun j _ => ?_)
      · cases fm <;> rfl
      · cases fm <;> simp

theorem length_rapMerkleMask : (c r : ℕ) →
    (rapMerkleMask Φ K md Mfin I Ifin r c).length = c + 1
  | 0, _ => rfl
  | c + 1, r => by
      show (rapMerkleMask Φ K md Mfin I Ifin r.succ c).length + 1 = c + 1 + 1
      rw [length_rapMerkleMask c r.succ]
end R2

section Fr2
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (L : Fri.FriLeaves (ω := ω) s) {Dg : Type} [Finite Dg] [DecidableEq Dg] (enc : F ↪ Dg) (dY : List ℕ → Dg)

theorem merkleMsgs_friMerkleMask : (c i : ℕ) → (h : i + c = k) → (fm : List (List ℕ)) →
    merkleMsgs dY (Fri.friMerkleMask s d l L Dg enc i c h) fm = (List.range c).map (fun j => dY (fm.getD j []))
  | 0, _, _, _ => rfl
  | c + 1, i, h, fm => by
      rw [List.range_succ_eq_map]
      show dY (fm.headD []) :: merkleMsgs dY (Fri.friMerkleMask s d l L Dg enc i.succ c (by omega)) fm.tail = _
      rw [merkleMsgs_friMerkleMask c i.succ (by omega) fm.tail, List.map_cons, List.map_map]
      refine congrArg₂ _ ?_ (List.map_congr_left fun j _ => ?_)
      · cases fm <;> rfl
      · cases fm <;> simp

theorem length_friMerkleMask : (c i : ℕ) → (h : i + c = k) →
    (Fri.friMerkleMask s d l L Dg enc i c h).length = c + 1
  | 0, _, _ => rfl
  | c + 1, i, h => by
      show (Fri.friMerkleMask s d l L Dg enc i.succ c (by omega)).length + 1 = c + 1 + 1
      rw [length_friMerkleMask c i.succ (by omega)]
end Fr2

/-- the flat messages `msgsOf` at the root positions -/
theorem msgsOf_root_lo (XI : ExecInst) (π : FlatProof) (j : ℕ) (hj : j < 4) :
    (msgsOf XI π).toList.getD (j + 1) [] = π.roots[j]! := by
  interval_cases j <;> simp [msgsOf]

theorem msgsOf_root_hi (XI : ExecInst) (π : FlatProof) (hs : π.roots.size = 4 + XI.k) (j : ℕ) (hj : j < XI.k) :
    (msgsOf XI π).toList.getD (8 + j) [] = π.roots[4 + j]! := by
  have : (msgsOf XI π).toList = [[], π.roots[0]!, π.roots[1]!, π.roots[2]!, π.roots[3]!, deepMsg π.vT π.vQ, [], []] ++
      (π.roots.toList.drop 4).take XI.k ++ [π.pfinal.toList.flatMap VF.K3.limbs] := by
    simp [msgsOf, Array.toList_extract]
  have hr : 4 + j < π.roots.size := by omega
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
    List.getElem?_append_right (by simp)]
  have hr2 : j + 4 < π.roots.size := by omega
  simp [hj, List.getElem?_drop, Nat.add_comm 4 j, getElem?_pos π.roots (j + 4) hr2, getElem!_pos π.roots (j + 4) hr2]


theorem length_msgsOf (XI : ExecInst) (π : FlatProof) (hs : π.roots.size = 4 + XI.k) :
    (msgsOf XI π).toList.length = 9 + XI.k := by
  simp [msgsOf, hs]
  omega

theorem getD_drop' (fm : List (List ℕ)) (n j : ℕ) : (fm.drop n).getD j [] = fm.getD (n + j) [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm n j]

theorem rootsOf_eq {k : ℕ} (π : FlatProof) (hr : π.roots.size = 4 + k) :
    rootsOf π = (List.range (4 + k)).map (fun j => dgOf π.roots[j]!) := by
  apply List.ext_getElem (by simp [rootsOf, hr])
  intro i h1 h2
  have hi : i < π.roots.size := by simpa [rootsOf] using h1
  simp [rootsOf, getElem!_pos π.roots i hi]

end MsgsM

/-! ## 3c. the verifier's challenges are the path's challenges (`fs_chal_dec`) -/

section Chals
variable {Input : Type}

/-- **`chalsOf` = `fs_chal_dec`**: for the flat view `FS = FSdec g` of a table, every round `i` of the flat verifier that draws challenges
(`roundNl i ≠ 0`) gets the encoding of the audited path's challenge `i`, the path of any messages decoded from the flat message list -/
theorem chalsOf_dec (XI : ExecInst) (π : FlatProof) (encZ : Input → List ℕ) (decZ : List ℕ → Input)
    (hz : ∀ x, decZ (encZ x) = x) (rounds : List Round) (ds : Decs rounds)
    (g : (k : Key Input PUnit rounds) → k.Challenge) (z : Input) (ms : PublicMessages rounds)
    (hm : MsgsDec rounds ds (msgsOf XI π).toList ms) (FS : FSFn)
    (hFS : ∀ x n, FS x n = FSdec rounds ds decZ g x) (i : ℕ) (hi : i < (msgsOf XI π).size) (hnl : roundNl XI i ≠ 0) :
    (chalsOf XI FS (encZ z) π)[i]! = (encPathD rounds ds (pathOf z rounds g ms)).getD i [] := by
  have hsz : i < ((Array.range (msgsOf XI π).size).map fun i =>
      if roundNl XI i == 0 then [] else FS (encZ z :: ((msgsOf XI π).extract 0 (i + 1)).toList) (roundNl XI i)).size := by
    simpa using hi
  unfold chalsOf
  rw [getElem!_pos _ i hsz]
  simp only [Array.getElem_map, Array.getElem_range]
  have hne : (roundNl XI i == 0) = false := by simpa using hnl
  rw [hne, if_neg (by simp), hFS, fs_chal_dec encZ decZ hz rounds ds g z (msgsOf XI π).toList ms hm i (by simpa using hi)]
  simp [Array.toList_extract]

end Chals

/-! ## 4. `hsk` and the `SelLinkC` assembly, in the context of `verifyFlat_sound''` (digest type `DgJ8`) -/

section Closed
open Polynomial ProtocolSpec Fri.Spec Domain BatchedFri.Spec BatchedFri.Spec.BatchingRound
open NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Exec.Inst

variable (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof) (hv : verifyFlat XI H FS zF π = true)

set_option hygiene false in
local notation "ωS" => smoothDomain XI.nD (nD_le_of_verify XI H FS zF π hv)
set_option hygiene false in
local notation "s1" => (fun _ : Fin (XI.k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ XI.nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ XI.nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin) (nb : ℕ)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec XI.k (ω := ωS) s1 XI.l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (enc : KC ↪ DgJ8)
  (md : PointMaskData P.colRoundX (Fin (2 ^ XI.nD)) B DgJ8) (L : Fri.FriLeaves (ω := ωS) s1)

set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l DgJ8 enc md L (S := S)
set_option hygiene false in
local notation "PS" => P.statement R0 Rest
set_option hygiene false in
local notation "PL" => friPlan (ω := ωS) P A R0 Rest RestV e
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin nb
set_option hygiene false in
local notation "BM" => bmask (S := S) s1 d XI.l DgJ8 enc L

/-- the audited skeleton list of the combined mask is the flat verifier's, `skelFlat XI j` for tree `j` (`nb = 4`) -/
theorem hsk_list (encB : B ↪ DgJ8) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb XI r))
    (hmd : md = mdX XI (by have := (flat_shape XI H FS zF π ((verifyFlat_iff XI H FS zF π).mp hv)).1; omega) P.colRoundX rk encB)
    (hL : L = LX XI (nD_le_of_verify XI H FS zF π hv)) (hnb : nb = 4) :
    merkleSkels (MC) = (List.range (4 + XI.k)).map (skelFlat XI) := by
  have h1 : merkleSkels (MC) = merkleSkels (RapP.rapMerkleMask Φ KC md.toRapMaskData
      (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I Ifin 0 nb) ++
      merkleSkels (Fri.friMerkleMask s1 d XI.l L DgJ8 enc 0 XI.k (by omega)) :=
    merkleSkels_append _ _
  rw [h1, merkleSkels_rapMerkleMask (Φ := Φ) (K := KC), merkleSkels_friMerkleMask s1 d XI.l L enc
    (fun j => skelOf (friSpec (2 ^ (XI.nD - (j + 1)))) (2 ^ (XI.nD - (j + 1))) (2 ^ (XI.nD - (j + 1))))
    (fun m => by subst hL; rfl), List.range_add, List.map_append, List.map_map, hnb]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine List.map_congr_left fun i hi => ?_
    have hi4 : i < 4 := List.mem_range.mp hi
    subst hmd
    simp only [Nat.zero_add, skelFlat, hi4, ite_true]
    rfl
  · refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, Nat.zero_add, skelFlat]
    have : ¬ 4 + j < 4 := by omega
    have e3 : 4 + j - 3 = j + 1 := by omega
    simp only [this, ite_false, e3]
    rfl

/-- **the selector link of the embedded openings**: with the verifier's own hash `H = Hof _ h` (any table `h`) the embedded openings
`openAllOf _ (flatTrees XI π)` have selectors marking every leaf of the verifier's selection `selsOf` (`SelLinkC`). -/
theorem selLinkC_embed (encB : B ↪ DgJ8) (rk : ∀ r, {c : ι ⊕ Fin P.nq // P.colRoundX c = r} ≃ Fin (Wb XI r))
    (hmd : md = mdX XI (by have := (flat_shape XI H FS zF π ((verifyFlat_iff XI H FS zF π).mp hv)).1; omega) P.colRoundX rk encB)
    (hL : L = LX XI (nD_le_of_verify XI H FS zF π hv)) (hnb : nb = 4)
    (h : NQuery (merkleSkels (MC)) → DgJ8) (hH : H = Hof (merkleSkels (MC)) h) :
    SelLinkC XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d DgJ8 enc md L
      (openAllOf (merkleSkels (MC)) (flatTrees XI π)) := by
  have hok := (verifyFlat_iff XI H FS zF π).mp hv
  have hlist := hsk_list (S := S) XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d enc md L encB rk hmd hL hnb
  have hlen : (merkleSkels (MC)).length = 4 + XI.k := by rw [hlist]; simp
  have hsk : ∀ j (hj : j < (merkleSkels (MC)).length), (merkleSkels (MC)).get ⟨j, hj⟩ = skelFlat XI j := by
    intro j hj; simp [hlist]
  have hok' : FlatOk XI (Hof (merkleSkels (MC)) h) FS zF π := by rw [← hH]; exact hok
  have hmdsk : ∀ b, b < 4 → md.skel b = skelFlat XI b := by
    intro b hb
    subst hmd
    simp only [skelFlat, hb, ite_true]
    rfl
  refine ⟨?_, ?_⟩
  · have e1 : MA.fstOpen (RM) (BM) (openAllOf (merkleSkels (MC)) (flatTrees XI π)) =
        openAllOf (merkleSkels (RM)) (flatTrees XI π) := fstOpen_openAllOf _ _ _
    rw [e1]
    refine selR_openAll md (Rok (P.statement R0 Rest) (friPlan (ω := ωS) P A R0 Rest RestV e)) I Ifin (QR XI π) nb 0 (flatTrees XI π) ?_
    intro b _ hb i hi
    have hb4 : b < 4 := by omega
    have hbl : b < (merkleSkels (MC)).length := by omega
    by_cases hne : (blockLayout XI).1[b]! = 0
    · exfalso
      have hsel : (selsOf XI π)[b]! = #[] := by
        rw [selsR XI π b hb4]; unfold treeSel; simp [Wb, hb4, hne]
      obtain ⟨_, ht⟩ := hi
      rw [hsel] at ht; simp at ht
    · have hsel := (tree_embed XI FS zF π (merkleSkels (MC)) h hok' hlen hsk ⟨b, hbl⟩).2
        (by simp [hne])
      rw [get_openAllOf, ftree_getD XI π b (by omega)] at hsel
      have key : ∀ (s' : Skeleton), s' = (merkleSkels (MC)).get ⟨b, hbl⟩ → ∀ (i : SkeletonLeafIndex s'),
          QR XI π b (leafNum i) → (mkOpeningD (ftree XI π b) s').selector.get i = true := by
        intro s' hs' i hi
        subst hs'
        rw [hsel, selOf_get]
        simpa [ftree, ftreeOf, isSelRP, isSelB] using QR_isSel XI π b _ hi
      rw [Nat.sub_zero, ftree_getD XI π b (by omega)]
      exact key _ ((hmdsk b hb4).trans (hsk b hbl).symm) i hi
  · have e1 : MA.sndOpen (RM) (BM) (openAllOf (merkleSkels (MC)) (flatTrees XI π)) =
        openAllOf (merkleSkels (BM)) ((flatTrees XI π).drop (merkleSkels (RM)).length) := sndOpen_openAllOf _ _ _
    rw [e1]
    have hl4 : (merkleSkels (RM)).length = 4 := by
      show (merkleSkels (RapP.rapMerkleMask Φ KC md.toRapMaskData (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I Ifin 0 nb)).length = 4
      rw [merkleSkels_rapMerkleMask (Φ := Φ) (K := KC)]; simp [hnb]
    rw [hl4]
    refine selF_openAll s1 d XI.l L enc (QF XI π) XI.k 0 (by omega) _ ?_
    intro b hb _ _ t ht
    have hbl : 4 + b < (merkleSkels (MC)).length := by omega
    have hsel := (tree_embed XI FS zF π (merkleSkels (MC)) h hok' hlen hsk ⟨4 + b, hbl⟩).2
      (by simp)
    rw [get_openAllOf, ftree_getD XI π (4 + b) (by omega)] at hsel
    have key : ∀ (s' : Skeleton), s' = (merkleSkels (MC)).get ⟨4 + b, hbl⟩ → ∀ (t : SkeletonLeafIndex s'),
        QF XI π b (leafNum t) → (mkOpeningD (ftree XI π (4 + b)) s').selector.get t = true := by
      intro s' hs' t ht
      subst hs'
      rw [hsel, selOf_get]
      simpa [ftree, ftreeOf, isSelFP, isSelB] using QF_isSel XI π b _ hb ht
    have hLs : L.skel ⟨b, hb⟩ = (merkleSkels (MC)).get ⟨4 + b, hbl⟩ := by
      rw [hsk (4 + b) hbl]
      subst hL
      simp only [skelFlat]
      have : ¬ 4 + b < 4 := by omega
      have e3 : 4 + b - 3 = b + 1 := by omega
      simp only [this, ite_false, e3]
      rfl
    have hg : ((flatTrees XI π).drop 4).getD (b - 0) ⟨fun _ => false, fun _ => default, [], default⟩ = ftree XI π (4 + b) := by
      rw [Nat.sub_zero, List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
        ftree_getD XI π (4 + b) (by omega)]
    rw [hg]
    exact key _ hLs t ht

/-- **the merkle messages**: the roots of the embedded flat messages, in merkle-round order, are the flat proof's roots -/
theorem merkleMsgs_msC (hnb : nb = 4) (hr : π.roots.size = 4 + XI.k) :
    merkleMsgs dgOf (MC) (msgsOf XI π).toList = rootsOf π := by
  have h1 : merkleMsgs dgOf (MC) (msgsOf XI π).toList = merkleMsgs dgOf (RM) (msgsOf XI π).toList ++
      merkleMsgs dgOf (BM) ((msgsOf XI π).toList.drop (RM).length) := merkleMsgs_append dgOf _ _ _
  have hl : (RM).length = 6 := by
    show (RapP.rapMerkleMask Φ KC md.toRapMaskData (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I Ifin 0 nb).length + 1 = 6
    rw [length_rapMerkleMask]; omega
  have h2 : merkleMsgs dgOf (RM) (msgsOf XI π).toList =
      (List.range 4).map (fun j => dgOf (π.roots[j]!)) := by
    show merkleMsgs dgOf (RapP.rapMerkleMask Φ KC md.toRapMaskData (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I Ifin 0 nb) _ = _
    rw [merkleMsgs_rapMerkleMask, hnb]
    refine List.map_congr_left fun j hj => ?_
    rw [← msgsOf_root_lo XI π j (List.mem_range.mp hj)]
    cases hm : (msgsOf XI π).toList <;> simp
  have h3 : merkleMsgs dgOf (BM) ((msgsOf XI π).toList.drop 6) =
      (List.range XI.k).map (fun j => dgOf (π.roots[4 + j]!)) := by
    show merkleMsgs dgOf (Fri.friMerkleMask s1 d XI.l L DgJ8 enc 0 XI.k (by omega)) (((msgsOf XI π).toList.drop 6).tail.tail) = _
    rw [merkleMsgs_friMerkleMask]
    refine List.map_congr_left fun j hj => ?_
    rw [← msgsOf_root_hi XI π hr j (List.mem_range.mp hj)]
    have : ∀ (l : List (List ℕ)), l.tail.tail.getD j [] = l.getD (j + 2) [] := by
      intro l; cases l <;> simp [List.getD_eq_getElem?_getD]
    rw [this, getD_drop', show 6 + (j + 2) = 8 + j by omega]
  rw [h1, hl, h2, h3, rootsOf_eq π hr, List.range_add, List.map_append, List.map_map]
  rfl

theorem length_msC (hnb : nb = 4) : (MC).length = 9 + XI.k := by
  have h1 : (MC).length = (RM).length + (BM).length := List.length_append ..
  have hl : (RM).length = 6 := by
    show (RapP.rapMerkleMask Φ KC md.toRapMaskData (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I Ifin 0 nb).length + 1 = 6
    rw [length_rapMerkleMask]; omega
  have hb : (BM).length = XI.k + 3 := by
    show (Fri.friMerkleMask s1 d XI.l L DgJ8 enc 0 XI.k (by omega)).length + 1 + 1 = XI.k + 3
    rw [length_friMerkleMask]
  omega

/-- **`chalsOf_embed`**: at J-8 (`nb = 4`), the flat verifier's challenges under the decode-based view `FSdec` of a table `g` of the
compiled protocol are the encodings of the challenges of the audited path of `embedMsgs` (rounds with `roundNl i ≠ 0`) -/
theorem chalsOf_embed {Op : Type} [Finite Op] [DecidableEq Op] {Input : Type} (hnb : nb = 4) (hr : π.roots.size = 4 + XI.k)
    (ds : MDec (MC)) (ω : Op) (encZ : Input → List ℕ) (decZ : List ℕ → Input) (hz : ∀ x, decZ (encZ x) = x)
    (g : (k : Key Input PUnit (compiledRoundsK DgJ8 Op (MC))) → k.Challenge) (z : Input)
    (hFS : ∀ x n, FS x n = FSdec _ (mDecs dgOf (MC) ds ω) decZ g x)
    (i : ℕ) (hi : i < (msgsOf XI π).size) (hnl : roundNl XI i ≠ 0) :
    (chalsOf XI FS (encZ z) π)[i]! =
      (encPathD _ (mDecs dgOf (MC) ds ω) (pathOf z _ g (embedMsgs dgOf (MC) ds ω (msgsOf XI π).toList))).getD i [] :=
  chalsOf_dec XI π encZ decZ hz _ _ g z _
    (embedMsgs_dec dgOf (MC) ds ω ω _ (by rw [length_msgsOf XI π hr, length_msC XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d enc md L hnb])) FS hFS i hi hnl

end Closed

/-! ## 6. non-vacuity: `goRoot` acceptance of a pruned opening on a concrete tree (kernel evaluation) -/

section Ex

/-- a concrete (non-injective-free, but computable) node hash on 5-limb digests -/
def exH (l : List ℕ) : Dg5 := [l.foldl (fun a x => (a * 31 + x) % 1000003) 7, 0, 0, 0, 0]
def exLeaf (i : ℕ) : Dg5 := [i + 10, 0, 0, 0, 0]

/-- the opening of leaf `1` of a 4-leaf tree: the frontier is `[right node, left sibling leaf]` (pre-order), and the recomputed root is the
root of the fully-selected tree -/
def exAccepts (sp : TSpec) (j : ℕ) : Bool :=
  let full := goRoot exH sp j #[0, 1, 2, 3] exLeaf #[] 1 0 4 0
  let node3 := exH ([tagNode, j, 3] ++ exLeaf 2 ++ exLeaf 3)
  let opened := goRoot exH sp j #[1] (fun _ => exLeaf 1) #[node3, exLeaf 0] 1 0 4 0
  full.isSome && opened == full.map (fun x => (x.1, 2))

/-- a FRI-shaped tree (tree number 4, `friSpec 4`) -/
example : exAccepts (friSpec 4) 4 = true := by decide +kernel
/-- a RAP-shaped tree (tree 0, `ragSpec 1 2`: width 1, half 2) -/
example : exAccepts (ragSpec 1 2) 0 = true := by decide +kernel
/-- and a wrong frontier is rejected (the root changes) -/
example : (goRoot exH (friSpec 4) 4 #[1] (fun _ => exLeaf 1) #[exLeaf 2, exLeaf 0] 1 0 4 0 ==
    (goRoot exH (friSpec 4) 4 #[0, 1, 2, 3] exLeaf #[] 1 0 4 0).map (fun x => (x.1, 2))) = false := by decide +kernel

end Ex

end NockvmE2E.Exec.E2E

open NockvmE2E.Exec.E2E in
#print axioms fstOpen_openAllOf
open NockvmE2E.Exec.E2E in
#print axioms sndOpen_openAllOf
open NockvmE2E.Exec.E2E in
#print axioms selF_openAll
open NockvmE2E.Exec.E2E in
#print axioms hsk_list
open NockvmE2E.Exec.E2E in
#print axioms selLinkC_embed
open NockvmE2E.Exec.E2E in
#print axioms merkleMsgs_msC
open NockvmE2E.Exec.E2E in
#print axioms chalsOf_dec
open NockvmE2E.Exec.E2E in
#print axioms chalsOf_embed
open NockvmE2E.Exec.E2E in
#print axioms length_msC
open NockvmE2E.Exec.E2E in
#print axioms msgsOf_root_hi
