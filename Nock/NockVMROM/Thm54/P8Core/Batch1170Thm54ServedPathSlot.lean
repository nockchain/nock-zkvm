/-
  Nock/NockVMROM/Thm54/P8Core/Batch1170Thm54ServedPathSlot.lean

  The
  remaining declarations stay in `Nock/RedTeam/Batch1170Thm54ServedPathSlot.lean`, which imports this module. This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`. -/
import Nock.NockVMROM.Thm54.P8Core.Batch1171Thm54C2InductionPositional
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenTierAComputeLink
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1170

open Nock
open Nock.Walk
open Nock.Reified
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.UniqueExponentsBridge
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch554
open Nock.RedTeam.Batch1171 (PR)

section PathSlot

variable {F K : Type} [Field F] [Field K] [Fintype F] [DecidableEq F] [Algebra F K] {M : ℕ}

theorem nounAt_append (p p' : List Bool) (n : Noun) :
    nounAt (p ++ p') n = (nounAt p n).bind (nounAt p') := by
  induction p generalizing n with
  | nil => simp [nounAt]
  | cons b p ih =>
      cases n with
      | atom k => cases b <;> simp [nounAt, nounChild]
      | cell l r => cases b <;> simp [nounAt, nounChild, ih]

theorem certAxis_eq_pathAxis (m : ℕ) (c : ℕ → Bool) :
    StrategyOfTracesR0.certAxis m c = pathAxis (bitsOf m c) := by
  induction m with
  | zero => simp [StrategyOfTracesR0.certAxis, bitsOf, pathAxis, pathAddress]
  | succ m ih =>
      rw [StrategyOfTracesR0.certAxis, bitsOf_succ, pathAxis_concat, ih]

theorem slot_certAxis (m : ℕ) (c : ℕ → Bool) (n : Noun) :
    Noun.slot (StrategyOfTracesR0.certAxis m c) n = nounAt (bitsOf m c) n := by
  rw [certAxis_eq_pathAxis, slot_pathAxis]

theorem Sf_congr_le' (fo fo' : ℕ → ℕ) (n : ℕ) (h : ∀ i, 1 ≤ i → i ≤ n → fo i = fo' i) :
    Sf fo n = Sf fo' n :=
  Finset.sum_congr rfl fun i hi => by
    have := Finset.mem_Icc.mp hi
    exact h i this.1 this.2

section Generic

variable (envsK : Fin M → Env K) (envsF : Fin M → Env F) (hM : 0 < M) (kroots q : ℕ)
/-- The pre-`z` noun at 1-indexed row `i`. -/
local notation "NN" => preZNounOfEnvs K q kroots envsF hM

theorem preFo_eq (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ M) :
    preFoOfEnvs envsF hM i = foOfMem envsF i := by
  unfold preFoOfEnvs foOfMem preLblOfEnvs
  rw [dif_pos (by omega), dif_pos ⟨h1, by omega⟩]
  rfl

theorem preLbl_fst (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ M) :
    (preLblOfEnvs envsF hM i).1 = memRowStateOf (envsF ⟨i - 1, by omega⟩) := by
  unfold preLblOfEnvs
  rw [dif_pos (by omega)]
  rfl

variable (hSf : kroots + Sf (foOfMem envsF) M = M) (hvalid : BFSValidF kroots (foOfMem envsF) M)
include hSf hvalid

theorem Sf_pre (n : ℕ) (hn : n ≤ M) :
    Sf (preFoOfEnvs envsF hM) n = Sf (foOfMem envsF) n :=
  Sf_congr_le' _ _ n fun i h1 h2 => preFo_eq envsF hM i h1 (by omega)

theorem buildTF_node (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ M) :
    buildTF kroots (preFoOfEnvs envsF hM) (preLblOfEnvs envsF hM) M i =
      NTree.node (preLblOfEnvs envsF hM i)
        ((List.range' (childIdx envsF kroots i 1)
          (MemoryTable.fanoutMem (memRowStateOf (envsF ⟨i - 1, by omega⟩)))).map
          (buildTF kroots (preFoOfEnvs envsF hM) (preLblOfEnvs envsF hM) M)) := by
  have hSf' : kroots + Sf (preFoOfEnvs envsF hM) M = M := by rw [Sf_pre envsF hM kroots hSf hvalid M le_rfl]; exact hSf
  have hv' : BFSValidF kroots (preFoOfEnvs envsF hM) M := by
    intro j hj1 hj2
    rw [Sf_pre envsF hM kroots hSf hvalid (j - 1) (by omega)]
    exact hvalid j hj1 hj2
  have hch := childIdxsF_eq kroots (preFoOfEnvs envsF hM) M hSf' hv' h1 h2
  have hfc : firstCF kroots (preFoOfEnvs envsF hM) i = childIdx envsF kroots i 1 := by
    unfold firstCF childIdx
    rw [Sf_pre envsF hM kroots hSf hvalid (i - 1) (by omega)]
    omega
  have hfo : preFoOfEnvs envsF hM i = MemoryTable.fanoutMem (memRowStateOf (envsF ⟨i - 1, by omega⟩)) := by
    rw [preFo_eq envsF hM i h1 h2]; unfold foOfMem; rw [dif_pos ⟨h1, by omega⟩]
  rw [← hfc, ← hfo, ← hch, ← buildTF_children]
  conv_lhs => rw [show buildTF kroots (preFoOfEnvs envsF hM) (preLblOfEnvs envsF hM) M i =
    NTree.node (buildTF kroots (preFoOfEnvs envsF hM) (preLblOfEnvs envsF hM) M i).label
      (buildTF kroots (preFoOfEnvs envsF hM) (preLblOfEnvs envsF hM) M i).children by
        cases buildTF kroots (preFoOfEnvs envsF hM) (preLblOfEnvs envsF hM) M i; rfl]
  rw [buildTF_label]

theorem child_lt (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ M) (l : ℕ) (hl : 1 ≤ l) :
    i < childIdx envsF kroots i l := by
  have := hvalid i h1 h2
  unfold childIdx; omega

/-- **Link (iv), generic core.** Every decoded `verify` / `read` path at exponent `e` from row
`i` is a `nounAt` path of the pre-`z` noun of row `i`, landing at the pre-`z` noun of a row of
that state and exponent. -/
theorem paths_nounAt (e : ℕ) :
    ∀ i, 1 ≤ i → i ≤ M →
      (∀ p ∈ vpaths e (decodedMTreeOfEnvs envsK envsF kroots i),
        ∃ j, RowAt envsF .verify_child e j ∧ nounAt p (NN i) = some (NN j)) ∧
      (∀ p ∈ rpaths e (decodedMTreeOfEnvs envsK envsF kroots i),
        ∃ j, RowAt envsF .read_root e j ∧ nounAt p (NN i) = some (NN j)) := by
  intro i
  induction hm : M + 1 - i using Nat.strong_induction_on generalizing i with
  | _ d ih =>
  intro h1 h2
  -- the child subtree: either in range (IH) or `halt`
  have hkid : ∀ l, 1 ≤ l →
      (∀ p ∈ vpaths e (decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i l)),
        ∃ j, RowAt envsF .verify_child e j ∧
          nounAt p (NN (childIdx envsF kroots i l)) = some (NN j)) ∧
      (∀ p ∈ rpaths e (decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i l)),
        ∃ j, RowAt envsF .read_root e j ∧
          nounAt p (NN (childIdx envsF kroots i l)) = some (NN j)) := by
    intro l hl
    have hlt := child_lt envsF kroots hSf hvalid i h1 h2 l hl
    by_cases hc : childIdx envsF kroots i l ≤ M
    · exact ih (M + 1 - childIdx envsF kroots i l) (by omega) _ rfl (by omega) hc
    · have : decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i l) = .halt := by
        rw [decodedMTreeOfEnvs, dif_neg (by omega)]
      rw [this]
      exact ⟨fun p hp => by simp [vpaths] at hp, fun p hp => by simp [rpaths] at hp⟩
  have hNi := buildTF_node envsF hM kroots hSf hvalid i h1 h2
  have hl1 := preLbl_fst envsF hM i h1 h2
  have hc1 := child_lt envsF kroots hSf hvalid i h1 h2 1 le_rfl
  have hc2 := child_lt envsF kroots hSf hvalid i h1 h2 2 (by omega)
  have hc12 : childIdx envsF kroots i 2 = childIdx envsF kroots i 1 + 1 := by
    unfold childIdx; omega
  have hNdef : NN i = decodePre K q
      (buildTF kroots (preFoOfEnvs envsF hM) (preLblOfEnvs envsF hM) M i) := rfl
  have hNc : ∀ j, NN j = decodePre K q
      (buildTF kroots (preFoOfEnvs envsF hM) (preLblOfEnvs envsF hM) M j) := fun _ => rfl
  rcases hpl : preLblOfEnvs envsF hM i with ⟨s, a⟩
  rw [hpl] at hl1
  simp only at hl1
  rcases hs : memRowStateOf (envsF ⟨i - 1, by omega⟩) with _ | _ | _ | _
  · -- decompose
    rw [hs] at hl1
    subst hl1
    rw [tree_decompose_of envsK envsF kroots i ⟨h1, h2⟩ hs, if_pos hc1, if_pos hc2]
    have hN : NN i = Noun.cell (NN (childIdx envsF kroots i 1))
        (NN (childIdx envsF kroots i 2)) := by
      rw [hNdef, hNi, hpl, hs, hc12, hNc, hNc]
      simp [MemoryTable.fanoutMem, List.range'_succ, decodePre]
    obtain ⟨hv1, hr1⟩ := hkid 1 le_rfl
    obtain ⟨hv2, hr2⟩ := hkid 2 (by omega)
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [vpaths, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩
      · obtain ⟨j, hj, hn⟩ := hv1 p' hp'
        exact ⟨j, hj, by rw [hN]; simpa [nounAt, nounChild] using hn⟩
      · obtain ⟨j, hj, hn⟩ := hv2 p' hp'
        exact ⟨j, hj, by rw [hN]; simpa [nounAt, nounChild] using hn⟩
    · intro p hp
      simp only [rpaths, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩
      · obtain ⟨j, hj, hn⟩ := hr1 p' hp'
        exact ⟨j, hj, by rw [hN]; simpa [nounAt, nounChild] using hn⟩
      · obtain ⟨j, hj, hn⟩ := hr2 p' hp'
        exact ⟨j, hj, by rw [hN]; simpa [nounAt, nounChild] using hn⟩
  · -- halt
    rw [tree_halt_of envsK envsF kroots i ⟨h1, h2⟩ hs]
    exact ⟨fun p hp => by simp [vpaths] at hp, fun p hp => by simp [rpaths] at hp⟩
  · -- read_root
    rw [hs] at hl1
    subst hl1
    rw [tree_read_of envsK envsF kroots i ⟨h1, h2⟩ hs, if_pos hc1]
    have hN : NN i = NN (childIdx envsF kroots i 1) := by
      rw [hNdef, hNi, hpl, hs, hNc]
      simp [MemoryTable.fanoutMem, decodePre]
    obtain ⟨hv1, hr1⟩ := hkid 1 le_rfl
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [vpaths] at hp
      obtain ⟨j, hj, hn⟩ := hv1 p hp
      exact ⟨j, hj, by rw [hN]; exact hn⟩
    · intro p hp
      simp only [rpaths, List.mem_append] at hp
      rcases hp with hp | hp
      · split_ifs at hp with he
        · simp only [List.mem_singleton] at hp
          subst hp
          exact ⟨i, ⟨by omega, h1, hs, he⟩, rfl⟩
        · simp at hp
      · obtain ⟨j, hj, hn⟩ := hr1 p hp
        exact ⟨j, hj, by rw [hN]; exact hn⟩
  · -- verify_child
    rw [hs] at hl1
    subst hl1
    rw [tree_verify_of envsK envsF kroots i ⟨h1, h2⟩ hs, if_pos hc1]
    have hN : NN i = NN (childIdx envsF kroots i 1) := by
      rw [hNdef, hNi, hpl, hs, hNc]
      simp [MemoryTable.fanoutMem, decodePre]
    obtain ⟨hv1, hr1⟩ := hkid 1 le_rfl
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [vpaths, List.mem_append] at hp
      rcases hp with hp | hp
      · split_ifs at hp with he
        · simp only [List.mem_singleton] at hp
          subst hp
          exact ⟨i, ⟨by omega, h1, hs, he⟩, rfl⟩
        · simp at hp
      · obtain ⟨j, hj, hn⟩ := hv1 p hp
        exact ⟨j, hj, by rw [hN]; exact hn⟩
    · intro p hp
      simp only [rpaths] at hp
      obtain ⟨j, hj, hn⟩ := hr1 p hp
      exact ⟨j, hj, by rw [hN]; exact hn⟩

/-- **Link (iv).** At a root `r` whose decoded tree pairs exponent `e` with the R4 path equation
`V = R ++ bitsOf m c`, the pre-`z` noun of the (unique) `verify_child` row at `e` is the Nock
`slot` of the pre-`z` noun of the (unique) `read_root` row at `e`, at axis `certAxis m c`. -/
theorem slot_of_paths (e m : ℕ) (cb : ℕ → Bool) (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ M)
    (hR : ExpInjOn envsF .read_root) (hV : ExpInjOn envsF .verify_child)
    {qq : List Bool}
    (hrp : rpaths e (decodedMTreeOfEnvs envsK envsF kroots r) = [qq])
    (hvp : vpaths e (decodedMTreeOfEnvs envsK envsF kroots r) = [qq ++ bitsOf m cb])
    {k k' : ℕ} (hk : RowAt envsF .read_root e k) (hk' : RowAt envsF .verify_child e k') :
    Noun.slot (StrategyOfTracesR0.certAxis m cb) (NN k) = some (NN k') := by
  obtain ⟨HV, HR⟩ := paths_nounAt envsK envsF hM kroots q hSf hvalid e r hr1 hr2
  obtain ⟨j, hj, hnj⟩ := HR qq (by rw [hrp]; exact List.mem_singleton_self _)
  obtain ⟨j', hj', hnj'⟩ := HV (qq ++ bitsOf m cb) (by rw [hvp]; exact List.mem_singleton_self _)
  have e1 := rowAt_unique envsF hR hj hk
  have e2 := rowAt_unique envsF hV hj' hk'
  subst e1 e2
  rw [nounAt_append, hnj] at hnj'
  rw [slot_certAxis]
  simpa using hnj'

end Generic

end PathSlot

section Positions

def zipT {α β : Type} : NTree α → NTree β → NTree (α × β)
  | .node a as, .node b bs => .node (a, b) (zipL as bs)
where
  zipL : List (NTree α) → List (NTree β) → List (NTree (α × β))
    | x :: xs, y :: ys => zipT x y :: zipL xs ys
    | _, _ => []

/-- Same shape. -/
def Sh {α β : Type} (x : NTree α) (y : NTree β) : Prop :=
  mapNTree (fun _ => ()) x = mapNTree (fun _ => ()) y

theorem zip_proj {α β : Type} :
    ∀ (n : ℕ) (x : NTree α) (y : NTree β), x.size ≤ n → Sh x y →
      mapNTree Prod.fst (zipT x y) = x ∧ mapNTree Prod.snd (zipT x y) = y := by
  intro n
  induction n with
  | zero => intro x y hx _; cases x; simp [NTree.size] at hx
  | succ n ih =>
    intro x y hx hsh
    obtain ⟨a, as⟩ := x
    obtain ⟨b, bs⟩ := y
    unfold Sh at hsh
    simp only [mapNTree, NTree.node.injEq, true_and] at hsh
    have key : ∀ (as : List (NTree α)) (bs : List (NTree β)),
        (∀ c ∈ as, c.size ≤ n) →
        as.map (mapNTree fun _ => ()) = bs.map (mapNTree fun _ => ()) →
        (zipT.zipL as bs).map (mapNTree Prod.fst) = as ∧
          (zipT.zipL as bs).map (mapNTree Prod.snd) = bs := by
      intro as
      induction as with
      | nil =>
          intro bs _ h
          cases bs with
          | nil => simp [zipT.zipL]
          | cons _ _ => simp at h
      | cons x xs ihx =>
          intro bs hs h
          cases bs with
          | nil => simp at h
          | cons y ys =>
              simp only [List.map_cons, List.cons.injEq] at h
              obtain ⟨h1, h2⟩ := ih x y (hs x (by simp)) h.1
              obtain ⟨h3, h4⟩ := ihx ys (fun c hc => hs c (by simp [hc])) h.2
              simp [zipT.zipL, h1, h2, h3, h4]
    have hs : ∀ c ∈ as, c.size ≤ n := by
      intro c hc
      have := Nock.RedTeam.Batch1021.child_size_le_of_node (row := a) (ch := as) (k := n)
        (by simpa using hx) hc
      exact this
    obtain ⟨h1, h2⟩ := key as bs hs hsh
    simp [zipT, mapNTree, h1, h2]

theorem pr_zip {α β : Type} {t : NTree α} {T : NTree β} (hsh : Sh t T)
    {u : NTree α} {w : NTree β} (h : PR t T u w) :
    ∃ z', InTree (zipT t T) z' ∧ mapNTree Prod.fst z' = u ∧ mapNTree Prod.snd z' = w := by
  induction h with
  | root =>
      obtain ⟨h1, h2⟩ := zip_proj t.size t T le_rfl hsh
      exact ⟨_, InTree.here _, h1, h2⟩
  | @child u0 w0 uc wc i _ hu hw ih =>
      obtain ⟨z', hz, h1, h2⟩ := ih
      have e1 : z'.children.map (mapNTree Prod.fst) = u0.children := by
        rw [← mapNTree_children, h1]
      have e2 : z'.children.map (mapNTree Prod.snd) = w0.children := by
        rw [← mapNTree_children, h2]
      have hu' := hu
      rw [← e1, List.getElem?_map] at hu'
      obtain ⟨zc, hzc, rfl⟩ := Option.map_eq_some_iff.1 hu'
      have hw' := hw
      rw [← e2, List.getElem?_map, hzc] at hw'
      simp only [Option.map_some, Option.some.injEq] at hw'
      exact ⟨zc, InTree_trans hz (InTree.sub (List.mem_of_getElem? hzc) (InTree.here _)), rfl, hw'⟩

theorem pr_pos {α β : Type} {t : NTree α} {T : NTree β} (hsh : Sh t T)
    {u : NTree α} {w : NTree β} (h : PR t T u w) :
    ∃ a : ℕ, (bfsForest [t])[a]? = some u ∧ (bfsForest [T])[a]? = some w := by
  obtain ⟨z', hz, h1, h2⟩ := pr_zip hsh h
  obtain ⟨p1, p2⟩ := zip_proj t.size t T le_rfl hsh
  have hmem : z' ∈ bfsForest [zipT t T] := (mem_bfsForest _ _).2 ⟨_, List.mem_singleton_self _, hz⟩
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 hmem
  refine ⟨a, ?_, ?_⟩
  · rw [← p1, TraceGen.bfsForest_mapNTree_singleton, List.getElem?_map, ha]; simp [h1]
  · rw [← p2, TraceGen.bfsForest_mapNTree_singleton, List.getElem?_map, ha]; simp [h2]

variable {K : Type} [Field K] {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}
set_option quotPrecheck false in
local notation "J" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

theorem J_children_f2 (n : ℕ) (row : (State × DTcomp K) × ℕ)
    (ch : List (NTree ((State × DTcomp K) × ℕ))) (s f : Noun) :
    List.Forall₂ (fun c k => ∃ s' f', k = J n c s' f') ch (J (n + 1) (.node row ch) s f).children := by
  simp only [c2JoinFuel, c2JoinKids, NTree.children]
  split <;> simp_all [List.forall₂_cons]

theorem J_state_shape :
    ∀ (n : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (s f : Noun), t.size ≤ n →
      mapNTree ComputeRowSkeleton.state (J n t s f) = mapNTree (fun l => l.1.1) t := by
  intro n
  induction n with
  | zero => intro t s f ht; cases t; simp [NTree.size] at ht
  | succ n ih =>
    intro t s f ht
    obtain ⟨row, ch⟩ := t
    have hch : ∀ c ∈ ch, c.size ≤ n := fun c hc =>
      Nock.RedTeam.Batch1021.child_size_le_of_node (row := row) (k := n) (by simpa using ht) hc
    have hF := J_children_f2 (sv := sv) (ax := ax) n row ch s f
    have heta : J (n + 1) (.node row ch) s f =
        .node (J (n + 1) (.node row ch) s f).label (J (n + 1) (.node row ch) s f).children := by
      cases J (n + 1) (.node row ch) s f; rfl
    rw [heta, mapNTree, mapNTree, c2JoinFuel_state]
    congr 1
    clear heta ht
    generalize (J (n + 1) (.node row ch) s f).children = ks at hF ⊢
    induction hF with
    | nil => rfl
    | @cons c k cs ks hck _ ihl =>
        obtain ⟨s', f', rfl⟩ := hck
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨ih c s' f' (hch c (by simp)), ihl (fun c' hc' => hch c' (List.mem_cons_of_mem _ hc'))⟩

theorem J_shape (t : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) :
    Sh t (J t.size t s f) := by
  unfold Sh
  have h := J_state_shape (sv := sv) (ax := ax) t.size t s f le_rfl
  have h1 := congrArg (mapNTree fun _ => ()) h
  rw [ReconTreeSize.mapNTree_comp, ReconTreeSize.mapNTree_comp] at h1
  exact h1.symm

end Positions

end Nock.RedTeam.Batch1170
