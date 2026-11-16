import Nock.NockVMROM.Thm54.RawTopologySoundness
import Nock.NockVMROM.Thm54.RawJointSoundness

/-!
# Randomized raw topology binding

The existing walk AIR checks the BFS scalar recurrence, but not the local edge payloads.  This
file gives the missing randomized check without placing `Fcomp`, `Fmem`, `RVT`, or
`RawTopologyBindingResidual` in verifier acceptance.

For every canonical BFS parent row the check contains:

* one deterministic field equality between a bounded encoding of the actual child count and the
  state-defined expected fanout; and
* one `gamma`-RLC field equality for each expected active child.  Compute RLCs contain exactly the
  nine `(s,f,e)` fingerprint coordinates; memory RLCs contain exactly the five `pt` coordinates.

The bounded fanout encoding sends an out-of-range compute count to `4` and an out-of-range memory
count to `3`.  `NodeEncoding.StateTagChar` therefore turns the field equality back into an exact
natural-number equality without any global no-wraparound assumption.

For the old raw strategy, the problem and topology payload arrays are committed after the NPR seed
and before `(alphaC,gamma,alphaM)`.  For the template strategy the exact problem depends on
`alphaM`, so its topology payload arrays are committed at `(z,alphaM)`, before the later shared
`gamma`.  In both chronologies the authoritative forest and raw child payload arrays are fixed
before `gamma`, so the existing shared challenge is sound.

`TopologyCompressedCheck` below is the field-level mathematical target of the mechanical layer.
It is not an arbitrary-trace acceptance API.  `RawTopologyAIR` implements the production
architecture: the prover supplies only phase-committed child payload arrays; the verifier
deterministically constructs fanout, active, expected-parent, and forest-first authoritative child
lookup columns, inserts those payloads, and evaluates segmented RAPs on that generated trace.
-/

namespace Nock.NockVMROM.Thm54

open Classical
open Nock Nock.Walk

set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [CharP K p]

/-! ## Canonical local payload encoders -/

/-- The exact compute edge payload: three fingerprints, hence nine field coordinates. -/
structure ComputeLinkPayload (K : Type*) where
  s : ComputeTable.FP K
  f : ComputeTable.FP K
  e : ComputeTable.FP K

namespace ComputeLinkPayload

def zero : ComputeLinkPayload K where
  s := 0
  f := 0
  e := 0

def ofTriple (x : ComputeTable.FP K × ComputeTable.FP K × ComputeTable.FP K) :
    ComputeLinkPayload K :=
  match x with
  | (s, f, e) => ⟨s, f, e⟩

/-- Canonical unpacked `(s,f,e)` coordinates, in fingerprint `(size,dyck,leaf)` order. -/
def encode (x : ComputeLinkPayload K) : Fin 9 → K
  | ⟨0, _⟩ => x.s.size
  | ⟨1, _⟩ => x.s.dyck
  | ⟨2, _⟩ => x.s.leaf
  | ⟨3, _⟩ => x.f.size
  | ⟨4, _⟩ => x.f.dyck
  | ⟨5, _⟩ => x.f.leaf
  | ⟨6, _⟩ => x.e.size
  | ⟨7, _⟩ => x.e.dyck
  | ⟨8, _⟩ => x.e.leaf

theorem encode_injective : Function.Injective (encode (K := K)) := by
  rintro ⟨as, af, ae⟩ ⟨bs, bf, be⟩ h
  have hs : as = bs := ComputeTable.FP.ext
    (congrFun h (0 : Fin 9))
    (congrFun h (1 : Fin 9))
    (congrFun h (2 : Fin 9))
  have hf : af = bf := ComputeTable.FP.ext
    (congrFun h (3 : Fin 9))
    (congrFun h (4 : Fin 9))
    (congrFun h (5 : Fin 9))
  have he : ae = be := ComputeTable.FP.ext
    (congrFun h (6 : Fin 9))
    (congrFun h (7 : Fin 9))
    (congrFun h (8 : Fin 9))
  subst bs
  subst bf
  subst be
  rfl

end ComputeLinkPayload

namespace MemoryLinkPayload

/-- Canonical unpacked `pt` coordinates, in `(size,dyck,leaf,indicator,counts)` order. -/
def encode (x : MemoryTable.Cell K) : Fin 5 → K
  | ⟨0, _⟩ => x.noun.size
  | ⟨1, _⟩ => x.noun.dyck
  | ⟨2, _⟩ => x.noun.leaf
  | ⟨3, _⟩ => x.indicator
  | ⟨4, _⟩ => x.counts

theorem encode_injective : Function.Injective (encode (K := K)) := by
  rintro ⟨an, ai, ac⟩ ⟨bn, bi, bc⟩ h
  have hn : an = bn := ComputeTable.FP.ext
    (congrFun h (0 : Fin 5))
    (congrFun h (1 : Fin 5))
    (congrFun h (2 : Fin 5))
  have hi : ai = bi := congrFun h (3 : Fin 5)
  have hc : ac = bc := congrFun h (4 : Fin 5)
  subst bn
  subst bi
  subst bc
  rfl

end MemoryLinkPayload

/-! ## Actual and expected row-local data -/

def computeActualPayload
    (t : NTree (ComputeTable.State × ComputeTable.DTcomp K)) (i : Fin 3) :
    ComputeLinkPayload K :=
  match t.childLabel i with
  | some c => ⟨c.2.2.1.s, c.2.2.1.f, c.2.2.1.e⟩
  | none => .zero

def computeExpectedPayload
    (t : NTree (ComputeTable.State × ComputeTable.DTcomp K)) (i : Fin 3) :
    ComputeLinkPayload K :=
  .ofTriple (ComputeTable.sfTriple t.label.2.2.1 i)

def memoryActualPayload
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) (i : Fin 2) :
    MemoryTable.Cell K :=
  match t.childLabel i with
  | some c => c.2.2.pt
  | none => MemoryTable.Cell.zero

def memoryExpectedPayload
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) (i : Fin 2) :
    MemoryTable.Cell K :=
  MemoryTable.memCell t.label i

/-- Exact bounded field encoding of an actual compute child count.  Counts above arity use tag 4. -/
def computeActualFanoutTag
    (t : NTree (ComputeTable.State × ComputeTable.DTcomp K)) : K :=
  if t.children.length ≤ 3 then (t.children.length : K) else (4 : K)

def computeExpectedFanoutTag
    (t : NTree (ComputeTable.State × ComputeTable.DTcomp K)) : K :=
  (ComputeTable.fanoutComp t.label.1 : K)

/-- Exact bounded field encoding of an actual memory child count.  Counts above arity use tag 3. -/
def memoryActualFanoutTag
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) : K :=
  if t.children.length ≤ 2 then (t.children.length : K) else (3 : K)

def memoryExpectedFanoutTag
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) : K :=
  (MemoryTable.fanoutMem t.label.1 : K)

theorem computeFanout_eq_of_tag_eq
    (hchar : NodeEncoding.StateTagChar K)
    (t : NTree (ComputeTable.State × ComputeTable.DTcomp K))
    (h : computeActualFanoutTag t = computeExpectedFanoutTag t) :
    ComputeTable.fanoutComp t.label.1 = t.children.length := by
  unfold NodeEncoding.StateTagChar at hchar
  unfold computeActualFanoutTag computeExpectedFanoutTag at h
  split at h
  · rename_i hle
    have hfan : ComputeTable.fanoutComp t.label.1 ≤ 3 :=
      (ComputeTable.comp_stateSep (K := K)).fanout_le t.label.1
    have hlen11 : t.children.length ∈ Set.Iic 11 :=
      hle.trans (by norm_num)
    have hfan11 : ComputeTable.fanoutComp t.label.1 ∈ Set.Iic 11 :=
      hfan.trans (by norm_num)
    have heq : t.children.length = ComputeTable.fanoutComp t.label.1 :=
      @hchar t.children.length hlen11 (ComputeTable.fanoutComp t.label.1) hfan11 h
    exact heq.symm
  · rename_i hle
    have hfan : ComputeTable.fanoutComp t.label.1 ≤ 3 :=
      (ComputeTable.comp_stateSep (K := K)).fanout_le t.label.1
    have hfour11 : (4 : ℕ) ∈ Set.Iic 11 := by norm_num
    have hfan11 : ComputeTable.fanoutComp t.label.1 ∈ Set.Iic 11 :=
      hfan.trans (by norm_num)
    have heq : 4 = ComputeTable.fanoutComp t.label.1 :=
      @hchar 4 hfour11 (ComputeTable.fanoutComp t.label.1) hfan11 h
    omega

theorem memoryFanout_eq_of_tag_eq
    (hchar : NodeEncoding.StateTagChar K)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (h : memoryActualFanoutTag t = memoryExpectedFanoutTag t) :
    MemoryTable.fanoutMem t.label.1 = t.children.length := by
  unfold NodeEncoding.StateTagChar at hchar
  unfold memoryActualFanoutTag memoryExpectedFanoutTag at h
  split at h
  · rename_i hle
    have hfan : MemoryTable.fanoutMem t.label.1 ≤ 2 :=
      (MemoryTable.mem_stateSep (K := K)).fanout_le t.label.1
    have hlen11 : t.children.length ∈ Set.Iic 11 :=
      hle.trans (by norm_num)
    have hfan11 : MemoryTable.fanoutMem t.label.1 ∈ Set.Iic 11 :=
      hfan.trans (by norm_num)
    have heq : t.children.length = MemoryTable.fanoutMem t.label.1 :=
      @hchar t.children.length hlen11 (MemoryTable.fanoutMem t.label.1) hfan11 h
    exact heq.symm
  · rename_i hle
    have hfan : MemoryTable.fanoutMem t.label.1 ≤ 2 :=
      (MemoryTable.mem_stateSep (K := K)).fanout_le t.label.1
    have hthree11 : (3 : ℕ) ∈ Set.Iic 11 := by norm_num
    have hfan11 : MemoryTable.fanoutMem t.label.1 ∈ Set.Iic 11 :=
      hfan.trans (by norm_num)
    have heq : 3 = MemoryTable.fanoutMem t.label.1 :=
      @hchar 3 hthree11 (MemoryTable.fanoutMem t.label.1) hfan11 h
    omega

/-! ## Data-only compressed verifier predicate -/

/-- Only row-local field equalities.  No topology, RVT, evaluator, or target predicate occurs. -/
def TopologyCompressedCheck
    (R : RawPlusIOSegmentedFamily F K) (γ : K) : Prop :=
  (∀ t ∈ R.computeWalkRows,
      computeActualFanoutTag t = computeExpectedFanoutTag t ∧
        ∀ i : Fin 3, (i : ℕ) < ComputeTable.fanoutComp t.label.1 →
          rlc γ (ComputeLinkPayload.encode (computeActualPayload t i)) =
            rlc γ (ComputeLinkPayload.encode (computeExpectedPayload t i))) ∧
    (∀ t ∈ R.memoryWalkRows,
      memoryActualFanoutTag t = memoryExpectedFanoutTag t ∧
        ∀ i : Fin 2, (i : ℕ) < MemoryTable.fanoutMem t.label.1 →
          rlc γ (MemoryLinkPayload.encode (memoryActualPayload t i)) =
            rlc γ (MemoryLinkPayload.encode (memoryExpectedPayload t i)))

/-! ## Exact collision events and workload -/

noncomputable def computeSlotBadGammas
    [Fintype K] [DecidableEq K]
    (t : NTree (ComputeTable.State × ComputeTable.DTcomp K)) (i : Fin 3) : Finset K :=
  if _hi : (i : ℕ) < ComputeTable.fanoutComp t.label.1 then
    if _hne :
        ComputeLinkPayload.encode (computeActualPayload t i) ≠
          ComputeLinkPayload.encode (computeExpectedPayload t i) then
      Finset.univ.filter fun γ =>
        rlc γ (ComputeLinkPayload.encode (computeActualPayload t i)) =
          rlc γ (ComputeLinkPayload.encode (computeExpectedPayload t i))
    else ∅
  else ∅

noncomputable def memorySlotBadGammas
    [Fintype K] [DecidableEq K]
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) (i : Fin 2) : Finset K :=
  if _hi : (i : ℕ) < MemoryTable.fanoutMem t.label.1 then
    if _hne :
        MemoryLinkPayload.encode (memoryActualPayload t i) ≠
          MemoryLinkPayload.encode (memoryExpectedPayload t i) then
      Finset.univ.filter fun γ =>
        rlc γ (MemoryLinkPayload.encode (memoryActualPayload t i)) =
          rlc γ (MemoryLinkPayload.encode (memoryExpectedPayload t i))
    else ∅
  else ∅

noncomputable def computeTopologyBadGammas
    (R : RawPlusIOSegmentedFamily F K) [Fintype K] [DecidableEq K] : Finset K :=
  ((Finset.range R.computeWalkRows.length) ×ˢ (Finset.univ : Finset (Fin 3))).biUnion
    fun x => computeSlotBadGammas
      (R.computeWalkRows.getD x.1 R.exec.computeTree) x.2

noncomputable def memoryTopologyBadGammas
    (R : RawPlusIOSegmentedFamily F K) [Fintype K] [DecidableEq K] : Finset K :=
  let fallback := R.exec.memoryForest.get
    ⟨0, List.length_pos_of_ne_nil R.exec.memoryForest_nonempty⟩
  ((Finset.range R.memoryWalkRows.length) ×ˢ (Finset.univ : Finset (Fin 2))).biUnion
    fun x => memorySlotBadGammas
      (R.memoryWalkRows.getD x.1 fallback) x.2

noncomputable def topologyBadGammas
    (R : RawPlusIOSegmentedFamily F K) [Fintype K] [DecidableEq K] : Finset K :=
  computeTopologyBadGammas R ∪ memoryTopologyBadGammas R

/-- `9` compute coordinates give degree at most `8`; `5` memory coordinates give degree at most
`4`.  There are at most three/two slots per active parent row. -/
def topologyWorkload (R : RawPlusIOSegmentedFamily F K) : ℕ :=
  R.cfg.compRows * 3 * 8 + R.cfg.memRows * 2 * 4

section Finite

variable [Fintype K] [DecidableEq K]

theorem computeSlotBadGammas_card_le
    (t : NTree (ComputeTable.State × ComputeTable.DTcomp K)) (i : Fin 3) :
    (computeSlotBadGammas t i).card ≤ 8 := by
  unfold computeSlotBadGammas
  split
  · split
    · rename_i hi hne
      simpa using rlc_collision_card_le hne
    · simp
  · simp

theorem memorySlotBadGammas_card_le
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) (i : Fin 2) :
    (memorySlotBadGammas t i).card ≤ 4 := by
  unfold memorySlotBadGammas
  split
  · split
    · rename_i hi hne
      simpa using rlc_collision_card_le hne
    · simp
  · simp

theorem computeTopologyBadGammas_card_le
    (R : RawPlusIOSegmentedFamily F K) :
    (computeTopologyBadGammas R).card ≤ R.cfg.compRows * 3 * 8 := by
  calc
    (computeTopologyBadGammas R).card ≤
        ∑ _x ∈
          ((Finset.range R.computeWalkRows.length) ×ˢ
            (Finset.univ : Finset (Fin 3))), 8 := by
      unfold computeTopologyBadGammas
      exact le_trans Finset.card_biUnion_le
        (Finset.sum_le_sum fun x _ => computeSlotBadGammas_card_le
          (R.computeWalkRows.getD x.1 R.exec.computeTree) x.2)
    _ = R.cfg.compRows * 3 * 8 := by
      simp [RawPlusIOSegmentedFamily.computeWalkRows, R.exec.compute_bfs_length]

theorem memoryTopologyBadGammas_card_le
    (R : RawPlusIOSegmentedFamily F K) :
    (memoryTopologyBadGammas R).card ≤ R.cfg.memRows * 2 * 4 := by
  let fallback := R.exec.memoryForest.get
    ⟨0, List.length_pos_of_ne_nil R.exec.memoryForest_nonempty⟩
  calc
    (memoryTopologyBadGammas R).card ≤
        ∑ _x ∈
          ((Finset.range R.memoryWalkRows.length) ×ˢ
            (Finset.univ : Finset (Fin 2))), 4 := by
      unfold memoryTopologyBadGammas
      dsimp only
      exact le_trans Finset.card_biUnion_le
        (Finset.sum_le_sum fun x _ => memorySlotBadGammas_card_le
          (R.memoryWalkRows.getD x.1 fallback) x.2)
    _ = R.cfg.memRows * 2 * 4 := by
      simp [RawPlusIOSegmentedFamily.memoryWalkRows, R.exec.memory_bfs_length]

theorem topologyBadGammas_card_le
    (R : RawPlusIOSegmentedFamily F K) :
    (topologyBadGammas R).card ≤ topologyWorkload R := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (computeTopologyBadGammas_card_le R)
      (memoryTopologyBadGammas_card_le R))

/-! ## Compressed-check soundness -/

private theorem computePayload_eq_of_check_outside_bad
    {R : RawPlusIOSegmentedFamily F K} {γ : K}
    (hcheck : TopologyCompressedCheck R γ)
    (hγ : γ ∉ topologyBadGammas R)
    {t : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (ht : t ∈ R.computeWalkRows) (i : Fin 3)
    (hi : (i : ℕ) < ComputeTable.fanoutComp t.label.1) :
    computeActualPayload t i = computeExpectedPayload t i := by
  apply ComputeLinkPayload.encode_injective
  by_contra hne
  have hidx := List.getElem_of_mem ht
  obtain ⟨k, hk, hkt⟩ := hidx
  have hget : R.computeWalkRows.getD k R.exec.computeTree = t := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact hkt
  have hmemComp : γ ∈ computeTopologyBadGammas R := by
    unfold computeTopologyBadGammas
    apply Finset.mem_biUnion.mpr
    refine ⟨(k, i), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk, Finset.mem_univ i⟩
    · rw [hget]
      simp only [computeSlotBadGammas, dif_pos hi, dif_pos hne,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hcheck.1 t ht).2 i hi
  exact hγ (Finset.mem_union_left _ hmemComp)

private theorem memoryPayload_eq_of_check_outside_bad
    {R : RawPlusIOSegmentedFamily F K} {γ : K}
    (hcheck : TopologyCompressedCheck R γ)
    (hγ : γ ∉ topologyBadGammas R)
    {t : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (ht : t ∈ R.memoryWalkRows) (i : Fin 2)
    (hi : (i : ℕ) < MemoryTable.fanoutMem t.label.1) :
    memoryActualPayload t i = memoryExpectedPayload t i := by
  apply MemoryLinkPayload.encode_injective
  by_contra hne
  obtain ⟨k, hk, hkt⟩ := List.getElem_of_mem ht
  let fallback := R.exec.memoryForest.get
    ⟨0, List.length_pos_of_ne_nil R.exec.memoryForest_nonempty⟩
  have hget : R.memoryWalkRows.getD k fallback = t := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact hkt
  have hmemMem : γ ∈ memoryTopologyBadGammas R := by
    unfold memoryTopologyBadGammas
    dsimp only
    apply Finset.mem_biUnion.mpr
    refine ⟨(k, i), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk, Finset.mem_univ i⟩
    · rw [hget]
      simp only [memorySlotBadGammas, dif_pos hi, dif_pos hne,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hcheck.2 t ht).2 i hi
  exact hγ (Finset.mem_union_right _ hmemMem)

theorem rawTopologyBindingResidual_of_compressedCheck
    (hchar : NodeEncoding.StateTagChar K)
    (R : RawPlusIOSegmentedFamily F K) (γ : K)
    (hcheck : TopologyCompressedCheck R γ)
    (hγ : γ ∉ topologyBadGammas R) :
    RawTopologyBindingResidual R := by
  constructor
  · intro t ht
    refine ⟨computeFanout_eq_of_tag_eq hchar t (hcheck.1 t ht).1, ?_⟩
    intro i hi
    have hlen : (i : ℕ) < t.children.length := by
      rw [← computeFanout_eq_of_tag_eq hchar t (hcheck.1 t ht).1]
      exact hi
    let child := t.children.get ⟨i, hlen⟩
    have hchild : t.childLabel i = some child.label := by
      simp [NTree.childLabel, NTree.childOpt, child, List.getElem?_eq_getElem hlen]
    have hpayload :=
      computePayload_eq_of_check_outside_bad hcheck hγ ht i hi
    change (t.childLabel i).map
      (fun c => (c.2.2.1.s, c.2.2.1.f, c.2.2.1.e)) =
        some (ComputeTable.sfTriple t.label.2.2.1 i)
    rw [hchild]
    simpa [computeActualPayload, computeExpectedPayload, hchild,
      ComputeLinkPayload.ofTriple] using congrArg
      (fun x : ComputeLinkPayload K => (x.s, x.f, x.e)) hpayload
  · intro t ht
    refine ⟨memoryFanout_eq_of_tag_eq hchar t (hcheck.2 t ht).1, ?_⟩
    intro i hi
    have hlen : (i : ℕ) < t.children.length := by
      rw [← memoryFanout_eq_of_tag_eq hchar t (hcheck.2 t ht).1]
      exact hi
    let child := t.children.get ⟨i, hlen⟩
    have hchild : t.childLabel i = some child.label := by
      simp [NTree.childLabel, NTree.childOpt, child, List.getElem?_eq_getElem hlen]
    have hpayload :=
      memoryPayload_eq_of_check_outside_bad hcheck hγ ht i hi
    change (t.childLabel i).map (fun c => c.2.2.pt) =
      some (MemoryTable.memCell t.label i)
    rw [hchild]
    simpa [memoryActualPayload, memoryExpectedPayload, hchild] using hpayload

/-- New topology check plus existing raw acceptance yields exact production topology outside the
explicitly counted gamma event. -/
theorem RawMessage.exactTopology_of_accepts_and_compressedCheck
    {R : RawPlusIOSegmentedFamily F K}
    {claim : P8PublicClaim} {ω : JointCoins K}
    (M : RawMessage R p) (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ i, (R.exec.memoryPubAt i).lambda = R.cfg.challenges.lam)
    (haccept : M.Accepts claim ω)
    (hcheck : TopologyCompressedCheck R (gamma ω))
    (hγ : gamma ω ∉ topologyBadGammas R) :
    ComputeExactTopology R.exec ∧ MemoryExactTopology R.exec :=
  M.exactTopology_of_accepts_and_binding hchar hlam haccept
    (rawTopologyBindingResidual_of_compressedCheck hchar R (gamma ω) hcheck hγ)

/-! ## Lift to the four sampled coins -/

/-- Lift a bad-gamma set while leaving `alphaC`, `alphaM`, and `z` unrestricted. -/
noncomputable def liftGamma (B : Finset K) : Finset (JointCoins K) :=
  liftCompute ((Finset.univ : Finset K) ×ˢ B)

@[simp] theorem mem_liftGamma_iff (B : Finset K) (ω : JointCoins K) :
    ω ∈ liftGamma B ↔ gamma ω ∈ B := by
  simp [liftGamma, computeCoins]

theorem card_liftGamma (B : Finset K) :
    (liftGamma B).card = B.card * Fintype.card K ^ 3 := by
  rw [liftGamma, card_liftCompute]
  simp only [Finset.card_product, Finset.card_univ]
  ring

noncomputable def topologyFailureEvent
    (R : RawPlusIOSegmentedFamily F K) : Finset (JointCoins K) :=
  liftGamma (topologyBadGammas R)

@[simp] theorem mem_topologyFailureEvent_iff
    (R : RawPlusIOSegmentedFamily F K) (ω : JointCoins K) :
    ω ∈ topologyFailureEvent R ↔ gamma ω ∈ topologyBadGammas R := by
  simp [topologyFailureEvent]

theorem topologyFailureEvent_card_le
    (R : RawPlusIOSegmentedFamily F K) :
    (topologyFailureEvent R).card ≤
      topologyWorkload R * Fintype.card K ^ 3 := by
  rw [topologyFailureEvent, card_liftGamma]
  exact Nat.mul_le_mul_right _ (topologyBadGammas_card_le R)

/-! ## Seed-fibered strategy event

`topologyFailureEvent R` is the correct lift for one fixed seed commitment.  An arbitrary raw
strategy may choose a different committed execution at each NPR seed, so its global event must
fiber over `z`; using one fixed `R` for all seeds would be unsound. -/

/-- One fixed-seed/fixed-bad-gamma fiber.  Only `alphaC` and `alphaM` remain unrestricted. -/
noncomputable def fixedSeedGammaEvent (z : K) (B : Finset K) :
    Finset (JointCoins K) :=
  ((Finset.univ : Finset K) ×ˢ B) ×ˢ
    ((Finset.univ : Finset K) ×ˢ ({z} : Finset K))

@[simp] theorem mem_fixedSeedGammaEvent_iff
    (z : K) (B : Finset K) (ω : JointCoins K) :
    ω ∈ fixedSeedGammaEvent z B ↔ gamma ω ∈ B ∧ nprSeed ω = z := by
  rcases ω with ⟨⟨αc, γ⟩, ⟨αm, z'⟩⟩
  simp [fixedSeedGammaEvent, gamma, nprSeed, eq_comm]

theorem card_fixedSeedGammaEvent (z : K) (B : Finset K) :
    (fixedSeedGammaEvent z B).card = B.card * Fintype.card K ^ 2 := by
  simp only [fixedSeedGammaEvent, Finset.card_product, Finset.card_univ,
    Finset.card_singleton]
  ring

/-- The honest strategy-level topology event: choose the seed commitment first, then expose only
the bad values of the subsequently sampled shared `gamma`; both alpha coordinates are free. -/
noncomputable def rawStrategyTopologyFailureEvent
    (T : RawP8Strategy F K p) : Finset (JointCoins K) :=
  (Finset.univ : Finset K).biUnion fun z =>
    if hz : z ≠ 0 then
      fixedSeedGammaEvent z
        (topologyBadGammas (T.afterSeed z hz).base)
    else ∅

/-- Sum of the exact per-seed degree workloads.  The zero-seed term is zero because raw
acceptance rejects that fiber. -/
noncomputable def rawStrategyTopologyWorkload
    (T : RawP8Strategy F K p) : ℕ :=
  ∑ z : K, if hz : z ≠ 0 then topologyWorkload (T.afterSeed z hz).base else 0

@[simp] theorem mem_rawStrategyTopologyFailureEvent_iff
    (T : RawP8Strategy F K p) (ω : JointCoins K) :
    ω ∈ rawStrategyTopologyFailureEvent T ↔
      ∃ hz : nprSeed ω ≠ 0,
        gamma ω ∈ topologyBadGammas (T.afterSeed (nprSeed ω) hz).base := by
  constructor
  · intro h
    rw [rawStrategyTopologyFailureEvent] at h
    obtain ⟨z, _hzmem, hfiber⟩ := Finset.mem_biUnion.mp h
    split at hfiber
    · rename_i hz
      obtain ⟨hbad, hseed⟩ :=
        (mem_fixedSeedGammaEvent_iff z _ ω).1 hfiber
      subst z
      refine ⟨hz, ?_⟩
      simpa only [proof_irrel_heq] using hbad
    · simp at hfiber
  · rintro ⟨hz, hbad⟩
    rw [rawStrategyTopologyFailureEvent]
    apply Finset.mem_biUnion.mpr
    refine ⟨nprSeed ω, Finset.mem_univ _, ?_⟩
    rw [dif_pos hz]
    exact (mem_fixedSeedGammaEvent_iff _ _ _).2 ⟨hbad, rfl⟩

theorem rawStrategyTopologyFailureEvent_card_le
    (T : RawP8Strategy F K p) :
    (rawStrategyTopologyFailureEvent T).card ≤
      rawStrategyTopologyWorkload T * Fintype.card K ^ 2 := by
  calc
    (rawStrategyTopologyFailureEvent T).card ≤
        ∑ z : K,
          (if hz : z ≠ 0 then
            fixedSeedGammaEvent z
              (topologyBadGammas (T.afterSeed z hz).base)
          else ∅).card := by
      unfold rawStrategyTopologyFailureEvent
      exact Finset.card_biUnion_le
    _ ≤ ∑ z : K,
          (if hz : z ≠ 0 then
            topologyWorkload (T.afterSeed z hz).base
          else 0) * Fintype.card K ^ 2 := by
      apply Finset.sum_le_sum
      intro z _
      split
      · rename_i hz
        rw [card_fixedSeedGammaEvent]
        exact Nat.mul_le_mul_right _
          (topologyBadGammas_card_le (T.afterSeed z hz).base)
      · simp
    _ = rawStrategyTopologyWorkload T * Fintype.card K ^ 2 := by
      rw [rawStrategyTopologyWorkload, Finset.sum_mul]

/-- Uniform per-seed form of the joint count.  This is cardinality/fiber summation, not an
independence argument. -/
theorem rawStrategyTopologyFailureEvent_card_le_uniform
    (T : RawP8Strategy F K p) (workload : ℕ)
    (hwork : ∀ z (hz : z ≠ 0),
      topologyWorkload (T.afterSeed z hz).base ≤ workload) :
    (rawStrategyTopologyFailureEvent T).card ≤
      workload * Fintype.card K ^ 3 := by
  refine (rawStrategyTopologyFailureEvent_card_le T).trans ?_
  have hsum : rawStrategyTopologyWorkload T ≤ Fintype.card K * workload := by
    unfold rawStrategyTopologyWorkload
    calc
      (∑ z : K, if hz : z ≠ 0 then
          topologyWorkload (T.afterSeed z hz).base else 0)
          ≤ ∑ _z : K, workload := by
            apply Finset.sum_le_sum
            intro z _
            split
            · exact hwork z ‹z ≠ 0›
            · omega
      _ = Fintype.card K * workload := by simp
  calc
    rawStrategyTopologyWorkload T * Fintype.card K ^ 2
        ≤ (Fintype.card K * workload) * Fintype.card K ^ 2 :=
      Nat.mul_le_mul_right _ hsum
    _ = workload * Fintype.card K ^ 3 := by ring

/-- Strategy-level end-to-end topology statement outside the correctly seed-fibered event. -/
theorem RawP8Strategy.exactTopology_of_accepts_and_compressedCheck
    (T : RawP8Strategy F K p) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0)
    (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ i, ((T.familyAt ω hz).exec.memoryPubAt i).lambda = (T.familyAt ω hz).cfg.challenges.lam)
    (haccept : T.Accepts ω)
    (hcheck : TopologyCompressedCheck (T.familyAt ω hz) (gamma ω))
    (hout : ω ∉ rawStrategyTopologyFailureEvent T) :
    ComputeExactTopology (T.familyAt ω hz).exec ∧
      MemoryExactTopology (T.familyAt ω hz).exec := by
  have hraw :
      (T.messageAt ω hz).Accepts T.claim ω := by
    simpa [RawP8Strategy.Accepts, hz, RawAccepts, proof_irrel_heq] using haccept
  apply (T.messageAt ω hz).exactTopology_of_accepts_and_compressedCheck
    hchar hlam hraw hcheck
  intro hbad
  apply hout
  apply (mem_rawStrategyTopologyFailureEvent_iff T ω).2
  refine ⟨hz, ?_⟩
  have hfixed :
      topologyBadGammas ((T.afterSeed (nprSeed ω) hz).atJointCoins ω) =
        topologyBadGammas (T.afterSeed (nprSeed ω) hz).base :=
    rfl
  rw [← hfixed]
  simpa [RawP8Strategy.familyAt] using hbad

/-! ## Challenge-order receipts -/

theorem RawP8SeedCommitment.topology_rows_seedFixed
    {claim : P8PublicClaim} {z : K}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p)
    (ω₁ ω₂ : JointCoins K) :
    (C.atJointCoins ω₁).computeWalkRows = (C.atJointCoins ω₂).computeWalkRows ∧
      (C.atJointCoins ω₁).memoryWalkRows = (C.atJointCoins ω₂).memoryWalkRows :=
  ⟨rfl, rfl⟩

theorem RawP8SeedCommitment.topology_badGammas_seedFixed
    {claim : P8PublicClaim} {z : K}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p)
    (ω : JointCoins K) :
    topologyBadGammas (C.atJointCoins ω) = topologyBadGammas C.base :=
  rfl

end Finite

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.rawTopologyBindingResidual_of_compressedCheck
#print axioms Nock.NockVMROM.Thm54.RawMessage.exactTopology_of_accepts_and_compressedCheck
#print axioms Nock.NockVMROM.Thm54.topologyBadGammas_card_le
#print axioms Nock.NockVMROM.Thm54.topologyFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.rawStrategyTopologyFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.rawStrategyTopologyFailureEvent_card_le_uniform
#print axioms Nock.NockVMROM.Thm54.RawP8Strategy.exactTopology_of_accepts_and_compressedCheck
#print axioms Nock.NockVMROM.Thm54.RawP8SeedCommitment.topology_badGammas_seedFixed
