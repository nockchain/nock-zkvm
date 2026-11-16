/-
  Nock/NockVMROM/Thm54/BelowDefs/HonestCommitment.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/HonestCommitment.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.BuildableExecution
import Nock.NockVMROM.Thm54.HonestCommitmentNodes
import Nock.NockVMROM.Thm54.ServedLookupBridge

namespace Nock.NockVMROM.Thm54

namespace HonestCommitment

open Nock Nock.Walk Nock.NockVMROM
open SemanticStrategy SemanticTimestampStrategy
open TemplateRawJointSoundness RawSemanticAssembly

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Local validity of one committed compute node at the honest sample `(z, α)`. -/
def ComputeNodeOK (z α : K) (t : NTree (ComputeNode K)) : Prop :=
  t.children.length = ComputeTable.fanoutComp t.label.skel.state ∧
    t.label.stamp.state = t.label.skel.state ∧
    BindComputeRow z t.label.skel t.label.row ∧
    ComputeTimestampSpecializesAt α t.label.stamp t.label.row

/-- Local validity of one committed memory node at the honest sample `(z, α)`. -/
def MemoryNodeOK (z α : K) (t : NTree (MemoryNode K)) : Prop :=
  t.children.length = MemoryTable.fanoutMem t.label.skel.state ∧
    t.label.stamp.state = t.label.skel.state ∧
    BindMemoryRowA z t.label.skel t.label.row ∧
    MemoryTimestampSpecializesAt α t.label.stamp t.label.row

/-- Every node of the committed compute tree is locally valid. -/
def ComputeNodesOK (z α : K) (T : NTree (ComputeNode K)) : Prop :=
  ∀ t, InTree T t → ComputeNodeOK z α t

/-- Every node of one committed memory tree is locally valid. -/
def MemoryNodesOK (z α : K) (T : NTree (MemoryNode K)) : Prop :=
  ∀ t, InTree T t → MemoryNodeOK z α t

theorem ComputeNodesOK.child {z α : K} {T c : NTree (ComputeNode K)}
    (h : ComputeNodesOK z α T) (hc : c ∈ T.children) : ComputeNodesOK z α c :=
  fun t ht => h t (InTree.sub hc ht)

theorem MemoryNodesOK.child {z α : K} {T c : NTree (MemoryNode K)}
    (h : MemoryNodesOK z α T) (hc : c ∈ T.children) : MemoryNodesOK z α c :=
  fun t ht => h t (InTree.sub hc ht)

/-- Assemble whole-tree validity from the root datum and the children's validity. -/
theorem ComputeNodesOK.mk' {z α : K} {lbl : ComputeNode K} {cs : List (NTree (ComputeNode K))}
    (hnode : ComputeNodeOK z α (.node lbl cs))
    (hcs : ∀ c ∈ cs, ComputeNodesOK z α c) : ComputeNodesOK z α (.node lbl cs) := by
  intro t ht
  cases ht with
  | here => exact hnode
  | sub hs h => exact hcs _ (by simpa using hs) t h

theorem MemoryNodesOK.mk' {z α : K} {lbl : MemoryNode K} {cs : List (NTree (MemoryNode K))}
    (hnode : MemoryNodeOK z α (.node lbl cs))
    (hcs : ∀ c ∈ cs, MemoryNodesOK z α c) : MemoryNodesOK z α (.node lbl cs) := by
  intro t ht
  cases ht with
  | here => exact hnode
  | sub hs h => exact hcs _ (by simpa using hs) t h

/-- The committed semantic skeleton is the node tree's skeleton projection: nouns, Nat axes, and
tree topology, all fixed before the seed. -/
def skeletonOfNodes (ct : NTree (ComputeNode K)) (mf : List (NTree (MemoryNode K))) :
    SemanticSkeleton where
  computeTree := mapNTree ComputeNode.skel ct
  memoryForest := mf.map (mapNTree MemoryNode.skel)

/-- **The honest prover's committed data for one supplied execution.**

The first seven fields are the commitment proper: the node trees carrying the pre-seed skeleton
rows and their committed Nat timestamp exponents, the identification of their row projection with
the supplied execution, their local validity at the honest sample, and the committed root line
number.  The remaining fields are the *seed-free semantic obligations on the committed skeleton
alone* — slot semantics, record equations, the comparison census and its leaf window, and the
`q`-boundedness of the committed nouns.  None of them mentions a seed, a template, a chip, a
trace, or an acceptance. -/
structure Data (E : BuildableNockExecution F K) where
  /-- The committed compute node tree. -/
  computeNodes : NTree (ComputeNode K)
  /-- The committed memory node forest. -/
  memoryNodes : List (NTree (MemoryNode K))
  compute_rows : mapNTree ComputeNode.row computeNodes = E.exec.computeTree
  memory_rows : memoryNodes.map (mapNTree MemoryNode.row) = E.execA.memoryForest
  computeOK : ComputeNodesOK E.cfg.challenges.z E.cfg.challenges.α computeNodes
  memoryOK : ∀ t ∈ memoryNodes, MemoryNodesOK E.cfg.challenges.z E.cfg.challenges.α t
  /-- **The committed root line-number exponent is zero.**

  *What it asserts.*  One `ℕ` equation on one committed node: the compute node the prover commits
  at the root of the compute tree — the row BFS visits first — carries line-number exponent `0`.
  It names no field element, no `α`, no `z`, and no `ln_prev` column.

  *Paper.*  Line-number construction is a **prover** step, which is why it is recorded here and not on `ExactExecution`, on
  `ChainedSemanticExactLanguage`, or in the compute AIR.  The compute table is a `RAP_walk`
  instance, so `RAP_walk`'s initial line constraint
  `ln(1) = α` (the paper, heading `806`; closed form `ln(k) = α^k` at the paper) applies
  to it by composition, and the worked `RAP_walk` table writes the literal value **`1`** in the
  `ln` column of the Seed-Input row that precedes row 1.
  Independently, the compute table's own timestamps have the closed form `z^i` counted from the
  first access, which is first-row `ln_prev = z⁰ = 1` with no identification of
  the two `ln` columns required.  the paper against the paper identifies the
  algorithm's `ln_prev` at row `i` with the constraint spec's `ln(i-1)`.

  *Cite repair.*  `1727` is **blank**:
  `\begin{algorithm}` for `V_comp` opens at `1720`, the `\Procedure` line is `1726`, and the first
  check — "Check that `((input_formula, formula_tail), 3, ln_prev · z) = mem_record₁`" — is on
  **`1728`**.

  *Non-vacuity.*  Satisfied by every honest commitment in the build, each by `rfl`:
  `DistinctCensusCommitment.dataD` (the released F97 fixture),
  `MultiRootHonestCommitment.dataM`, `HonestCommitment.Concrete.data73`, and — since the two
  exponent-relabelling maps rewrite the memory nodes only — `wrapDataExponents` and `normData` of
  any of them.  `GenericHonestData.dataOf` discharges it from `lnPrevExp_zero` with no change to
  its signature.  Receipts: `AO122.blast_radius_is_discharged`,
  `AO122.j03_witness_at_all_three_live_fixtures`.

  *What it licenses.*  `Data.firstLine` — `ResidualPremises.firstLine` becomes a consequence of
  holding a commitment, by a derivation through `ComputeNodeOK`'s `ComputeTimestampSpecializesAt`
  equation rather than by projection.  The field is **strictly stronger** than that conclusion:
  `AO122.F73Probe.converse_fails_at_concrete` re-stamps F73's own root by `orderOf α = 9` and
  satisfies the entire specialization equation against the same published row with `ln_prev` still
  `1`, so `ln_prev = 1` does not recover the committed exponent and this field is not a rename of
  the premise it discharges (contrast `FirstLineCarrier.c6_field_is_definitionally_firstLine`,
  which is `Iff.rfl`).

  *What it does NOT license.*  It does **not** remove `firstLine` from `ResidualPremises`, and
  `ResidualPremises` still has four fields.  `GenericHonestData.dataOf` consumes `P.firstLine` to
  prove `computeOK` — the base case of `ln_prev_pow_nat` — and the new field is `rfl` there, so the
  named-premises route to a commitment is unchanged
  (`GenericHonestPackage.dataOf_consumes_firstLine_and_q_eq`).  It is also not an AIR constraint:
  the compute chained AIR's boundary segment is still empty
  (`FirstLineCarrier.compute_air_boundary_segment_is_empty`) and `V_comp` still does not check the
  first row, so this is an honest-prover commitment condition, never something recovered from
  acceptance.

  *Narrowing.*  `Data E` now excludes commitments whose committed root line exponent is nonzero —
  for instance one that begins counting at `α¹`, or one obtained by re-stamping the root by a
  multiple of `orderOf α`, which is otherwise indistinguishable from the honest stamp.
  `no_universal_forestExponentOrder` and the ticked `ForestExponentOrder` row are unaffected,
  because their witnesses `wrapDataExponents D` and `normData D` carry `D`'s compute nodes across
  unchanged.

  This paragraph read "No such
  commitment exists in the build", which invites the reading that the excluded object is
  *unconstructible*.  It is not.  It survives `computeOK` because `ComputeNodesOK` is purely per-node — there is no
  parent/child exponent chain in it (`:421-436`) — and its one conjunct reading `lnPrevExponent`
  reads it only through `α ^ ·`, so a full `orderOf α` period is invisible.

  *…and why the exclusion is nevertheless SOUND.*  the paper **defines** the committed
  quantity to *be* the line number: the timestamp "is unique and represents the line number of the
  compute table at which the memory record was requested, thus having the closed form
  `z^{i} ∈ 𝕂,` where `i` is the compute table line number".  The honest ladder
  `GenericHonestData.lnPrevExp` is exactly that count, it is `0` at row zero
  for **every** execution (`Batch139.honest_ladder_pins_row_zero`), and at F73 its whole range is
  `{0}` (`Batch139.F73.excluded_exponent_is_not_a_line_number`), so the re-stamped exponent `9` is
  not the line number of any row of that table.  The excluded commitment is one whose committed `ℕ`
  **misdescribes** the line number, not an honest prover's alternative numbering; the `orderOf α`
  ambiguity that hides it at the published `K`-columns is a property of the fixture's small field,
  not a freedom the paper grants.  That is exactly why the pin has to be a *commitment* condition and can never be recovered from acceptance. -/
  root_line_exponent : computeNodes.label.stamp.lnPrevExponent = 0
  /-- One `K` equation on the same committed node as `root_line_exponent`: the
  honest prover's line-number origin, `α ^ 0` in the generator (`Gen.lean` `renderOp*Row`,
  `ComputeLineStartsAtZero`; `GenWF.renderNode_ln_prev`).

  *Why now.*  The deployed compute chip commits `isFirst · (ln_prev − 1) = 0` since stage 2A, so the
  honest trace is accepted only if the committed execution starts its line at `1`; this field is
  the completeness obligation that gate creates, carried where the paper puts line-number
  construction — on the prover's commitment.  `root_line_exponent` alone does not give it:
  `ComputeTimestampSpecializesAt` is relative (`ln = ln_prev · α^{…}`), so the committed exponent
  `0` says nothing about the published `K`-value (`AO-123(iv)`, `Data.firstLine`'s `horigin`).

  *What it is not.*  Not a `V_comp` check.  `Data.firstLine D D.root_line_origin : FirstLineStartsAtOne E.exec`. -/
  root_line_origin : computeNodes.label.row.2.2.1.ln_prev = 1
  /-- Committed leaf-size bound of the commitment object. -/
  nounSizeBound : ℕ
  /-- The paper's leaf window for the comparison census. -/
  Λ : ℕ
  slotSemantics : ∀ s ∈ computeSkeletonRows (skeletonOfNodes computeNodes memoryNodes),
    ServedLookupBridge.SkeletonSlotSemantics s
  recordEquations : ∀ s ∈ computeSkeletonRows (skeletonOfNodes computeNodes memoryNodes),
    ServedLookupBridge.SkeletonRecordEquations s
  census : EdgeComparisonCensus.CombinedSkeletonCensus K
    (skeletonOfNodes computeNodes memoryNodes) Λ
  sizeWindowBound : SizeWindowCounting.SizeWindowNounsBoundedBy
    (skeletonOfNodes computeNodes memoryNodes) Λ
  q_eq_ringChar : E.q = ringChar K
  skeletonBounded : (skeletonOfNodes computeNodes memoryNodes).BoundedBy E.q
  combinedBounded : ProductionP8Containment.CombinedBoundedBy K E.q
    (skeletonOfNodes computeNodes memoryNodes)

namespace Data

variable {E : BuildableNockExecution F K}

/-- The committed semantic skeleton of this commitment. -/
def skeleton (D : Data E) : SemanticSkeleton :=
  skeletonOfNodes D.computeNodes D.memoryNodes

end Data

end

end HonestCommitment

end Nock.NockVMROM.Thm54
