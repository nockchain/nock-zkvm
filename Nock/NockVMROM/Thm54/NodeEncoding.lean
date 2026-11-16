import Nock.NockVMROM.Thm54.PlusIOSegmentedRAP

/-!
# Concrete finite-coordinate walk-node encodings

Both encoders flatten the complete walk label, including the outer
walk state and the state repeated inside the table row. No field is packed into another field
coordinate.

The compute-state tag is the actual opcode number:

* `s0,...,s9` map to `0,...,9`;
* `cons` maps to `11` (opcode 10 is intentionally absent).

In particular this does not use `ComputeTable.State.toNat`, whose `s0` and `cons` values collide.
The exact field hypothesis is injectivity of `Nat.cast` on `0,...,11`.  It follows from
characteristic zero or from characteristic strictly greater than 11.

## Coordinate layouts

All intervals below are inclusive.

Compute (`93` coordinates; H1.W Option A adds six for `sf*_st`):

* `0`: outer compute-state tag;
* `1..5`: `Inputs.(α,z,a,b,c)`;
* `6`: `Pub.state`;
* `7..42`: the twelve `Pub` fingerprints, each in `(size,dyck,leaf)` order:
  `(s,f,e,sf1_s,sf1_f,sf1_e,sf2_s,sf2_f,sf2_e,sf3_s,sf3_f,sf3_e)`;
* `43..48`: `Pub.(sf1_st,sf2_st,sf3_st)`, each `Option K` as `(isSome, getD null)`;
* `49..50`: `Pub.(ln_prev,ln)`;
* `51..74`: `Pub.(mr1,mr2,mr3)`, each memory record in
  `(root.size,root.dyck,root.leaf,child.size,child.dyck,child.leaf,axis,ts)` order;
* `75..92`: `Dec.(f_h,f_t,f_th,f_tt,f_tth,f_ttt)`, each fingerprint in
  `(size,dyck,leaf)` order.

Memory (`36` coordinates):

* `0`: outer memory-state tag;
* `1..3`: `Inputs.(z,β,γ)`;
* `4`: `Pub.st`;
* `5..19`: `Pub.(pt,lc,rc)`, each cell in
  `(noun.size,noun.dyck,noun.leaf,indicator,counts)` order;
* `20..21`: `Pub.(lcSt,rcSt)`;
* `22..29`: `Pub.mem` in memory-record order;
* `30..31`: `Pub.(ipre,icur)`;
* `32..35`: `Pub.(cprime?,lambda?)` as `Option K` pairs.
-/

namespace Nock.NockVMROM.Thm54

open Nock

namespace NodeEncoding

/-- The paper Goldilocks prime is strictly greater than 11,
so opcode tags `{0,...,9} ∪ {11}` are distinct as field
elements.  This is a ℕ inequality; it does not bump any fixture `q`. -/

theorem goldilocks_p_gt_eleven : 11 < 2 ^ 64 - 2 ^ 32 + 1 := by
  norm_num

variable {K : Type*} [Field K]

/-! ## Exact characteristic separation -/

/-- The exact characteristic hypothesis used by the state-tag coordinates: natural-number casts
are injective on the closed interval `0,...,11`.  For a positive characteristic this is equivalent
to requiring characteristic strictly greater than `11`. -/
def StateTagChar (K : Type*) [Field K] : Prop :=
  Set.InjOn (fun n : ℕ => (n : K)) (Set.Iic 11)

/-- A field of characteristic `p > 11` satisfies `StateTagChar`. -/
theorem stateTagChar_of_charP (p : ℕ) [CharP K p] (hp : 11 < p) : StateTagChar K := by
  intro m hm n hn hmn
  apply CharP.natCast_injOn_Iio K p
  · exact lt_of_le_of_lt hm hp
  · exact lt_of_le_of_lt hn hp
  · exact hmn

/-- Paper hypothesis: opcode tags occupy `{0,...,9} ∪ {11}`,
so distinct nat-casts on `0,...,11` follow from `11 < ringChar K`.
The Goldilocks pin `p = 2^{64}-2^{32}+1` satisfies this. -/

theorem stateTagChar_of_ringChar_gt_eleven (h : 11 < ringChar K) : StateTagChar K :=
  haveI := ringChar.charP K
  stateTagChar_of_charP (ringChar K) h

/-- On positive characteristic, `StateTagChar` forces `11 < ringChar`.  Combined
with `stateTagChar_of_ringChar_gt_eleven`, the encoding extra is not strictly
stronger than the paper characteristic bound. -/

theorem ringChar_gt_eleven_of_stateTagChar (hchar : StateTagChar K)
    (hpos : 0 < ringChar K) : 11 < ringChar K := by
  haveI := ringChar.charP K
  by_contra hnot
  have hle : ringChar K ≤ 11 := Nat.not_lt.mp hnot
  have hcast : ((ringChar K : ℕ) : K) = ((0 : ℕ) : K) := by
    simp [CharP.cast_eq_zero]
  have heq : ringChar K = 0 :=
    hchar (show ringChar K ∈ Set.Iic 11 from hle)
      (by simp : (0 : ℕ) ∈ Set.Iic 11) hcast
  exact (Nat.ne_of_gt hpos) heq

/-- On positive characteristic, `StateTagChar` is exactly `11 < ringChar K`. -/

theorem stateTagChar_iff_ringChar_gt_eleven (hpos : 0 < ringChar K) :
    StateTagChar K ↔ 11 < ringChar K :=
  ⟨fun hchar => ringChar_gt_eleven_of_stateTagChar hchar hpos,
    stateTagChar_of_ringChar_gt_eleven⟩

/-- A characteristic-zero field satisfies `StateTagChar`. -/
theorem stateTagChar_of_charZero [CharZero K] : StateTagChar K := by
  intro m _ n _ hmn
  exact Nat.cast_injective hmn

/-- The current exact witness field `ZMod 17` satisfies the state-tag characteristic hypothesis. -/
theorem zmod17_stateTagChar [Fact (Nat.Prime 17)] : StateTagChar (ZMod 17) :=
  stateTagChar_of_charP (K := ZMod 17) 17 (by omega)

/-! ## State tags -/

/-- Injective compute opcode tag.  The `cons` state is opcode `11`, not `State.toNat cons = 0`. -/
def computeStateTag : ComputeTable.State → ℕ
  | .s0 => 0
  | .s1 => 1
  | .s2 => 2
  | .s3 => 3
  | .s4 => 4
  | .s5 => 5
  | .s6 => 6
  | .s7 => 7
  | .s8 => 8
  | .s9 => 9
  | .cons => 11

/-- The four memory-state tags in table order. -/
def memoryStateTag : MemoryTable.MState → ℕ
  | .decompose => 0
  | .halt => 1
  | .read_root => 2
  | .verify_child => 3

theorem computeStateTag_le (s : ComputeTable.State) : computeStateTag s ≤ 11 := by
  cases s <;> decide

theorem memoryStateTag_le (s : MemoryTable.MState) : memoryStateTag s ≤ 11 := by
  cases s <;> decide

theorem computeStateTag_injective : Function.Injective computeStateTag := by
  intro a b h
  cases a <;> cases b <;> simp_all [computeStateTag]

theorem memoryStateTag_injective : Function.Injective memoryStateTag := by
  intro a b h
  cases a <;> cases b <;> simp_all [memoryStateTag]

theorem computeStateCast_injective (hchar : StateTagChar K) :
    Function.Injective (fun s : ComputeTable.State => (computeStateTag s : K)) := by
  intro a b h
  apply computeStateTag_injective
  exact hchar (computeStateTag_le a) (computeStateTag_le b) h

theorem memoryStateCast_injective (hchar : StateTagChar K) :
    Function.Injective (fun s : MemoryTable.MState => (memoryStateTag s : K)) := by
  intro a b h
  apply memoryStateTag_injective
  exact hchar (memoryStateTag_le a) (memoryStateTag_le b) h

/-! ## Named widths -/

/-- One field coordinate for an injective finite-state tag. -/
abbrev stateTagWidth : ℕ := 1

/-- A fingerprint is `(size,dyck,leaf)`. -/
abbrev fpWidth : ℕ := 3

/-- A memory record is two fingerprints followed by `axis` and `ts`. -/
abbrev memRecWidth : ℕ := 2 * fpWidth + 2

/-- A memory cell is one fingerprint followed by `indicator` and `counts`. -/
abbrev cellWidth : ℕ := fpWidth + 2

/-- `Option K` tag pair: `(isSome, getD nullStateTag)`. -/
abbrev optionTagWidth : ℕ := 2

abbrev computeInputsWidth : ℕ := 5
/-- H1.W Option A: three `sf*_st : Option K` tags add `3 · optionTagWidth`. -/
abbrev computePubWidth : ℕ :=
  stateTagWidth + 12 * fpWidth + 2 + 3 * memRecWidth + 3 * optionTagWidth + optionTagWidth
abbrev computeDecWidth : ℕ := 6 * fpWidth
abbrev computeDataWidth : ℕ := computeInputsWidth + computePubWidth + computeDecWidth

abbrev computeFullRowWidth : ℕ := stateTagWidth + computeDataWidth
/-- **The compute walk label width: the paper's `LT_comp`** — one state
tag and the nine coordinates of `(subject, formula, evaluation)`. -/
abbrev computeNodeWidth : ℕ := stateTagWidth + 3 * fpWidth

abbrev memoryInputsWidth : ℕ := 3
abbrev memoryPubWidth : ℕ :=
  stateTagWidth + 3 * cellWidth + 2 * stateTagWidth + memRecWidth + 2 + 1 + 2 * optionTagWidth
abbrev memoryDataWidth : ℕ := memoryInputsWidth + memoryPubWidth
/-- Width of the retired full memory row encoder (`33`): state tag plus every data column.
Kept for `memoryFullRowEncode`; the deployed walk label is `memoryNodeWidth`. -/
abbrev memoryFullRowWidth : ℕ := stateTagWidth + memoryDataWidth
/-- **H1.W memory: the deployed memory walk label is the paper's
`x^mem`** — state tag plus the parent cell, `1 + 5 = 6` coordinates. -/
abbrev memoryNodeWidth : ℕ := stateTagWidth + cellWidth

theorem fp_width : fpWidth = 3 := rfl
theorem memRec_width : memRecWidth = 8 := rfl
theorem cell_width : cellWidth = 5 := rfl
theorem optionTag_width : optionTagWidth = 2 := rfl
theorem computeInputs_width : computeInputsWidth = 5 := rfl
theorem computePub_width : computePubWidth = 71 := rfl
theorem computeDec_width : computeDecWidth = 18 := rfl
theorem computeData_width : computeDataWidth = 94 := rfl
theorem computeFullRow_width : computeFullRowWidth = 95 := rfl
theorem computeNode_width : computeNodeWidth = 10 := rfl
theorem memoryInputs_width : memoryInputsWidth = 3 := rfl
theorem memoryPub_width : memoryPubWidth = 33 := rfl
theorem memoryData_width : memoryDataWidth = 36 := rfl
theorem memoryFullRow_width : memoryFullRowWidth = 37 := rfl
theorem memoryNode_width : memoryNodeWidth = 6 := rfl

/-! ## A proved coordinate-concatenation combinator

`Encoder.prod` probes the left block at `Fin.castAdd` and the right block at `Fin.natAdd`.
Thus all structure reconstruction below is reduced to coordinate equalities; there is no packing
assumption.
-/

structure Encoder (K A : Type*) where
  width : ℕ
  encode : A → Fin width → K
  injective : Function.Injective encode

namespace Encoder

def scalar : Encoder K K where
  width := 1
  encode := fun x _ => x
  injective := by
    intro a b h
    simpa using congrFun h (0 : Fin 1)

def prod {A B : Type*} (ea : Encoder K A) (eb : Encoder K B) : Encoder K (A × B) where
  width := ea.width + eb.width
  encode := fun x => Fin.addCases (ea.encode x.1) (eb.encode x.2)
  injective := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    apply Prod.ext
    · apply ea.injective
      funext i
      simpa only [Fin.addCases_left] using congrFun h (Fin.castAdd eb.width i)
    · apply eb.injective
      funext i
      simpa only [Fin.addCases_right] using congrFun h (Fin.natAdd ea.width i)

def pullback {A B : Type*} (e : Encoder K B) (pack : A → B)
    (hpack : Function.Injective pack) : Encoder K A where
  width := e.width
  encode := fun a => e.encode (pack a)
  injective := e.injective.comp hpack

end Encoder

/-! ## Primitive structure encoders -/

private def computeStateEncoder (hchar : StateTagChar K) :
    Encoder K ComputeTable.State where
  width := stateTagWidth
  encode := fun s _ => (computeStateTag s : K)
  injective := by
    intro a b h
    apply computeStateCast_injective hchar
    simpa using congrFun h (0 : Fin stateTagWidth)

private def memoryStateEncoder (hchar : StateTagChar K) :
    Encoder K MemoryTable.MState where
  width := stateTagWidth
  encode := fun s _ => (memoryStateTag s : K)
  injective := by
    intro a b h
    apply memoryStateCast_injective hchar
    simpa using congrFun h (0 : Fin stateTagWidth)

private def scalar2Encoder : Encoder K (K × K) :=
  Encoder.scalar.prod Encoder.scalar

/-- Encode `Bool` as `{0,1} ⊆ K` (paper `ver ∈ {0,1}`). -/
private def boolEncoder : Encoder K Bool where
  width := 1
  encode := fun b _ => if b then (1 : K) else 0
  injective := by
    intro a b h
    have := congrFun h (0 : Fin 1)
    cases a <;> cases b <;> simp_all

private def fpEncoder : Encoder K (ComputeTable.FP K) :=
  (Encoder.scalar.prod (Encoder.scalar.prod Encoder.scalar)).pullback
    (fun x => (x.size, (x.dyck, x.leaf)))
    (by
      intro a b h
      exact ComputeTable.FP.ext
        (congrArg Prod.fst h)
        (congrArg (fun x => x.2.1) h)
        (congrArg (fun x => x.2.2) h))

private def memRecEncoder : Encoder K (ComputeTable.MemRec K) :=
  (fpEncoder.prod (fpEncoder.prod scalar2Encoder)).pullback
    (fun r => (r.root, (r.child, (r.axis, r.ts))))
    (by
      intro a b h
      exact ComputeTable.MemRec.ext
        (congrArg Prod.fst h)
        (congrArg (fun x => x.2.1) h)
        (congrArg (fun x => x.2.2.1) h)
        (congrArg (fun x => x.2.2.2) h))

private def cellEncoder : Encoder K (MemoryTable.Cell K) :=
  (fpEncoder.prod scalar2Encoder).pullback
    (fun c => (c.noun, (c.indicator, c.counts)))
    (by
      intro a b h
      cases a
      cases b
      simpa only [MemoryTable.Cell.mk.injEq, Prod.mk.injEq] using h)

/-! ## Compute-label encoder -/

private def computeInputsEncoder : Encoder K (ComputeTable.Inputs K) :=
  (Encoder.scalar.prod
    (Encoder.scalar.prod
      (Encoder.scalar.prod
        (Encoder.scalar.prod Encoder.scalar)))).pullback
    (fun x => (x.α, (x.z, (x.a, (x.b, x.c)))))
    (by
      intro a b h
      cases a
      cases b
      simpa only [ComputeTable.Inputs.mk.injEq, Prod.mk.injEq] using h)

private def fp3Encoder :
    Encoder K (ComputeTable.FP K × (ComputeTable.FP K × ComputeTable.FP K)) :=
  fpEncoder.prod (fpEncoder.prod fpEncoder)

private def fp12Encoder :
    Encoder K
      ((ComputeTable.FP K × (ComputeTable.FP K × ComputeTable.FP K)) ×
        ((ComputeTable.FP K × (ComputeTable.FP K × ComputeTable.FP K)) ×
          ((ComputeTable.FP K × (ComputeTable.FP K × ComputeTable.FP K)) ×
            (ComputeTable.FP K × (ComputeTable.FP K × ComputeTable.FP K))))) :=
  fp3Encoder.prod (fp3Encoder.prod (fp3Encoder.prod fp3Encoder))

private def memRec3Encoder :
    Encoder K
      (ComputeTable.MemRec K × (ComputeTable.MemRec K × ComputeTable.MemRec K)) :=
  memRecEncoder.prod (memRecEncoder.prod memRecEncoder)

/-- Injective encoding of `Option K`: coordinate 0 is `0/1` (none/some), coordinate 1 is
`getD nullStateTag`.  Distinguishes `none` from `some nullStateTag`. -/
private def optionKEncoder : Encoder K (Option K) where
  width := 2
  encode := fun o i =>
    if (i : ℕ) = 0 then
      match o with
      | none => (0 : K)
      | some _ => (1 : K)
    else
      o.getD (↑ComputeTable.nullStateTag : K)
  injective := by
    intro a b heq
    have h0 := congrFun heq (⟨0, by decide⟩ : Fin 2)
    have h1 := congrFun heq (⟨1, by decide⟩ : Fin 2)
    dsimp at h0 h1
    match a, b with
    | none, none => rfl
    | some x, some y =>
        -- i = 1 takes the else branch
        change x = y at h1
        exact congrArg some h1
    | none, some _ =>
        change (0 : K) = 1 at h0
        exact absurd h0 zero_ne_one
    | some _, none =>
        change (1 : K) = 0 at h0
        exact absurd h0 one_ne_zero

private def option3Encoder : Encoder K (Option K × (Option K × Option K)) :=
  optionKEncoder.prod (optionKEncoder.prod optionKEncoder)

private def computePubEncoder (hchar : StateTagChar K) : Encoder K (ComputeTable.Pub K) :=
  (((computeStateEncoder hchar).prod
    ((fp12Encoder.prod option3Encoder).prod (scalar2Encoder.prod memRec3Encoder))).prod
      optionKEncoder).pullback
      (fun p =>
        ((p.state,
          ((((p.s, (p.f, p.e)),
              ((p.sf1_s, (p.sf1_f, p.sf1_e)),
                ((p.sf2_s, (p.sf2_f, p.sf2_e)),
                  (p.sf3_s, (p.sf3_f, p.sf3_e))))),
            (p.sf1_st, (p.sf2_st, p.sf3_st))),
            ((p.ln_prev, p.ln), (p.mr1, (p.mr2, p.mr3))))),
          p.certC?))
      (by
        intro a b h
        rcases a with ⟨astate, as, af, ae, a1st, a1s, a1f, a1e, a2st, a2s, a2f, a2e,
          a3st, a3s, a3f, a3e, alnp, aln, am1, am2, am3, ac⟩
        rcases b with ⟨bstate, bs, bf, be, b1st, b1s, b1f, b1e, b2st, b2s, b2f, b2e,
          b3st, b3s, b3f, b3e, blnp, bln, bm1, bm2, bm3, bc⟩
        simp only [Prod.mk.injEq] at h
        simp_all)

private def fp6Encoder :
    Encoder K
      ((ComputeTable.FP K × (ComputeTable.FP K × ComputeTable.FP K)) ×
        (ComputeTable.FP K × (ComputeTable.FP K × ComputeTable.FP K))) :=
  fp3Encoder.prod fp3Encoder

private def computeDecEncoder : Encoder K (ComputeTable.Dec K) :=
  fp6Encoder.pullback
    (fun d => ((d.f_h, (d.f_t, d.f_th)), (d.f_tt, (d.f_tth, d.f_ttt))))
    (by
      intro a b h
      cases a
      cases b
      simpa only [ComputeTable.Dec.mk.injEq, Prod.mk.injEq, and_assoc] using h)

private def computeDataEncoder (hchar : StateTagChar K) :
    Encoder K (ComputeTable.DTcomp K) :=
  computeInputsEncoder.prod ((computePubEncoder hchar).prod computeDecEncoder)

private def computeNodeEncoder (hchar : StateTagChar K) :
    Encoder K (ComputeTable.State × ComputeTable.DTcomp K) :=
  (computeStateEncoder hchar).prod (computeDataEncoder hchar)

/-- **Retired** complete-row encoder (`93` field coordinates at Option A). -/
def computeFullRowEncode (hchar : StateTagChar K) :
    (ComputeTable.State × ComputeTable.DTcomp K) → Fin computeFullRowWidth → K :=
  (computeNodeEncoder hchar).encode

theorem computeFullRowEncode_injective (hchar : StateTagChar K) :
    Function.Injective (computeFullRowEncode hchar) :=
  (computeNodeEncoder hchar).injective

/-- The opcode tag as a field element is `ComputeTable.stateTagField`. -/
theorem computeStateTag_cast (st : ComputeTable.State) :
    (computeStateTag st : K) = ComputeTable.stateTagField st := by
  cases st <;> simp [computeStateTag, ComputeTable.stateTagField]

/-- **The paper's `LT_comp` label vector**: coordinate `0` is the
row's opcode tag (`:1893`), coordinates `1..9` are the `size/dyck/leaf` coordinates of
`(subject, formula, evaluation)` — `ComputeTable.labelVecOfPub` of the row's `Pub`.  This is what
`RLC^γ(current_node)` commits in the walk (`:848-850`) and what a parent can declare for a child
(`:1684-1688`).  `ln`, `mem_record`, the decomposition and the subformula slots are **not** part
of the label (they are bound row-locally by `V_comp`, the chain and the IO argument). -/
def computeLabelVec (l : ComputeTable.State × ComputeTable.DTcomp K) : Fin computeNodeWidth → K :=
  ComputeTable.labelVecOfPub l.2.2.1

theorem computeLabelVec_eq_labelVecOfPub (l : ComputeTable.State × ComputeTable.DTcomp K) :
    computeLabelVec l = ComputeTable.labelVecOfPub l.2.2.1 := rfl

/-- **The deployed compute-walk label encoder: the `LT_comp` projection** (width `10`).  The
`StateTagChar` argument is retained for signature stability; the projection itself needs no
field hypothesis — only its label-injectivity below does. -/
def computeNodeEncode (_hchar : StateTagChar K) :
    (ComputeTable.State × ComputeTable.DTcomp K) → Fin computeNodeWidth → K :=
  computeLabelVec

theorem computeNodeEncode_eq_labelVec (hchar : StateTagChar K) :
    computeNodeEncode hchar = computeLabelVec := rfl

/-- The label vector determines the `LT_comp` projection (`ComputeTable.computeLabelOf`):
equal vectors have equal state (by `StateTagChar`) and equal `(s, f, e)`.  This replaces the
retired full-row injectivity everywhere the walk soundness theorems are applied. -/
theorem computeLabelVec_labelOf_eq (hchar : StateTagChar K)
    {a b : ComputeTable.State × ComputeTable.DTcomp K}
    (h : computeLabelVec a = computeLabelVec b) :
    ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b := by
  have h0 := congrFun h ⟨0, by decide⟩
  have h1 := congrFun h ⟨1, by decide⟩
  have h2 := congrFun h ⟨2, by decide⟩
  have h3 := congrFun h ⟨3, by decide⟩
  have h4 := congrFun h ⟨4, by decide⟩
  have h5 := congrFun h ⟨5, by decide⟩
  have h6 := congrFun h ⟨6, by decide⟩
  have h7 := congrFun h ⟨7, by decide⟩
  have h8 := congrFun h ⟨8, by decide⟩
  have h9 := congrFun h ⟨9, by decide⟩
  simp only [computeLabelVec, ComputeTable.labelVecOfPub] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hst : a.2.2.1.state = b.2.2.1.state := by
    apply computeStateCast_injective hchar
    simpa [computeStateTag_cast] using h0
  simp only [ComputeTable.computeLabelOf, ComputeTable.LTcomp.mk.injEq]
  refine ⟨hst, ?_, ?_, ?_⟩
  · cases hs : a.2.2.1.s; cases hs' : b.2.2.1.s
    simp_all
  · cases hs : a.2.2.1.f; cases hs' : b.2.2.1.f
    simp_all
  · cases hs : a.2.2.1.e; cases hs' : b.2.2.1.e
    simp_all

theorem computeNodeEncode_labelOf_eq (hchar : StateTagChar K)
    {a b : ComputeTable.State × ComputeTable.DTcomp K}
    (h : computeNodeEncode hchar a = computeNodeEncode hchar b) :
    ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b :=
  computeLabelVec_labelOf_eq hchar h

/-- The projection encoder is **not** injective on full rows: it ignores `mr1` (and `ln`, `Dec`,
the subformula slots). -/
theorem computeNodeEncode_ignores_mr1 (hchar : StateTagChar K)
    (st : ComputeTable.State) (inp : ComputeTable.Inputs K)
    (pub : ComputeTable.Pub K) (dec : ComputeTable.Dec K) (mr1' : ComputeTable.MemRec K) :
    computeNodeEncode hchar (st, (inp, (pub, dec))) =
      computeNodeEncode hchar (st, (inp, ({ pub with mr1 := mr1' }, dec))) := by
  funext k
  fin_cases k <;> rfl

/-! ## Memory-label encoder -/

private def memoryInputsEncoder : Encoder K (MemoryTable.Inputs K) :=
  (Encoder.scalar.prod (Encoder.scalar.prod Encoder.scalar)).pullback
    (fun x => (x.z, (x.β, x.γ)))
    (by
      intro a b h
      cases a
      cases b
      simpa only [MemoryTable.Inputs.mk.injEq, Prod.mk.injEq] using h)

private def cell3Encoder :
    Encoder K (MemoryTable.Cell K × (MemoryTable.Cell K × MemoryTable.Cell K)) :=
  cellEncoder.prod (cellEncoder.prod cellEncoder)

private def memoryState2Encoder (hchar : StateTagChar K) :
    Encoder K (MemoryTable.MState × MemoryTable.MState) :=
  (memoryStateEncoder hchar).prod (memoryStateEncoder hchar)

private def memoryPubEncoder (hchar : StateTagChar K) :
    Encoder K (MemoryTable.Pub K) :=
  ((memoryStateEncoder hchar).prod
    (cell3Encoder.prod
      ((memoryState2Encoder hchar).prod
        (memRecEncoder.prod (scalar2Encoder.prod
          (boolEncoder.prod (optionKEncoder.prod optionKEncoder))))))).pullback
    (fun p =>
      (p.st,
        ((p.pt, (p.lc, p.rc)),
          ((p.lcSt, p.rcSt), (p.mem, ((p.ipre, p.icur),
            (p.ver, (p.cprime?, p.lambda?))))))))
    (by
      intro a b h
      cases a
      cases b
      simpa only [MemoryTable.Pub.mk.injEq, Prod.mk.injEq, and_assoc] using h)

private def memoryDataEncoder (hchar : StateTagChar K) :
    Encoder K (MemoryTable.DTmem K) :=
  memoryInputsEncoder.prod (memoryPubEncoder hchar)

private def memoryNodeEncoder (hchar : StateTagChar K) :
    Encoder K (MemoryTable.MState × MemoryTable.DTmem K) :=
  (memoryStateEncoder hchar).prod (memoryDataEncoder hchar)

/-- The retired complete memory-row encoder (`33` field coordinates): the memory walk label until
H1.W's twenty-first move. -/
def memoryFullRowEncode (hchar : StateTagChar K) :
    (MemoryTable.MState × MemoryTable.DTmem K) → Fin memoryFullRowWidth → K :=
  (memoryNodeEncoder hchar).encode

theorem memoryFullRowEncode_injective (hchar : StateTagChar K) :
    Function.Injective (memoryFullRowEncode hchar) :=
  (memoryNodeEncoder hchar).injective

/-- The memory-state tag as a field element is `MemoryTable.mstateTagField`. -/
theorem memoryStateTag_cast (st : MemoryTable.MState) :
    (memoryStateTag st : K) = MemoryTable.mstateTagField st := by
  cases st <;> simp [memoryStateTag, MemoryTable.mstateTagField]

/-- **The paper's `x^mem` label vector**: coordinate `0` the row's state tag,
`1..3` the parent noun fingerprint, `4` `axis_counts_P`, `5` `axis_indicator_P` —
`MemoryTable.memoryLabelVec` of the row's `Pub`.  This is what the memory walk commits
(`:848-850`) and what a parent can declare for a child (`:2031`). -/
def memoryLabelVec (l : MemoryTable.MState × MemoryTable.DTmem K) : Fin memoryNodeWidth → K :=
  MemoryTable.memoryLabelVec l.2.2

theorem memoryLabelVec_eq_labelVec (l : MemoryTable.MState × MemoryTable.DTmem K) :
    memoryLabelVec l = MemoryTable.memoryLabelVec l.2.2 := rfl

/-- **The deployed memory walk label encoder** (H1.W memory, twenty-first move): the `x^mem`
projection, width `6`.  The `StateTagChar` argument is retained for the signature every consumer
already has; the encoder itself is `memoryLabelVec` and needs no character hypothesis. -/
def memoryNodeEncode (_hchar : StateTagChar K) :
    (MemoryTable.MState × MemoryTable.DTmem K) → Fin memoryNodeWidth → K :=
  memoryLabelVec

theorem memoryNodeEncode_eq_labelVec (hchar : StateTagChar K) :
    memoryNodeEncode hchar = memoryLabelVec := rfl

/-- The label vector determines the `x^mem` projection (`MemoryTable.memoryLabelOf`): equal
vectors have equal state (by `StateTagChar`) and equal parent cell.  This replaces the retired
full-row injectivity everywhere the memory walk soundness theorems are applied. -/
theorem memoryLabelVec_labelOf_eq (hchar : StateTagChar K)
    {a b : MemoryTable.MState × MemoryTable.DTmem K}
    (h : memoryLabelVec a = memoryLabelVec b) :
    MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b := by
  have h0 := congrFun h ⟨0, by decide⟩
  have h1 := congrFun h ⟨1, by decide⟩
  have h2 := congrFun h ⟨2, by decide⟩
  have h3 := congrFun h ⟨3, by decide⟩
  have h4 := congrFun h ⟨4, by decide⟩
  have h5 := congrFun h ⟨5, by decide⟩
  simp only [memoryLabelVec, MemoryTable.memoryLabelVec] at h0 h1 h2 h3 h4 h5
  have hst : a.2.2.st = b.2.2.st := by
    apply memoryStateCast_injective hchar
    simpa [memoryStateTag_cast] using h0
  simp only [MemoryTable.memoryLabelOf, MemoryTable.LTmem.mk.injEq]
  refine ⟨hst, ?_⟩
  cases hpa : a.2.2.pt with
  | mk an ai ac =>
    cases hpb : b.2.2.pt with
    | mk bn bi bc =>
      cases an
      cases bn
      simp_all

theorem memoryNodeEncode_labelOf_eq (hchar : StateTagChar K)
    {a b : MemoryTable.MState × MemoryTable.DTmem K}
    (h : memoryNodeEncode hchar a = memoryNodeEncode hchar b) :
    MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b :=
  memoryLabelVec_labelOf_eq hchar h

/-- **The deployed memory encoder reads none of `mem_record`, `intermediate`, the child cells or
the child states** — only `(state, parent cell)`.  The memory twin of
`computeNodeEncode_ignores_mr1`: the record is bound row-locally by `V_mem` and the IO
argument, not by the walk. -/
theorem memoryNodeEncode_ignores_mem (hchar : StateTagChar K)
    (st : MemoryTable.MState) (inp : MemoryTable.Inputs K)
    (pub : MemoryTable.Pub K) (mem' : ComputeTable.MemRec K) :
    memoryNodeEncode hchar (st, (inp, pub)) =
      memoryNodeEncode hchar (st, (inp, { pub with mem := mem' })) := by
  funext k
  fin_cases k <;> rfl

/-! ## Public coordinate probes and the collision regression -/

theorem computeFullRowEncode_outerState (hchar : StateTagChar K)
    (x : ComputeTable.State × ComputeTable.DTcomp K) :
    computeFullRowEncode hchar x (0 : Fin computeFullRowWidth) = (computeStateTag x.1 : K) := by
  unfold computeFullRowEncode computeNodeEncoder
  change Fin.addCases ((computeStateEncoder hchar).encode x.1)
      ((computeDataEncoder hchar).encode x.2) (0 : Fin (stateTagWidth + computeDataWidth)) =
    (computeStateTag x.1 : K)
  have hcast : (0 : Fin (stateTagWidth + computeDataWidth)) =
      Fin.castAdd computeDataWidth (0 : Fin stateTagWidth) := Fin.ext rfl
  erw [hcast, Fin.addCases_left]
  rfl

/-- Coordinate `0` of the deployed label is the row's own state tag. -/
theorem computeNodeEncode_state (hchar : StateTagChar K)
    (x : ComputeTable.State × ComputeTable.DTcomp K) :
    computeNodeEncode hchar x (0 : Fin computeNodeWidth) =
      (computeStateTag x.2.2.1.state : K) := by
  simp [computeNodeEncode, computeLabelVec, ComputeTable.labelVecOfPub, computeStateTag_cast]

/-- Coordinate `0` of the deployed memory label is the row's own state tag. -/
theorem memoryNodeEncode_state (hchar : StateTagChar K)
    (x : MemoryTable.MState × MemoryTable.DTmem K) :
    memoryNodeEncode hchar x (0 : Fin memoryNodeWidth) = (memoryStateTag x.2.2.st : K) := by
  rw [memoryStateTag_cast]
  rfl

theorem memoryFullRowEncode_outerState (hchar : StateTagChar K)
    (x : MemoryTable.MState × MemoryTable.DTmem K) :
    memoryFullRowEncode hchar x (0 : Fin memoryFullRowWidth) = (memoryStateTag x.1 : K) := by
  unfold memoryFullRowEncode memoryNodeEncoder
  change Fin.addCases ((memoryStateEncoder hchar).encode x.1)
      ((memoryDataEncoder hchar).encode x.2) (0 : Fin (stateTagWidth + memoryDataWidth)) =
    (memoryStateTag x.1 : K)
  have hcast : (0 : Fin (stateTagWidth + memoryDataWidth)) =
      Fin.castAdd memoryDataWidth (0 : Fin stateTagWidth) := Fin.ext rfl
  erw [hcast, Fin.addCases_left]
  rfl

/-- Regression for the old `State.toNat` collision: changing only `s0` to `cons` changes the
complete compute-node encoding. -/
theorem computeNodeEncode_s0_ne_cons (hchar : StateTagChar K)
    (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K) (dec : ComputeTable.Dec K) :
    computeNodeEncode hchar (ComputeTable.State.s0, (inp, ({ pub with state := .s0 }, dec))) ≠
      computeNodeEncode hchar (ComputeTable.State.cons, (inp, ({ pub with state := .cons }, dec))) := by
  intro h
  have hp := computeNodeEncode_labelOf_eq hchar h
  simp [ComputeTable.computeLabelOf] at hp

end NodeEncoding

/-! ## Filling `PlusIOSegmentedFamily`'s encoder fields -/

namespace PlusIOSegmentedFamily

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Build a `PlusIOSegmentedFamily` from an exact problem using the concrete complete node
encoders.  The three walk challenges are explicit and independent of the exact problem's table
challenge vector.  The public IO endpoints and the two capacity proofs remain explicit data. -/
def ofProblemWithConcreteNodeEncoders
    (problem : ExactCanonicalRAPProblem F K)
    (hchar : NodeEncoding.StateTagChar K)
    (computeWalkAlpha walkGamma memoryWalkAlpha : K)
    (requests responses outMem : IOField K)
    (progIO_capacity :
      problem.exec.derivedRequestIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h)
    (memIO_capacity :
      problem.exec.derivedResponseIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h) :
    PlusIOSegmentedFamily F K where
  problem := problem
  computeWalkAlpha := computeWalkAlpha
  memoryWalkAlpha := memoryWalkAlpha
  walkGamma := walkGamma
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode hchar
  compNodeEncode_labelOf := fun _ _ h => NodeEncoding.computeNodeEncode_labelOf_eq hchar h
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode hchar
  memNodeEncode_labelOf := fun _ _ h => NodeEncoding.memoryNodeEncode_labelOf_eq hchar h
  requests := requests
  responses := responses
  outMem := outMem
  progIO_capacity := progIO_capacity
  memIO_capacity := memIO_capacity

/-- Clearly scoped compatibility constructor for the existing P7 diagonal: both walk `α`
challenges use the table timestamp `α`, and the walk-node `γw` uses the table record-RLC `γ`.
New P8-facing code should use `ofProblemWithConcreteNodeEncoders` or
`ofProblemWithConcreteNodeEncodersAtJointCoins` instead. -/
def ofProblemWithConcreteNodeEncodersScopedP7
    (problem : ExactCanonicalRAPProblem F K)
    (hchar : NodeEncoding.StateTagChar K)
    (requests responses outMem : IOField K)
    (progIO_capacity :
      problem.exec.derivedRequestIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h)
    (memIO_capacity :
      problem.exec.derivedResponseIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h) :
    PlusIOSegmentedFamily F K :=
  ofProblemWithConcreteNodeEncoders problem hchar
    problem.cfg.challenges.α problem.cfg.challenges.γ problem.cfg.challenges.α
    requests responses outMem progIO_capacity memIO_capacity

/-- P8-facing constructor at `((αc, γw), (αm, z))`.  The walk layer consumes the first three
coordinates.  The fourth remains `nprSeed ω` for the separate seed-indexed label/commitment
strategy and does not rewrite the exact problem's table timestamp or record-RLC challenge. -/
def ofProblemWithConcreteNodeEncodersAtJointCoins
    (problem : ExactCanonicalRAPProblem F K)
    (hchar : NodeEncoding.StateTagChar K)
    (ω : JointCoins K)
    (requests responses outMem : IOField K)
    (progIO_capacity :
      problem.exec.derivedRequestIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h)
    (memIO_capacity :
      problem.exec.derivedResponseIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h) :
    PlusIOSegmentedFamily F K :=
  ofProblemWithConcreteNodeEncoders problem hchar
    (alphaC ω) (gamma ω) (alphaM ω)
    requests responses outMem progIO_capacity memIO_capacity

end PlusIOSegmentedFamily

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.NodeEncoding.computeNodeEncode_labelOf_eq
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.computeFullRowEncode_injective
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.computeNodeEncode_ignores_mr1
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.memoryFullRowEncode_injective
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.memoryNodeEncode_labelOf_eq
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.memoryNodeEncode_ignores_mem
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.stateTagChar_of_ringChar_gt_eleven
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.ringChar_gt_eleven_of_stateTagChar
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.stateTagChar_iff_ringChar_gt_eleven
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.goldilocks_p_gt_eleven
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.zmod17_stateTagChar
#print axioms Nock.NockVMROM.Thm54.NodeEncoding.computeNodeEncode_s0_ne_cons
#print axioms Nock.NockVMROM.Thm54.PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders
#print axioms Nock.NockVMROM.Thm54.PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncodersScopedP7
#print axioms Nock.NockVMROM.Thm54.PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncodersAtJointCoins
