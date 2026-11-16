import Nock.NockVMROM.Thm54.OptimizedComputeCoreInventory

/-!
# Author-approved normalized compute-row codec

This module implements the first concrete part of the author-approved R6 correctness delta.
It is not claimed to be paper-enumerated: the paper gives only aggregate counts.

The normalized row removes every materialized memory-record field.  On an accepted
`ComputeTable.Vcomp` row all three records are determined by the label, decomposition, state,
timestamp challenge, and line nonce.  The decoder reconstructs
those records by the exact equations used by `ComputeTable.memBlk`.

The resulting extension payload has exactly 58 `K` scalars:

* 12 label fingerprints × 3 coordinates = 36;
* 6 formula-decomposition fingerprints × 3 coordinates = 18;
* `ln_prev`, `ln`, `cons_inv`, `inv_gen` = 4.

The 13 base-field slots are:

* 11 state selectors;
* the state-derived walk fanout;
* the state-derived memory-request count.

The last two are structural summaries used by the future walk/IO fold.  `BaseWellFormed` makes
them load-bearing and rejects malformed encodings.  This file proves exact row round-tripping on
`Vcomp`; it does not yet claim that these slots suffice for the complete walk/program-IO trace.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeCodec

open Nock
open Nock.ComputeTable

noncomputable section

variable {F K : Type*} [Field F] [Field K]

/-! ## Typed physical columns -/

/-- Eleven selectors followed by two structural summaries. -/
abbrev BaseColumn := Fin 11 ⊕ Fin 2

/-- Fifty-four fingerprint coordinates followed by four scalar witnesses/nonces. -/
abbrev ExtensionColumn :=
  (Fin 12 × Fin 3) ⊕ ((Fin 6 × Fin 3) ⊕ Fin 4)

theorem baseColumn_card : Fintype.card BaseColumn = 13 := by
  simp

theorem extensionColumn_card : Fintype.card ExtensionColumn = 58 := by
  simp

/-- The normalized physical row: exactly thirteen `F` values and fifty-eight `K` values. -/
structure Row (F K : Type*) where
  base : BaseColumn → F
  extension : ExtensionColumn → K

/-! ## State selectors and the two structural base slots -/

/-- Fixed selector index for each of the eleven compute states. -/
def stateIndex : State → Fin 11
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
  | .cons => 10

theorem stateIndex_injective : Function.Injective stateIndex := by
  intro a b h
  cases a <;> cases b <;> simp [stateIndex] at h ⊢

/-- The two structural base summaries. -/
def encodeBase (st : State) : BaseColumn → F
  | .inl i => if i = stateIndex st then 1 else 0
  | .inr 0 => (fanoutComp st : F)
  | .inr 1 => (Nock.Framework.recordCount st : F)

/-- Deterministic decoding of a selector vector.  Malformed vectors are subsequently rejected by
`BaseWellFormed`; this function is total only so `decode` is total. -/
noncomputable def decodeState (base : BaseColumn → F) : State :=
  letI := Classical.decEq F
  if base (.inl (stateIndex .s0)) = 1 then .s0 else
  if base (.inl (stateIndex .s1)) = 1 then .s1 else
  if base (.inl (stateIndex .s2)) = 1 then .s2 else
  if base (.inl (stateIndex .s3)) = 1 then .s3 else
  if base (.inl (stateIndex .s4)) = 1 then .s4 else
  if base (.inl (stateIndex .s5)) = 1 then .s5 else
  if base (.inl (stateIndex .s6)) = 1 then .s6 else
  if base (.inl (stateIndex .s7)) = 1 then .s7 else
  if base (.inl (stateIndex .s8)) = 1 then .s8 else
  if base (.inl (stateIndex .s9)) = 1 then .s9 else
  .cons

theorem decodeState_encodeBase (st : State) :
    decodeState (encodeBase (F := F) st) = st := by
  cases st <;> simp [decodeState, encodeBase, stateIndex]

/-- Exact well-formedness of all thirteen base slots. -/
def BaseWellFormed (base : BaseColumn → F) : Prop :=
  base = encodeBase (decodeState base)

theorem encodeBase_wellFormed (st : State) :
    BaseWellFormed (encodeBase (F := F) st) := by
  simp [BaseWellFormed, decodeState_encodeBase]

theorem baseWellFormed_selectors (base : BaseColumn → F)
    (h : BaseWellFormed base) (i : Fin 11) :
    base (.inl i) = if i = stateIndex (decodeState base) then 1 else 0 := by
  rw [h]
  simp [encodeBase, decodeState_encodeBase]

theorem baseWellFormed_fanout (base : BaseColumn → F)
    (h : BaseWellFormed base) :
    base (.inr 0) = (fanoutComp (decodeState base) : F) := by
  rw [h]
  simp [encodeBase, decodeState_encodeBase]

theorem baseWellFormed_recordCount (base : BaseColumn → F)
    (h : BaseWellFormed base) :
    base (.inr 1) =
      (Nock.Framework.recordCount (decodeState base) : F) := by
  rw [h]
  simp [encodeBase, decodeState_encodeBase]

/-! ## Fingerprint blocks -/

/-- Coordinate projection of one NPR fingerprint. -/
def fpCoordinate (x : FP K) : Fin 3 → K
  | 0 => x.size
  | 1 => x.dyck
  | 2 => x.leaf

/-- Reassemble one fingerprint from its three physical coordinates. -/
def fpOfCoordinates (x : Fin 3 → K) : FP K :=
  ⟨x 0, x 1, x 2⟩

omit [Field K] in
@[simp] theorem fpOfCoordinates_fpCoordinate (x : FP K) :
    fpOfCoordinates (fpCoordinate x) = x := by
  cases x
  rfl

/-- The twelve label fingerprints in their fixed physical order
`s,f,e,sf1_s,sf1_f,sf1_e,sf2_s,sf2_f,sf2_e,sf3_s,sf3_f,sf3_e`. -/
def pubFingerprint (pub : Pub K) : Fin 12 → FP K
  | 0 => pub.s
  | 1 => pub.f
  | 2 => pub.e
  | 3 => pub.sf1_s
  | 4 => pub.sf1_f
  | 5 => pub.sf1_e
  | 6 => pub.sf2_s
  | 7 => pub.sf2_f
  | 8 => pub.sf2_e
  | 9 => pub.sf3_s
  | 10 => pub.sf3_f
  | 11 => pub.sf3_e

/-- The six decomposition fingerprints in order
`f_h,f_t,f_th,f_tt,f_tth,f_ttt`. -/
def decFingerprint (dec : Dec K) : Fin 6 → FP K
  | 0 => dec.f_h
  | 1 => dec.f_t
  | 2 => dec.f_th
  | 3 => dec.f_tt
  | 4 => dec.f_tth
  | 5 => dec.f_ttt

/-- Encode all fifty-eight extension values. -/
def encodeExtension (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    ExtensionColumn → K
  | .inl (r, c) => fpCoordinate (pubFingerprint pub r) c
  | .inr (.inl (r, c)) => fpCoordinate (decFingerprint dec r) c
  | .inr (.inr 0) => pub.ln_prev
  | .inr (.inr 1) => pub.ln
  | .inr (.inr 2) => ex.consInv
  | .inr (.inr 3) => ex.invGen

/-- Decode one label fingerprint role from the physical extension columns. -/
def decodePubFingerprint (x : ExtensionColumn → K) (r : Fin 12) : FP K :=
  fpOfCoordinates (fun c => x (.inl (r, c)))

/-- Decode one formula-decomposition role. -/
def decodeDecFingerprint (x : ExtensionColumn → K) (r : Fin 6) : FP K :=
  fpOfCoordinates (fun c => x (.inr (.inl (r, c))))

/-- Decode the complete decomposition row. -/
def decodeDec (x : ExtensionColumn → K) : Dec K where
  f_h := decodeDecFingerprint x 0
  f_t := decodeDecFingerprint x 1
  f_th := decodeDecFingerprint x 2
  f_tt := decodeDecFingerprint x 3
  f_tth := decodeDecFingerprint x 4
  f_ttt := decodeDecFingerprint x 5

/-- Decode the two inverse witnesses. -/
def decodeExtra (x : ExtensionColumn → K) : Extra K where
  consInv := x (.inr (.inr 2))
  invGen := x (.inr (.inr 3))

omit [Field K] in
@[simp] theorem decodeDec_encodeExtension (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    decodeDec (encodeExtension pub dec ex) = dec := by
  cases dec
  simp [decodeDec, decodeDecFingerprint, encodeExtension, decFingerprint,
    fpOfCoordinates, fpCoordinate]

omit [Field K] in
@[simp] theorem decodeExtra_encodeExtension (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    decodeExtra (encodeExtension pub dec ex) = ex := by
  cases ex
  rfl

/-! ## Record reconstruction -/

/-- The always-present first request record. -/
def expectedMr1 (inp : Inputs K) (pub : Pub K) (dec : Dec K) : MemRec K :=
  ⟨pub.f, dec.f_t, 3, pub.ln_prev * inp.α⟩

/-- The state-determined second request record. -/
def expectedMr2 (inp : Inputs K) (pub : Pub K) (dec : Dec K) : MemRec K :=
  match pub.state with
  | .s0 => ⟨pub.s, pub.e, dec.f_t.leaf, pub.ln_prev * inp.α ^ 2⟩
  | .s2 | .s5 | .s6 | .s7 | .s8 | .s9 =>
      ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
  | _ => MemRec.zero

/-- The state-determined third request record. -/
def expectedMr3 (inp : Inputs K) (pub : Pub K) (dec : Dec K) : MemRec K :=
  match pub.state with
  | .s6 => ⟨dec.f_tt, dec.f_tth, 2, pub.ln_prev * inp.α ^ 3⟩
  | .s9 => ⟨pub.sf1_e, pub.sf2_f, dec.f_th.leaf, pub.ln_prev * inp.α ^ 3⟩
  | _ => MemRec.zero

/-- The record-free label payload, with deterministic records reconstructed afterwards. -/
def decodePubCore (base : BaseColumn → F) (x : ExtensionColumn → K) : Pub K where
  state := decodeState base
  s := decodePubFingerprint x 0
  f := decodePubFingerprint x 1
  e := decodePubFingerprint x 2
  sf1_s := decodePubFingerprint x 3
  sf1_f := decodePubFingerprint x 4
  sf1_e := decodePubFingerprint x 5
  sf2_s := decodePubFingerprint x 6
  sf2_f := decodePubFingerprint x 7
  sf2_e := decodePubFingerprint x 8
  sf3_s := decodePubFingerprint x 9
  sf3_f := decodePubFingerprint x 10
  sf3_e := decodePubFingerprint x 11
  ln_prev := x (.inr (.inr 0))
  ln := x (.inr (.inr 1))
  mr1 := MemRec.zero
  mr2 := MemRec.zero
  mr3 := MemRec.zero

/-- Decode a complete compute row, regenerating all three memory records. -/
def decodePub (inp : Inputs K) (base : BaseColumn → F)
    (x : ExtensionColumn → K) : Pub K :=
  let dec := decodeDec x
  let core := decodePubCore base x
  { core with
    mr1 := expectedMr1 inp core dec
    mr2 := expectedMr2 inp core dec
    mr3 := expectedMr3 inp core dec }

/-- Normalize one ordinary compute row.  Memory records are intentionally not copied. -/
def encode (pub : Pub K) (dec : Dec K) (ex : Extra K) : Row F K where
  base := encodeBase pub.state
  extension := encodeExtension pub dec ex

/-- Decode one normalized row into the ordinary table row and auxiliary witnesses. -/
def decode (inp : Inputs K) (row : Row F K) : Pub K × Dec K × Extra K :=
  (decodePub inp row.base row.extension, decodeDec row.extension,
    decodeExtra row.extension)

theorem records_eq_expected_of_vcomp {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (h : Vcomp inp pub dec) :
    pub.mr1 = expectedMr1 inp pub dec ∧
      pub.mr2 = expectedMr2 inp pub dec ∧
      pub.mr3 = expectedMr3 inp pub dec := by
  obtain ⟨_, hmr1, _, hmem, _⟩ := h
  refine ⟨hmr1, ?_⟩
  cases hs : pub.state <;>
    simp only [memBlk, hs] at hmem <;>
    simp only [expectedMr2, expectedMr3, hs] <;>
    aesop

theorem decodePub_encode_of_vcomp {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {ex : Extra K} (h : Vcomp inp pub dec) :
    decodePub (F := F) inp (encodeBase pub.state) (encodeExtension pub dec ex) =
      { pub with sf1_st := none, sf2_st := none, sf3_st := none, certC? := none } := by
  obtain ⟨hmr1, hmr2, hmr3⟩ := records_eq_expected_of_vcomp h
  cases pub
  cases dec
  simp [decodePub, decodePubCore, decodePubFingerprint, encodeExtension,
    pubFingerprint, fpOfCoordinates, fpCoordinate, decodeState_encodeBase,
    decodeDec, decodeDecFingerprint, decFingerprint, expectedMr1, expectedMr2,
    expectedMr3] at hmr1 hmr2 hmr3 ⊢
  simp_all

/-- Exact normalized-codec roundtrip on every accepted compute row. -/
theorem decode_encode_of_vcomp {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {ex : Extra K} (h : Vcomp inp pub dec) :
    decode inp (encode (F := F) pub dec ex) =
      ({ pub with sf1_st := none, sf2_st := none, sf3_st := none, certC? := none }, dec, ex) := by
  simp [decode, encode, decodePub_encode_of_vcomp h]

omit [Field K] in
/-- Every encoded accepted row has all thirteen base slots well formed. -/
theorem encoded_base_wellFormed {pub : Pub K} {dec : Dec K} {ex : Extra K} :
    BaseWellFormed (encode (F := F) pub dec ex).base :=
  encodeBase_wellFormed pub.state

/-- A malformed selector vector cannot equal the encoding of its decoded state. -/
theorem malformed_base_rejected {base : BaseColumn → F}
    (h : base ≠ encodeBase (decodeState base)) :
    ¬ BaseWellFormed base := h

/-- Concrete malformed-row rejection: an all-zero base assignment cannot satisfy the canonical
selector/summary equations. -/
theorem zero_base_rejected :
    ¬ BaseWellFormed (fun _ : BaseColumn => (0 : F)) := by
  intro h
  have hs := baseWellFormed_selectors
    (fun _ : BaseColumn => (0 : F)) h
    (stateIndex (decodeState (fun _ : BaseColumn => (0 : F))))
  simp at hs

/-! ## Fixed endpoint-mask Base13 encoding

The production masked template retains the eleven selector slots and repurposes the two summary
slots as verifier-fixed first/last selectors.  Structural fanout and request count are derived
directly from the decoded one-hot state and therefore need no committed summary columns.
-/

def encodeBaseWithEndpointMasks (st : State) (isFirst isLast : F) :
    BaseColumn → F
  | .inl i => if i = stateIndex st then 1 else 0
  | .inr 0 => isFirst
  | .inr 1 => isLast

theorem decodeState_encodeBaseWithEndpointMasks (st : State) (isFirst isLast : F) :
    decodeState (encodeBaseWithEndpointMasks st isFirst isLast) = st := by
  cases st <;>
    simp [decodeState, encodeBaseWithEndpointMasks, stateIndex]

@[simp] theorem encodeBaseWithEndpointMasks_first
    (st : State) (isFirst isLast : F) :
    encodeBaseWithEndpointMasks st isFirst isLast (.inr 0) = isFirst :=
  rfl

@[simp] theorem encodeBaseWithEndpointMasks_last
    (st : State) (isFirst isLast : F) :
    encodeBaseWithEndpointMasks st isFirst isLast (.inr 1) = isLast :=
  rfl

/-- Fanout is a deterministic function of the one-hot-decoded state, not a trace slot. -/
def derivedFanout (base : BaseColumn → F) : F :=
  fanoutComp (decodeState base)

/-- Request count is likewise a deterministic function of the one-hot-decoded state. -/
def derivedRecordCount (base : BaseColumn → F) : F :=
  Nock.Framework.recordCount (decodeState base)

theorem derived_structural_values_of_endpoint_encoding
    (st : State) (isFirst isLast : F) :
    derivedFanout (encodeBaseWithEndpointMasks st isFirst isLast) = (fanoutComp st : F) ∧
      derivedRecordCount (encodeBaseWithEndpointMasks st isFirst isLast) =
        (Nock.Framework.recordCount st : F) := by
  simp [derivedFanout, derivedRecordCount, decodeState_encodeBaseWithEndpointMasks]

/-- Replace only the two base summary slots of an existing normalized row. -/
def Row.withEndpointMasks (row : Row F K) (isFirst isLast : F) : Row F K where
  base := encodeBaseWithEndpointMasks (decodeState row.base) isFirst isLast
  extension := row.extension

theorem Row.withEndpointMasks_state (row : Row F K) (isFirst isLast : F) :
    decodeState (row.withEndpointMasks isFirst isLast).base = decodeState row.base :=
  decodeState_encodeBaseWithEndpointMasks _ _ _

theorem Row.withEndpointMasks_extension (row : Row F K) (isFirst isLast : F) :
    (row.withEndpointMasks isFirst isLast).extension = row.extension :=
  rfl

#print axioms decodeState_encodeBase
#print axioms decodeDec_encodeExtension
#print axioms records_eq_expected_of_vcomp
#print axioms decode_encode_of_vcomp
#print axioms malformed_base_rejected
#print axioms zero_base_rejected
#print axioms decodeState_encodeBaseWithEndpointMasks
#print axioms derived_structural_values_of_endpoint_encoding
#print axioms Row.withEndpointMasks_state

end
end OptimizedComputeCodec
end Nock.NockVMROM.Thm54
