import Nock.NockVMROM.Thm54.OptimizedMemoryCoreInventory

/-!
# Typed `6/56` optimized memory row codec

This is the author-selected sharing map for the memory source core.  It stores the four `Vmem`
state selectors and fixed first/last masks in six base-field roles.  Hosted walk roles `34`/`35`/`36` are not reused.

The codec is position-free: its inputs are one exact row and local/aggregate scalar carriers.  It
contains no committed-line pointer, positional lookup, or back-reference.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemoryCodec

open Nock
open OptimizedMemoryCoreInventory

noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

local instance : DecidableEq F := Classical.decEq F

/-- One semantic source row before sharing.  All fields are acceptance-bearing roles from the
inventory; there is no residual or unnamed payload. -/
structure SemanticRow (F K : Type*) where
  state : MemoryTable.MState
  isFirst : F
  isLast : F
  table : MemoryTablePayloadRole → K
  walk : ForestWalkRole → K
  sampledIO : SampledMemoryIORole → K
  selectorMirror : StateSelectorMirrorRole → K
  walkInv : K

/-- Physical typed row at the selected source fingerprint. -/
structure EncodedRow (F K : Type*) where
  base : Fin 6 → F
  extension : ExtensionRole → K

@[ext] theorem SemanticRow.ext'
    {a b : SemanticRow F K}
    (hstate : a.state = b.state)
    (hfirst : a.isFirst = b.isFirst)
    (hlast : a.isLast = b.isLast)
    (htable : a.table = b.table)
    (hwalk : a.walk = b.walk)
    (hio : a.sampledIO = b.sampledIO)
    (hmirror : a.selectorMirror = b.selectorMirror)
    (hinv : a.walkInv = b.walkInv) : a = b := by
  cases a
  cases b
  simp_all

@[ext] theorem EncodedRow.ext'
    {a b : EncodedRow F K}
    (hbase : a.base = b.base)
    (hext : a.extension = b.extension) : a = b := by
  cases a
  cases b
  simp_all

def stateIndex : MemoryTable.MState → Fin 4
  | .decompose => 0
  | .halt => 1
  | .read_root => 2
  | .verify_child => 3

def stateSelector (s : MemoryTable.MState) (i : Fin 4) : F :=
  if i = stateIndex s then 1 else 0

def stateSlot (i : Fin 4) : Fin 6 := ⟨i, by omega⟩

def encodeBase (r : SemanticRow F K) : Fin 6 → F
  | ⟨i, hi⟩ =>
      if h4 : i < 4 then stateSelector r.state ⟨i, h4⟩
      else if i = 4 then r.isFirst else r.isLast

def encodeExtension (r : SemanticRow F K) : ExtensionRole → K
  | .inl i => r.table i
  | .inr (.inl i) => r.walk i
  | .inr (.inr (.inl i)) => r.sampledIO i
  | .inr (.inr (.inr (.inl i))) => r.selectorMirror i
  | .inr (.inr (.inr (.inr _))) => r.walkInv

/-- Explicit author-selected `6/56` row encoder. -/
def encode (r : SemanticRow F K) : EncodedRow F K :=
  ⟨encodeBase r, encodeExtension r⟩

/-- Decoder for the four one-hot controls.  The final branch is deliberately total; accepted-row
roundtrip below proves that malformed controls cannot masquerade as another state. -/
def decodeState (r : EncodedRow F K) : MemoryTable.MState :=
  if r.base 0 = 1 then .decompose
  else if r.base 1 = 1 then .halt
  else if r.base 2 = 1 then .read_root
  else .verify_child

def decode (r : EncodedRow F K) : SemanticRow F K where
  state := decodeState r
  isFirst := r.base 4
  isLast := r.base 5
  table := fun i => r.extension (.inl i)
  walk := fun i => r.extension (.inr (.inl i))
  sampledIO := fun i => r.extension (.inr (.inr (.inl i)))
  selectorMirror := fun i => r.extension (.inr (.inr (.inr (.inl i))))
  walkInv := r.extension (.inr (.inr (.inr (.inr 0))))

@[simp] theorem decodeState_encode (r : SemanticRow F K) :
    decodeState (encode r) = r.state := by
  rcases r with ⟨state, isFirst, isLast, table, walk, sampledIO, selectorMirror, walkInv⟩
  cases state <;>
    simp [decodeState, encode, encodeBase, stateSelector, stateIndex]

/-- Unconditional source-row roundtrip.  Every role is reconstructible from its physical host. -/
@[simp] theorem decode_encode (r : SemanticRow F K) :
    decode (encode r) = r := by
  apply SemanticRow.ext'
  · exact decodeState_encode r
  · rfl
  · rfl
  · funext i
    rfl
  · funext i
    rfl
  · funext i
    rfl
  · funext i
    rfl
  · rfl

theorem encode_injective : Function.Injective (encode (F := F) (K := K)) := by
  intro a b h
  rw [← decode_encode a, ← decode_encode b, h]

/-- Exact accepted control surface: one of all four `Vmem` states plus boolean fixed masks. -/
def AcceptedControls (r : EncodedRow F K) : Prop :=
  (∃ s : MemoryTable.MState, ∀ i : Fin 4, r.base (stateSlot i) = stateSelector s i) ∧
    r.base 4 * (r.base 4 - 1) = 0 ∧
    r.base 5 * (r.base 5 - 1) = 0

theorem encode_controls_accepted (r : SemanticRow F K)
    (hfirst : r.isFirst * (r.isFirst - 1) = 0)
    (hlast : r.isLast * (r.isLast - 1) = 0) :
    AcceptedControls (encode r) := by
  refine ⟨⟨r.state, ?_⟩, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [encode, encodeBase, stateSlot]
  · simpa [encode, encodeBase] using hfirst
  · simpa [encode, encodeBase] using hlast

theorem accepted_decodeState (r : EncodedRow F K)
    (h : AcceptedControls r) :
    ∀ i : Fin 4, r.base (stateSlot i) = stateSelector (decodeState r) i := by
  obtain ⟨⟨s, hs⟩, -, -⟩ := h
  have h0 : r.base 0 = stateSelector s 0 := by simpa [stateSlot] using hs 0
  have h1 : r.base 1 = stateSelector s 1 := by simpa [stateSlot] using hs 1
  have h2 : r.base 2 = stateSelector s 2 := by simpa [stateSlot] using hs 2
  have hd : decodeState r = s := by
    cases s with
    | decompose =>
        have hz : r.base 0 = 1 := by simpa [stateSelector, stateIndex] using h0
        rw [decodeState, if_pos hz]
    | halt =>
        have hz0 : r.base 0 = 0 := by simpa [stateSelector, stateIndex] using h0
        have hz1 : r.base 1 = 1 := by simpa [stateSelector, stateIndex] using h1
        have hn0 : r.base 0 ≠ 1 := by rw [hz0]; exact zero_ne_one
        rw [decodeState, if_neg hn0, if_pos hz1]
    | read_root =>
        have hz0 : r.base 0 = 0 := by simpa [stateSelector, stateIndex] using h0
        have hz1 : r.base 1 = 0 := by simpa [stateSelector, stateIndex] using h1
        have hz2 : r.base 2 = 1 := by simpa [stateSelector, stateIndex] using h2
        have hn0 : r.base 0 ≠ 1 := by rw [hz0]; exact zero_ne_one
        have hn1 : r.base 1 ≠ 1 := by rw [hz1]; exact zero_ne_one
        rw [decodeState, if_neg hn0, if_neg hn1, if_pos hz2]
    | verify_child =>
        have hz0 : r.base 0 = 0 := by simpa [stateSelector, stateIndex] using h0
        have hz1 : r.base 1 = 0 := by simpa [stateSelector, stateIndex] using h1
        have hz2 : r.base 2 = 0 := by simpa [stateSelector, stateIndex] using h2
        have hn0 : r.base 0 ≠ 1 := by rw [hz0]; exact zero_ne_one
        have hn1 : r.base 1 ≠ 1 := by rw [hz1]; exact zero_ne_one
        have hn2 : r.base 2 ≠ 1 := by rw [hz2]; exact zero_ne_one
        rw [decodeState, if_neg hn0, if_neg hn1, if_neg hn2]
  rw [hd]
  exact hs

/-- Accepted physical rows round-trip exactly, including all four states and both malformed-control
guards. -/
theorem encode_decode_of_accepted (r : EncodedRow F K)
    (h : AcceptedControls r) :
    encode (decode r) = r := by
  cases r with
  | mk base extension =>
      apply EncodedRow.ext'
      · funext i
        fin_cases i
        · change stateSelector (decodeState (⟨base, extension⟩ : EncodedRow F K)) 0 = base 0
          exact (accepted_decodeState (r := ⟨base, extension⟩) h 0).symm
        · change stateSelector (decodeState (⟨base, extension⟩ : EncodedRow F K)) 1 = base 1
          exact (accepted_decodeState (r := ⟨base, extension⟩) h 1).symm
        · change stateSelector (decodeState (⟨base, extension⟩ : EncodedRow F K)) 2 = base 2
          exact (accepted_decodeState (r := ⟨base, extension⟩) h 2).symm
        · change stateSelector (decodeState (⟨base, extension⟩ : EncodedRow F K)) 3 = base 3
          exact (accepted_decodeState (r := ⟨base, extension⟩) h 3).symm
        · rfl
        · rfl
      · funext i
        rcases i with i | i
        · rfl
        · rcases i with i | i
          · rfl
          · rcases i with i | i
            · rfl
            · rcases i with i | i
              · rfl
              · fin_cases i
                rfl

/-- The all-zero state vector is a compiled malformed-control rejection. -/
theorem all_zero_state_rejected (r : EncodedRow F K)
    (hzero : ∀ i : Fin 4, r.base (stateSlot i) = 0) :
    ¬ AcceptedControls r := by
  rintro ⟨⟨s, hs⟩, -, -⟩
  have hone := hs (stateIndex s)
  rw [stateSelector, if_pos rfl, hzero] at hone
  exact zero_ne_one hone

/-- A non-boolean first mask is rejected independently of every extension payload. -/
theorem malformed_first_mask_rejected (r : EncodedRow F K)
    (hbad : r.base 4 * (r.base 4 - 1) ≠ 0) :
    ¬ AcceptedControls r := by
  intro h
  exact hbad h.2.1

/-- A non-boolean last mask is rejected independently of every extension payload. -/
theorem malformed_last_mask_rejected (r : EncodedRow F K)
    (hbad : r.base 5 * (r.base 5 - 1) ≠ 0) :
    ¬ AcceptedControls r := by
  intro h
  exact hbad h.2.2

end
end OptimizedMemoryCodec
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCodec.decode_encode
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCodec.encode_injective
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCodec.encode_decode_of_accepted
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCodec.all_zero_state_rejected
