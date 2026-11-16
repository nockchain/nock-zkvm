import Nock.NockVMROM.Thm54.OptimizedComputeCodec

/-!
# Hybrid walk and program-IO overlay

**** overlay coords `0`/`1` remain walk `count`/`acc`; coords `2`/`3`/`4`
host `sf_state₁₋₃` (freed from walk `cur`/`cc`/`cm`, which are now in-gate RLCs).
The sampled accumulator stays at `sf3_f.leaf`, and the three inactive-safe sampled-denominator
witnesses stay in `sf3_e`.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeOverlay

open Nock
open Nock.ComputeTable
open OptimizedComputeCodec

noncomputable section

variable {F K : Type*} [Field F] [Field K]

/-- Nine live `K` values occupying the globally reconstructible `sf3_*` roles.
Until then they still carry walk `cur`/`cc`/`cm`. -/
structure OverlayValues (K : Type*) where
  walkCount : K
  walkAcc : K
  sf1_st : K
  sf2_st : K
  sf3_st : K
  ioAcc : K

structure SampledOverlayValues (K : Type*) extends OverlayValues K where
  denom0 : K
  denom1 : K
  denom2 : K

def overlayRoleA : State → Fin 12
  | .s0 => 3
  | .s1 => 2
  | .s2 => 3
  | .s3 | .s4 => 6
  | .s5 | .s6 | .s7 | .s8 | .s9 | .cons => 9

def overlayRoleB : State → Fin 12
  | .s0 => 4
  | .s1 => 3
  | .s2 => 4
  | .s3 | .s4 => 7
  | .s5 | .s6 | .s7 | .s8 | .s9 | .cons => 10

theorem overlayRoles_ne (st : State) : overlayRoleA st ≠ overlayRoleB st := by
  cases st <;> decide

def sampledOverlayA (v : SampledOverlayValues K) : FP K :=
  ⟨v.walkCount, v.walkAcc, v.sf1_st⟩

def overlayDenoms (v : SampledOverlayValues K) : FP K :=
  ⟨v.denom0, v.denom1, v.denom2⟩

/-- Encode walk count/acc, three `sf_state` tags, and four fixed sampled-IO values. -/
def sampledEncodeExtension (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : SampledOverlayValues K) : ExtensionColumn → K
  | .inl (r, c) =>
      if r = overlayRoleA pub.state then fpCoordinate (sampledOverlayA v) c
      else if r = overlayRoleB pub.state ∧ c = 0 then v.sf2_st
      else if r = overlayRoleB pub.state ∧ c = 1 then v.sf3_st
      else if r = 10 ∧ c = 2 then v.ioAcc
      else if r = 11 then fpCoordinate (overlayDenoms v) c
      else OptimizedComputeCodec.encodeExtension pub dec ex (.inl (r, c))
  | i => OptimizedComputeCodec.encodeExtension pub dec ex i

/-- Read all nine overlay values before restoring the table row. -/
def decodeSampledOverlay (base : BaseColumn → F)
    (x : ExtensionColumn → K) : SampledOverlayValues K :=
  let st := decodeState base
  let a := decodePubFingerprint x (overlayRoleA st)
  let b := decodePubFingerprint x (overlayRoleB st)
  let d := decodePubFingerprint x 11
  { toOverlayValues :=
      ⟨a.size, a.dyck, a.leaf, b.size, b.dyck, x (.inl (10, 2))⟩
    denom0 := d.size
    denom1 := d.dyck
    denom2 := d.leaf }

/-- Reconstruct the first active-state overwritten fingerprint. -/
def restoredA (base : BaseColumn → F) (x : ExtensionColumn → K) : FP K :=
  match decodeState base with
  | .s0 => 0
  | .s1 => decodeDecFingerprint x 1
  | .s2 => decodePubFingerprint x 0
  | .s3 | .s4 => 0
  | .s5 | .s6 | .s7 | .s8 | .s9 | .cons => 0

/-- Reconstruct the first two coordinates of the second active-state overwritten fingerprint. -/
def restoredB (base : BaseColumn → F) (x : ExtensionColumn → K) : FP K :=
  match decodeState base with
  | .s2 => decodeDecFingerprint x 2
  | _ => 0

/-- Reconstruct the fixed sampled-accumulator host coordinate `sf3_f.leaf`. -/
def restoredIOHost (base : BaseColumn → F) (x : ExtensionColumn → K) : K :=
  match decodeState base with
  | .s2 => (decodePubFingerprint x 8).leaf
  | _ => 0

/-- Reconstruct the fixed inactive-safe-denominator host `sf3_e`. -/
def restoredDenomHost (base : BaseColumn → F) (x : ExtensionColumn → K) : FP K :=
  match decodeState base with
  | .s2 => decodePubFingerprint x 2
  | _ => 0

/-- Restore every overwritten table coordinate before invoking the ordinary codec decoder. -/
def sampledRestoreExtension (base : BaseColumn → F)
    (x : ExtensionColumn → K) : ExtensionColumn → K
  | .inl (r, c) =>
      if r = overlayRoleA (decodeState base) then fpCoordinate (restoredA base x) c
      else if r = overlayRoleB (decodeState base) ∧ (c = 0 ∨ c = 1) then
        fpCoordinate (restoredB base x) c
      else if r = 10 ∧ c = 2 then restoredIOHost base x
      else if r = 11 then fpCoordinate (restoredDenomHost base x) c
      else x (.inl (r, c))
  | i => x i

/-- Recover `Option` tag from an overlay host (`nullStateTag` ↔ `none`). -/
noncomputable def optionTagOf (x : K) : Option K :=
  match Classical.decEq K x (ComputeTable.nullStateTag : K) with
  | isTrue _ => none
  | isFalse _ => some x

/-- Stamp overlay-hosted `sf*_st` onto a fingerprint-decoded `Pub`. -/
noncomputable def withOverlayTags (pub : Pub K) (v : OverlayValues K) : Pub K :=
  { pub with
    sf1_st := optionTagOf v.sf1_st
    sf2_st := optionTagOf v.sf2_st
    sf3_st := optionTagOf v.sf3_st }

/-- Encode a normalized table row together with live walk/IO values. -/
def sampledEncode (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : SampledOverlayValues K) : Row F K where
  base := OptimizedComputeCodec.encodeBase pub.state
  extension := sampledEncodeExtension pub dec ex v

/-- Decode the restored table row and the six overlaid values. -/
def sampledDecode (inp : Inputs K) (row : Row F K) :
    Pub K × Dec K × Extra K × SampledOverlayValues K :=
  let restored := sampledRestoreExtension row.base row.extension
  let v := decodeSampledOverlay row.base row.extension
  (withOverlayTags (decodePub inp row.base restored) v.toOverlayValues,
    decodeDec restored, decodeExtra restored, v)

omit [Field K] in
@[simp] theorem codec_encodeExtension_pub (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (r : Fin 12) (c : Fin 3) :
    OptimizedComputeCodec.encodeExtension pub dec ex (.inl (r, c)) =
      fpCoordinate (pubFingerprint pub r) c :=
  rfl

omit [Field K] in
@[simp] theorem decodeSampledOverlay_encode (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : SampledOverlayValues K) :
    decodeSampledOverlay (F := F) (OptimizedComputeCodec.encodeBase pub.state)
      (sampledEncodeExtension pub dec ex v) = v := by
  cases hs : pub.state <;>
    cases v <;>
    simp [hs, decodeSampledOverlay, decodePubFingerprint, sampledEncodeExtension,
      overlayRoleA, overlayRoleB, sampledOverlayA, overlayDenoms,
      fpOfCoordinates, fpCoordinate, decodeState_encodeBase]

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
theorem sampledRestore_encode_of_vcomp {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {ex : Extra K} {v : SampledOverlayValues K} (h : Vcomp inp pub dec) :
    sampledRestoreExtension (OptimizedComputeCodec.encodeBase (F := F) pub.state)
        (sampledEncodeExtension pub dec ex v) =
      OptimizedComputeCodec.encodeExtension pub dec ex := by
  obtain ⟨_, _, _, _, heval⟩ := h
  cases hs : pub.state <;>
    simp only [evalV, hs] at heval
  all_goals
    funext i
    rcases i with ⟨r, c⟩ | i
    · fin_cases r <;> fin_cases c <;>
        simp [sampledRestoreExtension, sampledEncodeExtension, restoredA, restoredB, restoredIOHost,
          restoredDenomHost, overlayRoleA, overlayRoleB, decodeState_encodeBase,
          OptimizedComputeCodec.encodeExtension, decodePubFingerprint,
          pubFingerprint, fpOfCoordinates, fpCoordinate,
          hs, sfz1, sfz2, sfz3] at heval ⊢ <;>
        aesop
    · simp [sampledRestoreExtension, sampledEncodeExtension]

/-- Exact roundtrip of the shared 13/58 overlay on every accepted compute row. -/
theorem sampledDecode_encode_of_vcomp {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {ex : Extra K} {v : SampledOverlayValues K} (h : Vcomp inp pub dec) :
    sampledDecode inp (sampledEncode (F := F) pub dec ex v) =
      (withOverlayTags
        { pub with sf1_st := none, sf2_st := none, sf3_st := none, certC? := none }
          v.toOverlayValues,
        dec, ex, v) := by
  simp [sampledDecode, sampledEncode, sampledRestore_encode_of_vcomp h,
    OptimizedComputeCodec.decodePub_encode_of_vcomp h, decodeSampledOverlay_encode]


def overlayA (v : OverlayValues K) : FP K :=
  ⟨v.walkCount, v.walkAcc, v.sf1_st⟩

def overlayB (v : OverlayValues K) : FP K :=
  ⟨v.sf2_st, v.sf3_st, v.ioAcc⟩

def encodeExtension (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : OverlayValues K) : ExtensionColumn → K
  | .inl (r, c) =>
      if r = overlayRoleA pub.state then fpCoordinate (overlayA v) c
      else if r = overlayRoleB pub.state then fpCoordinate (overlayB v) c
      else OptimizedComputeCodec.encodeExtension pub dec ex (.inl (r, c))
  | i => OptimizedComputeCodec.encodeExtension pub dec ex i

def decodeOverlay (base : BaseColumn → F) (x : ExtensionColumn → K) : OverlayValues K :=
  let st := decodeState base
  let a := decodePubFingerprint x (overlayRoleA st)
  let b := decodePubFingerprint x (overlayRoleB st)
  ⟨a.size, a.dyck, a.leaf, b.size, b.dyck, b.leaf⟩

def restoreExtension (base : BaseColumn → F)
    (x : ExtensionColumn → K) : ExtensionColumn → K
  | .inl (r, c) =>
      if r = overlayRoleA (decodeState base) then fpCoordinate (restoredA base x) c
      else if r = overlayRoleB (decodeState base) then fpCoordinate (restoredB base x) c
      else x (.inl (r, c))
  | i => x i

def encode (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : OverlayValues K) : Row F K where
  base := OptimizedComputeCodec.encodeBase pub.state
  extension := encodeExtension pub dec ex v

def decode (inp : Inputs K) (row : Row F K) :
    Pub K × Dec K × Extra K × OverlayValues K :=
  let restored := restoreExtension row.base row.extension
  let v := decodeOverlay row.base row.extension
  (withOverlayTags (decodePub inp row.base restored) v, decodeDec restored,
    decodeExtra restored, v)

omit [Field K] in
@[simp] theorem decodeOverlay_encode (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : OverlayValues K) :
    decodeOverlay (F := F) (OptimizedComputeCodec.encodeBase pub.state)
      (encodeExtension pub dec ex v) = v := by
  cases hs : pub.state <;>
    cases v <;>
    simp [hs, decodeOverlay, decodePubFingerprint, encodeExtension, overlayRoleA, overlayRoleB,
      overlayA, overlayB, fpOfCoordinates, fpCoordinate, decodeState_encodeBase]

theorem restoredA_encode_of_vcomp {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {ex : Extra K} {v : OverlayValues K} (h : Vcomp inp pub dec) :
    restoredA (F := F) (OptimizedComputeCodec.encodeBase pub.state)
        (encodeExtension pub dec ex v) =
      pubFingerprint pub (overlayRoleA pub.state) := by
  obtain ⟨_, _, _, _, heval⟩ := h
  cases hs : pub.state <;>
    simp only [evalV, hs] at heval <;>
    simp [restoredA, hs, decodeState_encodeBase, decodeDecFingerprint,
      decodePubFingerprint, encodeExtension, pubFingerprint,
      fpOfCoordinates, fpCoordinate, sfz1, sfz2, sfz3] at heval ⊢ <;>
    aesop

theorem restoredB_encode_of_vcomp {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {ex : Extra K} {v : OverlayValues K} (h : Vcomp inp pub dec) :
    restoredB (F := F) (OptimizedComputeCodec.encodeBase pub.state)
        (encodeExtension pub dec ex v) =
      pubFingerprint pub (overlayRoleB pub.state) := by
  obtain ⟨_, _, _, _, heval⟩ := h
  cases hs : pub.state <;>
    simp only [evalV, hs] at heval <;>
    simp [restoredB, decodeState_encodeBase, decodeDecFingerprint,
      encodeExtension, pubFingerprint, fpOfCoordinates, sfz1, sfz2, sfz3] at heval ⊢ <;>
    aesop

theorem restore_encode_of_vcomp {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {ex : Extra K} {v : OverlayValues K} (h : Vcomp inp pub dec) :
    restoreExtension (OptimizedComputeCodec.encodeBase (F := F) pub.state)
        (encodeExtension pub dec ex v) =
      OptimizedComputeCodec.encodeExtension pub dec ex := by
  have hA := restoredA_encode_of_vcomp (F := F) (ex := ex) (v := v) h
  have hB := restoredB_encode_of_vcomp (F := F) (ex := ex) (v := v) h
  funext i
  rcases i with ⟨r, c⟩ | i
  · by_cases ha : r = overlayRoleA pub.state
    · subst r
      simp [restoreExtension, decodeState_encodeBase, hA, pubFingerprint, fpCoordinate]
    · by_cases hb : r = overlayRoleB pub.state
      · subst r
        have hba : overlayRoleB pub.state ≠ overlayRoleA pub.state :=
          (overlayRoles_ne pub.state).symm
        simp [restoreExtension, decodeState_encodeBase,
          hba, hB, pubFingerprint, fpCoordinate]
      · simp [restoreExtension, encodeExtension, decodeState_encodeBase, ha, hb]
  · simp [restoreExtension, encodeExtension]

theorem decode_encode_of_vcomp {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {ex : Extra K} {v : OverlayValues K} (h : Vcomp inp pub dec) :
    decode inp (encode (F := F) pub dec ex v) =
      (withOverlayTags
        { pub with sf1_st := none, sf2_st := none, sf3_st := none, certC? := none } v,
        dec, ex, v) := by
  simp [decode, encode, restore_encode_of_vcomp h,
    OptimizedComputeCodec.decodePub_encode_of_vcomp h, decodeOverlay_encode]

/-- The physical extension count remains exactly 58 after sharing. -/
theorem extensionColumn_card : Fintype.card ExtensionColumn = 58 :=
  OptimizedComputeCodec.extensionColumn_card

#print axioms decodeSampledOverlay_encode
#print axioms sampledRestore_encode_of_vcomp
#print axioms sampledDecode_encode_of_vcomp
#print axioms decodeOverlay_encode
#print axioms restore_encode_of_vcomp
#print axioms decode_encode_of_vcomp

end
end OptimizedComputeOverlay
end Nock.NockVMROM.Thm54
