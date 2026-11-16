import Nock.NockVMROM.Thm54.OptimizedComputeOverlay

/-!
# The un-hosted 309 codec

**  Nothing existing is edited.**

The deployed `OptimizedComputeOverlay.sampledEncodeExtension` overwrites coordinates `0`/`1` of
the state-dependent fingerprint role `overlayRoleA st` with the walk `count` / `acc`, and
`sampledRestoreExtension` / `restoredA` reconstruct the overwritten fingerprint.  At width 309:

* `sampledEncodeExtension309` does **not** overwrite role-A coordinates `0`/`1` (they carry the
  genuine fingerprint coordinate); coordinate `2` still hosts `sf1_st`;
* `sampledRestoreExtension309` is the **identity** at role-A coordinates `0`/`1`;
* `walkCount` / `walkAcc` are emitted in the two new `𝕂` columns (`Row309.walk`, physical
  `303..305` / `306..308`);
* the role-B tag hosts (`sf2_st`, `sf3_st`), `ioAcc` (role `10.2`) and the three denominators
  (role `11`) are unchanged.
-/

namespace Nock.NockVMROM.Thm54
namespace Unhosted309

open Nock
open Nock.ComputeTable
open OptimizedComputeCodec
open OptimizedComputeOverlay

noncomputable section

variable {F K : Type*} [Field F] [Field K]
set_option linter.unusedSectionVars false

/-- One physical row at width 309: the deployed 13/58 row plus the two walk `𝕂` columns. -/
structure Row309 (F K : Type*) where
  row : Row F K
  walk : Fin 2 → K

/-- **`sampledEncodeExtension309`**: as deployed, except role-A coordinates `0`/`1` carry the
genuine fingerprint (no walk overwrite). -/
def sampledEncodeExtension309 (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : SampledOverlayValues K) : ExtensionColumn → K
  | .inl (r, c) =>
      if r = overlayRoleA pub.state ∧ c ≠ 2 then
        OptimizedComputeCodec.encodeExtension pub dec ex (.inl (r, c))
      else sampledEncodeExtension pub dec ex v (.inl (r, c))
  | i => sampledEncodeExtension pub dec ex v i

/-- **`sampledRestoreExtension309`**: the identity at role-A coordinates `0`/`1`. -/
def sampledRestoreExtension309 (base : BaseColumn → F)
    (x : ExtensionColumn → K) : ExtensionColumn → K
  | .inl (r, c) =>
      if r = overlayRoleA (decodeState base) ∧ c ≠ 2 then x (.inl (r, c))
      else sampledRestoreExtension base x (.inl (r, c))
  | i => sampledRestoreExtension base x i

/-- **`sampledEncode309`**: the row and the two walk columns. -/
def sampledEncode309 (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : SampledOverlayValues K) : Row309 F K where
  row := ⟨OptimizedComputeCodec.encodeBase pub.state, sampledEncodeExtension309 pub dec ex v⟩
  walk := ![v.walkCount, v.walkAcc]

/-- Read the overlay at 309: `walkCount` / `walkAcc` from the walk columns, the rest as
deployed. -/
def decodeSampledOverlay309 (row : Row309 F K) : SampledOverlayValues K :=
  let v := decodeSampledOverlay row.row.base row.row.extension
  { v with toOverlayValues := { v.toOverlayValues with
      walkCount := row.walk 0, walkAcc := row.walk 1 } }

/-- Decode at 309. -/
def sampledDecode309 (inp : Inputs K) (row : Row309 F K) :
    Pub K × Dec K × Extra K × SampledOverlayValues K :=
  let restored := sampledRestoreExtension309 row.row.base row.row.extension
  let v := decodeSampledOverlay309 row
  (withOverlayTags (decodePub inp row.row.base restored) v.toOverlayValues,
    decodeDec restored, decodeExtra restored, v)

/-- The two encodings differ only at role-A coordinates `0`/`1`. -/
theorem sampledEncodeExtension309_eq_of_not_host (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : SampledOverlayValues K) (i : ExtensionColumn)
    (hi : ∀ r c, i = .inl (r, c) → ¬ (r = overlayRoleA pub.state ∧ c ≠ 2)) :
    sampledEncodeExtension309 pub dec ex v i = sampledEncodeExtension pub dec ex v i := by
  rcases i with ⟨r, c⟩ | i
  · simp [sampledEncodeExtension309, hi r c rfl]
  · rfl

/-- At role-A coordinates `0`/`1` the 309 encoding is the genuine fingerprint coordinate. -/
theorem sampledEncodeExtension309_host (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : SampledOverlayValues K) (c : Fin 3) (hc : c ≠ 2) :
    sampledEncodeExtension309 pub dec ex v (.inl (overlayRoleA pub.state, c)) =
      fpCoordinate (pubFingerprint pub (overlayRoleA pub.state)) c := by
  simp [sampledEncodeExtension309, hc]

/-- The restore is the identity at role-A coordinates `0`/`1`. -/
theorem sampledRestoreExtension309_host (base : BaseColumn → F) (x : ExtensionColumn → K)
    (c : Fin 3) (hc : c ≠ 2) :
    sampledRestoreExtension309 base x (.inl (overlayRoleA (decodeState base), c)) =
      x (.inl (overlayRoleA (decodeState base), c)) := by
  simp [sampledRestoreExtension309, hc]

set_option maxHeartbeats 4000000 in
/-- **Exact restore of the 309 encoding** on every accepted row (`Vcomp`). -/
theorem sampledRestore309_encode309_of_vcomp {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {ex : Extra K} {v : SampledOverlayValues K} (h : Vcomp inp pub dec) :
    sampledRestoreExtension309 (OptimizedComputeCodec.encodeBase (F := F) pub.state)
        (sampledEncodeExtension309 pub dec ex v) =
      OptimizedComputeCodec.encodeExtension pub dec ex := by
  have hold := sampledRestore_encode_of_vcomp (F := F) (ex := ex) (v := v) h
  funext i
  rcases i with ⟨r, c⟩ | i
  · by_cases hh : r = overlayRoleA pub.state ∧ c ≠ 2
    · obtain ⟨rfl, hc⟩ := hh
      simp [sampledRestoreExtension309, decodeState_encodeBase, sampledEncodeExtension309, hc]
    · have hh' : ¬ (r = overlayRoleA (decodeState
          (OptimizedComputeCodec.encodeBase (F := F) pub.state)) ∧ c ≠ 2) := by
        rwa [decodeState_encodeBase]
      rw [← congrFun hold (.inl (r, c))]
      simp only [sampledRestoreExtension309, hh', if_false]
      -- the deployed restore at a non-host position reads only non-host positions
      obtain ⟨_, _, _, _, heval⟩ := h
      cases hs : pub.state <;> simp only [evalV, hs] at heval <;>
        fin_cases r <;> fin_cases c <;>
        simp_all [sampledRestoreExtension, sampledEncodeExtension309, sampledEncodeExtension,
          restoredA, restoredB, restoredIOHost, restoredDenomHost, decodeState_encodeBase,
          overlayRoleA, overlayRoleB, decodePubFingerprint, decodeDecFingerprint,
          fpOfCoordinates, fpCoordinate]
  · rw [← congrFun hold (.inr i)]
    rfl

/-- The overlay values are recovered exactly from a 309 row. -/
theorem decodeSampledOverlay309_encode (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : SampledOverlayValues K) :
    decodeSampledOverlay309 (sampledEncode309 (F := F) pub dec ex v) = v := by
  have hb : ∀ c : Fin 3, c ≠ 2 → True := fun _ _ => trivial
  have hold := decodeSampledOverlay_encode (F := F) pub dec ex v
  cases v with
  | mk ov d0 d1 d2 =>
    cases ov with
    | mk wc wa s1 s2 s3 io =>
      have hagree : decodeSampledOverlay (F := F) (OptimizedComputeCodec.encodeBase pub.state)
            (sampledEncodeExtension309 pub dec ex ⟨⟨wc, wa, s1, s2, s3, io⟩, d0, d1, d2⟩) =
          { decodeSampledOverlay (F := F) (OptimizedComputeCodec.encodeBase pub.state)
              (sampledEncodeExtension pub dec ex ⟨⟨wc, wa, s1, s2, s3, io⟩, d0, d1, d2⟩) with
            toOverlayValues := { (decodeSampledOverlay (F := F)
              (OptimizedComputeCodec.encodeBase pub.state)
              (sampledEncodeExtension pub dec ex ⟨⟨wc, wa, s1, s2, s3, io⟩, d0, d1, d2⟩)).toOverlayValues with
              walkCount := (pubFingerprint pub (overlayRoleA pub.state)).size
              walkAcc := (pubFingerprint pub (overlayRoleA pub.state)).dyck } } := by
        cases hs : pub.state <;>
          simp [decodeSampledOverlay, decodePubFingerprint, sampledEncodeExtension309,
            sampledEncodeExtension, overlayRoleA, overlayRoleB, sampledOverlayA, overlayDenoms,
            fpOfCoordinates, fpCoordinate, decodeState_encodeBase, hs,
            OptimizedComputeCodec.encodeExtension]
      simp only [decodeSampledOverlay309, sampledEncode309]
      rw [hagree, hold]
      rfl

/-- **Exact roundtrip of the 309 codec** on every accepted compute row. -/
theorem sampledDecode309_encode309_of_vcomp {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {ex : Extra K} {v : SampledOverlayValues K} (h : Vcomp inp pub dec) :
    sampledDecode309 inp (sampledEncode309 (F := F) pub dec ex v) =
      (withOverlayTags
        { pub with sf1_st := none, sf2_st := none, sf3_st := none, certC? := none }
          v.toOverlayValues,
        dec, ex, v) := by
  have hr := sampledRestore309_encode309_of_vcomp (F := F) (ex := ex) (v := v) h
  have hr' : sampledRestoreExtension309 (sampledEncode309 (F := F) pub dec ex v).row.base
      (sampledEncode309 (F := F) pub dec ex v).row.extension =
        OptimizedComputeCodec.encodeExtension pub dec ex := hr
  have hd := OptimizedComputeCodec.decode_encode_of_vcomp (F := F) (ex := ex) h
  simp only [OptimizedComputeCodec.decode, OptimizedComputeCodec.encode, Prod.mk.injEq] at hd
  simp only [sampledDecode309]
  rw [decodeSampledOverlay309_encode, hr']
  simp only [sampledEncode309]
  rw [hd.1, hd.2.1, hd.2.2]

#print axioms sampledRestore309_encode309_of_vcomp
#print axioms decodeSampledOverlay309_encode
#print axioms sampledDecode309_encode309_of_vcomp

end
end Unhosted309
end Nock.NockVMROM.Thm54
