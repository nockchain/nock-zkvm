/-
**`verdict9V`, the online (succinct) twin of `verdict9`**.
Same instance gates as `verdict9` (famGates, `l = 170`, `claimOf`, `linkGate9`), plus `setupGates` on the loaded instance, then the VK-split online
verifier `verifyOnlineE'` (`verifyOnline'`) with the preprocessing VK `vkOfRoot XI0 root` (instance stripped of its preprocessed coefficients,
`cols := fixCols XI0`, root = the committed VK root) and the side proof `πF`.  definitions and theorems are untouched.
NOT zero-knowledge.
-/
import NockvmE2E.J9A.RunGate9
import NockvmE2E.Exec.VKp
set_option autoImplicit false
namespace NockvmE2E.J9A.RunGate9V
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.J9A.RunGate9 NockvmE2E.Exec.J9AChips
open Nock.NockVMROM.Thm54 (P8PublicClaim)

/-- the preprocessing VK of instance `XI0` with committed root `root` (the shape `mkVKData'` builds: stripped instance, `fixCols`) -/
def vkOfRoot (XI0 : ExecInst) (root : Dg5) : VK :=
  VK.mk { XI0 with pre := XI0.pre.map (fun _ => #[]) } (fixCols XI0) root  -- positional: the global `X` token breaks `{ X := … }` here


/-- `verdict9`'s gates on the full instance, `setupGates`, then the online verifier against `vkOfRoot XI0 root` and the side proof -/
def verdict9V (XI0 : ExecInst) (root : Dg5) (H Hf : HFn) (FS FSf : FSFn) (z : List ℕ) (π : FlatProof) (πF : FixProof) :
    Except String P8PublicClaim :=
  match NockvmE2E.Exec.FamGates.famGatesFail famJ9A XI0 with
  | some e => .error s!"famGates j9a: {e}"
  | none =>
    if XI0.l != 170 then .error "l != 170" else
    match claimOf XI0.pubIn with
    | none => .error "claim: undecodable"
    | some c =>
      if !linkGate9 XI0 c then .error "linkGate9" else
      if !setupGates XI0 then .error "setupGates" else
      match verifyOnlineE' (vkOfRoot XI0 root) H Hf FS FSf z π πF with
      | .error e => .error e
      | .ok _ => .ok c

theorem verdict9V_sound {XI0 : ExecInst} {root : Dg5} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof} {πF : FixProof}
    {c : P8PublicClaim} (h : verdict9V XI0 root H Hf FS FSf z π πF = .ok c) :
    NockvmE2E.Exec.FamGates.famGates famJ9A XI0 = true ∧ XI0.l = 170 ∧ linkGate9 XI0 c = true ∧ setupGates XI0 = true ∧
      verifyOnline' (vkOfRoot XI0 root) H Hf FS FSf z π πF = true := by
  unfold verdict9V at h
  split at h
  · cases h
  · rename_i hf
    split at h
    · cases h
    · rename_i hl
      split at h
      · cases h
      · rename_i c' hc
        split at h
        · cases h
        · rename_i hg
          split at h
          · cases h
          · rename_i hs
            split at h
            · cases h
            · rename_i u hv
              cases h
              refine ⟨NockvmE2E.Exec.FamGates.famGatesFail_none.mp hf, ?_, ?_, ?_, ?_⟩
              · simpa using hl
              · simpa using hg
              · simpa using hs
              · unfold verifyOnline'
                rw [hv]

#print axioms verdict9V_sound

/-! ## indexer / online split.
The INDEXER runs the instance gates on the full instance once and emits the VK instance `stripInst XI0` (no `pre` coefficients, no public input).
The ONLINE verifier takes only that stripped instance + root (the vk file), the public input and the proofs; it never sees `XI0`. -/

/-- the instance the indexer publishes in the vk file: `pre` coefficients and the public input erased -/
def stripInst (XI0 : ExecInst) : ExecInst :=
  { XI0 with pre := XI0.pre.map (fun _ => #[]), pubIn := { claimCells := [], pins := [] } }

/-- the VK the online verifier reconstructs from the vk file `(Xs, root)` and the supplied public input `p` -/
def vkO (Xs : ExecInst) (p : PE.PubIn) (root : Dg5) : VK :=
  VK.mk { Xs with pubIn := p } (fixCols Xs) root

/-- the indexer link: what the indexer's gates establish on the full instance (everything `verdict9V` checks except the online verifier itself) -/
def IndexerCert (XI0 : ExecInst) : Prop :=
  NockvmE2E.Exec.FamGates.famGates famJ9A XI0 = true ∧ XI0.l = 170 ∧ setupGates XI0 = true ∧
    ∃ c, claimOf XI0.pubIn = some c ∧ linkGate9 XI0 c = true

/-- the indexer: the instance gates once, on the full instance; on success the stripped instance for the vk file -/
def indexer (XI0 : ExecInst) : Except String ExecInst :=
  match NockvmE2E.Exec.FamGates.famGatesFail famJ9A XI0 with
  | some e => .error s!"famGates j9a: {e}"
  | none =>
    if XI0.l != 170 then .error "l != 170" else
    match claimOf XI0.pubIn with
    | none => .error "claim: undecodable"
    | some c =>
      if !linkGate9 XI0 c then .error "linkGate9" else
      if !setupGates XI0 then .error "setupGates" else
      .ok (stripInst XI0)

theorem indexer_sound {XI0 Xs : ExecInst} (h : indexer XI0 = .ok Xs) : IndexerCert XI0 ∧ Xs = stripInst XI0 := by
  unfold indexer at h
  split at h
  · cases h
  · rename_i hf
    split at h
    · cases h
    · rename_i hl
      split at h
      · cases h
      · rename_i c hc
        split at h
        · cases h
        · rename_i hg
          split at h
          · cases h
          · rename_i hs
            cases h
            refine ⟨⟨NockvmE2E.Exec.FamGates.famGatesFail_none.mp hf, ?_, ?_, c, hc, ?_⟩, rfl⟩
            · simpa using hl
            · simpa using hs
            · simpa using hg

/-- the online verdict: only the vk file `(Xs, root)`, the public input `pubIn`, `z`, `π`, `πF`; no instance gates (the indexer's job) -/
def verdict9VO (Xs : ExecInst) (root : Dg5) (pubIn : PE.PubIn) (H Hf : HFn) (FS FSf : FSFn) (z : List ℕ) (π : FlatProof) (πF : FixProof) :
    Except String P8PublicClaim :=
  if !inpCanOk pubIn then .error "public input non-canonical" else
  match claimOf pubIn with
  | none => .error "claim: undecodable"
  | some c =>
    match verifyOnlineE' (vkO Xs pubIn root) H Hf FS FSf z π πF with
    | .error e => .error e
    | .ok _ => .ok c

theorem vkO_strip (XI0 : ExecInst) (root : Dg5) : vkO (stripInst XI0) XI0.pubIn root = vkOfRoot XI0 root := rfl

/-- online soundness.  `hcert`: the indexer's gates held on `XI0`; `hvk`: the vk file's instance is `stripInst XI0`;
`hPubBind` (NAMED HYPOTHESIS): the public input handed to the online verifier is the one `XI0` carries (the exe checks a Tip5 digest of the
public input against the one in the vk file, so this is collision resistance of that digest, not a kernel fact).  Conclusion = `verdict9V_sound`'s. -/
theorem verdict9VO_sound {XI0 Xs : ExecInst} {root : Dg5} {pubIn : PE.PubIn} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof}
    {πF : FixProof} {c : P8PublicClaim} (hcert : IndexerCert XI0) (hvk : Xs = stripInst XI0) (hPubBind : pubIn = XI0.pubIn)
    (h : verdict9VO Xs root pubIn H Hf FS FSf z π πF = .ok c) :
    NockvmE2E.Exec.FamGates.famGates famJ9A XI0 = true ∧ XI0.l = 170 ∧ linkGate9 XI0 c = true ∧ setupGates XI0 = true ∧
      verifyOnline' (vkOfRoot XI0 root) H Hf FS FSf z π πF = true := by
  obtain ⟨hf, hl, hs, c', hc', hg⟩ := hcert
  subst hvk hPubBind
  unfold verdict9VO at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i c'' hc''
      split at h
      · cases h
      · rename_i u hv
        cases h
        rw [hc''] at hc'
        cases hc'
        refine ⟨hf, hl, hg, hs, ?_⟩
        unfold verifyOnline'
        rw [vkO_strip] at hv
        rw [hv]

#print axioms indexer_sound
#print axioms verdict9VO_sound

end NockvmE2E.J9A.RunGate9V
