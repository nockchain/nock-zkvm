/-
  NockvmE2E/Z38/RunGate9LJ.lean   (twin of J9A/RunGate9L.lean)

  The verifier of the J-9 AL family WITH a template-jet table, over the fixed catalogue `catJ`.  ADDITIVE: `LinkOK9L`, `famGatesL`, `verdict9L*`
  and the headline are untouched.
  * `famGatesLJ = famGatesL ∧ jetPreOkF` (the J table's 18 fixed columns are checked);
  * `LinkOK9LJ = LinkBaseLJ ∧ JetLink`: `LinkBaseLJ` is `LinkOK9L` verbatim minus E1 (`hNof jet = 0`), E2 (`pins = []`) and E3 (`hNof jet = 0 → present[3] = false`,
    `∀ t, chip.id ≠ jetChipJ8`); `JetLink` is their replacement, one named decidable Prop per conjunct (`jLen jPinB jPinN …`), each mirroring a `DatumOK9AL` jet field
    (`hlay` length, `hsmall`, `huniq`, `hTpl` (regs ⊆ catJ), `hnd`, `hidx`, `hrk`, `hlt`, `hlenC`, `hlenCP`, `hdisjP`, `regs.length ≤ g`) plus the pin / call checks;
  * `verdict9LJ`, `verdict9LJV`, `indexerLJ`, `verdict9LJVO` with `_sound` lemmas: the verdicts of the `j9alj` exe arms.  The verify functions, `z` and the
    FS key are those of the base verifier (the pins and calls are NOT absorbed into the transcript; they are bound by the VK `pubDigest` and the Fix root).
  Only catalogue jets are covered.  Not zero-knowledge.
-/
import NockvmE2E.Z38.JetPreGate
import NockvmE2E.J8.RVUJ8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000
namespace NockvmE2E.Z38.RunGate9LJ
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.J9A.RunGate9 NockvmE2E.J9A.RunGate9V NockvmE2E.J9A.LagrJ9A
open NockvmE2E.J9A.RunGate9L
open NockvmE2E.Z38.JetPre NockvmE2E.Z38.CatJ
open NockvmE2E.Exec.J9ALChips (famJ9AL)
open NockvmE2E.Exec.VF (G PN based)
open NockvmE2E.J8.InstJ8 (P tabOf hNof)
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (claimBigs)
open Nock.Jet.ChipJ8 (tvKey)

/-! ## 1. the gates -/

def famGatesLJ (F : Fam) (XI : ExecInst) : Bool := famGatesL F XI && jetPreOkF XI

def famGatesLJFail (F : Fam) (XI : ExecInst) : Option String :=
  match famGatesLFail F XI with
  | some e => some e
  | none => if jetPreOkF XI then none else some "jetPreOkF (a jet preprocessed column is not the interpolation of the layout, or a jet mask is wrong)"

theorem famGatesLJ_sound {F : Fam} {XI : ExecInst} (h : famGatesLJ F XI = true) : famGatesL F XI = true ∧ jetPreOkF XI = true := by
  unfold famGatesLJ at h
  simpa [Bool.and_eq_true] using h

theorem famGatesLJFail_none {F : Fam} {XI : ExecInst} : famGatesLJFail F XI = none ↔ famGatesLJ F XI = true := by
  have h := @famGatesLFail_none F XI
  unfold famGatesLJFail famGatesLJ
  cases hf : famGatesLFail F XI with
  | some e =>
    rw [hf] at h
    cases hG : famGatesL F XI
    · simp [hG]
    · exact absurd (h.mpr hG) (by simp)
  | none =>
    rw [hf] at h
    have hG : famGatesL F XI = true := h.mp rfl
    cases hj : jetPreOkF XI <;> simp [hG, hj]

/-! ## 2. the link gate -/

deriving instance DecidableEq for NockvmE2E.Exec.PE.Tok

/-- **`JetLink`**: the jet block of the link (replaces E1, E2 and `∀ t, chip.id ≠ jetChipJ8`); one named conjunct each, all decidable.
J1 the layout has exactly `hNof jet` rows (unconditional: with no jet table it forces `pins = calls = []`); J2 pin bounds (the `PrimsLink` form);
J3 the pin nouns are the catalogue templates' `compile` tokens (`InpLink9.hpin`); J4 regs ⊆ catJ ids; J5 regs Nodup; J6 prims disjoint from regs;
J7 `hsmall` (`StmtP9AL.hsmall`); J8 `huniq` (`StmtP9AL.huniq`); J9 every call id is a registry id. -/
def jLen (XI : ExecInst) : Prop := (layJ XI.pubIn).length = hNof XI "jetChipJ8"
def jPinB (XI : ExecInst) : Prop :=
  ∀ q ∈ XI.pubIn.pins, q.key < PN ∧ q.idx < PN ∧ q.hi < PN ∧ q.lo < PN ∧ ¬ (q.hi = 0 ∧ q.lo = 0)
def jPinN (XI : ExecInst) : Prop :=
  ∀ q ∈ XI.pubIn.pins, q.noun = NockvmE2E.J8.RVUJ8.toks (Nock.Jet.Autogen.compile P (catJ.toCR.Rt q.key))
def jRegsCat (XI : ExecInst) : Prop := ∀ id ∈ regsOfPub XI.pubIn, id ∈ catJ.toCR.regs
def jRegsNd (XI : ExecInst) : Prop := (regsOfPub XI.pubIn).Nodup
def jDisj (XI : ExecInst) : Prop := ∀ q ∈ XI.pubIn.prims, q.id ∉ regsOfPub XI.pubIn
def jSmall (XI : ExecInst) : Prop := ∀ q ∈ layJ XI.pubIn, q.id < P ∧ q.cid < P ∧ q.nid < P ∧ q.n1 < P ∧ q.n2 < P
def jUniq (XI : ExecInst) : Prop := ((layJ XI.pubIn).filterMap tvKey).Nodup
def jCalls (XI : ExecInst) : Prop := ∀ i ∈ XI.pubIn.calls, i ∈ regsOfPub XI.pubIn

def JetLink (XI : ExecInst) : Prop :=
  jLen XI ∧ jPinB XI ∧ jPinN XI ∧ jRegsCat XI ∧ jRegsNd XI ∧ jDisj XI ∧ jSmall XI ∧ jUniq XI ∧ jCalls XI

instance (XI : ExecInst) : Decidable (JetLink XI) := by
  unfold JetLink jLen jPinB jPinN jRegsCat jRegsNd jDisj jSmall jUniq jCalls; infer_instance

/-- `LinkOK9L` in the same order minus exactly three conjuncts: `hNof jet = 0`, `pins = []`, `∀ t, chip.id ≠ jetChipJ8`
(`hNof jet = 0 → present[3]! = false` and `PrimsLink` are kept verbatim) -/
def LinkBaseLJ (XI : ExecInst) (c : P8PublicClaim) : Prop :=
  1 ≤ kOfL XI ∧ kOfL XI ≤ hNof XI "walkChipJ8" ∧
  ((tabOf XI "walkChipHQK").isSome = true → 1 ≤ kVOfL XI ∧ kVOfL XI ≤ hNof XI "walkChipHQK") ∧
  ((tabOf XI "walkChipHQK").isSome = false → kVOfL XI = 0) ∧
  ((∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < P) ∧
   (∀ x ∈ (claimCells c).map (claimNoun c) ++ (claimBigs P c).map (claimNoun c),
      x.leaves ≤ Nock.NockVMROM.Thm54.VclL.fuelChip ∧ ∀ v ∈ x.leafList, Nock.Atoms.lenL v ≤ hNof XI "atomChipHQL" + 2) ∧
   isCellN c.formula = true) ∧
  XI.pubIn.claimCells = (claimCells c).map (NockvmE2E.J8.RVUJ8.claimRec (claimNoun c)) ++
      (claimBigs P c).map (NockvmE2E.J8.RVUJ8.claimRec (claimNoun c)) ∧
  XI.pubIn.atoms = (List.finRange 3).filterMap (fun i => match claimNoun c i with
      | .atom v => if P ≤ v then none else some (i.val, v) | .cell _ _ => none) ∧
  (∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id ≠ "aluChipJ9" →
      (chipNumeralF famJ9AL XI.tabs[t].chip).getD 0 = NockvmE2E.J9A.E2EJ9AToyR.numP XI (kOfL XI) (kVOfL XI) (NockvmE2E.J9A.GenJ9A.sigma9 XI t)) ∧
  (∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id = "aluChipJ9" → (chipNumeralF famJ9AL XI.tabs[t].chip).getD 0 = 0) ∧
  (hNof XI "jetChipJ8" = 0 → XI.pubLay.present[3]! = false) ∧
  ((if (tabOf XI "walkChipHQK").isSome then kVOfL XI else 0) = 0 → XI.pubLay.present[5]! = false) ∧
  ((tabOf XI "axisChipJ9").isSome = false → XI.pubLay.present[6]! = false) ∧
  ((tabOf XI "splitChipJ9").isSome = false → XI.pubLay.present[7]! = false) ∧
  PrimsLink XI

instance (XI : ExecInst) (c : P8PublicClaim) : Decidable (LinkBaseLJ XI c) := by unfold LinkBaseLJ; infer_instance

/-- **`LinkOK9LJ`**: the link of the J-9 AL verifier with template jets over `catJ` -/
def LinkOK9LJ (XI : ExecInst) (c : P8PublicClaim) : Prop := LinkBaseLJ XI c ∧ JetLink XI

instance (XI : ExecInst) (c : P8PublicClaim) : Decidable (LinkOK9LJ XI c) := by unfold LinkOK9LJ; infer_instance

/-- the runtime gate -/
def linkGate9LJ (XI : ExecInst) (c : P8PublicClaim) : Bool := decide (LinkOK9LJ XI c)

/-! ## 3. the verdicts -/

def verdict9LJ (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List ℕ) (π : FlatProof) : Except String P8PublicClaim :=
  match famGatesLJFail famJ9AL XI with
  | some e => .error s!"famGates j9alj: {e}"
  | none =>
    if XI.l != 170 then .error "l != 170" else
    if !inpCanOkL XI.pubIn then .error "public input non-canonical" else
    match claimOf XI.pubIn with
    | none => .error "claim: undecodable"
    | some c =>
      if !linkGate9LJ XI c then .error "linkGate9LJ" else
      match verifyFlatE XI H FS z π with
      | .error e => .error e
      | .ok _ => .ok c

theorem verdict9LJ_sound {XI : ExecInst} {H : HFn} {FS : FSFn} {z : List ℕ} {π : FlatProof} {c : P8PublicClaim}
    (h : verdict9LJ XI H FS z π = .ok c) :
    famGatesLJ famJ9AL XI = true ∧ XI.l = 170 ∧ inpCanOkL XI.pubIn = true ∧ linkGate9LJ XI c = true ∧
      verifyFlatE XI H FS z π = .ok () := by
  unfold verdict9LJ at h
  split at h
  · cases h
  · rename_i hf
    split at h
    · cases h
    · rename_i hl
      split at h
      · cases h
      · rename_i hcan
        split at h
        · cases h
        · rename_i c' hc
          split at h
          · cases h
          · rename_i hg
            split at h
            · cases h
            · rename_i u hv
              cases h
              refine ⟨famGatesLJFail_none.mp hf, ?_, ?_, ?_, hv⟩
              · simpa using hl
              · simpa using hcan
              · simpa using hg

def verdict9LJV (XI0 : ExecInst) (root : Dg5) (H Hf : HFn) (FS FSf : FSFn) (z : List ℕ) (π : FlatProof) (πF : FixProof) :
    Except String P8PublicClaim :=
  match famGatesLJFail famJ9AL XI0 with
  | some e => .error s!"famGates j9alj: {e}"
  | none =>
    if XI0.l != 170 then .error "l != 170" else
    if !inpCanOkL XI0.pubIn then .error "public input non-canonical" else
    match claimOf XI0.pubIn with
    | none => .error "claim: undecodable"
    | some c =>
      if !linkGate9LJ XI0 c then .error "linkGate9LJ" else
      if !setupGates XI0 then .error "setupGates" else
      match verifyOnlineE' (vkOfRoot XI0 root) H Hf FS FSf z π πF with
      | .error e => .error e
      | .ok _ => .ok c

theorem verdict9LJV_sound {XI0 : ExecInst} {root : Dg5} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof} {πF : FixProof}
    {c : P8PublicClaim} (h : verdict9LJV XI0 root H Hf FS FSf z π πF = .ok c) :
    famGatesLJ famJ9AL XI0 = true ∧ XI0.l = 170 ∧ inpCanOkL XI0.pubIn = true ∧ linkGate9LJ XI0 c = true ∧ setupGates XI0 = true ∧
      verifyOnline' (vkOfRoot XI0 root) H Hf FS FSf z π πF = true := by
  unfold verdict9LJV at h
  split at h
  · cases h
  · rename_i hf
    split at h
    · cases h
    · rename_i hl
      split at h
      · cases h
      · rename_i hcan
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
                refine ⟨famGatesLJFail_none.mp hf, ?_, ?_, ?_, ?_, ?_⟩
                · simpa using hl
                · simpa using hcan
                · simpa using hg
                · simpa using hs
                · unfold verifyOnline'
                  rw [hv]

/-- the indexer link at the jet family -/
def IndexerCertLJ (XI0 : ExecInst) : Prop :=
  famGatesLJ famJ9AL XI0 = true ∧ XI0.l = 170 ∧ inpCanOkL XI0.pubIn = true ∧ setupGates XI0 = true ∧
    ∃ c, claimOf XI0.pubIn = some c ∧ linkGate9LJ XI0 c = true

def indexerLJ (XI0 : ExecInst) : Except String ExecInst :=
  match famGatesLJFail famJ9AL XI0 with
  | some e => .error s!"famGates j9alj: {e}"
  | none =>
    if XI0.l != 170 then .error "l != 170" else
    if !inpCanOkL XI0.pubIn then .error "public input non-canonical" else
    match claimOf XI0.pubIn with
    | none => .error "claim: undecodable"
    | some c =>
      if !linkGate9LJ XI0 c then .error "linkGate9LJ" else
      if !setupGates XI0 then .error "setupGates" else
      .ok (stripInst XI0)

theorem indexerLJ_sound {XI0 Xs : ExecInst} (h : indexerLJ XI0 = .ok Xs) : IndexerCertLJ XI0 ∧ Xs = stripInst XI0 := by
  unfold indexerLJ at h
  split at h
  · cases h
  · rename_i hf
    split at h
    · cases h
    · rename_i hl
      split at h
      · cases h
      · rename_i hcan
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
              refine ⟨⟨famGatesLJFail_none.mp hf, ?_, ?_, ?_, c, hc, ?_⟩, rfl⟩
              · simpa using hl
              · simpa using hcan
              · simpa using hs
              · simpa using hg

def verdict9LJVO (Xs : ExecInst) (root : Dg5) (pubIn : PE.PubIn) (H Hf : HFn) (FS FSf : FSFn) (z : List ℕ) (π : FlatProof) (πF : FixProof) :
    Except String P8PublicClaim :=
  if !inpCanOkL pubIn then .error "public input non-canonical" else
  match claimOf pubIn with
  | none => .error "claim: undecodable"
  | some c =>
    match verifyOnlineE' (vkO Xs pubIn root) H Hf FS FSf z π πF with
    | .error e => .error e
    | .ok _ => .ok c

theorem verdict9LJVO_sound {XI0 Xs : ExecInst} {root : Dg5} {pubIn : PE.PubIn} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof}
    {πF : FixProof} {c : P8PublicClaim} (hcert : IndexerCertLJ XI0) (hvk : Xs = stripInst XI0) (hPubBind : pubIn = XI0.pubIn)
    (h : verdict9LJVO Xs root pubIn H Hf FS FSf z π πF = .ok c) :
    famGatesLJ famJ9AL XI0 = true ∧ XI0.l = 170 ∧ linkGate9LJ XI0 c = true ∧ setupGates XI0 = true ∧
      verifyOnline' (vkOfRoot XI0 root) H Hf FS FSf z π πF = true := by
  obtain ⟨hf, hl, hcan, hs, c', hc', hg⟩ := hcert
  subst hvk hPubBind
  unfold verdict9LJVO at h
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

end NockvmE2E.Z38.RunGate9LJ

#print axioms NockvmE2E.Z38.RunGate9LJ.famGatesLJ_sound
#print axioms NockvmE2E.Z38.RunGate9LJ.famGatesLJFail_none
#print axioms NockvmE2E.Z38.RunGate9LJ.verdict9LJ_sound
#print axioms NockvmE2E.Z38.RunGate9LJ.verdict9LJV_sound
#print axioms NockvmE2E.Z38.RunGate9LJ.indexerLJ_sound
#print axioms NockvmE2E.Z38.RunGate9LJ.verdict9LJVO_sound
