/-
the J-9 AL twins of the J-9 A gates and verdicts (`RunGate9`, `RunGate9V`).
* `maskOkFL`: the mask check of `maskOkF` on the ALU's columns `0, 1` only (columns `2..4` are the preg layout, not masks);
* `pregOkF`: the ALU's preprocessed columns `2, 3, 4` (`sP, pId, pOp`) evaluate, on the first `hN` nodes, to `pregCol prims 0 / 1 / 2` with `prims`
  read from `XI.pubIn.prims` (nock `CheckJ9AL.pregCol`; the soundness bridge `PregLagrange.preL_eval_pregCol`);
* `famGatesL`: shape, shapeX, chips, maskL, numeral, preg;
* `linkGate9L`: `LinkOK9` at `famJ9AL` (keeping `hNof jetChipJ8 = 0`, `pins = []`, no jet table) + the prims link;
* `verdict9L`, `verdict9LV`, `indexerL`, `verdict9LVO` with their `_sound` lemmas (twins of `verdict9_sound`, `verdict9V_sound`, `indexer_sound`,
  `verdict9VO_sound`).
The loader is untrusted: the verdicts are evaluated on the instance the exe loaded.  NOT zero-knowledge.
-/
import NockvmE2E.J9A.RunGate9V
import NockvmE2E.Exec.J9ALChipsFam
import NockvmE2E.Exec.VField
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
set_option autoImplicit false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000
namespace NockvmE2E.J9A.RunGate9L
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.J9A.RunGate9 NockvmE2E.J9A.RunGate9V NockvmE2E.J9A.LagrJ9A
open NockvmE2E.Exec.J9ALChips (famJ9AL)
open NockvmE2E.Exec.MaskOk
open NockvmE2E.Exec.VF (G PN based)
open NockvmE2E.J8.InstJ8 (P tabOf hNof)
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (claimBigs)

/-! ## 1. the gates -/

/-- `tabMaskF` except that the ALU's mask check covers its columns `0, 1` only -/
def tabMaskFL (F : Fam) (XX : ExecInst) (t : TabInst) : Option Nat :=
  if t.chip.id == "aluChipJ9" then
    ((F.preIdx t.chip.id).toList.take 2).zipIdx.foldl (fun acc (c, pos) =>
      match acc, maskCol XX t.hN pos (XX.pre.getD (t.col0 + c) #[]) with
      | some a, some k => some (max a k)
      | _, _ => none) (some 0)
  else tabMaskF F XX t

def maskOkFL (F : Fam) (XX : ExecInst) : Bool := XX.tabs.all fun t => (tabMaskFL F XX t).isSome

/-- the preg value `pregCol prims k i` (`k = 0 : sP`, `1 : pId`, `2 : pOp`) as a field element -/
def pregVal (prims : List PE.PrimRec) (k i : Nat) : G :=
  if k == 0 then (if i < prims.length then (1 : G) else 0)
  else if k == 1 then UInt64.ofNat ((prims.map (·.id)).getD i 0)
  else UInt64.ofNat ((prims.map (·.code)).getD i 0)

/-- **`pregOkF`**: at the ALU table, `#prims ≤ hN`, ids and codes are canonical, and the preprocessed columns `2, 3, 4` are the Lagrange
interpolations of `pregCol prims 0, 1, 2` over the first `hN` nodes `hGen^i`.  Tables other than the ALU are not constrained. -/
def pregOkF (XX : ExecInst) : Bool := XX.tabs.all fun t =>
  if t.chip.id == "aluChipJ9" then
    decide (XX.pubIn.prims.length ≤ t.hN) &&
    XX.pubIn.prims.all (fun q => decide (q.id < PN) && decide (q.code < PN)) &&
    (List.range 3).all fun k =>
      let p := XX.pre.getD (t.col0 + 2 + k) #[]
      decide (p.size ≤ t.hN) && evalNodes p XX.hGen t.hN == (Array.range t.hN).map (pregVal XX.pubIn.prims k)
  else true

def famGatesL (F : Fam) (XI : ExecInst) : Bool :=
  shapeOkF F XI && shapeXOkF F XI && chipsOkF F XI && maskOkFL F XI && numeralOkF F XI && pregOkF XI

def famGatesLFail (F : Fam) (XI : ExecInst) : Option String :=
  if !shapeOkF F XI then some "shapeOkF (instance is not shaped like the family)"
  else if !shapeXOkF F XI then some "shapeXOkF (nq/pubCap/blockTab/public layout)"
  else if !chipsOkF F XI then some "chipsOkF (a loaded chip is not a literal of the family)"
  else if !maskOkFL F XI then some "maskOkFL (a preprocessed mask column is not the first/last/root-row pattern)"
  else if !numeralOkF F XI then some "numeralOkF (a walk chip's numeral differs from its root-mask kroots)"
  else if !pregOkF XI then some "pregOkF (an ALU preg column is not the interpolation of the primitive table)"
  else none

theorem famGatesL_sound {F : Fam} {XI : ExecInst} (h : famGatesL F XI = true) :
    shapeOkF F XI = true ∧ shapeXOkF F XI = true ∧ chipsOkF F XI = true ∧ maskOkFL F XI = true ∧ numeralOkF F XI = true ∧
      pregOkF XI = true := by
  unfold famGatesL at h
  simp only [Bool.and_eq_true] at h
  tauto

theorem famGatesLFail_none {F : Fam} {XI : ExecInst} : famGatesLFail F XI = none ↔ famGatesL F XI = true := by
  unfold famGatesLFail famGatesL
  cases shapeOkF F XI <;> cases shapeXOkF F XI <;> cases chipsOkF F XI <;> cases maskOkFL F XI <;> cases numeralOkF F XI <;>
    cases pregOkF XI <;> simp

/-! ## 2. the link gate -/

/-- the numerals the gate reads off the loaded chips, at the AL family -/
def numOfIdL (XI : ExecInst) (id : String) : ℕ :=
  match XI.tabs.toList.find? (fun t => t.chip.id == id) with
  | some t => (chipNumeralF famJ9AL t.chip).getD 0
  | none => 0
def kOfL (XI : ExecInst) : ℕ := numOfIdL XI "walkChipJ8"
def kVOfL (XI : ExecInst) : ℕ := if (tabOf XI "walkChipHQK").isSome then numOfIdL XI "walkChipHQK" else 0

/-- the primitive table of the public input as nock's `prims : List (ℕ × PrimOp)` (`code` decoded by `RealIOJ9AL.primCode`'s inverse); `none` on an
unknown code -/
def primOfCode : ℕ → Option Nock.Jet.Prim.PrimOp
  | 1 => some .add | 2 => some .sub | 3 => some .lt | 4 => some .mul | 5 => some .div | 6 => some .mod | _ => none

def primsOfPub (ps : List PE.PrimRec) : Option (List (ℕ × Nock.Jet.Prim.PrimOp)) := ps.mapM fun q => (primOfCode q.code).map (q.id, ·)

/-- the prims link: the public input's `prims` decode to a primitive table whose re-encoding is the public input's (so the codes are the `primCode`s of
the datum's ops), and the static conjuncts of nock `checkStaticJ9AL` on `prims` (`rkP ≠ (0,0)`, all `< p`, `Nodup` ids, `nL + n < p`,
`prims.length ≤ nL`, `3 + regs + prims + nL + 2 nC < p`, with `regs = []`; `prims ∩ regs = ∅` is vacuous).  `nL = hNof aluChipJ9`, `nC = hNof cellChipHQKW`. -/
def primsRoundTrip (ps : List PE.PrimRec) : Bool :=
  match primsOfPub ps with
  | some qs => decide (qs.map (fun q => (q.1, Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL.primCode q.2)) = ps.map (fun q => (q.id, q.code)))
  | none => false

def PrimsLink (XI : ExecInst) : Prop :=
  primsRoundTrip XI.pubIn.prims = true ∧
  (∀ q ∈ XI.pubIn.prims, q.id < PN ∧ q.idx < PN ∧ q.hi < PN ∧ q.lo < PN ∧ ¬ (q.hi = 0 ∧ q.lo = 0)) ∧
  (XI.pubIn.prims.map (·.id)).Nodup ∧
  XI.pubIn.prims.length ≤ hNof XI "aluChipJ9" ∧
  hNof XI "aluChipJ9" + hNof XI "computeChipVCLHX9" < PN ∧
  3 + XI.pubIn.prims.length + hNof XI "aluChipJ9" + 2 * hNof XI "cellChipHQKW" < PN ∧
  ((tabOf XI "aluChipJ9").isSome = false → XI.pubIn.prims = [] ∧ XI.pubLay.present[8]! = false)

instance (XI : ExecInst) : Decidable (PrimsLink XI) := by unfold PrimsLink; infer_instance

/-- `LinkOK9` at the AL family (numerals read at `famJ9AL`; the eight J-9 A tables through `sigma9`, the ALU's numeral is `0`; keeps
`hNof jetChipJ8 = 0`, `pins = []`, no jet table), the ALU absent-layout condition, and `PrimsLink` -/
def LinkOK9L (XI : ExecInst) (c : P8PublicClaim) : Prop :=
  hNof XI "jetChipJ8" = 0 ∧ 1 ≤ kOfL XI ∧ kOfL XI ≤ hNof XI "walkChipJ8" ∧
  ((tabOf XI "walkChipHQK").isSome = true → 1 ≤ kVOfL XI ∧ kVOfL XI ≤ hNof XI "walkChipHQK") ∧
  ((tabOf XI "walkChipHQK").isSome = false → kVOfL XI = 0) ∧
  ((∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < P) ∧
   (∀ x ∈ (claimCells c).map (claimNoun c) ++ (claimBigs P c).map (claimNoun c),
      x.leaves ≤ Nock.NockVMROM.Thm54.VclL.fuelChip ∧ ∀ v ∈ x.leafList, Nock.Atoms.lenL v ≤ hNof XI "atomChipHQL" + 2) ∧
   isCellN c.formula = true) ∧
  XI.pubIn.claimCells = (claimCells c).map (NockvmE2E.J8.RVUJ8.claimRec (claimNoun c)) ++
      (claimBigs P c).map (NockvmE2E.J8.RVUJ8.claimRec (claimNoun c)) ∧
  XI.pubIn.pins = [] ∧
  XI.pubIn.atoms = (List.finRange 3).filterMap (fun i => match claimNoun c i with
      | .atom v => if P ≤ v then none else some (i.val, v) | .cell _ _ => none) ∧
  (∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id ≠ "aluChipJ9" →
      (chipNumeralF famJ9AL XI.tabs[t].chip).getD 0 = NockvmE2E.J9A.E2EJ9AToyR.numP XI (kOfL XI) (kVOfL XI) (NockvmE2E.J9A.GenJ9A.sigma9 XI t)) ∧
  (∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id = "aluChipJ9" → (chipNumeralF famJ9AL XI.tabs[t].chip).getD 0 = 0) ∧
  (hNof XI "jetChipJ8" = 0 → XI.pubLay.present[3]! = false) ∧
  ((if (tabOf XI "walkChipHQK").isSome then kVOfL XI else 0) = 0 → XI.pubLay.present[5]! = false) ∧
  ((tabOf XI "axisChipJ9").isSome = false → XI.pubLay.present[6]! = false) ∧
  ((tabOf XI "splitChipJ9").isSome = false → XI.pubLay.present[7]! = false) ∧
  (∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id ≠ "jetChipJ8") ∧
  PrimsLink XI

instance (XI : ExecInst) (c : P8PublicClaim) : Decidable (LinkOK9L XI c) := by unfold LinkOK9L; infer_instance

/-- the runtime gate -/
def linkGate9L (XI : ExecInst) (c : P8PublicClaim) : Bool := decide (LinkOK9L XI c)

/-- the public input is canonical, prim records included -/
def inpCanOkL (inp : PE.PubIn) : Bool :=
  inpCanOk inp && inp.prims.all fun q => based q.id && based q.code && based q.idx && based q.hi && based q.lo

/-! ## 3. the verdicts -/

def verdict9L (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List ℕ) (π : FlatProof) : Except String P8PublicClaim :=
  match famGatesLFail famJ9AL XI with
  | some e => .error s!"famGates j9al: {e}"
  | none =>
    if XI.l != 170 then .error "l != 170" else
    if !inpCanOkL XI.pubIn then .error "public input non-canonical" else
    match claimOf XI.pubIn with
    | none => .error "claim: undecodable"
    | some c =>
      if !linkGate9L XI c then .error "linkGate9L" else
      match verifyFlatE XI H FS z π with
      | .error e => .error e
      | .ok _ => .ok c

theorem verdict9L_sound {XI : ExecInst} {H : HFn} {FS : FSFn} {z : List ℕ} {π : FlatProof} {c : P8PublicClaim}
    (h : verdict9L XI H FS z π = .ok c) :
    famGatesL famJ9AL XI = true ∧ XI.l = 170 ∧ inpCanOkL XI.pubIn = true ∧ linkGate9L XI c = true ∧ verifyFlatE XI H FS z π = .ok () := by
  unfold verdict9L at h
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
              refine ⟨famGatesLFail_none.mp hf, ?_, ?_, ?_, hv⟩
              · simpa using hl
              · simpa using hcan
              · simpa using hg

def verdict9LV (XI0 : ExecInst) (root : Dg5) (H Hf : HFn) (FS FSf : FSFn) (z : List ℕ) (π : FlatProof) (πF : FixProof) :
    Except String P8PublicClaim :=
  match famGatesLFail famJ9AL XI0 with
  | some e => .error s!"famGates j9al: {e}"
  | none =>
    if XI0.l != 170 then .error "l != 170" else
    if !inpCanOkL XI0.pubIn then .error "public input non-canonical" else
    match claimOf XI0.pubIn with
    | none => .error "claim: undecodable"
    | some c =>
      if !linkGate9L XI0 c then .error "linkGate9L" else
      if !setupGates XI0 then .error "setupGates" else
      match verifyOnlineE' (vkOfRoot XI0 root) H Hf FS FSf z π πF with
      | .error e => .error e
      | .ok _ => .ok c

theorem verdict9LV_sound {XI0 : ExecInst} {root : Dg5} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof} {πF : FixProof}
    {c : P8PublicClaim} (h : verdict9LV XI0 root H Hf FS FSf z π πF = .ok c) :
    famGatesL famJ9AL XI0 = true ∧ XI0.l = 170 ∧ inpCanOkL XI0.pubIn = true ∧ linkGate9L XI0 c = true ∧ setupGates XI0 = true ∧
      verifyOnline' (vkOfRoot XI0 root) H Hf FS FSf z π πF = true := by
  unfold verdict9LV at h
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
                refine ⟨famGatesLFail_none.mp hf, ?_, ?_, ?_, ?_, ?_⟩
                · simpa using hl
                · simpa using hcan
                · simpa using hg
                · simpa using hs
                · unfold verifyOnline'
                  rw [hv]

/-- the indexer link at the AL family -/
def IndexerCertL (XI0 : ExecInst) : Prop :=
  famGatesL famJ9AL XI0 = true ∧ XI0.l = 170 ∧ inpCanOkL XI0.pubIn = true ∧ setupGates XI0 = true ∧
    ∃ c, claimOf XI0.pubIn = some c ∧ linkGate9L XI0 c = true

def indexerL (XI0 : ExecInst) : Except String ExecInst :=
  match famGatesLFail famJ9AL XI0 with
  | some e => .error s!"famGates j9al: {e}"
  | none =>
    if XI0.l != 170 then .error "l != 170" else
    if !inpCanOkL XI0.pubIn then .error "public input non-canonical" else
    match claimOf XI0.pubIn with
    | none => .error "claim: undecodable"
    | some c =>
      if !linkGate9L XI0 c then .error "linkGate9L" else
      if !setupGates XI0 then .error "setupGates" else
      .ok (stripInst XI0)

theorem indexerL_sound {XI0 Xs : ExecInst} (h : indexerL XI0 = .ok Xs) : IndexerCertL XI0 ∧ Xs = stripInst XI0 := by
  unfold indexerL at h
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
              refine ⟨⟨famGatesLFail_none.mp hf, ?_, ?_, ?_, c, hc, ?_⟩, rfl⟩
              · simpa using hl
              · simpa using hcan
              · simpa using hs
              · simpa using hg

def verdict9LVO (Xs : ExecInst) (root : Dg5) (pubIn : PE.PubIn) (H Hf : HFn) (FS FSf : FSFn) (z : List ℕ) (π : FlatProof) (πF : FixProof) :
    Except String P8PublicClaim :=
  if !inpCanOkL pubIn then .error "public input non-canonical" else
  match claimOf pubIn with
  | none => .error "claim: undecodable"
  | some c =>
    match verifyOnlineE' (vkO Xs pubIn root) H Hf FS FSf z π πF with
    | .error e => .error e
    | .ok _ => .ok c

theorem verdict9LVO_sound {XI0 Xs : ExecInst} {root : Dg5} {pubIn : PE.PubIn} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof}
    {πF : FixProof} {c : P8PublicClaim} (hcert : IndexerCertL XI0) (hvk : Xs = stripInst XI0) (hPubBind : pubIn = XI0.pubIn)
    (h : verdict9LVO Xs root pubIn H Hf FS FSf z π πF = .ok c) :
    famGatesL famJ9AL XI0 = true ∧ XI0.l = 170 ∧ linkGate9L XI0 c = true ∧ setupGates XI0 = true ∧
      verifyOnline' (vkOfRoot XI0 root) H Hf FS FSf z π πF = true := by
  obtain ⟨hf, hl, hcan, hs, c', hc', hg⟩ := hcert
  subst hvk hPubBind
  unfold verdict9LVO at h
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

end NockvmE2E.J9A.RunGate9L

#print axioms NockvmE2E.J9A.RunGate9L.famGatesL_sound
#print axioms NockvmE2E.J9A.RunGate9L.famGatesLFail_none
#print axioms NockvmE2E.J9A.RunGate9L.verdict9L_sound
#print axioms NockvmE2E.J9A.RunGate9L.verdict9LV_sound
#print axioms NockvmE2E.J9A.RunGate9L.indexerL_sound
#print axioms NockvmE2E.J9A.RunGate9L.verdict9LVO_sound
