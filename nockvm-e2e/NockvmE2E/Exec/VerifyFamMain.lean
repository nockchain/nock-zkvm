/-
the family-generic verify exe.  Separate from `VerifyMain` (J-8 behaviour unchanged): importing `FamGates` (via nock/Mathlib)
adds a global `X` token that makes `VerifyMain`'s source fail to parse, and `VerifyMain` owns the root `main`.  `tip5H`/`tip5FS` below are
verbatim copies of `VerifyMain`'s (cross-checked by the executed ACCEPT on the J-8 samples through both exes).
  nockvm-e2e-verify-fam verify --family j8|j9a <inst.json> <proof.json>
  nockvm-e2e-verify-fam gates  --family j8|j9a <inst.json>
The IO is a thin `if` over the pure `famGatesFail`.
-/
import NockvmE2E.Exec.Verify
import NockvmE2E.Exec.Tip5Core
import NockvmE2E.Exec.Tip5Fast
import NockvmE2E.Exec.FamGates
import NockvmE2E.Exec.FlatFam
import NockvmE2E.J9A.RunGate9
import NockvmE2E.J9A.RunGate9V
import NockvmE2E.J9A.RunGate9L
import NockvmE2E.Z38.RunGate9LJ
import NockvmE2E.J9AL.RunGate9LB
import NockvmE2E.Z38.RunGate9LJB
import NockvmE2E.J9A.RunGate9VS
import NockvmE2E.J9AL.RunGate9LS
import NockvmE2E.Z38.RunGate9LJS
import NockvmE2E.Exec.FixProve
import NockvmE2E.Exec.FlatF
set_option autoImplicit false

namespace NockvmE2E.Exec.VFam
open Lean NockvmE2E.Exec.VF NockvmE2E.Exec.J NockvmE2E.Exec.V

def tip5H : HFn := Tip5Core.hashVarlen
def tip5FS : FSFn := fun key nl =>
  match key with
  | [] => []
  | z :: ms =>
    Tip5Core.squeeze (ms.foldl (fun s m => Tip5Core.absorb s Tip5Core.tMsg m)
      (Tip5Core.absorb (Tip5Core.hashVarlen [Tip5Core.tIni]) Tip5Core.tIn z)) nl

/-- the side proof's own Fiat-Shamir oracle (verbatim copy of `VerifyMain.tip5FSfix`) -/
def tip5FSfix : FSFn := fun key nl =>
  match key with
  | [] => []
  | z :: ms =>
    Tip5Core.squeeze (ms.foldl (fun s m => Tip5Core.absorb s Tip5Core.tMsg m)
      (Tip5Core.absorb (Tip5Core.hashVarlen [Tip5Core.tIni + 0x100]) Tip5Core.tIn z)) nl

/-- the side Merkle hash: `hFix tip5H`, exactly what `VerifyMain.verifyOnlineExe` (`verifyOnlineE`) uses -/
def hFixT : HFn := hFix tip5H

/-- `ζ` of the main proof (verbatim copy of `VerifyMain.mainZeta`) -/
def mainZeta (FS : FSFn) (z : List Nat) (π : FlatProof) : VF.K3 :=
  K3.ofLimbs (FS (z :: [[], π.roots[0]!, π.roots[1]!, π.roots[2]!, π.roots[3]!]) 3)

/-- digest of the public input (Tip5 over the bytes of its canonical JSON); the vk file carries it, the online exe compares -/
def pubDigest (p : NockvmE2E.Exec.PE.PubIn) : List Nat :=
  tip5H ((pubInJ p).compress.toUTF8.toList.map (·.toNat))

abbrev famJ9A := NockvmE2E.Exec.J9AChips.famJ9A
abbrev famJ9AL := NockvmE2E.Exec.J9ALChips.famJ9AL

def famOf? : String → Option NockvmE2E.Exec.ShapeF.Fam
  | "j8" => some NockvmE2E.Exec.ShapeF.famJ8
  | "j9a" => some NockvmE2E.Exec.J9AChips.famJ9A
  | "j9al" => some NockvmE2E.Exec.J9ALChips.famJ9AL
  | "j9alj" => some NockvmE2E.Exec.J9ALChips.famJ9AL   -- J-9 AL with template jets over `catJ` (verdicts `verdict9LJ*`)
  | _ => none

/-- j8: `loadInst` (unchanged); other families: `loadInstF` (their table layout and `pubMode`) -/
def loadFam (fam : String) (F : NockvmE2E.Exec.ShapeF.Fam) (path : String) : IO (Except String ExecInst) :=
  if fam == "j8" then do pure (.ok (← loadInst path))
  else try do pure (.ok (← NockvmE2E.Exec.FlatFam.loadInstF F path)) catch e => pure (.error (toString e))

def gateIO (fam : String) (F : NockvmE2E.Exec.ShapeF.Fam) (XI : ExecInst) : IO Bool :=
  -- S5: the theorem's `hl` (`l = 170`), next to the famGates call
  if XI.l != 170 then do IO.println s!"REJECT: l != 170 (l = {XI.l})"; pure false
  else if fam == "j9alj" then
  match NockvmE2E.Z38.RunGate9LJ.famGatesLJFail F XI with
  | some e => do IO.println s!"REJECT: famGates {fam}: {e}"; pure false
  | none => do IO.println s!"famGates {fam}: all seven gates pass (incl. jetPreOkF)"; pure true
  else if fam == "j9al" then
  match NockvmE2E.J9A.RunGate9L.famGatesLFail F XI with
  | some e => do IO.println s!"REJECT: famGates {fam}: {e}"; pure false
  | none => do IO.println s!"famGates {fam}: all six gates pass"; pure true
  else
  match NockvmE2E.Exec.FamGates.famGatesFail F XI with
  | some e => do IO.println s!"REJECT: famGates {fam}: {e}"; pure false
  | none => do IO.println s!"famGates {fam}: all five gates pass"; pure true

/-- negatives: an in-memory tamper of the loaded J-9 AL instance (the exe's `--tamper-*` flags) -/
def tamperL (t : String) (XI : ExecInst) : ExecInst :=
  if t == "--tamper-prim-code" then
    { XI with pubIn := { XI.pubIn with prims := XI.pubIn.prims.mapIdx fun i q => if i == 0 then { q with code := q.code + 1 } else q } }
  else if t == "--tamper-add-prim" then
    { XI with pubIn := { XI.pubIn with prims := XI.pubIn.prims ++ [{ id := 7, code := 1, idx := 5, hi := 0, lo := 43 }] } }
  else if t == "--tamper-preg" then
    match XI.tabs.toList.find? (·.chip.id == "aluChipJ9") with
    | some tb => { XI with pre := XI.pre.modify (tb.col0 + 3) fun a => if a.isEmpty then #[1] else a.modify 0 (· + 1) }
    | none => XI
  else XI

/-- the instance gates of `verdict9L` without the proof (`gates-only`): famGatesL, `l`, canonical public input, claim decode, `linkGate9L` -/
def gateOnlyL (XI : ExecInst) : IO Bool := do
  if !(← gateIO "j9al" NockvmE2E.Exec.J9ALChips.famJ9AL XI) then return false
  if !NockvmE2E.J9A.RunGate9L.inpCanOkL XI.pubIn then do IO.println "REJECT: public input non-canonical"; return false
  match NockvmE2E.J9A.RunGate9.claimOf XI.pubIn with
  | none => do IO.println "REJECT: claim: undecodable"; pure false
  | some c =>
    if !NockvmE2E.J9A.RunGate9L.linkGate9L XI c then do IO.println "REJECT: linkGate9L"; pure false
    else do IO.println "linkGate9L: ok"; pure true

/-- the instance gates of `verdict9LJ` without the proof: famGatesLJ, `l`, canonical public input (calls included), claim decode, `linkGate9LJ` -/
def gateOnlyLJ (XI : ExecInst) : IO Bool := do
  if !(← gateIO "j9alj" NockvmE2E.Exec.J9ALChips.famJ9AL XI) then return false
  if !NockvmE2E.J9A.RunGate9L.inpCanOkL XI.pubIn then do IO.println "REJECT: public input non-canonical"; return false
  match NockvmE2E.J9A.RunGate9.claimOf XI.pubIn with
  | none => do IO.println "REJECT: claim: undecodable"; pure false
  | some c =>
    if !NockvmE2E.Z38.RunGate9LJ.linkGate9LJ XI c then do IO.println "REJECT: linkGate9LJ"; pure false
    else do IO.println "linkGate9LJ: ok"; pure true

/-- the claim the exe prints (`[subject formula result]`, nouns as `[a b]`) -/
def renderNoun : Nock.Noun → String
  | .atom n => toString n
  | .cell a b => s!"[{renderNoun a} {renderNoun b}]"
def renderClaim (c : Nock.NockVMROM.Thm54.P8PublicClaim) : String :=
  s!"[{renderNoun c.subject} {renderNoun c.formula} {renderNoun c.result}]"

def main (args : List String) : IO UInt32 := do
  match args with
  | "gates-only" :: "--family" :: "j9al" :: instPath :: tam =>
    let XI ← match (← loadFam "j9al" NockvmE2E.Exec.J9ALChips.famJ9AL instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9al: {e}"; return 1
    let XI := tam.foldl (fun x t => tamperL t x) XI
    pure (if (← gateOnlyL XI) then 0 else 1)
  | "gates-only" :: "--family" :: "j9alj" :: instPath :: _ =>
    let XI ← match (← loadFam "j9alj" NockvmE2E.Exec.J9ALChips.famJ9AL instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9alj: {e}"; return 1
    pure (if (← gateOnlyLJ XI) then 0 else 1)
  -- SCRATCH PROBE (UNTRUSTED, not a verdict, no theorem): everything `verdict9L` runs EXCEPT the link gate (`LinkOK9L` rejects `hNof jet != 0`
  -- by design).  Reports each gate, then runs the honest quotient/FRI check `verifyFlatE`.  Never use its output as a verification.
  | ["probe-quot", "--family", "j9al", instPath, proofPath] =>
    let F := NockvmE2E.Exec.J9ALChips.famJ9AL
    let XI ← match (← loadFam "j9al" F instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9al: {e}"; return 1
    IO.println "PROBE (untrusted, link gate skipped; not a verification)"
    IO.println s!"hNof jetChipJ8 = {NockvmE2E.J8.InstJ8.hNof XI "jetChipJ8"}; pins {XI.pubIn.pins.length}; prims {XI.pubIn.prims.length}"
    IO.println s!"shapeOkF {NockvmE2E.Exec.ShapeF.shapeOkF F XI}  shapeXOkF {NockvmE2E.Exec.ShapeF.shapeXOkF F XI}  chipsOkF {NockvmE2E.Exec.ShapeF.chipsOkF F XI}"
    IO.println s!"maskOkFL {NockvmE2E.J9A.RunGate9L.maskOkFL F XI}  numeralOkF {NockvmE2E.J9A.LagrJ9A.numeralOkF F XI}  pregOkF {NockvmE2E.J9A.RunGate9L.pregOkF XI}  l={XI.l}  inpCanOkL {NockvmE2E.J9A.RunGate9L.inpCanOkL XI.pubIn}"
    match NockvmE2E.J9A.RunGate9.claimOf XI.pubIn with
    | none => IO.println "claim: undecodable"
    | some c => IO.println s!"claim decodes; linkGate9L (informational, expected false with a jet table) = {NockvmE2E.J9A.RunGate9L.linkGate9L XI c}"
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    let t0 ← IO.monoMsNow
    let r := verifyFlatE XI tip5H tip5FS z π
    let t1 ← IO.monoMsNow
    match r with
    | .ok _ => IO.println s!"PROBE quotient/FRI verifyFlatE: ACCEPT ({t1 - t0} ms)  [untrusted probe]"; pure 0
    | .error e => IO.println s!"PROBE quotient/FRI verifyFlatE: REJECT: {e} ({t1 - t0} ms)  [untrusted probe]"; pure 1
  | ["gates", "--family", fam, instPath] =>
    let some F := famOf? fam | IO.eprintln s!"unknown family {fam} (j8 | j9a)"; return 2
    let XI ← match (← loadFam fam F instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load {fam}: {e}"; return 1
    pure (if (← gateIO fam F XI) then 0 else 1)
  | ["verify", "--family", fam, instPath, proofPath] =>
    let some F := famOf? fam | IO.eprintln s!"unknown family {fam} (j8 | j9a)"; return 2
    let XI ← match (← loadFam fam F instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load {fam}: {e}"; return 1
    if !(← gateIO fam F XI) then return 1
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    let t0 ← IO.monoMsNow
    if fam == "j9a" then
      -- INST-PARSE S4 (route iii): the loader is untrusted; `verdict9` (kernel: `verdict9_sound`) re-checks the gates, `l = 170`, the
      -- claim decode and `linkGate9` on the instance actually loaded, then runs `verifyFlatE`
      let r := NockvmE2E.J9A.RunGate9.verdict9 XI tip5H tip5FS z π
      let t1 ← IO.monoMsNow
      match r with
      | .ok c => IO.println s!"ACCEPT-UNCOVERED claim {renderClaim c} (famGates {fam}; {t1 - t0} ms; no end-to-end theorem covers this command; use verify --vk or nockvm-e2e-verify-cert)"; pure 0
      | .error e => IO.println s!"REJECT: {e} ({t1 - t0} ms)"; pure 1
    else if fam == "j9alj" then
      let r := NockvmE2E.Z38.RunGate9LJ.verdict9LJ XI tip5H tip5FS z π
      let t1 ← IO.monoMsNow
      match r with
      | .ok c => IO.println s!"ACCEPT-UNCOVERED claim {renderClaim c} (famGates {fam}; {t1 - t0} ms; no end-to-end theorem covers this command; use verify --vk or nockvm-e2e-verify-cert)"; pure 0
      | .error e => IO.println s!"REJECT: {e} ({t1 - t0} ms)"; pure 1
    else if fam == "j9al" then
      let r := NockvmE2E.J9A.RunGate9L.verdict9L XI tip5H tip5FS z π
      let t1 ← IO.monoMsNow
      match r with
      | .ok c => IO.println s!"ACCEPT-UNCOVERED claim {renderClaim c} (famGates {fam}; {t1 - t0} ms; no end-to-end theorem covers this command; use verify --vk or nockvm-e2e-verify-cert)"; pure 0
      | .error e => IO.println s!"REJECT: {e} ({t1 - t0} ms)"; pure 1
    else
    let r := verifyFlatE XI tip5H tip5FS z π
    let t1 ← IO.monoMsNow
    match r with
    | .ok _ => IO.println s!"ACCEPT-UNCOVERED (famGates {fam}; {t1 - t0} ms; no end-to-end theorem covers this command; use verify --vk or nockvm-e2e-verify-cert)"; pure 0
    | .error e => IO.println s!"REJECT: {e} ({t1 - t0} ms)"; pure 1
  -- the J-9 A online (succinct) path.  The VK file is `{version, root, inst}`; the loaded instance is the FULL one (the instance
  -- gates need it); `verdict9V` builds the stripped VK from it and the committed root.
  | ["vk-setup", "--family", "j9a", instPath, vkPath] =>
    let XI ← match (← loadFam "j9a" famJ9A instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9a: {e}"; return 1
    if !(← gateIO "j9a" famJ9A XI) then return 1
    let t0 ← IO.monoMsNow
    match setupData' XI hFixT with
    | none => IO.println "REJECT: setup gates fail"; pure 1
    | some D =>
      IO.FS.writeFile vkPath (Json.mkObj [("version", natJ 1), ("root", limbsJ D.vk.root), ("inst", Json.str instPath)]).compress
      IO.println s!"vk-setup: ok, {D.vk.cols.size} fixed columns, root {D.vk.root} ({(← IO.monoMsNow) - t0} ms)"
      pure 0
  | ["fix-prove", "--family", "j9a", instPath, proofPath, fixPath] =>
    let XI ← match (← loadFam "j9a" famJ9A instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9a: {e}"; return 1
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    -- thin wrapper over the prover's function (`FixProve.proveFixFor`)
    let t0 ← IO.monoMsNow
    match NockvmE2E.Exec.FixProve.proveFixFor XI z π with
    | none => IO.println "REJECT: setup gates fail"; pure 1
    | some πF =>
      IO.FS.writeFile fixPath (FixProof.toJson πF).compress
      IO.println s!"fix-prove: ok ({(← IO.monoMsNow) - t0} ms)"
      pure 0
  -- INDEXER.  Instance gates + setup once on the FULL instance; writes the vk file
  -- `{version 2, root, pubDigest, inst}` (`inst` = the instance JSON with `pre` and `pubIn` erased) and the public input `pub.json`.
  | ["index", "--family", "j9a", instPath, vkPath, pubPath] =>
    let XI ← match (← loadFam "j9a" famJ9A instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9a: {e}"; return 1
    let t0 ← IO.monoMsNow
    match NockvmE2E.J9A.RunGate9V.indexer XI with
    | .error e => IO.println s!"REJECT: indexer: {e}"; pure 1
    | .ok _ =>
    match setupData' XI hFixT with
    | none => IO.println "REJECT: setup gates fail"; pure 1
    | some D =>
      let j ← readJson instPath
      let stripped := (j.setObjVal! "pre" (Json.arr ((arr (get j "pre")).map fun _ => Json.arr #[]))).setObjVal! "pubIn"
        (pubInJ { claimCells := [], pins := [] })
      let pubJ := pubInJ XI.pubIn
      IO.FS.writeFile pubPath pubJ.compress
      IO.FS.writeFile vkPath (Json.mkObj [("version", natJ 2), ("root", limbsJ D.vk.root), ("pubDigest", limbsJ (pubDigest XI.pubIn)),
        ("inst", stripped)]).compress
      IO.println s!"index: ok, {D.vk.cols.size} fixed columns, root {D.vk.root} ({(← IO.monoMsNow) - t0} ms)"
      pure 0
  -- ONLINE.  Only vk.json + pub.json + proof + fix; the full instance is never loaded.
  | ["verify-online", "--family", "j9a", vkPath, pubPath, proofPath, fixPath] =>
    let t0 ← IO.monoMsNow
    let vj ← readJson vkPath
    let root ← IO.ofExcept ((limbsE "root" (get vj "root")).mapError IO.userError)
    let dg ← IO.ofExcept ((limbsE "pubDigest" (get vj "pubDigest")).mapError IO.userError)
    let pubIn ← IO.ofExcept ((pubInE (← readJson pubPath)).mapError IO.userError)
    if pubDigest pubIn != dg then
      IO.println "REJECT: public input digest differs from the vk's"; return 1
    let ij := get vj "inst"
    let chips ← (arr (get ij "tabs")).mapM fun t => NockvmE2E.Exec.Tr.loadChip (str (get t "chip"))
    let F := famJ9A
    let Xs ← match NockvmE2E.Exec.FlatF.parseInstF F.ids F.tabOf F.tabLens F.pubMode ij chips with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: vk instance: {e}"; return 1
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    let πF ← IO.ofExcept ((FixProof.ofJson (← readJson fixPath)).mapError IO.userError)
    let t1 ← IO.monoMsNow
    let r := NockvmE2E.J9A.RunGate9V.verdict9VO Xs root pubIn tip5H hFixT tip5FS tip5FSfix z π πF
    let t2 ← IO.monoMsNow
    match r with
    | .ok c => IO.println s!"ACCEPT-UNCOVERED claim {renderClaim c} (online, vk only; load {t1 - t0} ms, verify {t2 - t1} ms; no end-to-end theorem covers this command; use verify --vk or nockvm-e2e-verify-cert)"; pure 0
    | .error e => IO.println s!"REJECT: {e} (load {t1 - t0} ms, verify {t2 - t1} ms)"; pure 1
  | ["verify", "--family", "j9a", "--vk", vkPath, instPath, proofPath, fixPath] =>
    let vj ← readJson vkPath
    let root ← IO.ofExcept ((limbsE "root" (get vj "root")).mapError IO.userError)
    let XI ← match (← loadFam "j9a" famJ9A instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9a: {e}"; return 1
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    let πF ← IO.ofExcept ((FixProof.ofJson (← readJson fixPath)).mapError IO.userError)
    let t0 ← IO.monoMsNow
    let r := NockvmE2E.J9A.RunGate9VS.verdict9VS XI root tip5H hFixT tip5FS tip5FSfix z π πF
    let t1 ← IO.monoMsNow
    match r with
    | .ok c => IO.println s!"ACCEPT claim {renderClaim c} (online, VK; famGates j9a; {t1 - t0} ms)"; pure 0
    | .error e => IO.println s!"REJECT: {e} ({t1 - t0} ms)"; pure 1
  -- the J-9 AL online path (twins of the j9a arms above; `verdict9LV` is the verdict of the headline `nock_e2e_J9AL_succinct`)
  | ["vk-setup", "--family", "j9al", instPath, vkPath] =>
    let XI ← match (← loadFam "j9al" famJ9AL instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9al: {e}"; return 1
    if !(← gateIO "j9al" famJ9AL XI) then return 1
    let t0 ← IO.monoMsNow
    match setupData' XI hFixT with
    | none => IO.println "REJECT: setup gates fail"; pure 1
    | some D =>
      IO.FS.writeFile vkPath (Json.mkObj [("version", natJ 1), ("root", limbsJ D.vk.root), ("inst", Json.str instPath)]).compress
      IO.println s!"vk-setup: ok, {D.vk.cols.size} fixed columns, root {D.vk.root} ({(← IO.monoMsNow) - t0} ms)"
      pure 0
  | ["fix-prove", "--family", "j9al", instPath, proofPath, fixPath] =>
    let XI ← match (← loadFam "j9al" famJ9AL instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9al: {e}"; return 1
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    let t0 ← IO.monoMsNow
    match NockvmE2E.Exec.FixProve.proveFixFor XI z π with
    | none => IO.println "REJECT: setup gates fail"; pure 1
    | some πF =>
      IO.FS.writeFile fixPath (FixProof.toJson πF).compress
      IO.println s!"fix-prove: ok ({(← IO.monoMsNow) - t0} ms)"
      pure 0
  | ["verify", "--family", "j9al", "--vk", vkPath, instPath, proofPath, fixPath] =>
    let vj ← readJson vkPath
    let root ← IO.ofExcept ((limbsE "root" (get vj "root")).mapError IO.userError)
    let XI ← match (← loadFam "j9al" famJ9AL instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9al: {e}"; return 1
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    let πF ← IO.ofExcept ((FixProof.ofJson (← readJson fixPath)).mapError IO.userError)
    let t0 ← IO.monoMsNow
    -- `verdict9LVS` (`verdict9LVB` at the recomputed VK root; `verdict9LVS_sound.1` is the premise of `nock_e2e_J9AL_succinct_B`; corollary `_S`)
    let r := NockvmE2E.J9AL.RunGate9LS.verdict9LVS XI root tip5H hFixT tip5FS tip5FSfix z π πF
    let t1 ← IO.monoMsNow
    match r with
    | .ok c => IO.println s!"ACCEPT claim {renderClaim c} (online, VK; famGates j9al; {t1 - t0} ms)"; pure 0
    | .error e => IO.println s!"REJECT: {e} ({t1 - t0} ms)"; pure 1
  -- the J-9 AL template-jet path (`j9alj`): twins of EVERY j9al arm; verdicts `verdict9LJ` / `verdict9LJV` / `indexerLJ` / `verdict9LJVO`
  | ["vk-setup", "--family", "j9alj", instPath, vkPath] =>
    let XI ← match (← loadFam "j9alj" famJ9AL instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9alj: {e}"; return 1
    if !(← gateIO "j9alj" famJ9AL XI) then return 1
    let t0 ← IO.monoMsNow
    match setupData' XI hFixT with
    | none => IO.println "REJECT: setup gates fail"; pure 1
    | some D =>
      IO.FS.writeFile vkPath (Json.mkObj [("version", natJ 1), ("root", limbsJ D.vk.root), ("inst", Json.str instPath)]).compress
      IO.println s!"vk-setup: ok, {D.vk.cols.size} fixed columns, root {D.vk.root} ({(← IO.monoMsNow) - t0} ms)"
      pure 0
  | ["fix-prove", "--family", "j9alj", instPath, proofPath, fixPath] =>
    let XI ← match (← loadFam "j9alj" famJ9AL instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9alj: {e}"; return 1
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    let t0 ← IO.monoMsNow
    match NockvmE2E.Exec.FixProve.proveFixFor XI z π with
    | none => IO.println "REJECT: setup gates fail"; pure 1
    | some πF =>
      IO.FS.writeFile fixPath (FixProof.toJson πF).compress
      IO.println s!"fix-prove: ok ({(← IO.monoMsNow) - t0} ms)"
      pure 0
  | ["verify", "--family", "j9alj", "--vk", vkPath, instPath, proofPath, fixPath] =>
    let vj ← readJson vkPath
    let root ← IO.ofExcept ((limbsE "root" (get vj "root")).mapError IO.userError)
    let XI ← match (← loadFam "j9alj" famJ9AL instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9alj: {e}"; return 1
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    let πF ← IO.ofExcept ((FixProof.ofJson (← readJson fixPath)).mapError IO.userError)
    let t0 ← IO.monoMsNow
    -- `verdict9LJVS` (`verdict9LJVB` at the recomputed VK root; corollary `nock_e2e_J9ALJ_succinct_S`)
    let r := NockvmE2E.Z38.RunGate9LJS.verdict9LJVS XI root tip5H hFixT tip5FS tip5FSfix z π πF
    let t1 ← IO.monoMsNow
    match r with
    | .ok c => IO.println s!"ACCEPT claim {renderClaim c} (online, VK; famGates j9alj; {t1 - t0} ms)"; pure 0
    | .error e => IO.println s!"REJECT: {e} ({t1 - t0} ms)"; pure 1
  | ["index", "--family", "j9alj", instPath, vkPath, pubPath] =>
    let XI ← match (← loadFam "j9alj" famJ9AL instPath) with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: load j9alj: {e}"; return 1
    let t0 ← IO.monoMsNow
    match NockvmE2E.Z38.RunGate9LJ.indexerLJ XI with
    | .error e => IO.println s!"REJECT: indexer: {e}"; pure 1
    | .ok _ =>
    match setupData' XI hFixT with
    | none => IO.println "REJECT: setup gates fail"; pure 1
    | some D =>
      let j ← readJson instPath
      let stripped := (j.setObjVal! "pre" (Json.arr ((arr (get j "pre")).map fun _ => Json.arr #[]))).setObjVal! "pubIn"
        (pubInJ { claimCells := [], pins := [] })
      let pubJ := pubInJ XI.pubIn
      IO.FS.writeFile pubPath pubJ.compress
      IO.FS.writeFile vkPath (Json.mkObj [("version", natJ 2), ("root", limbsJ D.vk.root), ("pubDigest", limbsJ (pubDigest XI.pubIn)),
        ("inst", stripped)]).compress
      IO.println s!"index: ok, {D.vk.cols.size} fixed columns, root {D.vk.root} ({(← IO.monoMsNow) - t0} ms)"
      pure 0
  | ["verify-online", "--family", "j9alj", vkPath, pubPath, proofPath, fixPath] =>
    let t0 ← IO.monoMsNow
    let vj ← readJson vkPath
    let root ← IO.ofExcept ((limbsE "root" (get vj "root")).mapError IO.userError)
    let dg ← IO.ofExcept ((limbsE "pubDigest" (get vj "pubDigest")).mapError IO.userError)
    let pubIn ← IO.ofExcept ((pubInE (← readJson pubPath)).mapError IO.userError)
    if pubDigest pubIn != dg then
      IO.println "REJECT: public input digest differs from the vk's"; return 1
    let ij := get vj "inst"
    let chips ← (arr (get ij "tabs")).mapM fun t => NockvmE2E.Exec.Tr.loadChip (str (get t "chip"))
    let F := famJ9AL
    let Xs ← match NockvmE2E.Exec.FlatF.parseInstF F.ids F.tabOf F.tabLens F.pubMode ij chips with
      | .ok x => pure x
      | .error e => do IO.println s!"REJECT: vk instance: {e}"; return 1
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    let πF ← IO.ofExcept ((FixProof.ofJson (← readJson fixPath)).mapError IO.userError)
    let t1 ← IO.monoMsNow
    let r := NockvmE2E.Z38.RunGate9LJB.verdict9LJVOB Xs root pubIn tip5H hFixT tip5FS tip5FSfix z π πF
    let t2 ← IO.monoMsNow
    match r with
    | .ok c => IO.println s!"ACCEPT-UNCOVERED claim {renderClaim c} (online, vk only; load {t1 - t0} ms, verify {t2 - t1} ms; no end-to-end theorem covers this command; use verify --vk or nockvm-e2e-verify-cert)"; pure 0
    | .error e => IO.println s!"REJECT: {e} (load {t1 - t0} ms, verify {t2 - t1} ms)"; pure 1
  | _ =>
    IO.eprintln "usage: nockvm-e2e-verify-fam probe-quot --family j9al <inst> <proof> (Z38-1 UNTRUSTED probe, link gate skipped) | gates --family j8|j9a <inst> | verify --family j8|j9a <inst> <proof> | vk-setup --family j9a <inst> <vk.json> | fix-prove --family j9a <inst> <proof> <fix.json> | verify --family j9a --vk <vk.json> <inst> <proof> <fix.json> | gates|gates-only|verify --family j9alj | vk-setup|fix-prove|index --family j9alj | verify --family j9alj --vk <vk> <inst> <proof> <fix> | verify-online --family j9alj <vk> <pub> <proof> <fix> (Z38-2) | vk-setup|fix-prove --family j9al (as j9a) | verify --family j9al --vk <vk.json> <inst> <proof> <fix.json>"
    pure 2

end NockvmE2E.Exec.VFam

def main (args : List String) : IO UInt32 := NockvmE2E.Exec.VFam.main args
