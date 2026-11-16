/-
The BYTES layer of the certified verifier (`nockvm-e2e-verify-cert`, `CERTIFIED.md`).

`verifyBytesL` / `verifyBytesLJ` are PURE functions of the file bytes: vk file, instance file, the chip documents the instance names, proof file, fix file.
They parse (`Lean.Json.parse` + the exe's own `Flat` decoders, all `Except String`), then run `verdict9LVS` / `verdict9LJVS` at the Tip5 oracles.
`main` of `VerifyCertMain` is `print ∘ verifyBytes ∘ readFiles` and nothing else.

Soundness needs no parser correctness: the `_S` theorems quantify over EVERY `XI0 root z π πF`, so `verifyBytes*_spec` only has to say that an `.ok`
comes from `verdict9LVS` / `verdict9LJVS` at SOME parsed values (`CertSound*.lean` then applies `nock_e2e_J9AL(J)_succinct_S`).
The chips are NOT trusted: `chipsOkF` (inside the verdict's gates) compares every parsed chip with the family's literal.
-/
import NockvmE2E.Exec.Verify
import NockvmE2E.Exec.Tip5Core
import NockvmE2E.Exec.Tip5Fast
import NockvmE2E.Exec.FlatFam
import NockvmE2E.J9AL.RunGate9LS
import NockvmE2E.Z38.RunGate9LJS
import NockvmE2E.Exec.FixProve
import NockvmE2E.Exec.FlatF
set_option autoImplicit false

namespace NockvmE2E.Exec.Cert
open Lean NockvmE2E.Exec.VF NockvmE2E.Exec.J NockvmE2E.Exec.V

/-! The Tip5 oracles: verbatim copies of `VerifyFamMain.tip5H` / `tip5FS` / `tip5FSfix` / `hFixT` (that file owns `main`, so it cannot be imported). -/
def tip5H : HFn := Tip5Core.hashVarlen
def tip5FS : FSFn := fun key nl =>
  match key with
  | [] => []
  | z :: ms =>
    Tip5Core.squeeze (ms.foldl (fun s m => Tip5Core.absorb s Tip5Core.tMsg m)
      (Tip5Core.absorb (Tip5Core.hashVarlen [Tip5Core.tIni]) Tip5Core.tIn z)) nl
def tip5FSfix : FSFn := fun key nl =>
  match key with
  | [] => []
  | z :: ms =>
    Tip5Core.squeeze (ms.foldl (fun s m => Tip5Core.absorb s Tip5Core.tMsg m)
      (Tip5Core.absorb (Tip5Core.hashVarlen [Tip5Core.tIni + 0x100]) Tip5Core.tIn z)) nl
def hFixT : HFn := hFix tip5H

abbrev famJ9AL := NockvmE2E.Exec.J9ALChips.famJ9AL

/-- bytes → JSON (UTF-8 check, then core's parser) -/
def parseBytes (b : ByteArray) : Except String Json :=
  match String.fromUTF8? b with
  | some s => Json.parse s
  | none => .error "not valid UTF-8"

/-- pure twin of `Tr.loadChip` (same field reads; the chip is untrusted: `chipsOkF` re-checks it against the family literal) -/
def chipOfJson (d : Json) : Except String Tr.Chip := do
  let c := (arr (get d "chips"))[0]!
  let sh ← (arr (get c "shared")).mapM Tr.parseEx
  let sk := (arr (get c "shared")).foldl (fun a j => a.push (Tr.isKJ a j)) #[]
  let ck := (arr (get c "constraints")).map fun j => Tr.isKJ sk (get j "expr")
  let cons ← (arr (get c "constraints")).mapM fun j => do
    let k ← match str (get j "kind") with
      | "row" => pure 0 | "transition" => pure 1 | "boundary" => pure 2 | "terminal" => pure 3
      | s => throw s!"constraint kind {s}"
    let e ← Tr.parseEx (get j "expr")
    pure ({ kind := k, round := nat (get j "round"), deg := nat (get j "degree"), e := e : Tr.Con })
  let cols := arr (get c "columns")
  let colRound := cols.map fun x => nat (get x "round")
  let bc := (cols.filter fun x => bool (get (get x "field") "base")).size
  pure { id := str (get c "id"), shared := sh, cons := cons, colRound := colRound, sharedK := sk, consK := ck, baseCols := bc, width := cols.size }

/-- the chip files the instance names (`main` reads them; the order is that of `tabs`) -/
def chipPaths (instB : ByteArray) : Except String (List String) := do
  let j ← parseBytes instB
  pure ((arr (get j "tabs")).toList.map fun t => str (get t "chip"))

/-- all inputs of one verification, decoded: `(XI0, vk root, z, π, πF)` -/
def parseInputs (F : NockvmE2E.Exec.ShapeF.Fam) (vkB instB : ByteArray) (chipBs : List ByteArray) (proofB fixB : ByteArray) :
    Except String (ExecInst × Dg5 × List Nat × FlatProof × FixProof) := do
  let vj ← parseBytes vkB
  let root ← limbsE "root" (get vj "root")
  let ij ← parseBytes instB
  let chips ← chipBs.toArray.mapM fun b => do chipOfJson (← parseBytes b)
  let XI ← NockvmE2E.Exec.FlatF.parseInstF F.ids F.tabOf F.tabLens F.pubMode ij chips
  let pj ← parseBytes proofB
  let π ← FlatProof.ofJson pj
  let z ← natsE "z" (get pj "z")
  let πF ← FixProof.ofJson (← parseBytes fixB)
  pure (XI, root, z.toList, π, πF)

/-- `j9al` certified verdict: the bytes → `verdict9LVS` at the Tip5 oracles -/
def verifyBytesL (vkB instB : ByteArray) (chipBs : List ByteArray) (proofB fixB : ByteArray) : Except String Nock.NockVMROM.Thm54.P8PublicClaim := do
  let (XI, root, z, π, πF) ← parseInputs famJ9AL vkB instB chipBs proofB fixB
  NockvmE2E.J9AL.RunGate9LS.verdict9LVS XI root tip5H hFixT tip5FS tip5FSfix z π πF

/-- `j9alj` certified verdict: the bytes → `verdict9LJVS` -/
def verifyBytesLJ (vkB instB : ByteArray) (chipBs : List ByteArray) (proofB fixB : ByteArray) : Except String Nock.NockVMROM.Thm54.P8PublicClaim := do
  let (XI, root, z, π, πF) ← parseInputs famJ9AL vkB instB chipBs proofB fixB
  NockvmE2E.Z38.RunGate9LJS.verdict9LJVS XI root tip5H hFixT tip5FS tip5FSfix z π πF

theorem verifyBytesL_spec {vkB instB : ByteArray} {chipBs : List ByteArray} {proofB fixB : ByteArray} {c : Nock.NockVMROM.Thm54.P8PublicClaim}
    (h : verifyBytesL vkB instB chipBs proofB fixB = .ok c) :
    ∃ (XI : ExecInst) (root : Dg5) (z : List Nat) (π : FlatProof) (πF : FixProof),
      parseInputs famJ9AL vkB instB chipBs proofB fixB = .ok (XI, root, z, π, πF) ∧
      NockvmE2E.J9AL.RunGate9LS.verdict9LVS XI root tip5H hFixT tip5FS tip5FSfix z π πF = .ok c := by
  unfold verifyBytesL at h
  cases hp : parseInputs famJ9AL vkB instB chipBs proofB fixB with
  | error e => rw [hp] at h; exact absurd h (by simp [bind, Except.bind])
  | ok r =>
    obtain ⟨XI, root, z, π, πF⟩ := r
    rw [hp] at h
    exact ⟨XI, root, z, π, πF, rfl, h⟩

theorem verifyBytesLJ_spec {vkB instB : ByteArray} {chipBs : List ByteArray} {proofB fixB : ByteArray} {c : Nock.NockVMROM.Thm54.P8PublicClaim}
    (h : verifyBytesLJ vkB instB chipBs proofB fixB = .ok c) :
    ∃ (XI : ExecInst) (root : Dg5) (z : List Nat) (π : FlatProof) (πF : FixProof),
      parseInputs famJ9AL vkB instB chipBs proofB fixB = .ok (XI, root, z, π, πF) ∧
      NockvmE2E.Z38.RunGate9LJS.verdict9LJVS XI root tip5H hFixT tip5FS tip5FSfix z π πF = .ok c := by
  unfold verifyBytesLJ at h
  cases hp : parseInputs famJ9AL vkB instB chipBs proofB fixB with
  | error e => rw [hp] at h; exact absurd h (by simp [bind, Except.bind])
  | ok r =>
    obtain ⟨XI, root, z, π, πF⟩ := r
    rw [hp] at h
    exact ⟨XI, root, z, π, πF, rfl, h⟩

/-- the claim the exe prints (`[subject formula result]`, nouns as `[a b]`) -/
def renderNoun : Nock.Noun → String
  | .atom n => toString n
  | .cell a b => s!"[{renderNoun a} {renderNoun b}]"
def renderClaim (c : Nock.NockVMROM.Thm54.P8PublicClaim) : String :=
  s!"[{renderNoun c.subject} {renderNoun c.formula} {renderNoun c.result}]"

/-- family dispatch + the printed line (pure); exit code 0 iff ACCEPT -/
def verifyReport (fam : String) (vkB instB : ByteArray) (chipBs : List ByteArray) (proofB fixB : ByteArray) : UInt32 × String :=
  let r := if fam == "j9al" then verifyBytesL vkB instB chipBs proofB fixB
    else if fam == "j9alj" then verifyBytesLJ vkB instB chipBs proofB fixB
    else .error s!"unknown family {fam} (j9al | j9alj)"
  match r with
  | .ok c => (0, s!"ACCEPT claim {renderClaim c} (certified; famGates {fam})")
  | .error e => (1, s!"REJECT: {e}")

end NockvmE2E.Exec.Cert
