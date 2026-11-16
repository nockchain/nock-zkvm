/-
`nockvm-e2e-verify-cert`: the certified verifier exe.  `main` is exactly `print ∘ verifyReport ∘ readFiles`: it reads the files named on the command
line (and the chip documents the instance names, via the pure `chipPaths`), hands the BYTES to the pure `Cert.verifyReport`, prints its line, exits with
its code.  No other logic.  The kernel theorems about the printed ACCEPT are `Cert.verifyBytesL_sound` / `verifyBytesLJ_sound` (`CertSoundL.lean`,
`CertSoundLJ.lean`); trusted base: this file's file I/O, the Lean compiler and runtime, the C toolchain (`CERTIFIED.md`).
  nockvm-e2e-verify-cert verify --family j9al|j9alj --vk <vk.json> <inst.json> <proof.json> <fix.json>
-/
import NockvmE2E.Exec.CertBytes
set_option autoImplicit false

open NockvmE2E.Exec.Cert in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["verify", "--family", fam, "--vk", vkPath, instPath, proofPath, fixPath] =>
    let vkB ← IO.FS.readBinFile vkPath
    let instB ← IO.FS.readBinFile instPath
    let chipBs ← (match chipPaths instB with | .ok ps => ps | .error _ => []).mapM IO.FS.readBinFile
    let proofB ← IO.FS.readBinFile proofPath
    let fixB ← IO.FS.readBinFile fixPath
    let (rc, line) := verifyReport fam vkB instB chipBs proofB fixB
    IO.println line
    pure rc
  | _ =>
    IO.eprintln "usage: nockvm-e2e-verify-cert verify --family j9al|j9alj --vk <vk.json> <inst.json> <proof.json> <fix.json>"
    pure 2
