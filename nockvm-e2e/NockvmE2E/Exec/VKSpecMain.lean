/-
  NockvmE2E/Exec/VKSpecMain.lean   (pcs (b); executed, Mathlib-free)
  `nockvm-e2e-vkspec <inst.json>...`: for each J-8 instance, compare the deployed `setup'` root with the spec root `vkSpec` under
  (1) the real side hash `hFix tip5H`, (2) a toy hash (so the comparison does not depend on Tip5), (3) negative control: spec of an instance
  with one `pre` coefficient + 1 must differ from the deployed root.  Run under a memory cap.
-/
import NockvmE2E.Exec.VKSpecExe
import NockvmE2E.Exec.Flat
set_option autoImplicit false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF NockvmE2E.Exec.J

def toyHash : HFn := fun l => [l.foldl (fun a x => (a * 1000003 + x + 17) % 18446744069414584321) 5, l.length, 1, 2, 3]

def timedM {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let r := f ()
  let _ ← IO.FS.Stream.flush (← IO.getStdout)
  let t1 ← IO.monoMsNow
  pure (r, t1 - t0)

def checkOne (path : String) : IO Bool := do
  let X ← loadInst path
  IO.println s!"== {path}: nD={X.nD} hN={X.hN} k={X.k} nc={X.nc} setupGates={setupGates X}"
  let Hr : HFn := hFix Tip5Core.hashVarlen
  let (ok1, t1) ← timedM fun _ => specRootCheck X Hr
  IO.println s!"  real Tip5 (hFix): deployed root == spec root && cols equal: {ok1} ({t1} ms)"
  let (ok2, t2) ← timedM fun _ => specRootCheck X toyHash
  IO.println s!"  toy hash: {ok2} ({t2} ms)"
  match setup' X Hr with
  | none => IO.println "  setup' = none"; pure false
  | some vk =>
    IO.println s!"  deployed root {vk.root}  cols {vk.cols.size}"
    IO.println s!"  spec root     {(vkSpec X Hr).root}"
    -- negative control: one pre coefficient + 1
    match (List.range X.nc).find? (fun c => X.colKind[c]! == 1 && X.pre[c]!.size > 0) with
    | none => pure (ok1 && ok2)
    | some c =>
      let Xb := { X with pre := X.pre.set! c (X.pre[c]!.modify 0 (· + 1)) }
      let ne := (vkSpec Xb Hr).root != vk.root
      IO.println s!"  negative control (pre[{c}][0] + 1 changes the spec root): {ne}"
      pure (ok1 && ok2 && ne)

def main (args : List String) : IO UInt32 := do
  let mut ok := true
  for a in args do ok := (← checkOne a) && ok
  IO.println (if ok then "vkspec-check: ALL OK" else "vkspec-check: FAILED")
  pure (if ok then 0 else 1)

end NockvmE2E.Exec.V

def main (args : List String) : IO UInt32 := NockvmE2E.Exec.V.main args
