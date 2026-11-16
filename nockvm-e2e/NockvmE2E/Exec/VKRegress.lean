/-
  NockvmE2E/Exec/VKRegress.lean   (HSpec  regression; executed, Mathlib-free)
  `nockvm-e2e-vkregress <inst.json>...`: the OLD setup (verbatim copy of the pre- VK.lean: `pmulFast`/`PF.ntt`, `PF.cosetLde`, `partial fxSubRoot`)
  against the NEW `setupData` (`prodLinR`, `cosetLdeR`, `fxSubRootF`): `polys`, `lde`, `levels`, `vk.cols`, `vk.root` must be identical
  under `hFix Tip5Core.hashVarlen`.  Prints the wall times.  Run under a memory cap.
-/
import NockvmE2E.Exec.VK
import NockvmE2E.Exec.Flat
import NockvmE2E.Exec.Tip5Core
import NockvmE2E.Exec.Tip5Fast
set_option autoImplicit false

namespace NockvmE2E.Exec.V.Old
open Lean NockvmE2E.Exec.VF NockvmE2E.Exec.J NockvmE2E.Exec.V

def ceilLog2 (n : Nat) : Nat := Id.run do
  let mut h := 0
  while 2 ^ h < n do h := h + 1
  return h

def pmulNaive (a b : Array G) : Array G := Id.run do
  let mut r : Array G := Array.replicate (a.size + b.size - 1) 0
  for i in [0:a.size] do
    for j in [0:b.size] do
      r := r.modify (i + j) (VF.add · (VF.mul a[i]! b[j]!))
  return r

def pmulFast (a b : Array G) : Array G :=
  if a.size ≤ 32 || b.size ≤ 32 then pmulNaive a b else
  let n := a.size + b.size - 1
  let m := ceilLog2 n
  let w := PF.root m
  let pad (x : Array G) : Array G := x ++ Array.replicate (2 ^ m - x.size) 0
  let fa := PF.ntt (pad a) m w
  let fb := PF.ntt (pad b) m w
  ((PF.intt ((Array.range (2 ^ m)).map fun i => VF.mul fa[i]! fb[i]!) m w)).extract 0 n

def prodLin (pts : Array G) : Nat → Nat → Nat → Array G
  | 0, _, _ => #[1]
  | f + 1, lo, hi =>
    if hi ≤ lo then #[1]
    else if hi - lo == 1 then #[VF.neg pts[lo]!, 1]
    else
      let mid := (lo + hi) / 2
      pmulFast (prodLin pts f lo mid) (prodLin pts f mid hi)

def fixPoly (X : ExecInst) (orb : Array G) : FixCol → Array G
  | .pre c => X.pre[c]!
  | .zh => prodLin orb (X.hN + 1) 0 X.hN
  | .zout t => prodLin orb (X.hN + 1) (tabHN X t) X.hN

partial def fxSubRoot (H : HFn) (j : Nat) (leafAt : Nat → G) (idx cnt lo : Nat) : Dg5 :=
  if cnt == 1 then [(leafAt lo).toNat, 0, 0, 0, 0] else
  let L := (cnt + 1) / 2
  H ([tagNode, j, idx] ++ fxSubRoot H j leafAt (2 * idx) L lo ++ fxSubRoot H j leafAt (2 * idx + 1) (cnt - L) (lo + L))

def fxRagLevels (H : HFn) (j W half : Nat) (lde : Array (Array G)) : Array (Array Dg5) :=
  let groups := fxParRange half 8 fun g =>
    let side (s : Nat) : Dg5 := fxSubRoot H j (fun r => (lde[r]!)[g + s * half]!) (2 * (half + g) + s) W 0
    H ([tagNode, j, half + g] ++ side 0 ++ side 1)
  fxLevelsUp H j groups (Nat.log2 half)

def setupData (X : ExecInst) (H : HFn) : Option VKData :=
  if !setupGates X then none else
  let cols := fixCols X
  let orb := orbitPts X
  let polys := cols.map (fixPoly X orb)
  let half0 := 2 ^ (X.nD - 1)
  let lde := polys.map fun p => PF.cosetLde p X.nD X.dGen
  let lv := fxRagLevels (hFix H) 0 cols.size half0 lde
  some { vk := { X := { X with pre := X.pre.map (fun _ => #[]) }, cols := cols, root := lv[0]![0]! },
         polys := polys, lde := lde, levels := lv }

end NockvmE2E.Exec.V.Old

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF NockvmE2E.Exec.J

def timedR {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let r := f ()
  let _ ← IO.FS.Stream.flush (← IO.getStdout)
  let t1 ← IO.monoMsNow
  pure (r, t1 - t0)

def regressOne (path : String) : IO Bool := do
  let X ← loadInst path
  IO.println s!"== {path}: nD={X.nD} hN={X.hN} k={X.k} nc={X.nc} setupGates={setupGates X}"
  let Hr : HFn := hFix Tip5Core.hashVarlen
  let (o, tOld) ← timedR fun _ =>
    match Old.setupData X Tip5Core.hashVarlen with
    | some d => (d.polys.size + d.lde.size + d.levels.size, some d) | none => (0, none)
  let (n, tNew) ← timedR fun _ =>
    match setupData X Tip5Core.hashVarlen with
    | some d => (d.polys.size + d.lde.size + d.levels.size, some d) | none => (0, none)
  let _ := Hr
  IO.println s!"  old setup {tOld} ms, new setup {tNew} ms"
  match o.2, n.2 with
  | some a, some b =>
    let pe := a.polys == b.polys
    let le := a.lde == b.lde
    let ve := a.levels == b.levels
    let ce := a.vk.cols == b.vk.cols
    let re := a.vk.root == b.vk.root
    IO.println s!"  polys equal {pe}, lde equal {le}, levels equal {ve}, cols equal {ce}, root equal {re} (root {b.vk.root}; {b.polys.size} polys)"
    pure (pe && le && ve && ce && re)
  | none, none => IO.println "  both none"; pure true
  | _, _ => IO.println "  MISMATCH none/some"; pure false

def mainR (args : List String) : IO UInt32 := do
  let mut ok := true
  for a in args do ok := (← regressOne a) && ok
  IO.println (if ok then "vkregress: ALL IDENTICAL" else "vkregress: FAILED")
  pure (if ok then 0 else 1)

end NockvmE2E.Exec.V

def main (args : List String) : IO UInt32 := NockvmE2E.Exec.V.mainR args
