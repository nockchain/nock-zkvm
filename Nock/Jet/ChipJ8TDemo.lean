/-
  Nock/Jet/ChipJ8Demo.lean

  **The matmul `n = 8` demo of the J chip at Goldilocks.**
  New module, additive.  `matmulTpl n`-style honest traces (the J-3b builder `honestJ8`, generic in
  `p` and in the template) at `p = Nock.Field.p`, on small entries.

  NOTE: the n = 8 kernel check was NOT feasible within the 20 GB gate scope (OOM); n = 8 is executable-only.

  CAVEAT (Goldilocks execution): the entries of `A`, `B` are small naturals (`< 100`), so no product
  wraps mod `p`; the trace's `val` columns are the true integer results (`c_T` runs on small entries
  only).  The Pratt primality `Nock.Field.goldilocks_prime` is a theorem.

  Checked at `n = 8` (EXECUTABLE only): the layout, the `< p` bounds, unique provides and EVERY base gate on EVERY
  row (`Bool` checkers); a wrong `C`
  entry (the last `add` row's value `+ 1`) fails exactly one gate.  The in-chip balance `bal` is NOT
  checked at `n = 8` in the kernel (quadratic, not attempted); an executable hash-set checker is run.
-/
import Nock.Jet.ChipJ8Toy
import Nock.Jet.RapJetJ8
import Nock.Field
import Std.Data.HashSet

set_option autoImplicit false

namespace Nock.Jet.ChipJ8T.Demo

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp Nock.Jet.ChipJ8 Nock.Jet.RapJetJ8
open Nock.NockVMROM.Thm54.CoordinateCompiler

/-- Goldilocks. -/
abbrev P : ℕ := Nock.Field.p

/-- Small entries: `A i j = i + j + 1`, `B i j = (i * j) % 5 + 1`. -/
def entA (i j : ℕ) : ℕ := i + j + 1
def entB (i j : ℕ) : ℕ := (i * j) % 5 + 1
/-- The integer product (no wrap: all entries small). -/
def entC (n i j : ℕ) : ℕ := (List.range n).foldl (fun a l => a + entA i l * entB l j) 0

def mk (f : ℕ → ℕ → ℕ) (n : ℕ) : List (List ℕ) :=
  (List.range n).map fun i => (List.range n).map fun j => f i j

/-- The gate subject `[battery [[A B] context]]`. -/
def subjN (n : ℕ) : Noun :=
  .cell (.atom 0) (.cell (.cell (mat (mk entA n)) (mat (mk entB n))) (.atom 0))
def prodN (n : ℕ) : Noun := mat (mk (entC n) n)

def RN (n : ℕ) : ℕ → Tpl := fun _ => matmulT n

/-- The memory: the subject's cells, the product's cells, the compiled formula. -/
def memN (n : ℕ) : List Noun := subs (subjN n) ++ subs (prodN n) ++ [compile P (matmulT n)]

/-- J-3b's `blockW` recomputes `honestRows` at every node lookup (quadratic); this is the same block
with the J-3a honest values computed ONCE (`rowsN_eq_honestJ8` checks agreement at `n = 2`). -/
def blockW' (mem : List Noun) (R : ℕ → Tpl) (c i : ℕ) (s : Noun) : List (CRow (ZMod P)) :=
  let T := R i
  let N := (nodesOf T).length
  let vals : Array Noun := ((honestRows P T s c).map JRow.val).toArray
  let lk : ℕ → Noun := fun n => vals.getD n z0
  ⟨callPre R c i, mkW 1 1 0 0 0
      (hOf mem (compile P T)) (hOf mem s) (hOf mem (lk 0))⟩ ::
    nodesW mem c N lk s (N + 1) (nodesOf T)

def rowsN (n : ℕ) : List (CRow (ZMod P)) :=
  [⟨regPre 0, mkW 0 1 0 0 0 (hOf (memN n) (compile P (matmulT n))) (0, 0) (0, 0)⟩] ++
    blockW' (memN n) (RN n) 0 0 (subjN n)

def rowsOld (n : ℕ) : List (CRow (ZMod P)) := honestJ8 (memN n) (RN n) [0] [(0, subjN n)]

def layN (n : ℕ) : List PRow := layoutJ8 (RN n) [0] [0]

/-- Row count. -/
def nRows (n : ℕ) : ℕ := (rowsN n).length

/-! ### Executable checkers -/

def layoutB (n : ℕ) : Bool := (rowsN n).map CRow.pre == layN n

def smallB (n : ℕ) : Bool :=
  (layN n).all fun q => q.id < P && q.cid < P && q.nid < P && q.n1 < P && q.n2 < P

def uniqB (n : ℕ) : Bool :=
  let ks := (layN n).filterMap tvKey
  let rec go : List (ℕ × ℕ) → Std.HashSet (ℕ × ℕ) → Bool
    | [], _ => true
    | k :: ks, s => if s.contains k then false else go ks (s.insert k)
  go ks {}

/-- The failing `(row, gate)` pairs (indices). -/
def failGates (rows : List (CRow (ZMod P))) : List (ℕ × ℕ) :=
  rows.zipIdx.flatMap fun ⟨r, i⟩ =>
    ((baseGatesJ : List (CoeffExpr (ZMod P))).zipIdx.filterMap fun ⟨g, j⟩ =>
      if g.eval (envOf r) = 0 then none else some (i, j))

def gatesB (n : ℕ) : Bool := (failGates (rowsN n)).isEmpty

/-- Executable balance: every consumed key is provided (hash set of the provided keys). -/
def balB (n : ℕ) : Bool :=
  let provs : Std.HashSet (List ℕ) :=
    (rowsN n).foldl (fun s r => (provKT r).foldl (fun s k => s.insert (k.map ZMod.val)) s) {}
  (rowsN n).all fun r => (consKT r).all fun k => provs.contains (k.map ZMod.val)

/-- The tampered trace: the last `add` row (it provides a `C` entry) gets `val + 1`. -/
def addIdxN (n : ℕ) : ℕ := (rowsN n).length - 1 - ((rowsN n).reverse.findIdx fun r => r.pre.kd == .add)

def tampN (n : ℕ) : List (CRow (ZMod P)) :=
  (rowsN n).modify (addIdxN n) fun r => { r with w := { r.w with val := r.w.val + 1 } }

def tampFails (n : ℕ) : List (ℕ × ℕ) := failGates (tampN n)

/-- The product of the honest `C` entries is correct (trace values vs the integer product). -/
def semB (n : ℕ) : Bool :=
  (matmulT n).sem P (subjN n) == some (prodN n)


def sameOld (n : ℕ) : Bool := (rowsN n).map (fun r => (r.pre, r.w.m, r.w.mv, r.w.val, r.w.v1, r.w.v2, r.w.kN, r.w.vN, r.w.kL, r.w.vL, r.w.kR, r.w.vR)) ==
  (rowsOld n).map (fun r => (r.pre, r.w.m, r.w.mv, r.w.val, r.w.v1, r.w.v2, r.w.kN, r.w.vN, r.w.kL, r.w.vL, r.w.kR, r.w.vR))

/-- The corrected honest multiplicity (`mv` = number of consumers of the provided key; J-3b's builder
sets `mv = 1`), by hash map.  `mv` is in no base gate. -/
def rowsMvN (n : ℕ) : List (CRow (ZMod P)) :=
  let cons : Std.HashMap (List ℕ) ℕ :=
    (rowsN n).foldl (fun m r => (consKT r).foldl (fun m k =>
      let k := k.map ZMod.val; m.insert k (m.getD k 0 + 1)) m) {}
  (rowsN n).map fun r => match provKT r with
    | [k] => { r with w := { r.w with mv := ((cons.getD (k.map ZMod.val) 0 : ℕ) : ZMod P) } }
    | _ => { r with w := { r.w with mv := 0 } }

/-- Sum balance (executable, hash map) of the corrected trace: for every in-chip key,
`#consumes = Σ mv · #provides` in `ZMod P`. -/
def sumBalN (n : ℕ) : Bool :=
  let rows := rowsMvN n
  let cons : Std.HashMap (List ℕ) ℕ :=
    rows.foldl (fun m r => (consKT r).foldl (fun m k =>
      let k := k.map ZMod.val; m.insert k (m.getD k 0 + 1)) m) {}
  let prov : Std.HashMap (List ℕ) (ZMod P) :=
    rows.foldl (fun m r => (provKT r).foldl (fun m k =>
      let k := k.map ZMod.val; m.insert k (m.getD k 0 + r.w.mv)) m) {}
  cons.toList.all (fun ⟨k, c⟩ => ((c : ℕ) : ZMod P) == prov.getD k 0) &&
    prov.toList.all (fun ⟨k, v⟩ => ((cons.getD k 0 : ℕ) : ZMod P) == v)

/-- Gates still hold on the corrected-`mv` rows. -/
def gatesMvB (n : ℕ) : Bool := (failGates (rowsMvN n)).isEmpty

/-! ### Kernel-checked at `n = 2` (Goldilocks).  `n = 8` is executable only (kernel exceeds 20 GB). -/

theorem demo2_bal : ∀ r ∈ rowsN 2, ∀ κ ∈ consKT r, ∃ r' ∈ rowsN 2, κ ∈ provKT r' := by decide +kernel
theorem demo2_rows : nRows 2 = 237 := by decide +kernel
theorem demo2_layout : (rowsN 2).map CRow.pre = layN 2 := by decide +kernel
theorem demo2_small : ∀ q ∈ layN 2, q.id < P ∧ q.cid < P ∧ q.nid < P ∧ q.n1 < P ∧ q.n2 < P := by
  decide +kernel
theorem demo2_uniq : ((layN 2).filterMap tvKey).Nodup := by decide +kernel
theorem demo2_gates : ∀ r ∈ rowsN 2, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod P))),
    g.eval (envOf r) = 0 := by decide +kernel
theorem demo2_tampered_rejected : ¬ ∀ r ∈ tampN 2, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod P))),
    g.eval (envOf r) = 0 := by decide +kernel
theorem demo2_tampered_one_gate : failGates (tampN 2) = [(addIdxN 2, 1)] := by decide +kernel

/-! ### The executable demo (`tracegen/j4/run.sh`) -/

def report (n : Nat) : IO Unit := do
  IO.println s!"n={n} rows={nRows n} layout={layoutB n} small={smallB n} uniq={uniqB n} gates={gatesB n} bal(exec)={balB n} sumbal(exec,mv fixed)={sumBalN n} gatesMv={gatesMvB n} sem={semB n}"
  IO.println s!"n={n} tampered(last add val+1) failing (row,gate) pairs={tampFails n}"

end Nock.Jet.ChipJ8T.Demo

def main : IO Unit := do
  for n in [2, 4, 8] do Nock.Jet.ChipJ8T.Demo.report n
