/-
  NockvmE2E/Exec/Trace.lean

  Loads (a) a J-8 chip DAG document `j8_<chip>.json` (`shared` nodes + `constraints`, SCHEMA.md "DAG documents"),
  (b) a trace `<chip>.trace.json` (round-0 base columns + round-1/2 𝕂 columns, expanded to base-coordinate columns),
  (c) `coins.json` (the 19 frame coins + 22 derived γ'-power slots, as 𝕂 values by slot),
  and evaluates the constraints with ONE interpreter in which every value is an `E3` (base values lifted), so the same
  `evalCons` serves a row of the trace, an LDE point (base inputs) and the DEEP point ζ (𝕂 inputs).
  Semantics follow `nockvm-air/src/check.rs`/`expr.rs`: `ext_var` reads columns `baseCols + 3e + t` (cur/next) as
  `Σ_t v_t x^t`; public 𝕂 value `e` = flat public slots `3e..3e+2`; `ext_chal i` = coin/derived slot `i`.
-/
import NockvmE2E.Exec.Json
import NockvmE2E.Exec.ProverField
set_option autoImplicit false

namespace NockvmE2E.Exec.Tr
open Lean NockvmE2E.Exec.PF NockvmE2E.Exec.J

inductive Ex where
  | var (kind : Nat) (i : Nat)      -- kind 0 = trace_cur, 1 = trace_next, 2 = public_val
  | cF (v : UInt64)
  | add (a b : Ex) | sub (a b : Ex) | mul (a b : Ex) | neg (a : Ex) | pow (a : Ex) (n : Nat)
  | extVar (kind : Nat) (e : Nat)
  | chal (i : Nat)
  | ref (i : Nat)
  deriving Inhabited

def kindOf (s : String) : Except String Nat :=
  match s with
  | "trace_cur" => pure 0 | "trace_next" => pure 1 | "public_val" => pure 2
  | _ => throw s!"unsupported var kind {s}"

def ofInt (z : Int) : F :=
  if z ≥ 0 then UInt64.ofNat (z.toNat % P.toNat) else PF.neg (UInt64.ofNat ((-z).toNat % P.toNat))

partial def parseEx (j : Json) : Except String Ex := do
  let some (k, v) := single j | throw "expr: not a one-key object"
  let two : Except String (Ex × Ex) := do
    let xs := arr v
    if xs.size != 2 then throw s!"{k}: arity"
    pure (← parseEx xs[0]!, ← parseEx xs[1]!)
  match k with
  | "ref" => pure (.ref (nat v))
  | "var" => pure (.var (← kindOf (str (get v "kind"))) (nat (get v "index")))
  | "ext_var" => pure (.extVar (← kindOf (str (get v "kind"))) (nat (get v "ext_index")))
  | "ext_chal" => pure (.chal (nat (get v "index")))
  | "const_f" => pure (.cF (UInt64.ofNat ((str v).toNat!  % P.toNat)))
  | "const_z" => pure (.cF (ofInt (int v)))
  | "add" | "ext_add" => let (a, b) ← two; pure (.add a b)
  | "sub" | "ext_sub" => let (a, b) ← two; pure (.sub a b)
  | "mul" | "ext_mul" => let (a, b) ← two; pure (.mul a b)
  | "neg" | "ext_neg" => pure (.neg (← parseEx v))
  | "lift" | "ext_lift" => parseEx v
  | "pow" =>
    let xs := arr v
    pure (.pow (← parseEx xs[0]!) (nat xs[1]!))
  | _ => throw s!"unsupported expr tag {k}"

structure Con where
  kind : Nat      -- 0 row, 1 transition, 2 boundary, 3 terminal
  round : Nat
  deg : Nat
  e : Ex
  deriving Inhabited

structure Chip where
  id : String
  shared : Array Ex
  cons : Array Con
  colRound : Array Nat   -- round of each physical column
  sharedK : Array Bool   -- shared node is 𝕂-typed (`Expr::is_k_in`)
  consK : Array Bool
  baseCols : Nat
  width : Nat

def isKJ (sk : Array Bool) (j : Json) : Bool :=
  match single j with
  | some (k, v) =>
    if k == "ref" then sk[nat v]! else
    ["ext_var", "ext_chal", "ext_lift", "ext_add", "ext_sub", "ext_mul", "ext_neg"].contains k
  | none => false

def loadChip (path : String) : IO Chip := do
  let d ← readJson path
  let c := (arr (get d "chips"))[0]!
  let sh ← (arr (get c "shared")).mapM fun j => IO.ofExcept (parseEx j |>.mapError IO.userError)
  let sk := (arr (get c "shared")).foldl (fun a j => a.push (isKJ a j)) #[]
  let ck := (arr (get c "constraints")).map fun j => isKJ sk (get j "expr")
  let cons ← (arr (get c "constraints")).mapM fun j => do
    let k ← match str (get j "kind") with
      | "row" => pure 0 | "transition" => pure 1 | "boundary" => pure 2 | "terminal" => pure 3
      | s => throw (IO.userError s!"constraint kind {s}")
    let e ← IO.ofExcept (parseEx (get j "expr") |>.mapError IO.userError)
    pure { kind := k, round := nat (get j "round"), deg := nat (get j "degree"), e := e : Con }
  let cols := arr (get c "columns")
  let colRound := cols.map fun x => nat (get x "round")
  let bc := (cols.filter fun x => bool (get (get x "field") "base")).size
  pure { id := str (get c "id"), shared := sh, cons := cons, colRound := colRound, sharedK := sk, consK := ck, baseCols := bc, width := cols.size }

structure Tr where
  nRows : Nat
  pub : Array F
  cols : Array (Array F)      -- physical columns, each of length nRows

def loadTrace (path : String) (ch : Chip) : IO Tr := do
  let d ← readJson path
  let n := nat (get d "n_rows")
  let bc := nat (get d "base_cols")
  if bc != ch.baseCols || nat (get d "width") != ch.width then
    throw (IO.userError s!"{path}: shape {bc}/{nat (get d "width")} vs doc {ch.baseCols}/{ch.width}")
  let mut cols : Array (Array F) := Array.replicate ch.width (Array.replicate n 0)
  let main := arr (get d "main")
  for r in [0:n] do
    let row := arr main[r]!
    for c in [0:bc] do
      cols := cols.modify c fun a => a.set! r (u64 row[c]!)
  for (key, ikey) in [("aux_r1", "aux_r1_ext_index"), ("aux_r2", "aux_r2_ext_index")] do
    let aux := arr (get d key)
    let idx := (arr (get d ikey)).map nat
    for r in [0:n] do
      let row := arr aux[r]!
      for p in [0:idx.size] do
        let v := arr row[p]!
        for t in [0:3] do
          cols := cols.modify (bc + 3 * idx[p]! + t) fun a => a.set! r (u64 v[t]!)
  pure { nRows := n, pub := (arr (get d "public_flat")).map u64, cols := cols }

/-- coin/derived slots as 𝕂 values (`coins.json`). -/
def loadSlots (path : String) : IO (Array E3) := do
  let d ← readJson path
  let mk (j : Json) : E3 := let l := arr (get j "limbs"); ⟨u64 l[0]!, u64 l[1]!, u64 l[2]!⟩
  let mut slots : Array E3 := Array.replicate 64 E3.zero
  for c in arr (get d "coins") do slots := slots.set! (nat (get c "index")) (mk c)
  for c in arr (get d "derived") do slots := slots.set! (nat (get c "slot")) (mk c)
  pure slots

structure Env where
  cur : Array E3
  next : Array E3
  pub : Array F
  chal : Array E3
  bc : Nat

@[inline] def Env.extV (arr : Array E3) (bc e : Nat) : E3 :=
  E3.add (E3.add arr[bc + 3 * e]! (E3.mul arr[bc + 3 * e + 1]! E3.gen)) (E3.mul arr[bc + 3 * e + 2]! E3.gen2)

partial def ev (env : Env) (memo : Array E3) : Ex → E3
  | .var 0 i => env.cur[i]!
  | .var 1 i => env.next[i]!
  | .var _ i => E3.ofF env.pub[i]!
  | .cF v => E3.ofF v
  | .add a b => E3.add (ev env memo a) (ev env memo b)
  | .sub a b => E3.sub (ev env memo a) (ev env memo b)
  | .mul a b => E3.mul (ev env memo a) (ev env memo b)
  | .neg a => E3.neg (ev env memo a)
  | .pow a n => E3.pow (ev env memo a) n
  | .extVar 0 e => Env.extV env.cur env.bc e
  | .extVar 1 e => Env.extV env.next env.bc e
  | .extVar _ e => ⟨env.pub[3 * e]!, env.pub[3 * e + 1]!, env.pub[3 * e + 2]!⟩
  | .chal i => env.chal[i]!
  | .ref i => memo[i]!

/-- all constraint values at one point/row -/
def evalCons (ch : Chip) (env : Env) : Array E3 := Id.run do
  let mut memo : Array E3 := Array.mkEmpty ch.shared.size
  for s in ch.shared do memo := memo.push (ev env memo s)
  return ch.cons.map fun c => ev env memo c.e

/-- columns read at `trace_next` by some node of the DAG -/
partial def nextColsOf (ch : Chip) : Array Nat := Id.run do
  let mut seen : Array Bool := Array.replicate ch.width false
  let rec go (e : Ex) (seen : Array Bool) : Array Bool :=
    match e with
    | .var 1 i => seen.set! i true
    | .extVar 1 e => (seen.set! (ch.baseCols + 3 * e) true |>.set! (ch.baseCols + 3 * e + 1) true |>.set! (ch.baseCols + 3 * e + 2) true)
    | .add a b | .sub a b | .mul a b => go b (go a seen)
    | .neg a | .pow a _ => go a seen
    | _ => seen
  for s in ch.shared do seen := go s seen
  for c in ch.cons do seen := go c.e seen
  return (Array.range ch.width).filter fun i => seen[i]!

/-- Checker semantics of `nockvm-air/src/check.rs`: row `r` of the real trace, `next` = row `r+1` or zeros. Returns the first
violation `(constraint, row)`. -/
def rowCheck (ch : Chip) (tr : Tr) (slots : Array E3) : Option (Nat × Nat) := Id.run do
  let n := tr.nRows
  for r in [0:n] do
    let cur := (Array.range ch.width).map fun c => E3.ofF tr.cols[c]![r]!
    let next := (Array.range ch.width).map fun c => if r + 1 < n then E3.ofF tr.cols[c]![r + 1]! else E3.zero
    let vals := evalCons ch { cur := cur, next := next, pub := tr.pub, chal := slots, bc := ch.baseCols }
    for i in [0:ch.cons.size] do
      let k := ch.cons[i]!.kind
      let applies := match k with | 0 => true | 1 => r + 1 < n | 2 => r == 0 | _ => r + 1 == n
      if applies && vals[i]! != E3.zero then return some (i, r)
  return none

end NockvmE2E.Exec.Tr
