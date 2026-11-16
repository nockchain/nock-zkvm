/-
  NockvmE2E/Exec/Json.lean -- thin helpers over core `Lean.Json` (parser + compact printer).
-/
import Lean.Data.Json
set_option autoImplicit false

namespace NockvmE2E.Exec.J
open Lean

def get (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null
def arr (j : Json) : Array Json := (j.getArr?).toOption.getD #[]
def nat (j : Json) : Nat := (j.getNat?).toOption.getD 0
def int (j : Json) : Int := (j.getInt?).toOption.getD 0
def str (j : Json) : String := (j.getStr?).toOption.getD ""
def bool (j : Json) : Bool := (j.getBool?).toOption.getD false
def u64 (j : Json) : UInt64 := UInt64.ofNat (nat j)

/-- the only key/value of a one-key object -/
def single (j : Json) : Option (String × Json) :=
  match j.getObj? with
  | .ok kvs => kvs.toList.head?
  | .error _ => none

def readJson (path : String) : IO Json := do
  let s ← IO.FS.readFile path
  match Json.parse s with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"json {path}: {e}")

def natJ (n : Nat) : Json := Json.num (JsonNumber.fromNat n)

end NockvmE2E.Exec.J
