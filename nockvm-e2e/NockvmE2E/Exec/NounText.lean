/-
  NockvmE2E/Exec/NounText.lean   (UNTRUSTED tooling, no theorem)

  Noun text parser for the free-program front end: atoms are decimal naturals, cells are `[a b]`, and `[a b c]` is `[a [b c]]`
  (the Hoon / Nock convention).  Whitespace separates tokens.  Malformed input gives an `Except.error` with the character
  position and a short reason.  Also `--prims id:op,...` parsing.
-/
import Nock.Tree
import Nock.Jet.PrimJ9

set_option autoImplicit false

namespace NockvmE2E.Exec.NounText
open Nock

/-- `[a b c]` ↦ `[a [b c]]` -/
def foldCell : List Noun → Noun
  | [] => .atom 0
  | [x] => x
  | x :: xs => .cell x (foldCell xs)

/-- parse state: the characters and the current position -/
structure St where
  cs : Array Char
  pos : Nat

def St.peek (s : St) : Option Char := s.cs[s.pos]?

partial def skipWs (s : St) : St :=
  match s.peek with
  | some c => if c.isWhitespace then skipWs { s with pos := s.pos + 1 } else s
  | none => s

def describe (s : St) : String :=
  match s.peek with
  | some c => s!"at character {s.pos + 1} ('{c}')"
  | none => s!"at the end of the input (after {s.pos} characters)"

partial def digits (s : St) (acc : Nat) (any : Bool) : Bool × Nat × St :=
  match s.peek with
  | some c => if c.isDigit then digits { s with pos := s.pos + 1 } (acc * 10 + (c.toNat - '0'.toNat)) true else (any, acc, s)
  | none => (any, acc, s)

mutual
/-- one noun -/
partial def pNoun (s : St) : Except String (Noun × St) := do
  let s := skipWs s
  match s.peek with
  | none => throw s!"expected a noun, found nothing {describe s}"
  | some '[' =>
    let s1 := { s with pos := s.pos + 1 }
    let (items, s2) ← pItems s1 []
    match items with
    | [] => throw s!"empty cell '[]' {describe s}"
    | [_] => throw s!"a cell needs at least two elements, found one, before {describe s2}"
    | _ =>
      pure (foldCell items, s2)
  | some c =>
    if c.isDigit then
      let (_, n, s1) := digits s 0 false
      -- an atom must end at whitespace, a bracket, or the end
      match s1.peek with
      | some d => if d.isWhitespace || d == '[' || d == ']' then pure (.atom n, s1)
                  else throw s!"bad character in atom {describe s1} (atoms are decimal digits only)"
      | none => pure (.atom n, s1)
    else throw s!"unexpected character {describe s} (expected a decimal atom or '[')"

/-- elements up to the closing bracket -/
partial def pItems (s : St) (acc : List Noun) : Except String (List Noun × St) := do
  let s := skipWs s
  match s.peek with
  | none => throw s!"unclosed '[': missing ']' {describe s}"
  | some ']' => pure (acc.reverse, { s with pos := s.pos + 1 })
  | some _ =>
    let (n, s1) ← pNoun s
    pItems s1 (n :: acc)
end

/-- parse a complete noun; trailing junk is an error -/
def parseNoun (txt : String) : Except String Noun := do
  let (n, s) ← pNoun ⟨txt.toList.toArray, 0⟩
  let s := skipWs s
  match s.peek with
  | none => pure n
  | some _ => throw s!"trailing input after the noun {describe s}"

/-- `parseNoun` with the flag name in the message -/
def parseNounFlag (flag txt : String) : Except String Noun :=
  match parseNoun txt with
  | .ok n => .ok n
  | .error e => .error s!"{flag}: cannot parse '{txt}': {e}"

/-- the text form: `[a [b c]]` printed with explicit brackets everywhere (reparses to the same noun) -/
def showNoun : Noun → String
  | .atom n => toString n
  | .cell a b => "[" ++ showNoun a ++ " " ++ showNoun b ++ "]"

def primNames : List (String × Nock.Jet.Prim.PrimOp) :=
  [("add", .add), ("sub", .sub), ("lt", .lt), ("dec", .dec), ("mul", .mul), ("div", .div), ("mod", .mod)]

/-- strip leading and trailing whitespace -/
def trimS (s : String) : String :=
  (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse).asString

/-- `7:add,8:mul` ↦ `[(7, add), (8, mul)]` -/
def parsePrims (txt : String) : Except String (List (Nat × Nock.Jet.Prim.PrimOp)) :=
  if (trimS txt).isEmpty then .ok [] else
  (txt.splitOn ",").mapM fun item =>
    match (trimS item).splitOn ":" with
    | [i, o] =>
      match (trimS i).toNat?, primNames.lookup (trimS o) with
      | some n, some op => .ok (n, op)
      | none, _ => .error s!"--prims: '{trimS i}' in '{item}' is not a decimal id (expected id:op, e.g. 7:add)"
      | _, none => .error s!"--prims: unknown primitive '{trimS o}' in '{item}' (one of {primNames.map (·.1)})"
    | _ => .error s!"--prims: '{item}' is not of the form id:op (e.g. 7:add,8:mul)"

end NockvmE2E.Exec.NounText
