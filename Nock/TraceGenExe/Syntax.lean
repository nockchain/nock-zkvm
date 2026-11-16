/-
  Nock/TraceGenExe/Syntax.lean

  Text syntax: `[a b c]` is
  right-associated (`[a [b c]]`), atoms are decimal (`_` and `.` separators allowed, as in Urbit's
  `1.000`).  No `.jam` reader: no `cue` exists in the tree (searched for `cue`/`jam`/`Jam`).
-/
import Nock.Tree

namespace Nock.TraceGenExe
open Nock

/-- Fold a nonempty item list right-associatively into a noun. -/
def foldCell : List Noun → Option Noun
  | [] => none
  | [_] => none
  | [a, b] => some (.cell a b)
  | a :: rest => (foldCell rest).map (.cell a)

/-- Parse a noun from text.  Iterative (an explicit stack of open brackets), so deep nesting
does not use the native stack. -/
def parseNoun (s : String) : Except String Noun := Id.run do
  -- stack of open frames; each frame holds its items in REVERSE order
  let mut stack : List (List Noun) := []
  let mut top : Option Noun := none
  let mut cur : Option Nat := none
  let push (stack : List (List Noun)) (top : Option Noun) (n : Noun) :
      Except String (List (List Noun) × Option Noun) :=
    match stack with
    | [] => match top with
            | none => .ok ([], some n)
            | some _ => .error "trailing input after the noun"
    | fr :: rest => .ok ((n :: fr) :: rest, top)
  for c in s.toList ++ [' '] do
    if c.isDigit then
      cur := some ((cur.getD 0) * 10 + (c.toNat - '0'.toNat))
    else if c == '_' || c == '.' then
      if cur.isNone then return .error "separator outside an atom"
    else
      -- flush a pending atom
      if let some v := cur then
        match push stack top (.atom v) with
        | .ok (st, tp) => stack := st; top := tp
        | .error e => return .error e
        cur := none
      if c == '[' then stack := [] :: stack
      else if c == ']' then
        match stack with
        | [] => return .error "unbalanced ']'"
        | fr :: rest =>
          match foldCell fr.reverse with
          | none => return .error "a bracket needs at least two items"
          | some n =>
            match push rest top n with
            | .ok (st, tp) => stack := st; top := tp
            | .error e => return .error e
      else if c.isWhitespace then pure ()
      else return .error s!"unexpected character '{c}'"
  if !stack.isEmpty then return .error "unbalanced '['"
  match top with
  | some n => return .ok n
  | none => return .error "empty input"

/-- Print a noun: `[a b c]` with right spines flattened. -/
partial def printNounAux (n : Noun) (out : Array String) : Array String :=
  match n with
  | .atom v => out.push (toString v)
  | .cell a b =>
    let out := out.push "["
    let out := printNounAux a out
    let rec spine (t : Noun) (out : Array String) : Array String :=
      match t with
      | .cell x y => spine y (printNounAux x (out.push " "))
      | .atom v => out.push " " |>.push (toString v)
    let out := spine b out
    out.push "]"

def printNoun (n : Noun) : String := String.intercalate "" (printNounAux n #[]).toList

end Nock.TraceGenExe
