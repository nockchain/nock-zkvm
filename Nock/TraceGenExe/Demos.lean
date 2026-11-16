/-
  Nock/TraceGenExe/Demos.lean

  The tree has no source for E2's
  six programs, so these are written here and checked against `Nock.eval` (`Nock/TraceGenExe/AgreeDemo.lean`).
-/
namespace Nock.TraceGenExe

def decF : String :=
  "[8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1]"

def addBody : String :=
  "[6 [5 [0 12] [0 15]] [0 13] [9 2 [0 2] [[4 0 12] [4 0 13]] 0 7]]"

def addF : String := s!"[8 [[1 0] [0 2]] 8 [1 {addBody}] 9 2 0 1]"

def mulBody : String :=
  s!"[6 [5 [0 12] [0 15]] [0 13] [9 2 [0 2] [[4 0 12] [2 [[0 13] [0 14]] [1 {addF}]]] 0 7]]"

def mulF : String := s!"[8 [[1 0] [1 0]] 8 [1 {mulBody}] 9 2 0 1]"

def fibBody : String :=
  s!"[6 [5 [0 12] [0 7]] [0 26] [9 2 [0 2] [[4 0 12] [0 27] [2 [[0 26] [0 27]] [1 {addF}]]] 0 7]]"

def fibF : String := s!"[8 [[1 0] [1 0] [1 1]] 8 [1 {fibBody}] 9 2 0 1]"

def ackArm : String :=
  s!"[6 [5 [1 0] [0 6]] [4 0 7] [6 [5 [1 0] [0 7]] [9 2 [0 2] [2 [0 6] [1 {decF}]] [1 1]] [9 2 [0 2] [2 [0 6] [1 {decF}]] [9 2 [0 2] [0 6] [2 [0 7] [1 {decF}]]]]]]"

def ackF : String := s!"[9 2 [1 {ackArm}] 0 1]"

/-- `(name, subject, formula)`. -/
def demos : List (String × String × String) :=
  [ ("toy1", "0", "[1 0]"),
    ("toy2", "0", "[0 1]"),
    ("dec", "42", decF),
    ("add", "[5 7]", addF),
    ("mul", "[3 4]", mulF),
    ("fib", "10", fibF),
    ("ack", "[2 3]", ackF),
    ("dec1000", "1000", decF),
    ("fib20", "20", fibF),
    ("ack32", "[3 2]", ackF) ]

end Nock.TraceGenExe
