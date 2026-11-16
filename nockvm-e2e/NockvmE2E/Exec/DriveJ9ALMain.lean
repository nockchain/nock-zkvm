/-
  NockvmE2E/Exec/DriveJ9ALMain.lean -- root of `nockvm-e2e-j9al-prove`; the logic is `DriveJ9AL.run`.
  Untrusted tooling.  Run under a memory cap; outputs outside the repo.
-/
import NockvmE2E.Exec.DriveJ9AL

def main (args : List String) : IO UInt32 := NockvmE2E.Exec.DriveJ9AL.run args
