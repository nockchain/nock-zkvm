/-
  Nock/RedTeam/Batch864Thm54ReviewU1Numerals.lean

This file measures where it comes
  from: the pre-C1 proof of `certLt_one_of_window` went through `leftover_msb_lt_of_window` /
  `exists_first_msb_lt` (the `msbVal` route). Those constants still exist, and the set
  `D := closure {leftover_msb_lt_of_window, exists_first_msb_lt} \ closure capstone` is what left
  the reach; the new route `exists_msb_diff_of_lt` (Nat.findGreatest) and `fill_shift_le_u1` are
  what entered. Positive control: `exists_msb_diff_of_lt` and `certLt_one_of_window` are in the
  capstone closure. -/
import Nock.RedTeam.Batch593Thm54FormRAxisConsumers

set_option autoImplicit false

namespace Nock.RedTeam.Batch864

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let cap := Batch593.closureOf env Batch593.capstone
  let ns := `Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
  for n in [ns ++ `exists_msb_diff_of_lt, ns ++ `certLt_one_of_window, ns ++ `certLt_one_of_first_lt] do
    unless cap.contains n do throwError m!"positive control failed: {n} not in the capstone closure"
  let oldRoots := [ns ++ `leftover_msb_lt_of_window, ns ++ `exists_first_msb_lt]
  for n in oldRoots do
    unless env.contains n do throwError m!"{n} missing"
    if cap.contains n then throwError m!"{n} is still in the capstone closure"
  let mut old : NameSet := {}
  for r in oldRoots do
    for n in (Batch593.closureOf env r).toList do old := old.insert n
  let dropped := old.toList.filter fun n => !cap.contains n
  let newRoots := [ns ++ `exists_msb_diff_of_lt]
  let mut nw : NameSet := {}
  for r in newRoots do
    for n in (Batch593.closureOf env r).toList do nw := nw.insert n
  let added := nw.toList.filter fun n => cap.contains n && !old.contains n


  -- H1.5b Part 2a: 41 772 → 41 864.

  -- Repair (ii): 41 869 → 41 870.

  -- 45 288 since S2

  unless cap.size == 40965 do throwError m!"capstone closure moved: {cap.size}"

  -- again, through the new pole chooser's slack proof.
  unless dropped.length == 68 do throwError m!"D moved: {dropped.length}"
  logInfo m!"capstone closure: {cap.size}; left the reach (old msb route, D): {dropped.length}; \
    reached through exists_msb_diff_of_lt and not the old route (upper bound on what entered): {added.length}"
  logInfo m!"D = {dropped}"

end Nock.RedTeam.Batch864
