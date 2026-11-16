/-
  Nock/RedTeam/Batch1064Thm54RepairIIChainCensus.lean

  **Measured, not
  read off).**
-/
set_option autoImplicit false

namespace Nock.RedTeam.Batch1064

/-- Chain sites where the generator passes the memory walk coin (`mwa := α`): 34 (4 one-line
`hcard … (fun _ => 0) 0` triples and 30 three-line triples), all in
`GenNockCompilesBounded.lean` (`_p61`, `_p62`, `GoodSeed.p61`.. `p66`); none in the carrier.
Pre-greenlight (QJ): 34. -/
def mwaSites : Nat := 34

/-- Memory `hordM` discharges rewritten (`compilerWalkOrder_of_le packageOrbit (hmem.trans hcap)`
replaced by `memRowsL_le_orderOf_of_shape hmemOrd`, or `hmemOrd` itself at the B-form `_p61`): 18.
The 18 compute discharges (`hcomp.trans hcap`) stay; `cwa` / `wg` stay `compilerWalkCoin`.
Pre-greenlight: 18. -/
def hordMSites : Nat := 18

/-- Internal `hmemOrd` binders threaded as `programMemShape α t ≤ orderOf α` (below §1): 26
(7 in the bounded module: `_p62`, `p62`..`p67`; 19 in the carrier: `p68`..`p75`, `p69_at`,
`nockCompiles`, the converses incl. `p75_of_p76`); plus 2 B-form binders at `_p61` / `p61`
(`memRows ≤ orderOf α`, already `≤`).  Pre-greenlight: 28 total (26 + 2), in the fit-form `+ 3 <`
spelling; the adjudication's `weaken.py` turned the 26 into `≤`.  No site needed `<`. -/
def internalBinders : Nat := 26

def bFormBinders : Nat := 2

/-- §1-level declarations whose `hwin` is retyped (`p76`, `zmod`, `p76_of_zmod`). -/
def retypedHwin : Nat := 3

/-- Every other module naming a
chain theorem (56 modules / 245 unquoted uses by `consumers.py`, against the pre-greenlight's 34)
builds unchanged: they name `nockCompiles_zmod` / `p76`, whose arity is unchanged, or read
binder names only.  Two more docstrings were retired (`Batch481`, `Batch994`); no consumer
needed a new §1 hypothesis. -/
def consumerModulesChanged : Nat := 20

/-- The §1 signature after (ii), the one binder that changes (26/13 unchanged). -/
def newHwin : String :=
  "(hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3 < orderOf α ∧ programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf α)"

def oldHwin : String :=
  "(hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3 < orderOf α)"

theorem mwaSites_eq : mwaSites = 4 + 30 := rfl
theorem binders_eq : internalBinders + bFormBinders = 28 := rfl
set_option maxRecDepth 20000 in
theorem newHwin_ne_oldHwin : newHwin ≠ oldHwin := by decide


/-- `mwa := α` → `mwa := αW` at all 34 chain sites (4 one-line + 30 three-line). -/
def s2MwaSites : Nat := 34
/-- Memory `hordM` discharges retargeted to `orderOf αW` (6 B-form `hmemOrd`, 12 through
`memRowsL_le_orderOf_of_shapeW`). -/
def s2HordMSites : Nat := 18
/-- Internal `hmemOrd` binders retyped: 26 shape-form (`programMemShape αW t ≤ orderOf αW`) +
2 B-form (`memRows ≤ orderOf αW`); plus the three §1 `hwin` pairs (`p76`, `zmod`, `p76_of_zmod`). -/
def s2HmemOrdBinders : Nat := 28
/-- Explicit `αW` binders added right after `α`: 9 in the bounded module (`_p61`, `_p62`,
`p61`..`p67`), 22 in the carrier (`p68`..`p76`, the converses, `nockCompiles`, `zmod`,
`p76_of_zmod`), plus `nockCompilesHostile`. -/
def s2AlphaWBinders : Nat := 9 + 22 + 1
/-- Conclusions gaining `package.optimized.family.memoryWalkAlpha = mwa` (`rfl` at
`exists_package_of_carrier`): 2 in `GenNockCompiles` (`exists_package_of_carrier`,
`nockCompiles_of_accepted`), 9 in the bounded module (`_accepted_bounded`, `_of_grom`, `_atTree`,
`_p61`, `_p62`, `p64`..`p67`), 12 in the carrier, and `nockCompilesHostile`.  The off-path
`nockCompiles_of_rom`, `_atRomSeed`, `p61`, `p62`, `p63` keep their three conjuncts. -/
def s2ConclusionSites : Nat := 2 + 9 + 12 + 1
def s2ConsumerModulesChanged : Nat := 30

theorem s2_counts : s2MwaSites = 4 + 30 ∧ s2HmemOrdBinders = 26 + 2 ∧ s2AlphaWBinders = 32 :=
  ⟨rfl, rfl, rfl⟩

end Nock.RedTeam.Batch1064
