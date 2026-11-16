/-
  Nock/RedTeam/Batch3534Thm54J8sRegUnread.lean

  **FINDING G-J1 (read set) — the registry rows' handle
  `(kN, vN)` is read by no consume of the J chip.**  JB's open hypothesis `hReg` (`D (kN, vN) = compile p (R id)`
  on every `.reg` row) is the J-3b `MemoryBB.reg` field; in `jetTemplateJ8T` no consume slot (`ents0T`,
  `ents1T`, the export reads `entsX`) and no service provide (`ents3`) has a `.reg` entry, and `baseGatesJ`
  selects only `cst / add / mul / rp / sl / sr`; the `.reg` row only PROVIDES `keyRg = (id, kN, vN)` (in-chip,
  tag 2), which a call row consumes and re-exports as the `h_c` of its `TAG_jet` record.  So `(kN, vN)` at a
  registry row is a free witness, and `hReg` cannot follow from the chips (nor from `claimK_genuine`, which
  needs a consumed claim record): it needs a chip change (a `.reg`-row consume of the cell-table claim key with
  the public fingerprint `E (compile p (R id))`) or a public pin.  Read-set receipt, not a hostile trace.
-/
import Nock.Jet.RapJetJ8

namespace Nock.RedTeam.Batch3534

open Nock.Jet.ChipJ8

/-- No consume slot and no service provide of the J chip selects a `.reg` row. -/
theorem reg_row_unconsumed :
    ∀ e ∈ ents0T ++ ents1T ++ entsX ++ ents3, e.1 ≠ Kd.reg := by decide

/-- The `.reg` row's only slot entry is the in-chip provide `keyRg` (tag-last). -/
theorem reg_row_provides_only_keyRg :
    ents2T.filter (fun e => e.1 == Kd.reg) = [(Kd.reg, tagLast keyRg)] := by decide

#print axioms reg_row_unconsumed
#print axioms reg_row_provides_only_keyRg

end Nock.RedTeam.Batch3534
