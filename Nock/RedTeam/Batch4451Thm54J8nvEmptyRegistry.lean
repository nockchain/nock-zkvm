/-
  Nock/RedTeam/Batch4451Thm54J8nvEmptyRegistry.lean

  A compiled completeness obstruction:
  `AcceptsJ8'''` forces a non-empty J layout (`hnJ` + `hlay`), so the empty registry with a jet-free layout has no
  inhabitant (`no_acceptsL_empty_registry`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.NVJ8

namespace Nock.RedTeam.Batch4451

open Nock.NockVMROM.Thm54.VclL.Handle

#check @NVJ8.regs_or_ids_of_acceptsL
#check @NVJ8.no_acceptsL_empty_registry
#print axioms NVJ8.layoutJ8_nil
#print axioms NVJ8.regs_or_ids_of_acceptsL
#print axioms NVJ8.no_acceptsL_empty_registry

end Nock.RedTeam.Batch4451
