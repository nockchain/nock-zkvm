/-
  Nock/RedTeam/Batch4749Thm54TgJ8Check.lean

  The assembled executable J-8
  checker.  The frame coin vectors executably, each proved equal to the original: **`chalsMJ8E_spec`**
  (`K3.toK (chalsMJ8E χe j) = chalsMJ8 deltaF (toχ χe) j`), **`chalsAJ8ZE_spec`** (`chalsAJ8Z`), **`chalsJJ8E_spec`**
  (`chalsJJ8`), and the compute publics **`pubVJ8E_spec`** (`= pubVJ8 deltaF powerBasis3 …`).  The input `InJ8`, its
  validity `ValidJ8` (decided by `validB`, orbit orders by `ordOK_iff`), the spec objects built from it (`mkPb`:
  nodes `ω^i`, orbits from the input's generators; `mkTr`: the row interpolants), and **`checkJ8_iff`**: under the
  registry premise `RegOK I Rg`, `checkJ8 I = true ↔ ∃ hv : ValidJ8 I, AcceptsJ8V deltaF powerBasis3 (mkPb I hv) Rg
  I.c (toχ I.χ) I.M.toMsg (mkTr I) I.r I.g`.  NOT claimed: anything about the registry equation (a premise); a
  native run (see the S6 receipt).
-/
import Nock.V1J8.CheckJ8

namespace Nock.RedTeam.Batch4749

#check @Nock.V1J8.Check.checkJ8_iff
#print axioms Nock.V1J8.Check.checkJ8_iff
#print axioms Nock.V1J8.Check.chipsB_iff
#print axioms Nock.V1J8.Check.chalsMJ8E_spec
#print axioms Nock.V1J8.Check.chalsAJ8ZE_spec
#print axioms Nock.V1J8.Check.chalsJJ8E_spec
#print axioms Nock.V1J8.Check.pubVJ8E_spec
#print axioms Nock.V1J8.Check.validB_iff

end Nock.RedTeam.Batch4749
