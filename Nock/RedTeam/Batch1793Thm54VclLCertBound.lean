/-
  Nock/RedTeam/Batch1793Thm54VclLCertBound.lean

  **V1's path-length certificate pins `len ≤ 62`.**
  Production: `Thm54/VclL/Chips/CertBound.lean`.  NC: without the bound the certificate wraps
  (`cert_wraps_without_bound`, `p = 31`, `k = 93`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.CertBound

namespace Nock.RedTeam.Batch1793

open Nock.NockVMROM.Thm54.VclL.Chips.CertBound

#print axioms bits_sum_nat
#print axioms len_le_of_cert
#print axioms len_le_62_of_chip
#print axioms len_bound_of_hcons
#print axioms cert_wraps_without_bound

end Nock.RedTeam.Batch1793
