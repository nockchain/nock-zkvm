/-
  Nock/RedTeam/Batch4506Thm54J8nv2AbsentJ.lean

  **4505 (`Handle/JGenJ8`, `FinalJ8IG`, `HokLJ8G`,
  `AcceptsJ8G`, `AcceptsJ8Z{B,W,X,H,L}G`, `LinkJ8NV`).**

  * `AcceptsJ8G.ofL` / `toL_of_pos`: the present case IS `AcceptsJ8'''`; `absent_layout`: the absent case has
    `regs = ids = []`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8NV

namespace Nock.RedTeam.Batch4506

open Nock.NockVMROM.Thm54.VclL.Handle

/-- **At an empty J table the J block is exactly the four zero publics.** -/
theorem absent_iff {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
    (δ : ZMod p) (b : Module.Basis (Fin 3) (ZMod p) K) {hJ nJ : ℕ} (h0 : nJ = 0)
    (nodesJ : Fin nJ → ZMod p) (orbitJ : Nock.NockVMROM.Thm54.StrictExtension.StrictOrbitDomain (ZMod p) 3 hJ)
    (chalsJ pubsJ : ℕ → K) (lay : Fin nJ → Nock.Jet.ChipJ8.PRow)
    (PJ : Fin (Nock.Jet.ChipJ8.jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → Polynomial (ZMod p)) :
    JGenJ8.JChipOK δ b nodesJ orbitJ chalsJ pubsJ lay PJ ↔
      (pubsJ 0 = 0 ∧ pubsJ 1 = 0 ∧ pubsJ 2 = 0 ∧ pubsJ 3 = 0) := by
  constructor
  · rintro (⟨-, -, -, h, -⟩ | ⟨-, h⟩)
    · exact absurd h (by omega)
    · exact h
  · intro h; exact Or.inr ⟨h0, h⟩

#check @JGenJ8.JChipOK
#check @AcceptsJ8G.AcceptsJ8''''
#check @LinkJ8NV.probJ8NV_final
#print axioms absent_iff
#print axioms JGenJ8.jet_tagged_sumG
#print axioms JGenJ8.jet_export_sumG
#print axioms FinalJ8IG.acceptsJ8_holdsN_EIG
#print axioms HokLJ8G.acceptsJ8_holdsN_finalLG
#print axioms AcceptsJ8G.ofL
#print axioms AcceptsJ8G.toL_of_pos
#print axioms AcceptsJ8G.absent_layout
#print axioms AcceptsJ8G.nJ_zero_of_empty
#print axioms LinkJ8NV.linkXUG_of_R5
#print axioms LinkJ8NV.probJ8NV_final

end Nock.RedTeam.Batch4506
