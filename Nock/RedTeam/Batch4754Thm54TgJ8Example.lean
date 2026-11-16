/-
  Nock/RedTeam/Batch4754Thm54TgJ8Example.lean

  The example's
  `InJ8` at any coin vector, its six chips filled by the module fills (compute `FillX.colXE`, cell / walk / atom
  `FillMem.{Cell,Walk,Atom}.cols`, each proved equal to its honest builder: B4750 / B4751 / B4752 / B4753), J and
  the atom walk absent.  The receipt checks, by `rfl`, that the input's memory chips ARE the proved fills (so the
  exe `nockvm-j8check`, which checks `Example.honest χ`, runs on exactly the objects of `interpOf_cell`,
  `interpOf_walk`, `interpOf_atom`).  Native verdicts are not kernel-checked here.
-/
import Nock.V1J8.Example

namespace Nock.RedTeam.Batch4754

open Nock.V1J8.Example Nock.V1J8.FillMem Nock.V1J8.Exe Nock.V1J8.Check

theorem honest_cell (χe : CoinsE) : (honest χe).C = ⟨1, 2, ω6g, Cell.cols (coOf χe) mv mx mx1 mh⟩ := rfl
theorem honest_walk (χe : CoinsE) : (honest χe).W = ⟨1, 1, ω6g, Walk.cols (coOf χe) (chalsMJ8E χe 0) 0 0⟩ := rfl
theorem honest_atom (χe : CoinsE) : (honest χe).A = ⟨1, 1, ω6g, Atom.cols (coOfA χe) (zE χe)⟩ := rfl

#print axioms honest_cell
#print axioms honest_walk
#print axioms honest_atom

end Nock.RedTeam.Batch4754
