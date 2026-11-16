/-
  Nock: the Lean 4 library behind the J-8 arithmetization of Nock (see README.md and docs/j8/SPEC.md).

  Entry points: `Nock.Reference` (the reference interpreter `evalN`), `Nock.Jet.Semantics` (`HoldsN`, jet
  registries), `Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8` / `CleanJ8V` / `LinkJ9G` (soundness),
  `Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed` / `ComplJ9BClosed` (completeness), `Nock.V1J8.CheckJ8`
  (the executable checker), `Nock.DriverJ8.TranscriptJ8` (Fiat-Shamir).
  J-9 A: `Nock.NockVMROM.Thm54.VclL.Handle.J9A.ProbJ9A` (soundness) / `J9A.ComplJ9AClosed` (completeness);
  `Nock.V1J9A.GenJ9AX` / `GenJ9AXJ` (executable generators); `GenPortJ9AHonest` / `GenPortJ9AHonestJ` /
  `ComplClosedChecked` (executable link and completeness at jet-calling runs).
  J-9 AL (big-atom arithmetic primitives on the ALU chip): `…Handle.J9AL.ProbJ9AL` (soundness) /
  `J9AL.ComplJ9ALClosed` (completeness); `Nock.V1J9AL.CheckJ9ALIff` (the executable checker);
  `GenPortJ9ALHonestJ` / `GenPortJ9ALHStaged` (executable link and the staged generator).
  `Nock.RedTeam.*` are numbered modules; the number is a sequence index only.
  No module declares an axiom; `scripts/delivery-axioms.lean` prints the axioms of the headline theorems.
-/

import Nock.Tree
import Nock.Reference
import Nock.Verb
import Nock.Trace
import Nock.Semantics
import Nock.Dyck
import Nock.Agreement
import Nock.Field
import Nock.NPR
import Nock.NounValidation
import Nock.SetEq
import Nock.Walk
import Nock.WalkPrefix
import Nock.IO
import Nock.ComputeTable
import Nock.MemoryTable
import Nock.TableWFBounds
import Nock.AxisBatching
import Nock.AxisBridge
import Nock.NockVM
import Nock.AIR
import Nock.AIRPacked
import Nock.Counts
import Nock.NMR
import Nock.Framework
import Nock.Framework.Thm54
import Nock.NMRMEF
import Nock.NockVMROM.Language
import Nock.NockVMROM.Separation
import Nock.NockVMROM.OneHot
import Nock.NockVMROM.Cost
import Nock.NockVMROM.TraceEncoding
import Nock.NockVMROM.Asymptotic
import Nock.NockVMROM.CanonicalRAP
import Nock.NockVMROM.Completeness
import Nock.NockVMROM.Soundness
import Nock.NockVMROM.TwoRAP
import Nock.NockVMROM.Traversal
import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Thm54
import Nock.FieldEmbedding
import Nock.PaperFieldBridge
import Nock.WalkForest
import Nock.GlobalCarryRecognizer
import Nock.AxisDescent
import Nock.AxisDescentCapstone
import Nock.PaperNames
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AClosed
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.E2EJ9AIface
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.NounWalk
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ProviderJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.WitX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9AChipsAxioms
import Nock.NockVMROM.Thm54.VclL.Handle.ProviderG
import Nock.V1J9A.GenJ9AX
import Nock.V1J9A.GenJ9AXJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot
import Nock.V1J9A.CheckJ9AIffComp
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry
import Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRowPerm
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipPort
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbCellG
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellE
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkE
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomE
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHXASE
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHLinkJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ProbJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALClosed
import Nock.V1J9AL.CheckJ9ALIff
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.E2EJ9ALIface
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.PregLagrange
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.PregTableCheck
import Nock.RedTeam
