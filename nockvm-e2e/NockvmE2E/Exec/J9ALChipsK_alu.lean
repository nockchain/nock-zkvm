/-
  NockvmE2E/Exec/J9ALChipsK_alu.lean   (the kernel tie of the ALU literal `chipAlu`)

  `tieB` of `J8ChipsK` hard-codes `jDers`; the ALU's verifier chip uses `aluDers = jDers ++ yDers` (Emit/ChipsJ9AL.lean).  The whole-literal tie is
  SPLIT (a whole-literal `decide +kernel` OOMs): the shared table, the constraint expressions in slices of 60, the constraint count and the dimensions
  are separate kernel theorems.  `verifierChipT c0 aluDers jMeta` of the DAG chip `c0` of `aluSpec` has `shared = dnSeen.1 ++ c0.shared.map f`
  and constraint expressions `c0.cons.map (f ∘ e)`; the five checks say these equal `chipAlu`'s.
-/
import NockvmE2E.Exec.J8ChipsK
import NockvmE2E.Exec.J9ALChips
import NockvmE2E.Emit.ChipsJ9AL

set_option autoImplicit false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.Exec.J9ALChips
open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.VC NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8ChipsK NockvmE2E.Emit Nock.Emit

/-- the shared table: derived slots of `aluDers` then the DAG definitions, remapped -/
def tieSharedAL (s : TSpec) (lit : Chip) : Bool :=
  match chipOfDag (emitDag s) with
  | none => false
  | some c0 =>
    let dnS := dnSeen aluDers jMeta
    let f := fOf (orderOf jMeta) (drefOf aluDers dnS.2)
    let m := dnS.1.size
    exListEqB (dnS.1.toList ++ c0.shared.toList.map (mapExT f m)) lit.shared.toList

/-- constraints `lo .. lo + n` -/
def tieConsAL (s : TSpec) (lit : Chip) (lo n : Nat) : Bool :=
  match chipOfDag (emitDag s) with
  | none => false
  | some c0 =>
    let dnS := dnSeen aluDers jMeta
    let f := fOf (orderOf jMeta) (drefOf aluDers dnS.2)
    let m := dnS.1.size
    exListEqB (((c0.cons.toList.map (fun c => mapExT f m c.e)).drop lo).take n) (((lit.cons.toList.map (·.e)).drop lo).take n)

def tieLenAL (s : TSpec) (lit : Chip) : Bool :=
  match chipOfDag (emitDag s) with
  | none => false
  | some c0 => c0.cons.size == lit.cons.size

def tieDimsAL (s : TSpec) (lit : Chip) : Bool :=
  lit.baseCols == s.baseCols.sum && lit.width == s.baseCols.sum + 3 * s.extCols.sum

theorem J9ALChipsK_alu_shared : tieSharedAL aluSpec chipAlu = true := by decide +kernel
theorem J9ALChipsK_alu_cons0 : tieConsAL aluSpec chipAlu 0 60 = true := by decide +kernel
theorem J9ALChipsK_alu_cons1 : tieConsAL aluSpec chipAlu 60 60 = true := by decide +kernel
theorem J9ALChipsK_alu_cons2 : tieConsAL aluSpec chipAlu 120 60 = true := by decide +kernel
theorem J9ALChipsK_alu_cons3 : tieConsAL aluSpec chipAlu 180 60 = true := by decide +kernel
theorem J9ALChipsK_alu_cons4 : tieConsAL aluSpec chipAlu 240 60 = true := by decide +kernel
theorem J9ALChipsK_alu_len : tieLenAL aluSpec chipAlu = true := by decide +kernel
theorem J9ALChipsK_alu_dims : tieDimsAL aluSpec chipAlu = true := by decide +kernel

end NockvmE2E.Exec.J9ALChips

#print axioms NockvmE2E.Exec.J9ALChips.J9ALChipsK_alu_shared
#print axioms NockvmE2E.Exec.J9ALChips.J9ALChipsK_alu_cons0
#print axioms NockvmE2E.Exec.J9ALChips.J9ALChipsK_alu_cons4
#print axioms NockvmE2E.Exec.J9ALChips.J9ALChipsK_alu_len
#print axioms NockvmE2E.Exec.J9ALChips.J9ALChipsK_alu_dims
