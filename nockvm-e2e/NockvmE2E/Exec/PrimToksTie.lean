/-
the kernel tie of the executed token table `PE.primToks` (Exec/PrimToks.lean, generated)
to nock's primitive formula nouns `Nock.Jet.Prim.primC`: for every op but `dec`, `PE.primToks (primCode op)` is the preorder token list
of `primC op`.  One `decide +kernel` per op (a list of at most ~300 tokens; never a whole instance).
Not zero-knowledge.
-/
import NockvmE2E.Exec.PrimToks
import NockvmE2E.J8.RVUJ8
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.PrimToksTie

open NockvmE2E.Exec.PE
open NockvmE2E.J8.RVUJ8 (toks)
open Nock.Jet.Prim (PrimOp primC)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (primCode)

deriving instance DecidableEq for Tok

theorem primToks_add : primToks (primCode PrimOp.add) = some (toks (primC PrimOp.add)) := by decide +kernel
theorem primToks_sub : primToks (primCode PrimOp.sub) = some (toks (primC PrimOp.sub)) := by decide +kernel
theorem primToks_lt : primToks (primCode PrimOp.lt) = some (toks (primC PrimOp.lt)) := by decide +kernel
theorem primToks_mul : primToks (primCode PrimOp.mul) = some (toks (primC PrimOp.mul)) := by decide +kernel
theorem primToks_div : primToks (primCode PrimOp.div) = some (toks (primC PrimOp.div)) := by decide +kernel
theorem primToks_mod : primToks (primCode PrimOp.mod) = some (toks (primC PrimOp.mod)) := by decide +kernel

/-- **the tie**: the executed token table is the token list of nock's primitive formula, for each of the six ALU primitives -/
theorem primToks_primCode (op : PrimOp) (h : op ≠ PrimOp.dec) :
    primToks (primCode op) = some (toks (primC op)) := by
  cases op
  · exact primToks_add
  · exact primToks_sub
  · exact primToks_lt
  · exact absurd rfl h
  · exact primToks_mul
  · exact primToks_div
  · exact primToks_mod

/-- `dec` has no ALU opcode: `primCode dec = 0` and the table has no entry for it -/
theorem primToks_dec : primToks (primCode PrimOp.dec) = none := by decide +kernel

end NockvmE2E.Exec.PrimToksTie

#print axioms NockvmE2E.Exec.PrimToksTie.primToks_primCode
#print axioms NockvmE2E.Exec.PrimToksTie.primToks_dec
