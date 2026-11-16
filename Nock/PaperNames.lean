/-
  Nock.PaperNames — paper-label aliases.

  Every numbered environment in the paper that carries a proof obligation is aliased here to
  its Lean declaration under its EXACT tex `\label`, so a paper object is findable in Lean by its
  paper name (Lean identifiers admit `:` inside guillemets `«…»`). Pure aliases.
-/
import Batteries.Tactic.Alias
import Nock.IO
import Nock.SetEq
import Nock.Tree
import Nock.Dyck
import Nock.Walk
import Nock.Trace
import Nock.NPR
import Nock.NounValidation
import Nock.NMR
import Nock.ComputeTable
import Nock.MemoryTable
import Nock.NockVM
import Nock.Framework
import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
import Nock.PaperNamesForestControl
import Nock.Field

/-! ## §2 Preliminaries -/
alias «Def:IOP» := Nock.Framework.IOP
alias «Def:RAP» := Nock.Framework.RAP
alias «Def:Proper_BT» := Nock.BTree
alias «Def:tree_nodes» := Nock.Noun.internal
alias «Def:noun» := Nock.Noun
alias «Def:MEF» := Nock.Framework.MEF
alias «Lem:MEM_1» := Nock.IO.MEM_1_subset
alias «Lem:ldse_mse» := Nock.SetEq.ldse_mse
alias «Lem:mse_ldse_equiv» := Nock.SetEq.mse_ldse_equiv
alias «Lem:MEM_2» := Nock.IO.MEM_2_uSE
alias «lem:set_inclusion» := Nock.SetEq.set_inclusion
alias «lem_mio_ldse» := Nock.IO.mio_ldse
alias «Lem:pbt_size» := Nock.Noun.pbt_size_of_size
alias «Lem:optimal_dyck» := Nock.BTree.dyck_iff_encode

/-! ## §3 Compilation framework -/
alias «Def:MES» := Nock.Framework.MES
alias «Def:Canonical_RAP» := Nock.Framework.CanonicalRAP
alias «Def:one-hot» := Nock.Framework.OpcodeMemOneHot
alias «Def:unique_request» := Nock.IO.UniqueRequest
alias «cor_uni_req_uni_resp» := Nock.IO.cor_uni_req_uni_resp
alias «Thm:IO_result» := Nock.IO.io_result_LIO
alias «Def:RVT» := Nock.Walk.RVT
alias «Example:fibonacci» := Nock.Framework.Fib.fib_slt_RVT
alias «Def:traversable» := Nock.Framework.Traversable
alias «Def:state_data_separation» := Nock.Walk.StateSep
alias «Thm:Walk_IOP» := Nock.Walk.Walk_IOP_final_prob
alias «Corr:forest» := Nock.Walk.Walk_IOP_forest_final_prob

/-! ## §4 Formalizing Nock -/
alias «Def:verb» := Nock.Verb
alias «Algorithm:Opcode_Updates_verb» := Nock.Verb.redex
alias «Algorithm:Noun_Operators» := Nock.Verb.reduce
alias «Algorithm:Unroll_Operator» := Nock.Verb.reduce
alias «Algorithm:Transition_Function» := Nock.Verb.NockCheck
alias «Algorithm:Valid_Noun» := Nock.checkValidNoun
alias «Def:NockProgram» := Nock.Verb.program
alias «Def:eval_trace» := Nock.Verb.Consistent
alias «Def:Nock» := Nock.Verb.Finite
alias «Corr:valid_invalid_finite» := Nock.Verb.finite_of_valid_or_invalid
alias «Lem:domain» := Nock.Verb.domain
alias «lemma:equiv_continuations» := Nock.Verb.equiv_continuations
alias «Thm:deterministic_Trace» := Nock.Verb.deterministic_Trace_strict
alias «Def:NPR_Phi» := Nock.NPR.Φ
alias «def:ion_univariate» := Nock.NPR.fn
alias «lem:ion_univariate_sec» := Nock.NPR.collision_prob_le
alias «corr:ion_single_security» := Nock.NPR.collision_table_prob_le
alias «Lem:decomp» := Nock.Noun.decomp
alias «Lem:NPR_decomp» := Nock.NPR.NPR_decomp
alias «Thm:Noun_Validation» := Nock.Noun_Validation

/-! ## §5 NockVM concrete tables -/
alias «Def:NMR_poly» := Nock.NMR.PolyRec
alias «Def:NMR» := Nock.NMR.Rec
alias «Cor:NMR_size» := Nock.NMR.nmr_size
alias «Thm:comp_38» := Nock.ComputeTable.comp_stateSep
alias «Thm:mem_38» := Nock.MemoryTable.mem_stateSep
alias «Algorithm:NockCompute» := Nock.ComputeTable.Vcomp
alias «Algorithm:Memspec» := Nock.MemoryTable.Vmem
alias «Thm:NockVMROM» := Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
alias «Lem:equiv_compute» := Nock.ComputeTable.equiv_compute
alias «Lem:equiv_mem» := Nock.MemoryTable.equiv_mem
