import Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8
import Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8V
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed
import Nock.Jet.VerifiedRegistry
import Nock.RedTeam.Batch4776Thm54NVJetClean
import Nock.RedTeam.Batch4777Thm54NVJetConst
import Nock.RedTeam.Batch4779Thm54NVEq5Regime
import Nock.RedTeam.Batch4812Thm54J9bNVFinal
import Nock.RedTeam.Batch4842Thm54J8ComplClose
import Nock.RedTeam.Batch4856Thm54J9BComplToy
import Nock.V1J8.FastCheck
import Nock.DriverJ8.TranscriptJ8
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ProbJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AAbsent
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AClosed
import Nock.RedTeam.Batch4881Thm54J9APredNC
import Nock.RedTeam.Batch4882Thm54J9AComplAbsent
import Nock.RedTeam.Batch4883Thm54J9AComplToy
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.E2EJ9AIface
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ProviderJ9A
import Nock.V1J9A.GenJ9AX
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot
import Nock.V1J9A.CheckJ9AIffComp
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin
import Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALClosed
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ProbJ9AL
import Nock.RedTeam.Batch4921Thm54J9ALComplToy
import Nock.RedTeam.Batch4922Thm54J9ALPredNC
import Nock.RedTeam.Batch4923Thm54J9ALAttackNC
import Nock.RedTeam.Batch4930Thm54J9ALPrimNonvac
import Nock.RedTeam.Batch4932Thm54J9ALMulDemo
import Nock.RedTeam.Batch4933Thm54J9ALLtDemo
import Nock.RedTeam.Batch4934Thm54J9ALDivDemo
import Nock.RedTeam.Batch4935Thm54J9ALNoAluInhabitant
import Nock.RedTeam.Batch4936Thm54J9ALGenLinkToy
import Nock.RedTeam.Batch4937Thm54J9AMatmulGenLink
import Nock.V1J9AL.CheckJ9ALIff
import Nock.RedTeam.Batch4890Thm54T0Lang
import Nock.RedTeam.Batch4891Thm54T0Compl
import Nock.RedTeam.Batch4892Thm54T0Demo
import Nock.RedTeam.Batch4893Thm54T0DemoNum
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.E2EJ9ALIface
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.PregLagrange
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.PregTableCheck
import Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed
import Nock.RedTeam.Batch4938Thm54TUP1Toy
import Nock.RedTeam.Batch4939Thm54J9ALTplJetToy
/-! Prints the axioms of the headline theorems of the delivery: J-8, J-9 B, J-9 A (executable link, good coin, and
completeness at jet-calling runs with a checked registry), opaque-noun (`N`-typed) jets, and J-9 AL (big-atom
arithmetic primitives on the ALU chip: soundness, completeness, the executable checker and generator, the staged
generator, and the generator link at a matrix-multiplication program). Run with `lake env lean scripts/delivery-axioms.lean`. -/
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8.probJ8V_final_clean
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8V.probJ8V_verified
#print axioms Nock.Jet.VerifiedRegistry.ofCompiled
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G.probJ9B_final_clean
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed.complJ8_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed.complJ9B_closed
#print axioms Nock.RedTeam.Batch4776.nvJet_hyps_final_clean
#print axioms Nock.RedTeam.Batch4777.nvJet_final_const
#print axioms Nock.RedTeam.Batch4779.eq5_final_const
#print axioms Nock.RedTeam.Batch4812.probJ9B_nonvacuous_demo
#print axioms Nock.RedTeam.Batch4842.complJ8_closed_toy
#print axioms Nock.RedTeam.Batch4842.complJ8_closed_toy_figure
#print axioms Nock.RedTeam.Batch4856.complJ9B_toy
#print axioms Nock.RedTeam.Batch4856.complJ9B_toy_figure
#print axioms Nock.V1J8.Check.checkFast_eq
#print axioms Nock.V1J8.Check.checkJ8_iff
#print axioms Nock.DriverJ8.TranscriptJ8.pub_before_first_squeeze
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ProbJ9A.probJ9A_final_clean
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAbsent.complJ9A_closed_absent
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AClosed.complJ9A_closed
#print axioms Nock.RedTeam.Batch4881.probJ9A_nonvacuous_demo
#print axioms Nock.RedTeam.Batch4882.complJ9A_absent_toy
#print axioms Nock.RedTeam.Batch4882.complJ9A_absent_toy_figure
#print axioms Nock.RedTeam.Batch4883.complJ9A_toy
#print axioms Nock.RedTeam.Batch4883.complJ9A_toy_figure
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.ptrE_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.infoOfE_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.sxE_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.mvE_getD
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.genJ9A_pointer_data
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface.epsilonOf_listJ9A
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface.soundJ9A_pointwise
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface.oneRound_listJ9A
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ProviderG.acceptsGenericG_j8_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ9A.acceptsGeneric_j9a_iff
#print axioms Nock.V1J9A.FillX9.colX9E_eq
#print axioms Nock.V1J9A.FillX9.nodeLab9E_eq
#print axioms Nock.V1J9A.CompX9.gatesHX9_src
#print axioms Nock.V1J9A.CompX9.checkCompX9_gates_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A.genJ9AX_data
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips.axGenE_cols
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips.pubsXE_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips.spGenE_cols
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips.pubsSE_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot.compGenX9_rho
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot.compGenX9_rhoS
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot.compGenX9_eq_closed
#print axioms Nock.V1J9A.CheckJ9AIffComp.checkJ9AX_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest.genJ9AX_honest_at
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest.genJ9AX_honest
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest.checkJ9AX_genJ9AX
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin.badE_le
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin.epsC_lt
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin.exists_good_coinE
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked.complJ8_closed_of
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked.complJ9A_closed_of
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked.complJ9B_closed_of
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ.genJ9AXJ_honest_at
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ.genJ9AXJ_honest
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ.checkJ9AX_genJ9AXJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ.badE_leJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ.epsC_ltJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ.exists_good_coinEJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALClosed.complJ9AL_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALClosed.complJ9AL_closed_of
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ.checkJ9ALX_genJ9ALXJ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ.genJ9ALXJ_honest
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ.genJ9ALXJ_honest_at
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ.honest_rec_atJL
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.checkJ9ALX_staged
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.checkJ9AX_stagedA
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.runStagedA_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.runStaged_assemble
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.runStaged_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ProbJ9AL.probJ9AL_final_clean
#print axioms Nock.RedTeam.Batch4921.complJ9AL_toy
#print axioms Nock.RedTeam.Batch4922.false_claim_rejected_AL
#print axioms Nock.RedTeam.Batch4922.wrap_claim_rejected_AL
#print axioms Nock.RedTeam.Batch4923.nc16_cell_operand_rejected_AL
#print axioms Nock.RedTeam.Batch4923.opConfusion_rejected
#print axioms Nock.RedTeam.Batch4930.acceptsJ9AL_withPrims
#print axioms Nock.RedTeam.Batch4932.complJ9AL_toy_figure
#print axioms Nock.RedTeam.Batch4933.complJ9AL_toy_figure
#print axioms Nock.RedTeam.Batch4934.complJ9AL_toy_figure
#print axioms Nock.RedTeam.Batch4935.acceptsJ9AL_noAlu
#print axioms Nock.RedTeam.Batch4936.genLink_toy
#print axioms Nock.RedTeam.Batch4937.genLinkMat
#print axioms Nock.V1J9AL.CheckJ9ALIff.checkJ9ALX_iff
#print axioms Nock.Jet.Autogen.compile_faithful
#print axioms Nock.Jet.Autogen.compile_complete
#print axioms Nock.Jet.Autogen.compile_jetSpec_faithful
#print axioms Nock.Jet.Interp.interp_sound
#print axioms Nock.Jet.Interp.interp_complete
#print axioms Nock.RedTeam.Batch4892.complJ9A_closed_of_N
#print axioms Nock.RedTeam.Batch4892.complJ9A_N_figure
#print axioms Nock.RedTeam.Batch4893.good_coin_N
#print axioms Nock.RedTeam.Batch4893.numerics_N
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9ALIface.listJ9AL
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9ALIface.epsilonOf_listJ9AL
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9ALIface.soundJ9AL_pointwise
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9ALIface.oneRound_listJ9AL
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE.preL_eval_pregCol

-- ALU on any fitting orbit (honest completeness without the orbit-height equality).
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree.lastRow_S_zero
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree.honest_rec_atJL'
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree.genJ9ALXJ_honest_at'
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree.genJ9ALXJ_honest_at_of'
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE.pregTableOK_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE.pregOK_of_tableCheck
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE.pregOK_of_tableCheck_interp
-- Trace uniqueness of the J-8 AIR on the P1 fragment (ops 0, 7, 10, cons).
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.trace_unique_good_final
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.canon_eq_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.trace_unique_prob_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.trace_unique_prob_119
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.trace_unique_prob_split
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.hcovC_P1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonSideP1.canon_complete'
-- The trace-uniqueness bound at a concrete claim, no claim-side hypothesis.
#print axioms Nock.RedTeam.Batch4938.toy_trace_unique_119
-- A J-9 AL run that calls a compiled template jet (the template clause is not vacuous).
#print axioms Nock.RedTeam.Batch4939.genLinkTpl
#print axioms Nock.RedTeam.Batch4939.complJ9AL_tpl
#print axioms Nock.RedTeam.Batch4939.honestTpl
#print axioms Nock.RedTeam.Batch4939.rowsTpl_le
#print axioms Nock.RedTeam.Batch4939.nRowsTpl_le_768
#print axioms Nock.RedTeam.Batch4939.honestTplUnif
