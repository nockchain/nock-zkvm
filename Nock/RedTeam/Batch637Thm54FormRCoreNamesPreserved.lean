/-
  Nock/RedTeam/Batch637Thm54FormRCoreNamesPreserved.lean

This file recomputes them
  on the current tree and FAILS TO BUILD on any difference.

  * **R1 (explicit, per name).**  All 712 public constants of the five source modules: the
    type hash is unchanged; a definition's value hash is unchanged; the current module is the
    recorded one — 335 moved (to `FormRCore.PwFunctional` / `PwEvent` / `Majorant` / `Mtree` and
    `FormRTemplatePolynomial`), the rest stayed.  Same fully qualified names: no alias is needed.

  * **Excluded, disclosed.**  `_private` names: their names embed the module, so the 18 private
    match-equation auxiliaries of `Batch554.ofM` / `place` / `pw` and `Batch575.formRPw` were
    renamed with the move.  Theorem
    proof terms are not compared: 12 differ — the 11 auto-generated `eq_def` lemmas of the moved
    recursive definitions (their proofs cite those private auxiliaries) and
    `Batch556.event_probability_le` (elaborated without `GoldilocksParameters` in scope).
  In-file control: the R1 checker
    fed a deliberately wrong row reports it (`PC`).

  -- the paper
-/
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.RedTeam.Batch363Thm54AcceptedContent
import Nock.RedTeam.Batch554Thm54PwFunctional
import Nock.RedTeam.Batch555Thm54PwCertificate
import Nock.RedTeam.Batch556Thm54PwEvent
import Nock.RedTeam.Batch557Thm54RangeGadget
import Nock.RedTeam.Batch558Thm54FormRJoin
import Nock.RedTeam.Batch575Thm54FormRMtree
import Nock.RedTeam.Batch576Thm54FormRNegatives
import Nock.RedTeam.Batch577Thm54FormRCompleteness
import Nock.RedTeam.Batch581Thm54FormREvent
import Nock.RedTeam.Batch582Thm54FormRCompletenessHazard
import Nock.RedTeam.Batch583Thm54DeployedStaging
import Nock.RedTeam.Batch584Thm54StagingChronology
import Nock.RedTeam.Batch619Thm54FormRReadSet
import Nock.RedTeam.Batch620Thm54AtomRoundF1
import Nock.RedTeam.Batch621Thm54FormRNumerals
import Nock.RedTeam.Batch622Thm54FormRReviewRepairs
import Nock.RedTeam.Batch624Thm54FormREventA4
import Nock.RedTeam.Batch625Thm54FormREventStaging
import Nock.RedTeam.Batch626Thm54FormREventNested
import Nock.RedTeam.Batch627Thm54FormREventMirror
import Nock.RedTeam.Batch628Thm54LambdaEventLift
import Nock.RedTeam.Batch629Thm54LambdaEventFrontier
import Nock.RedTeam.Batch633Thm54LambdaEventUnguarded
import Nock.RedTeam.Batch634Thm54LambdaEventImportCycle
import Nock.RedTeam.Batch635Thm54FormRCoreImportGraph
import Nock.RedTeam.Batch636Thm54FormRGuardedBelowPinned
import Nock.RedTeam.Batch641Thm54LambdaEventGuarded
import Nock.RedTeam.Batch646Thm54LambdaEventHostileForm
import Nock.NockVMROM.Thm54.FormRCore
import Nock.NockVMROM.Thm54.FormRTemplatePolynomial

set_option autoImplicit false

namespace Nock.RedTeam.Batch637

open Lean

/- Three on-demand equation lemmas
(`formREnvelope.eq_1`, `formRPolyOfCert.eq_1`, `formRRootBad.eq_1`) left `FormRAxisEvent` (their generating `simpa`
was replaced) and are dropped from the per-name rows; R2 still counts them in their new modules. -/
/-- Module codes used in `namesAtBase`. -/
def modCodes : List (String × Name) :=
  [("B554", `Nock.RedTeam.Batch554Thm54PwFunctional),
    ("B556", `Nock.RedTeam.Batch556Thm54PwEvent),
    ("B557", `Nock.RedTeam.Batch557Thm54RangeGadget),
    ("B575", `Nock.RedTeam.Batch575Thm54FormRMtree),
    ("EVT", `Nock.NockVMROM.Thm54.FormRAxisEvent),
    ("C554", `Nock.NockVMROM.Thm54.FormRCore.PwFunctional),
    ("C556", `Nock.NockVMROM.Thm54.FormRCore.PwEvent),
    ("C557", `Nock.NockVMROM.Thm54.FormRCore.Majorant),
    ("C575", `Nock.NockVMROM.Thm54.FormRCore.Mtree),
    ("TPL", `Nock.NockVMROM.Thm54.FormRTemplatePolynomial)]

def modOfCode (c : String) : Name := ((modCodes.find? (·.1 == c)).map (·.2)).getD .anonymous


def namesAtBase : String := "Nock.NockVMROM.Thm54.FormRAxisEvent.CertInRange EVT EVT 2687799593 1565536288
Nock.NockVMROM.Thm54.FormRAxisEvent.FormRPathValid EVT EVT 4191293512 314592164
Nock.NockVMROM.Thm54.FormRAxisEvent.FormRRootIdentity EVT EVT 4191293512 2811473734
Nock.NockVMROM.Thm54.FormRAxisEvent.alphaMIdx EVT EVT 2954556447 3191639911
Nock.NockVMROM.Thm54.FormRAxisEvent.alphaMIdx._proof_1 EVT EVT 3786512696 -
Nock.NockVMROM.Thm54.FormRAxisEvent.alphaM_not_prior EVT EVT 13909908 -
Nock.NockVMROM.Thm54.FormRAxisEvent.alphaM_prior EVT EVT 455749790 -
Nock.NockVMROM.Thm54.FormRAxisEvent.certAxisAt EVT EVT 2851697266 1307408794
Nock.NockVMROM.Thm54.FormRAxisEvent.certAxisAt.eq_1 EVT EVT 204174398 -
Nock.NockVMROM.Thm54.FormRAxisEvent.certAxisAt_active EVT EVT 4180839686 -
Nock.NockVMROM.Thm54.FormRAxisEvent.certAxisVia EVT TPL 3004433206 3536474804
Nock.NockVMROM.Thm54.FormRAxisEvent.certAxisVia_preEncode EVT EVT 3711766022 -
Nock.NockVMROM.Thm54.FormRAxisEvent.certBitsOf EVT TPL 528545301 1055329520
Nock.NockVMROM.Thm54.FormRAxisEvent.certBitsOf.eq_1 EVT EVT 2524917159 -
Nock.NockVMROM.Thm54.FormRAxisEvent.certInRange_of_lt EVT EVT 250707883 -
Nock.NockVMROM.Thm54.FormRAxisEvent.certShiftOf EVT TPL 1272646107 1847539620
Nock.NockVMROM.Thm54.FormRAxisEvent.encode_Cprime_eq_C'poly_eval EVT EVT 203337561 -
Nock.NockVMROM.Thm54.FormRAxisEvent.encode_T_eq_Tpoly_eval EVT EVT 3187838700 -
Nock.NockVMROM.Thm54.FormRAxisEvent.encodedTBad EVT EVT 506314384 1311843254
Nock.NockVMROM.Thm54.FormRAxisEvent.encodedTBad.eq_1 EVT EVT 1400444212 -
Nock.NockVMROM.Thm54.FormRAxisEvent.encodedTBad_not_readsOn EVT EVT 289052825 -
Nock.NockVMROM.Thm54.FormRAxisEvent.formRBadAt EVT EVT 3517784908 3753515499
Nock.NockVMROM.Thm54.FormRAxisEvent.formRBadAt.eq_1 EVT EVT 3105987127 -
Nock.NockVMROM.Thm54.FormRAxisEvent.formRBadAt_eq_template EVT EVT 2084283013 -
Nock.NockVMROM.Thm54.FormRAxisEvent.formRBadAt_readsOn EVT EVT 3016328082 -
Nock.NockVMROM.Thm54.FormRAxisEvent.formRBadAt_readsOn_empty EVT EVT 2143354970 -
Nock.NockVMROM.Thm54.FormRAxisEvent.formREnvelope EVT EVT 1734377074 822207594
Nock.NockVMROM.Thm54.FormRAxisEvent.formRGuard EVT EVT 3245193957 3242523744
Nock.NockVMROM.Thm54.FormRAxisEvent.formRGuardedAxisFailureEvent EVT EVT 2100075398 2285814973
Nock.NockVMROM.Thm54.FormRAxisEvent.formRGuardedAxisFailureEvent_card_le EVT EVT 1803587115 -
Nock.NockVMROM.Thm54.FormRAxisEvent.formRGuardedBad EVT EVT 2100075398 1372767622
Nock.NockVMROM.Thm54.FormRAxisEvent.formRGuardedUnion EVT EVT 2044065807 3518326393
Nock.NockVMROM.Thm54.FormRAxisEvent.formRN EVT TPL 746024774 1650014233
Nock.NockVMROM.Thm54.FormRAxisEvent.formRN_sub_one EVT TPL 541741069 -
Nock.NockVMROM.Thm54.FormRAxisEvent.formRPolyOfCert EVT TPL 3823722678 2164113155
Nock.NockVMROM.Thm54.FormRAxisEvent.formRRootBad EVT EVT 2349474105 2356190552
Nock.NockVMROM.Thm54.FormRAxisEvent.formRRootBad_card_le EVT EVT 2192609536 -
Nock.NockVMROM.Thm54.FormRAxisEvent.formRRootStructureCheck EVT EVT 4191293512 470709664
Nock.NockVMROM.Thm54.FormRAxisEvent.formRTemplatePolynomial EVT TPL 1426812128 499716746
Nock.NockVMROM.Thm54.FormRAxisEvent.formRTemplatePolynomial.eq_1 EVT EVT 814310023 -
Nock.NockVMROM.Thm54.FormRAxisEvent.formRTemplate_identity_iff_path EVT EVT 3289708023 -
Nock.NockVMROM.Thm54.FormRAxisEvent.formR_event_numerator_le_work EVT EVT 2192470914 -
Nock.NockVMROM.Thm54.FormRAxisEvent.formR_identity_iff_path EVT EVT 1868001248 -
Nock.NockVMROM.Thm54.FormRAxisEvent.lamIdx EVT EVT 2954556447 2653826857
Nock.NockVMROM.Thm54.FormRAxisEvent.lam_not_prior EVT EVT 585219346 -
Nock.NockVMROM.Thm54.FormRAxisEvent.lambdaBad_not_readsOn EVT EVT 3195308264 -
Nock.NockVMROM.Thm54.FormRAxisEvent.lambda_prior EVT EVT 3605209289 -
Nock.NockVMROM.Thm54.FormRAxisEvent.lambda_round_eq_alphaM EVT EVT 1935439049 -
Nock.NockVMROM.Thm54.FormRAxisEvent.landedRound EVT EVT 3077916575 923825928
Nock.NockVMROM.Thm54.FormRAxisEvent.landedRound_joint EVT EVT 1749861877 -
Nock.NockVMROM.Thm54.FormRAxisEvent.landedRound_joint._proof_1 EVT EVT 2157936837 -
Nock.NockVMROM.Thm54.FormRAxisEvent.landedVec EVT EVT 3067387391 3509959631
Nock.NockVMROM.Thm54.FormRAxisEvent.landedVec_alphaM EVT EVT 308460736 -
Nock.NockVMROM.Thm54.FormRAxisEvent.landedVec_lambda EVT EVT 1421879197 -
Nock.NockVMROM.Thm54.FormRAxisEvent.landed_card EVT EVT 3896492332 -
Nock.NockVMROM.Thm54.FormRAxisEvent.preEncode EVT EVT 2298652968 1352121130
Nock.NockVMROM.Thm54.FormRAxisEvent.preEncode.eq_1 EVT EVT 1673301091 -
Nock.NockVMROM.Thm54.FormRAxisEvent.readRowAt EVT TPL 1773765572 965072967
Nock.NockVMROM.Thm54.FormRAxisEvent.readRowAt_read_root EVT TPL 2723485431 -
Nock.NockVMROM.Thm54.FormRAxisEvent.restOf EVT EVT 1861761422 283143606
Nock.NockVMROM.Thm54.FormRAxisEvent.restOf.eq_1 EVT EVT 1767345927 -
Nock.NockVMROM.Thm54.FormRAxisEvent.seedIdx EVT EVT 2954556447 3963467804
Nock.NockVMROM.Thm54.FormRAxisEvent.specialize_eq_encode_preEncode EVT EVT 85470593 -
Nock.NockVMROM.Thm54.FormRAxisEvent.templateCertAxis EVT TPL 300803768 462827720
Nock.NockVMROM.Thm54.FormRAxisEvent.templateRowCertAxis EVT TPL 42878388 163728531
Nock.NockVMROM.Thm54.FormRAxisEvent.templateRowCertAxis.eq_1 EVT EVT 2779383510 -
Nock.NockVMROM.Thm54.FormRAxisEvent.template_lam_is_sampled EVT EVT 851148761 -
Nock.RedTeam.Batch554.Cpoly B554 C554 423983272 3944574579
Nock.RedTeam.Batch554.Cpoly.eq_1 B554 C554 4039102841 -
Nock.RedTeam.Batch554.Cpoly_split B554 C554 2073631748 -
Nock.RedTeam.Batch554.Cpoly_split._proof_1_2 B554 C554 1329254545 -
Nock.RedTeam.Batch554.Cpoly_split._proof_1_3 B554 C554 194202660 -
Nock.RedTeam.Batch554.Cpoly_split._proof_1_5 B554 C554 3515582965 -
Nock.RedTeam.Batch554.WT B554 C554 1872112561 -
Nock.RedTeam.Batch554.WT._sizeOf_1 B554 C554 858294463 3410319434
Nock.RedTeam.Batch554.WT._sizeOf_inst B554 C554 1395953612 269572762
Nock.RedTeam.Batch554.WT.below B554 C554 3269896318 270791229
Nock.RedTeam.Batch554.WT.brecOn B554 C554 426030399 1400250357
Nock.RedTeam.Batch554.WT.brecOn.eq B554 C554 3971144389 -
Nock.RedTeam.Batch554.WT.brecOn.go B554 C554 674498077 1008807868
Nock.RedTeam.Batch554.WT.casesOn B554 C554 2048451524 759265635
Nock.RedTeam.Batch554.WT.ctorElim B554 C554 3636634268 1007951160
Nock.RedTeam.Batch554.WT.ctorElimType B554 C554 2218371976 3167686652
Nock.RedTeam.Batch554.WT.ctorIdx B554 C554 40370994 96835574
Nock.RedTeam.Batch554.WT.fork B554 C554 3300222880 -
Nock.RedTeam.Batch554.WT.fork.elim B554 C554 4222791527 304548084
Nock.RedTeam.Batch554.WT.fork.inj B554 C554 314903332 -
Nock.RedTeam.Batch554.WT.fork.injEq B554 C554 1106782299 -
Nock.RedTeam.Batch554.WT.fork.noConfusion B554 C554 1379428755 2033145499
Nock.RedTeam.Batch554.WT.fork.sizeOf_spec B554 C554 1393630320 -
Nock.RedTeam.Batch554.WT.leaf B554 C554 2313394883 -
Nock.RedTeam.Batch554.WT.leaf.elim B554 C554 301931017 900677094
Nock.RedTeam.Batch554.WT.leaf.sizeOf_spec B554 C554 1393585088 -
Nock.RedTeam.Batch554.WT.noConfusion B554 C554 1007433219 1039534845
Nock.RedTeam.Batch554.WT.noConfusionType B554 C554 2866558280 2370724253
Nock.RedTeam.Batch554.WT.rec B554 C554 398857194 -
Nock.RedTeam.Batch554.WT.recOn B554 C554 554504881 521174533
Nock.RedTeam.Batch554.WT.wrap B554 C554 1038010941 -
Nock.RedTeam.Batch554.WT.wrap.elim B554 C554 2928176459 3510263552
Nock.RedTeam.Batch554.WT.wrap.inj B554 C554 3120240877 -
Nock.RedTeam.Batch554.WT.wrap.injEq B554 C554 1232047222 -
Nock.RedTeam.Batch554.WT.wrap.noConfusion B554 C554 3438269214 2735917308
Nock.RedTeam.Batch554.WT.wrap.sizeOf_spec B554 C554 2210779183 -
Nock.RedTeam.Batch554.X_pow_mul_Cpoly B554 C554 1143066600 -
Nock.RedTeam.Batch554.X_pow_mul_Cpoly._proof_1_2 B554 C554 492895496 -
Nock.RedTeam.Batch554.addr B554 C554 828944129 460991881
Nock.RedTeam.Batch554.addr.eq_1 B554 B554 575997658 -
Nock.RedTeam.Batch554.addrFrom B554 C554 1153591924 1214271984
Nock.RedTeam.Batch554.addrFrom.eq_1 B554 C554 1995500515 -
Nock.RedTeam.Batch554.addrFrom_append B554 C554 3334513917 -
Nock.RedTeam.Batch554.addrFrom_cons B554 C554 1936029326 -
Nock.RedTeam.Batch554.addrFrom_linear B554 C554 528222150 -
Nock.RedTeam.Batch554.addrP B554 C554 3000996788 191610580
Nock.RedTeam.Batch554.addrP.eq_1 B575 C575 1372496383 -
Nock.RedTeam.Batch554.addrPFrom B554 C554 193738941 352743763
Nock.RedTeam.Batch554.addrPFrom.eq_1 B554 C554 1939553222 -
Nock.RedTeam.Batch554.addrPFrom_eval B554 C554 1622922042 -
Nock.RedTeam.Batch554.addrPFrom_linear B554 C554 413689772 -
Nock.RedTeam.Batch554.addrP_append B554 C554 373262826 -
Nock.RedTeam.Batch554.addrP_bitsOf B554 C554 1294799481 -
Nock.RedTeam.Batch554.addrP_bitsOf._proof_1_2 B554 C554 2320151302 -
Nock.RedTeam.Batch554.addrP_coeff B554 C554 479938876 -
Nock.RedTeam.Batch554.addrP_coeff_gt B554 C554 2077760736 -
Nock.RedTeam.Batch554.addrP_coeff_gt._proof_1_1 B554 C554 1118329168 -
Nock.RedTeam.Batch554.addrP_coeff_gt._proof_1_2 B554 C554 1793874884 -
Nock.RedTeam.Batch554.addrP_coeff_length B554 C554 326678766 -
Nock.RedTeam.Batch554.addrP_eval B554 C554 1768801047 -
Nock.RedTeam.Batch554.addrP_injective B554 C554 4011284478 -
Nock.RedTeam.Batch554.addrP_injective._proof_1_1 B554 C554 3319041774 -
Nock.RedTeam.Batch554.addrP_injective._proof_1_2 B554 C554 948537971 -
Nock.RedTeam.Batch554.addrP_ne_zero B554 C554 892714313 -
Nock.RedTeam.Batch554.addrP_nil B554 C554 3951667027 -
Nock.RedTeam.Batch554.addrP_snoc B554 C554 1416195806 -
Nock.RedTeam.Batch554.addr_append B554 C554 3092831518 -
Nock.RedTeam.Batch554.addr_cons B554 C554 969697480 -
Nock.RedTeam.Batch554.addr_nil B554 C554 3858774214 -
Nock.RedTeam.Batch554.bit B554 C554 3573831452 3837641699
Nock.RedTeam.Batch554.bit.eq_1 B554 C554 2423608749 -
Nock.RedTeam.Batch554.bit_inj B554 C554 366738125 -
Nock.RedTeam.Batch554.bitsOf B554 C554 596920212 1451736935
Nock.RedTeam.Batch554.bitsOf.eq_1 B554 C554 1843169963 -
Nock.RedTeam.Batch554.bitsOf_length B554 C554 794052200 -
Nock.RedTeam.Batch554.bitsOf_succ B554 C554 2490844597 -
Nock.RedTeam.Batch554.bracket B554 C554 1458357845 519366606
Nock.RedTeam.Batch554.bracket.eq_1 B554 C554 2599385687 -
Nock.RedTeam.Batch554.bracket_coeff_padding B554 C554 1091188250 -
Nock.RedTeam.Batch554.bracket_coeff_padding._proof_1_1 B554 C554 2164609649 -
Nock.RedTeam.Batch554.bracket_coeff_padding._proof_1_2 B554 C554 796889080 -
Nock.RedTeam.Batch554.bracket_coeff_padding._proof_1_3 B554 C554 2358274339 -
Nock.RedTeam.Batch554.bracket_coeff_padding._proof_1_4 B554 C554 3573623716 -
Nock.RedTeam.Batch554.bracket_eval B554 C554 556470483 -
Nock.RedTeam.Batch554.bracket_honest B554 C554 3405730351 -
Nock.RedTeam.Batch554.bracket_zero_iff B554 C554 1385497244 -
Nock.RedTeam.Batch554.bracket_zero_iff._proof_1_1 B554 C554 4006841212 -
Nock.RedTeam.Batch554.bracket_zero_iff._proof_1_2 B554 C554 229018236 -
Nock.RedTeam.Batch554.bracket_zero_iff._proof_1_3 B554 C554 3324691540 -
Nock.RedTeam.Batch554.bracket_zero_prefix B554 C554 3515851494 -
Nock.RedTeam.Batch554.certified_axis_ne_zero B554 C554 2714533488 -
Nock.RedTeam.Batch554.certified_axis_ne_zero._proof_1_1 B554 C554 3402728898 -
Nock.RedTeam.Batch554.cnt B554 C554 2600813317 2523882718
Nock.RedTeam.Batch554.cnt._f B554 C554 2456102400 486131177
Nock.RedTeam.Batch554.cnt._sunfold B554 C554 2600813317 1710828719
Nock.RedTeam.Batch554.cnt.eq_1 B554 C554 2283990551 -
Nock.RedTeam.Batch554.cnt.eq_2 B554 C554 2681752464 -
Nock.RedTeam.Batch554.cnt.eq_3 B554 C554 830689408 -
Nock.RedTeam.Batch554.cnt.eq_def B554 C554 1010393218 -
Nock.RedTeam.Batch554.cntM B554 C554 3029101507 3147045584
Nock.RedTeam.Batch554.cntM.eq_1 B554 C554 1617297650 -
Nock.RedTeam.Batch554.cntM_decompose B554 C554 1458514927 -
Nock.RedTeam.Batch554.cntM_halt B554 C554 1766978749 -
Nock.RedTeam.Batch554.cntM_read B554 C554 635175413 -
Nock.RedTeam.Batch554.cntM_verify B554 C554 2239990485 -
Nock.RedTeam.Batch554.cntTerm B554 C554 3913107772 1824027254
Nock.RedTeam.Batch554.cntTerm.eq_1 B554 C554 4011716250 -
Nock.RedTeam.Batch554.coeff_cntM B554 C554 1951409886 -
Nock.RedTeam.Batch554.cross_root_both_nonzero B554 C554 3175340511 -
Nock.RedTeam.Batch554.cross_root_both_nonzero._proof_1_2 B554 C554 2818406959 -
Nock.RedTeam.Batch554.forged_six_for_five B554 B554 2072279865 -
Nock.RedTeam.Batch554.functional B554 C554 3637675461 -
Nock.RedTeam.Batch554.honestTree B554 C554 1759848170 1649532938
Nock.RedTeam.Batch554.honestTree.eq_1 B554 C554 1917419720 -
Nock.RedTeam.Batch554.honestTree_paths B554 C554 534674575 -
Nock.RedTeam.Batch554.honestTree_paths_other B554 C554 512167700 -
Nock.RedTeam.Batch554.honest_five_exact B554 B554 2022935735 -
Nock.RedTeam.Batch554.honest_single_record B554 C554 2568220858 -
Nock.RedTeam.Batch554.ofM B554 C554 2717109016 4233241406
Nock.RedTeam.Batch554.ofM._f B554 C554 2904388188 866198690
Nock.RedTeam.Batch554.ofM._sunfold B554 C554 2717109016 3462804147
Nock.RedTeam.Batch554.ofM.eq_1 B554 C554 2400104889 -
Nock.RedTeam.Batch554.ofM.eq_2 B554 C554 2174007824 -
Nock.RedTeam.Batch554.ofM.eq_3 B554 C554 1082510667 -
Nock.RedTeam.Batch554.ofM.eq_4 B554 C554 2834565700 -
Nock.RedTeam.Batch554.ofM.eq_def B554 C554 4047028889 -
Nock.RedTeam.Batch554.ofM.match_1 B554 C554 2070133508 57102305
Nock.RedTeam.Batch554.place B554 C554 2435785970 1182296335
Nock.RedTeam.Batch554.place._f B554 C554 2274711427 3717831545
Nock.RedTeam.Batch554.place._sunfold B554 C554 2435785970 2991648910
Nock.RedTeam.Batch554.place._unsafe_rec B554 C554 2435785970 602985981
Nock.RedTeam.Batch554.place.eq_1 B554 C554 1340113209 -
Nock.RedTeam.Batch554.place.eq_2 B554 C554 1055763826 -
Nock.RedTeam.Batch554.place.eq_3 B554 C554 2945018402 -
Nock.RedTeam.Batch554.place.eq_def B554 C554 4169809844 -
Nock.RedTeam.Batch554.place.match_1 B554 C554 1870656741 2779414296
Nock.RedTeam.Batch554.pw B554 C554 2600813317 1026885003
Nock.RedTeam.Batch554.pw._f B554 C554 2456102400 2951882363
Nock.RedTeam.Batch554.pw._sunfold B554 C554 2600813317 4085186131
Nock.RedTeam.Batch554.pw.eq_1 B554 C554 226329460 -
Nock.RedTeam.Batch554.pw.eq_2 B554 C554 1603908095 -
Nock.RedTeam.Batch554.pw.eq_3 B554 C554 1827164483 -
Nock.RedTeam.Batch554.pw.eq_def B554 C554 2116944334 -
Nock.RedTeam.Batch554.pw.match_1 B554 C554 2519222641 160881588
Nock.RedTeam.Batch554.pwM B554 C554 3029101507 2381735894
Nock.RedTeam.Batch554.pwM.eq_1 B554 C554 1766233740 -
Nock.RedTeam.Batch554.pwM_decompose B554 C554 842635192 -
Nock.RedTeam.Batch554.pwM_halt B554 C554 187580723 -
Nock.RedTeam.Batch554.pwM_read B554 C554 1253709194 -
Nock.RedTeam.Batch554.pwM_verify B554 C554 1190175937 -
Nock.RedTeam.Batch554.pwTerm B554 C554 3913107772 3744804881
Nock.RedTeam.Batch554.pwTerm.eq_1 B554 C554 2195666126 -
Nock.RedTeam.Batch554.read_over_leaf_rejected B554 C554 587782829 -
Nock.RedTeam.Batch554.rpaths B554 C554 3129682357 3861647457
Nock.RedTeam.Batch554.rpaths._f B554 C554 2421632211 4093317163
Nock.RedTeam.Batch554.rpaths._sunfold B554 C554 3129682357 3938642566
Nock.RedTeam.Batch554.rpaths._unsafe_rec B554 C554 3129682357 2828270874
Nock.RedTeam.Batch554.rpaths.eq_1 B554 C554 3222016076 -
Nock.RedTeam.Batch554.rpaths.eq_2 B554 C554 970152086 -
Nock.RedTeam.Batch554.rpaths.eq_3 B554 C554 3027562060 -
Nock.RedTeam.Batch554.rpaths.eq_4 B554 C554 331636985 -
Nock.RedTeam.Batch554.rpaths.eq_def B554 C554 309736594 -
Nock.RedTeam.Batch554.rpaths_place B554 C554 353878642 -
Nock.RedTeam.Batch554.sameTsTree B554 B554 1063160258 795056401
Nock.RedTeam.Batch554.sameTsTree.eq_1 B554 B554 3126451826 -
Nock.RedTeam.Batch554.same_node_forces_axis_one B554 C554 2239987457 -
Nock.RedTeam.Batch554.same_node_forces_axis_one._proof_1_1 B554 C554 596649097 -
Nock.RedTeam.Batch554.same_ts_cancellation B554 B554 429647170 -
Nock.RedTeam.Batch554.same_ts_cancellation_nonzero B554 B554 1592423081 -
Nock.RedTeam.Batch554.shift_cnt B554 C554 3089688066 -
Nock.RedTeam.Batch554.shift_pw B554 C554 845049887 -
Nock.RedTeam.Batch554.single_record B554 C554 3612503834 -
Nock.RedTeam.Batch554.slot_five_ne_six B554 B554 126165367 -
Nock.RedTeam.Batch554.sumAddr B554 C554 3979152142 2007463318
Nock.RedTeam.Batch554.sumAddr.eq_1 B554 C554 3688650754 -
Nock.RedTeam.Batch554.sumAddr_append B554 C554 2611542079 -
Nock.RedTeam.Batch554.sumAddr_shift B554 C554 2805220830 -
Nock.RedTeam.Batch554.sumPow B554 C554 3979152142 2692735444
Nock.RedTeam.Batch554.sumPow.eq_1 B554 C554 910095478 -
Nock.RedTeam.Batch554.sumPow_append B554 C554 3427049938 -
Nock.RedTeam.Batch554.sumPow_shift B554 C554 1284524719 -
Nock.RedTeam.Batch554.t1_rejected B554 B554 3956413693 -
Nock.RedTeam.Batch554.t2_rejected B554 B554 4046110348 -
Nock.RedTeam.Batch554.tfull_rejected B554 B554 1948827892 -
Nock.RedTeam.Batch554.verify_above_read_rejected B554 C554 1691096031 -
Nock.RedTeam.Batch554.verify_above_read_rejected._proof_1_1 B554 C554 4167774302 -
Nock.RedTeam.Batch554.vpaths B554 C554 3129682357 62750653
Nock.RedTeam.Batch554.vpaths._f B554 C554 2421632211 2518435487
Nock.RedTeam.Batch554.vpaths._sunfold B554 C554 3129682357 948015909
Nock.RedTeam.Batch554.vpaths._unsafe_rec B554 C554 3129682357 597301691
Nock.RedTeam.Batch554.vpaths.eq_1 B554 C554 3990651413 -
Nock.RedTeam.Batch554.vpaths.eq_2 B554 C554 2260482349 -
Nock.RedTeam.Batch554.vpaths.eq_3 B554 C554 2449795206 -
Nock.RedTeam.Batch554.vpaths.eq_4 B554 C554 159719498 -
Nock.RedTeam.Batch554.vpaths.eq_def B554 C554 318682124 -
Nock.RedTeam.Batch554.vpaths_place B554 C554 2071665397 -
Nock.RedTeam.Batch554.wraps B554 C554 4145247248 4128860009
Nock.RedTeam.Batch554.wraps._f B554 C554 348840163 1327689310
Nock.RedTeam.Batch554.wraps._sunfold B554 C554 4145247248 1427546329
Nock.RedTeam.Batch554.wraps._unsafe_rec B554 C554 4145247248 2758562531
Nock.RedTeam.Batch554.wraps.eq_1 B554 C554 2984088126 -
Nock.RedTeam.Batch554.wraps.eq_2 B554 C554 523352410 -
Nock.RedTeam.Batch554.wraps.eq_3 B554 C554 3546552174 -
Nock.RedTeam.Batch554.wraps.eq_def B554 C554 3440959290 -
Nock.RedTeam.Batch556.F B556 C556 4294616278 1995706179
Nock.RedTeam.Batch556.Fpoly B556 C556 2733931841 2467175228
Nock.RedTeam.Batch556.Fpoly_coeff B556 C556 1319080098 -
Nock.RedTeam.Batch556.Fpoly_eval B556 C556 1315196569 -
Nock.RedTeam.Batch556.Fα B556 C556 1152303280 3670739687
Nock.RedTeam.Batch556.Fα_coeff B556 C556 3004847371 -
Nock.RedTeam.Batch556.Fα_eval B556 C556 4274407155 -
Nock.RedTeam.Batch556.Fα_natDegree_le B556 C556 1868324576 -
Nock.RedTeam.Batch556.accept_card_le_root B556 C556 3715893608 -
Nock.RedTeam.Batch556.accept_subset_root B556 C556 3206918747 -
Nock.RedTeam.Batch556.bivariate_bad_card_le B556 C556 1666331894 -
Nock.RedTeam.Batch556.bivariate_bad_card_le._simp_1_1 B556 C556 1043127905 -
Nock.RedTeam.Batch556.cylinder_card B556 C556 262194478 -
Nock.RedTeam.Batch556.cylinder_card._simp_1_1 B556 C556 1253103447 -
Nock.RedTeam.Batch556.cylinder_card._simp_1_2 B556 C556 3747553994 -
Nock.RedTeam.Batch556.evalGRom_op0_unguarded B556 B556 4178103752 -
Nock.RedTeam.Batch556.event_probability_le B556 C556 3003182827 -
Nock.RedTeam.Batch556.figures_unmoved_31 B556 B556 223069121 -
Nock.RedTeam.Batch556.figures_unmoved_32 B556 B556 1703831886 -
Nock.RedTeam.Batch556.forest_zero_iff B556 C556 198304638 -
Nock.RedTeam.Batch556.new_summand_small B556 B556 2872350230 -
Nock.RedTeam.Batch556.no_cancelling_roots B556 C556 127809416 -
Nock.RedTeam.Batch556.pwAccountingWork B556 B556 9906956 1795624362
Nock.RedTeam.Batch556.pwAccountingWork.eq_1 B556 B556 2991322764 -
Nock.RedTeam.Batch556.pwAccountingWork_majorises B556 B556 2621797583 -
Nock.RedTeam.Batch556.pwAccountingWork_majorises._proof_1_1 B556 B556 2190716937 -
Nock.RedTeam.Batch556.same_ts_roots_in_collision_event B556 B556 1891577286 -
Nock.RedTeam.Batch556.same_ts_roots_in_collision_event._proof_1_1 B556 B556 384791554 -
Nock.RedTeam.Batch556.same_ts_roots_in_collision_event._proof_1_2 B556 B556 860495420 -
Nock.RedTeam.Batch557.RunAxesBoundedBy B557 B557 3487083517 231568618
Nock.RedTeam.Batch557.accepted_row_axis B557 B557 1083838052 -
Nock.RedTeam.Batch557.at_most_one_term B557 B557 3129110638 -
Nock.RedTeam.Batch557.axis_guard_bites B557 B557 3262423405 -
Nock.RedTeam.Batch557.bitsOf_succ B557 B557 3826175816 -
Nock.RedTeam.Batch557.boolean_degree B557 B557 1613762927 -
Nock.RedTeam.Batch557.bracket_zero_iff_at_bitLength B557 B557 2826028133 -
Nock.RedTeam.Batch557.brief_gadget_accepts_1024_at_769 B557 B557 3319397086 -
Nock.RedTeam.Batch557.brief_gadget_accepts_34_at_31 B557 B557 572671482 -
Nock.RedTeam.Batch557.brief_top_correct_at_goldilocks B557 B557 1656286912 -
Nock.RedTeam.Batch557.ceil3 B557 B557 2546708756 617729098
Nock.RedTeam.Batch557.ceil3.eq_1 B557 B557 2585787421 -
Nock.RedTeam.Batch557.cert_eq_val B557 B557 2942491226 -
Nock.RedTeam.Batch557.cert_mod_unique_of_lt B557 B557 4276113301 -
Nock.RedTeam.Batch557.clog_10 B557 B557 1329199103 -
Nock.RedTeam.Batch557.clog_17 B557 B557 1401496794 -
Nock.RedTeam.Batch557.clog_5 B557 B557 3482370834 -
Nock.RedTeam.Batch557.clog_64 B557 B557 4216657515 -
Nock.RedTeam.Batch557.colC B557 B557 2504765742 3381066000
Nock.RedTeam.Batch557.colC.eq_1 B557 B557 1403345386 -
Nock.RedTeam.Batch557.colE B557 B557 1605787215 2211789561
Nock.RedTeam.Batch557.colM B557 B557 2504765742 3813056511
Nock.RedTeam.Batch557.colM.eq_1 B557 B557 1636302528 -
Nock.RedTeam.Batch557.colP B557 B557 1605787215 1523738658
Nock.RedTeam.Batch557.colP.eq_1 B557 B557 3658157329 -
Nock.RedTeam.Batch557.colTop B557 B557 1605787215 3061239434
Nock.RedTeam.Batch557.colTop.eq_1 B557 B557 3994021975 -
Nock.RedTeam.Batch557.compute_gates_64 B557 B557 2126310461 -
Nock.RedTeam.Batch557.compute_width_64 B557 B557 3974313189 -
Nock.RedTeam.Batch557.compute_width_vs_28th B557 B557 1017477967 -
Nock.RedTeam.Batch557.eqK B557 B557 4113182427 1868965560
Nock.RedTeam.Batch557.eqK._f B557 B557 3463763688 1561374040
Nock.RedTeam.Batch557.eqK._sunfold B557 B557 4113182427 1530487697
Nock.RedTeam.Batch557.eqK._unsafe_rec B557 B557 4113182427 1808062774
Nock.RedTeam.Batch557.eqK.eq_1 B557 B557 4828453 -
Nock.RedTeam.Batch557.eqK.eq_2 B557 B557 2559871841 -
Nock.RedTeam.Batch557.eqK.eq_def B557 B557 3626959600 -
Nock.RedTeam.Batch557.eqK.match_1 B557 B557 3310288960 2916497061
Nock.RedTeam.Batch557.eqK_bool B557 B557 1020207872 -
Nock.RedTeam.Batch557.eqK_bool._simp_1_4 B557 B557 3462990727 -
Nock.RedTeam.Batch557.evalGAxRom B557 B557 2422164734 499280110
Nock.RedTeam.Batch557.evalGAxRom._f B557 B557 3670094778 535981251
Nock.RedTeam.Batch557.evalGAxRom._sparseCasesOn_1 B557 B557 2334663261 1385501301
Nock.RedTeam.Batch557.evalGAxRom._sparseCasesOn_1.else_eq B557 B557 1071072270 -
Nock.RedTeam.Batch557.evalGAxRom._sparseCasesOn_4 B557 B557 1490707450 1994998827
Nock.RedTeam.Batch557.evalGAxRom._sparseCasesOn_4.else_eq B557 B557 3817969850 -
Nock.RedTeam.Batch557.evalGAxRom._sparseCasesOn_7 B557 B557 3269219483 1193146799
Nock.RedTeam.Batch557.evalGAxRom._sparseCasesOn_7.else_eq B557 B557 286310526 -
Nock.RedTeam.Batch557.evalGAxRom._sunfold B557 B557 2422164734 3899609772
Nock.RedTeam.Batch557.evalGAxRom._unsafe_rec B557 B557 2422164734 3413096992
Nock.RedTeam.Batch557.evalGAxRom.eq_1 B557 B557 993647578 -
Nock.RedTeam.Batch557.evalGAxRom.eq_10 B557 B557 3391710283 -
Nock.RedTeam.Batch557.evalGAxRom.eq_11 B557 B557 3430339545 -
Nock.RedTeam.Batch557.evalGAxRom.eq_12 B557 B557 3203814188 -
Nock.RedTeam.Batch557.evalGAxRom.eq_13 B557 B557 1572882051 -
Nock.RedTeam.Batch557.evalGAxRom.eq_14 B557 B557 766757816 -
Nock.RedTeam.Batch557.evalGAxRom.eq_15 B557 B557 1758546524 -
Nock.RedTeam.Batch557.evalGAxRom.eq_16 B557 B557 4026279449 -
Nock.RedTeam.Batch557.evalGAxRom.eq_17 B557 B557 4212492851 -
Nock.RedTeam.Batch557.evalGAxRom.eq_18 B557 B557 196533409 -
Nock.RedTeam.Batch557.evalGAxRom.eq_19 B557 B557 594754901 -
Nock.RedTeam.Batch557.evalGAxRom.eq_2 B557 B557 1981937924 -
Nock.RedTeam.Batch557.evalGAxRom.eq_20 B557 B557 2217562451 -
Nock.RedTeam.Batch557.evalGAxRom.eq_21 B557 B557 3109935817 -
Nock.RedTeam.Batch557.evalGAxRom.eq_3 B557 B557 208004095 -
Nock.RedTeam.Batch557.evalGAxRom.eq_4 B557 B557 2227913830 -
Nock.RedTeam.Batch557.evalGAxRom.eq_5 B557 B557 4045447001 -
Nock.RedTeam.Batch557.evalGAxRom.eq_6 B557 B557 2931797766 -
Nock.RedTeam.Batch557.evalGAxRom.eq_7 B557 B557 1566089491 -
Nock.RedTeam.Batch557.evalGAxRom.eq_8 B557 B557 2099764600 -
Nock.RedTeam.Batch557.evalGAxRom.eq_9 B557 B557 3481730576 -
Nock.RedTeam.Batch557.evalGAxRom.eq_def B557 B557 2607515342 -
Nock.RedTeam.Batch557.evalGAxRom.match_1 B557 B557 3086337295 764536992
Nock.RedTeam.Batch557.evalGAxRom.match_1.congr_eq_1 B557 B557 646549523 -
Nock.RedTeam.Batch557.evalGAxRom.match_1.congr_eq_2 B557 B557 4278309818 -
Nock.RedTeam.Batch557.evalGAxRom.match_10 B557 B557 619676843 2934106892
Nock.RedTeam.Batch557.evalGAxRom.match_10.congr_eq_1 B557 B557 1597971993 -
Nock.RedTeam.Batch557.evalGAxRom.match_10.congr_eq_2 B557 B557 738128875 -
Nock.RedTeam.Batch557.evalGAxRom.match_10.congr_eq_3 B557 B557 3238280055 -
Nock.RedTeam.Batch557.evalGAxRom.match_12 B557 B557 1231690975 1635080995
Nock.RedTeam.Batch557.evalGAxRom.match_14 B557 B557 2357268965 4034323918
Nock.RedTeam.Batch557.evalGAxRom.match_14.congr_eq_1 B557 B557 1655530981 -
Nock.RedTeam.Batch557.evalGAxRom.match_14.congr_eq_2 B557 B557 1526689965 -
Nock.RedTeam.Batch557.evalGAxRom.match_16 B557 B557 1756017231 483356913
Nock.RedTeam.Batch557.evalGAxRom.match_18 B557 B557 2700913130 1262336669
Nock.RedTeam.Batch557.evalGAxRom.match_20 B557 B557 97175521 4129293088
Nock.RedTeam.Batch557.evalGAxRom.match_4 B557 B557 1812739228 1646766290
Nock.RedTeam.Batch557.evalGAxRom.match_7 B557 B557 3050790665 1247650188
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes B557 B557 3457764180 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_34 B557 B557 3725436072 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_35 B557 B557 1917433872 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_36 B557 B557 2541492046 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_37 B557 B557 1011643031 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_38 B557 B557 2085385268 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_39 B557 B557 2368264201 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_40 B557 B557 3648810718 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_42 B557 B557 1684734507 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_43 B557 B557 3603759822 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_45 B557 B557 946130891 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_46 B557 B557 2958140211 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_47 B557 B557 1489495047 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_48 B557 B557 967812828 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_49 B557 B557 1565293999 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_50 B557 B557 583476222 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._proof_1_51 B557 B557 1117926182 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._simp_1_1 B557 B557 1221579123 -
Nock.RedTeam.Batch557.evalGRom_boundedBy_axes._simp_1_2 B557 B557 2748003501 -
Nock.RedTeam.Batch557.exists_cert B557 B557 2461460252 -
Nock.RedTeam.Batch557.exists_cert._proof_1_1 B557 B557 3466115748 -
Nock.RedTeam.Batch557.exists_cert._proof_1_2 B557 B557 3332420868 -
Nock.RedTeam.Batch557.exists_cert._proof_1_4 B557 B557 614572058 -
Nock.RedTeam.Batch557.figures_unmoved_31' B557 B557 2119699788 -
Nock.RedTeam.Batch557.figures_unmoved_32' B557 B557 2478479516 -
Nock.RedTeam.Batch557.fixture_widths B557 B557 1482868531 -
Nock.RedTeam.Batch557.foldl_mul_degree B557 B557 1376684290 -
Nock.RedTeam.Batch557.gadget_complete B557 B557 2257083949 -
Nock.RedTeam.Batch557.gadget_complete._proof_1_1 B557 B557 4134966723 -
Nock.RedTeam.Batch557.gadget_complete._proof_1_2 B557 B557 795931678 -
Nock.RedTeam.Batch557.gadget_complete._proof_1_3 B557 B557 1815871564 -
Nock.RedTeam.Batch557.gadget_sound B557 B557 972306223 -
Nock.RedTeam.Batch557.gadget_sound._proof_1_1 B557 B557 254613981 -
Nock.RedTeam.Batch557.gadget_sound._proof_1_2 B557 B557 4048263168 -
Nock.RedTeam.Batch557.gadget_sound._proof_1_3 B557 B557 841827321 -
Nock.RedTeam.Batch557.goldilocksBit B557 B557 722437228 1730374438
Nock.RedTeam.Batch557.goldilocksTerms B557 B557 1699764672 1593559151
Nock.RedTeam.Batch557.goldilocksTerms.eq_1 B557 B557 1740960166 -
Nock.RedTeam.Batch557.goldilocksTerms_length B557 B557 283053013 -
Nock.RedTeam.Batch557.goldilocks_ltGate_degree_le B557 B557 345679823 -
Nock.RedTeam.Batch557.goldilocks_ltGate_degree_le._simp_1_2 B557 B557 1312591297 -
Nock.RedTeam.Batch557.goldilocks_scale B557 B557 3565226466 -
Nock.RedTeam.Batch557.goldilocks_top_shift B557 B557 3893692676 -
Nock.RedTeam.Batch557.helperAt B557 B557 2504765742 1292371559
Nock.RedTeam.Batch557.helperAt_degree B557 B557 2460525074 -
Nock.RedTeam.Batch557.helperPin B557 B557 132628539 355085613
Nock.RedTeam.Batch557.helperPin.eq_1 B557 B557 1736068142 -
Nock.RedTeam.Batch557.helperPin_degree B557 B557 2997965305 -
Nock.RedTeam.Batch557.lin B557 B557 488604730 38985862
Nock.RedTeam.Batch557.lin.eq_1 B557 B557 1254208565 -
Nock.RedTeam.Batch557.linExpr B557 B557 162424373 2932658992
Nock.RedTeam.Batch557.linExpr.eq_1 B557 B557 697559775 -
Nock.RedTeam.Batch557.linExpr_degree B557 B557 1314750199 -
Nock.RedTeam.Batch557.lin_bit B557 B557 717644783 -
Nock.RedTeam.Batch557.ltCert B557 B557 3401873842 1231500494
Nock.RedTeam.Batch557.ltCert.eq_1 B557 B557 2921868510 -
Nock.RedTeam.Batch557.ltCert_eq B557 B557 4286931910 -
Nock.RedTeam.Batch557.ltGate B557 B557 2936021367 184806897
Nock.RedTeam.Batch557.ltGate.eq_1 B557 B557 1759697115 -
Nock.RedTeam.Batch557.ltGate_degree_le B557 B557 809926699 -
Nock.RedTeam.Batch557.ltK B557 B557 4113182427 1388272195
Nock.RedTeam.Batch557.ltK._f B557 B557 3463763688 1561789321
Nock.RedTeam.Batch557.ltK._sunfold B557 B557 4113182427 2607152102
Nock.RedTeam.Batch557.ltK._unsafe_rec B557 B557 4113182427 1985451351
Nock.RedTeam.Batch557.ltK.eq_1 B557 B557 1472975948 -
Nock.RedTeam.Batch557.ltK.eq_2 B557 B557 3564451757 -
Nock.RedTeam.Batch557.ltK.eq_def B557 B557 2765282160 -
Nock.RedTeam.Batch557.ltK_bool B557 B557 3621964912 -
Nock.RedTeam.Batch557.ltK_bool._simp_1_7 B557 B557 3462990727 -
Nock.RedTeam.Batch557.ltK_expand B557 B557 2841369289 -
Nock.RedTeam.Batch557.ltK_expand._simp_1_4 B557 B557 3462990727 -
Nock.RedTeam.Batch557.ltL B557 B557 4280903205 1339348433
Nock.RedTeam.Batch557.ltL._f B557 B557 4141990442 3429995642
Nock.RedTeam.Batch557.ltL._sparseCasesOn_1 B557 B557 232071730 1208867370
Nock.RedTeam.Batch557.ltL._sparseCasesOn_1.else_eq B557 B557 487533682 -
Nock.RedTeam.Batch557.ltL._sunfold B557 B557 4280903205 2986392962
Nock.RedTeam.Batch557.ltL._unsafe_rec B557 B557 4280903205 1732737907
Nock.RedTeam.Batch557.ltL.eq_1 B557 B557 1176269881 -
Nock.RedTeam.Batch557.ltL.eq_2 B557 B557 958739670 -
Nock.RedTeam.Batch557.ltL.eq_def B557 B557 3132027834 -
Nock.RedTeam.Batch557.ltL.match_1 B557 B557 3726342420 3961437174
Nock.RedTeam.Batch557.ltL_iff B557 B557 3074581517 -
Nock.RedTeam.Batch557.ltL_iff._proof_1_8 B557 B557 933204360 -
Nock.RedTeam.Batch557.ltL_iff._proof_1_9 B557 B557 2457043630 -
Nock.RedTeam.Batch557.ltL_iff._simp_1_7 B557 B557 3462990727 -
Nock.RedTeam.Batch557.lusGBy_boundedBy B557 B557 2072466051 -
Nock.RedTeam.Batch557.mRangeGate B557 B557 2936021367 1792627360
Nock.RedTeam.Batch557.mRangeGate.eq_1 B557 B557 2423584619 -
Nock.RedTeam.Batch557.mRangeGate_degree_le B557 B557 3984356278 -
Nock.RedTeam.Batch557.pPin B557 B557 2517329158 55408308
Nock.RedTeam.Batch557.pPin.eq_1 B557 B557 1293886421 -
Nock.RedTeam.Batch557.pbits B557 B557 3633872711 2549354160
Nock.RedTeam.Batch557.pbits.eq_1 B557 B557 1015857950 -
Nock.RedTeam.Batch557.pbits_3_5 B557 B557 1478340851 -
Nock.RedTeam.Batch557.pbits_4_10 B557 B557 180302932 -
Nock.RedTeam.Batch557.pbits_inj B557 B557 3385357598 -
Nock.RedTeam.Batch557.pbits_length B557 B557 1160739736 -
Nock.RedTeam.Batch557.pbits_succ B557 B557 1774627830 -
Nock.RedTeam.Batch557.pbits_succ._proof_1_2 B557 B557 464915228 -
Nock.RedTeam.Batch557.pwAccountingWork' B557 C557 3512939730 2932478779
Nock.RedTeam.Batch557.pwAccountingWork'.eq_1 B557 B557 3541892108 -
Nock.RedTeam.Batch557.pwAccountingWork'_64 B557 B557 1503542146 -
Nock.RedTeam.Batch557.pwAccountingWork'_majorises B557 C557 1285897857 -
Nock.RedTeam.Batch557.pwAccountingWork'_majorises._proof_1_1 B557 C557 29758606 -
Nock.RedTeam.Batch557.rangeColumns B557 B557 9906956 1101984332
Nock.RedTeam.Batch557.rangeColumns.eq_1 B557 B557 4139590622 -
Nock.RedTeam.Batch557.rangeColumns_10 B557 B557 4109373321 -
Nock.RedTeam.Batch557.rangeColumns_17 B557 B557 1902471349 -
Nock.RedTeam.Batch557.rangeColumns_64 B557 B557 3635181939 -
Nock.RedTeam.Batch557.rangeGates B557 B557 2546708756 591439694
Nock.RedTeam.Batch557.rangeGates.eq_1 B557 B557 282154940 -
Nock.RedTeam.Batch557.rangeGates_10 B557 B557 3049176136 -
Nock.RedTeam.Batch557.rangeGates_17 B557 B557 159853380 -
Nock.RedTeam.Batch557.rangeGates_64 B557 B557 1335624654 -
Nock.RedTeam.Batch557.rangeK B557 B557 994397701 3307273744
Nock.RedTeam.Batch557.rangeK.eq_1 B557 B557 3673322540 -
Nock.RedTeam.Batch557.range_gate_iff B557 B557 548555589 -
Nock.RedTeam.Batch557.range_gate_iff._proof_1_3 B557 B557 2836571610 -
Nock.RedTeam.Batch557.range_gate_vacuous_pow2 B557 B557 23851837 -
Nock.RedTeam.Batch557.range_gate_vacuous_pow2._proof_1_1 B557 B557 1211051598 -
Nock.RedTeam.Batch557.result_boundedBy_of_hyps B557 B557 4154456011 -
Nock.RedTeam.Batch557.result_boundedBy_of_hyps._proof_1_1 B557 B557 1672064170 -
Nock.RedTeam.Batch557.runAxesBoundedBy_of_hyps B557 B557 3764074386 -
Nock.RedTeam.Batch557.runAxesBoundedBy_of_hyps._proof_1_1 B557 B557 1672064170 -
Nock.RedTeam.Batch557.shiftBits B557 B557 2546708756 334031047
Nock.RedTeam.Batch557.shiftBits.eq_1 B557 B557 3909616867 -
Nock.RedTeam.Batch557.shiftBits_covers B557 B557 2598143818 -
Nock.RedTeam.Batch557.shiftBits_covers._proof_1_1 B557 B557 2182835543 -
Nock.RedTeam.Batch557.size_31 B557 B557 410628636 -
Nock.RedTeam.Batch557.size_65537 B557 B557 3471314667 -
Nock.RedTeam.Batch557.size_769 B557 B557 1409525445 -
Nock.RedTeam.Batch557.size_goldilocks B557 B557 2797655390 -
Nock.RedTeam.Batch557.size_spec B557 B557 3178007136 -
Nock.RedTeam.Batch557.sumExpr B557 B557 2936021367 2781720417
Nock.RedTeam.Batch557.sumExpr._f B557 B557 1781669159 102581927
Nock.RedTeam.Batch557.sumExpr._sunfold B557 B557 2936021367 900067359
Nock.RedTeam.Batch557.sumExpr._unsafe_rec B557 B557 2936021367 962776012
Nock.RedTeam.Batch557.sumExpr.eq_1 B557 B557 2592184190 -
Nock.RedTeam.Batch557.sumExpr.eq_2 B557 B557 3443151302 -
Nock.RedTeam.Batch557.sumExpr.eq_def B557 B557 2204024407 -
Nock.RedTeam.Batch557.sumExpr.match_1 B557 B557 1288541003 230950168
Nock.RedTeam.Batch557.sumExpr_degree_le B557 B557 3015124490 -
Nock.RedTeam.Batch557.term B557 B557 1036226383 617851661
Nock.RedTeam.Batch557.term.eq_1 B557 B557 3970465366 -
Nock.RedTeam.Batch557.termAt B557 B557 1867283116 2381987081
Nock.RedTeam.Batch557.termAt_degree_le B557 B557 1955501551 -
Nock.RedTeam.Batch557.termAt_degree_le._proof_1_4 B557 B557 1602155271 -
Nock.RedTeam.Batch557.termAt_degree_le._simp_1_1 B557 B557 1312591297 -
Nock.RedTeam.Batch557.termAt_degree_le._simp_1_2 B557 B557 3706964957 -
Nock.RedTeam.Batch557.termExpr B557 B557 920037774 3431287217
Nock.RedTeam.Batch557.termExpr.eq_1 B557 B557 297082421 -
Nock.RedTeam.Batch557.termExpr_degree B557 B557 1575445636 -
Nock.RedTeam.Batch557.termExpr_degree_le B557 B557 2457134038 -
Nock.RedTeam.Batch557.termExpr_degree_le._proof_1_1 B557 B557 4102968117 -
Nock.RedTeam.Batch557.term_ne_zero_iff B557 B557 3079392362 -
Nock.RedTeam.Batch557.term_ne_zero_iff._simp_1_2 B557 B557 1535653342 -
Nock.RedTeam.Batch557.toNat_eq_one B557 B557 2150319261 -
Nock.RedTeam.Batch557.topBrief B557 B557 3091944575 3069922644
Nock.RedTeam.Batch557.topBrief.eq_1 B557 B557 2287710113 -
Nock.RedTeam.Batch557.topK B557 B557 994397701 3010345575
Nock.RedTeam.Batch557.topK.eq_1 B557 B557 1980800918 -
Nock.RedTeam.Batch557.topPin B557 B557 2517329158 559730145
Nock.RedTeam.Batch557.topPin.eq_1 B557 B557 905010907 -
Nock.RedTeam.Batch557.topPin_degrees B557 B557 3357116939 -
Nock.RedTeam.Batch557.top_eq_one_iff B557 B557 3848613539 -
Nock.RedTeam.Batch557.top_eq_zero_of_ne B557 B557 2559755203 -
Nock.RedTeam.Batch557.top_shift_zero_bits_accepted B557 B557 2391504500 -
Nock.RedTeam.Batch557.top_shift_zero_bits_accepted._proof_1_1 B557 B557 394502498 -
Nock.RedTeam.Batch557.top_shift_zero_bits_accepted._proof_1_2 B557 B557 3761279571 -
Nock.RedTeam.Batch557.top_shift_zero_bits_accepted._proof_1_3 B557 B557 4214027429 -
Nock.RedTeam.Batch557.top_shift_zero_bits_accepted._proof_1_4 B557 B557 3301873661 -
Nock.RedTeam.Batch557.val B557 B557 27352352 1007683659
Nock.RedTeam.Batch557.val._f B557 B557 1134019291 1164766184
Nock.RedTeam.Batch557.val._sunfold B557 B557 27352352 2566548407
Nock.RedTeam.Batch557.val._unsafe_rec B557 B557 27352352 3928025652
Nock.RedTeam.Batch557.val.eq_1 B557 B557 229611040 -
Nock.RedTeam.Batch557.val.eq_2 B557 B557 3756249038 -
Nock.RedTeam.Batch557.val.eq_def B557 B557 1678138553 -
Nock.RedTeam.Batch557.val.match_1 B557 B557 2817197741 686084325
Nock.RedTeam.Batch557.val_bitsOf B557 B557 2035543970 -
Nock.RedTeam.Batch557.val_bitsOf._proof_1_4 B557 B557 295735032 -
Nock.RedTeam.Batch557.val_inj B557 B557 3244915647 -
Nock.RedTeam.Batch557.val_inj._proof_1_5 B557 B557 2004966688 -
Nock.RedTeam.Batch557.val_inj._proof_1_6 B557 B557 2687070651 -
Nock.RedTeam.Batch557.val_inj._proof_1_7 B557 B557 2489617474 -
Nock.RedTeam.Batch557.val_inj._simp_1_1 B557 B557 3462990727 -
Nock.RedTeam.Batch557.val_lt B557 B557 2272870108 -
Nock.RedTeam.Batch557.val_lt._proof_1_4 B557 B557 1502594132 -
Nock.RedTeam.Batch557.val_lt._proof_1_5 B557 B557 2293279315 -
Nock.RedTeam.Batch557.val_pbits B557 B557 888874722 -
Nock.RedTeam.Batch575.C'poly B575 C575 423983272 3599927495
Nock.RedTeam.Batch575.C'poly.eq_1 B575 C575 2363925257 -
Nock.RedTeam.Batch575.Cpoly_false B575 C575 4172716618 -
Nock.RedTeam.Batch575.Padding B575 C575 210794549 3732629751
Nock.RedTeam.Batch575.Paired B575 C575 1622607706 1541369280
Nock.RedTeam.Batch575.Paired.eq_1 B575 B575 4213184491 -
Nock.RedTeam.Batch575.Tpoly B575 C575 2121760106 984166618
Nock.RedTeam.Batch575.Tpoly.eq_1 B575 C575 290792602 -
Nock.RedTeam.Batch575.UniqueExponents B575 C575 1818197113 2073113259
Nock.RedTeam.Batch575.Y B575 C575 2788190218 156279486
Nock.RedTeam.Batch575.Y.eq_1 B575 C575 1340994943 -
Nock.RedTeam.Batch575.absent_coeff B575 C575 2446254165 -
Nock.RedTeam.Batch575.addrP_cons B575 C575 935935045 -
Nock.RedTeam.Batch575.axis1 B575 B575 2546708756 2713819238
Nock.RedTeam.Batch575.axis1.eq_1 B575 B575 2924158850 -
Nock.RedTeam.Batch575.axis1bits B575 B575 454481631 1154790266
Nock.RedTeam.Batch575.coeff_const_X_pow B575 C575 164292591 -
Nock.RedTeam.Batch575.coeff_formR B575 C575 1870712493 -
Nock.RedTeam.Batch575.counts_zero_iff_coeffs B575 C575 156022112 -
Nock.RedTeam.Batch575.decompCount B575 C575 1106012378 2637358257
Nock.RedTeam.Batch575.decompCount._f B575 C575 415629541 3586517379
Nock.RedTeam.Batch575.decompCount._sunfold B575 C575 1106012378 3484228163
Nock.RedTeam.Batch575.decompCount._unsafe_rec B575 C575 1106012378 4164717698
Nock.RedTeam.Batch575.decompCount.eq_1 B575 C575 1018808576 -
Nock.RedTeam.Batch575.decompCount.eq_2 B575 C575 1787353190 -
Nock.RedTeam.Batch575.decompCount.eq_3 B575 C575 2713463818 -
Nock.RedTeam.Batch575.decompCount.eq_4 B575 C575 2996390162 -
Nock.RedTeam.Batch575.decompCount.eq_def B575 C575 3515389077 -
Nock.RedTeam.Batch575.decompCount_le_nodeCount B575 C575 3790669797 -
Nock.RedTeam.Batch575.decompCount_le_nodeCount._f B575 C575 746577396 3535708055
Nock.RedTeam.Batch575.decompCount_le_nodeCount._proof_1_13 B575 C575 3729162437 -
Nock.RedTeam.Batch575.decompCount_le_nodeCount._proof_1_14 B575 C575 3324421111 -
Nock.RedTeam.Batch575.decompCount_le_nodeCount.match_1_1 B575 C575 3410202841 1182909447
Nock.RedTeam.Batch575.degY_le B575 C575 2421478158 -
Nock.RedTeam.Batch575.degY_le._proof_1_1 B575 C575 1545534301 -
Nock.RedTeam.Batch575.formRCounts B575 C575 3968821151 3806377078
Nock.RedTeam.Batch575.formRCounts._f B575 C575 2448364561 3052000575
Nock.RedTeam.Batch575.formRCounts._sunfold B575 C575 3968821151 2931052149
Nock.RedTeam.Batch575.formRCounts.eq_1 B575 C575 678834917 -
Nock.RedTeam.Batch575.formRCounts.eq_2 B575 C575 1451396026 -
Nock.RedTeam.Batch575.formRCounts.eq_3 B575 C575 1177279459 -
Nock.RedTeam.Batch575.formRCounts.eq_4 B575 C575 1935138103 -
Nock.RedTeam.Batch575.formRCounts.eq_def B575 C575 654582710 -
Nock.RedTeam.Batch575.formRPw B575 C575 953072127 3099697772
Nock.RedTeam.Batch575.formRPw._f B575 C575 3892300044 3879558801
Nock.RedTeam.Batch575.formRPw._sunfold B575 C575 953072127 1071332316
Nock.RedTeam.Batch575.formRPw.eq_1 B575 C575 1332292823 -
Nock.RedTeam.Batch575.formRPw.eq_2 B575 C575 1122816923 -
Nock.RedTeam.Batch575.formRPw.eq_3 B575 C575 2590078036 -
Nock.RedTeam.Batch575.formRPw.eq_4 B575 C575 136335947 -
Nock.RedTeam.Batch575.formRPw.eq_def B575 C575 2945621367 -
Nock.RedTeam.Batch575.formRPw.match_1 B575 C575 2070133508 57102305
Nock.RedTeam.Batch575.formR_coeff_cases B575 C575 570329753 -
Nock.RedTeam.Batch575.formR_counts_zero_iff B575 C575 386390178 -
Nock.RedTeam.Batch575.formR_counts_zero_iff._proof_1_1 B575 C575 3107749508 -
Nock.RedTeam.Batch575.formR_counts_zero_iff._proof_1_2 B575 C575 156455894 -
Nock.RedTeam.Batch575.formR_counts_zero_iff._proof_1_7 B575 C575 3925695886 -
Nock.RedTeam.Batch575.formR_counts_zero_iff._proof_1_8 B575 C575 251934638 -
Nock.RedTeam.Batch575.formR_counts_zero_iff.match_1_3 B575 C575 4154404134 2784593402
Nock.RedTeam.Batch575.formR_counts_zero_iff.match_1_5 B575 C575 2028674872 3249635240
Nock.RedTeam.Batch575.formR_event_card B575 C575 1017274713 -
Nock.RedTeam.Batch575.formR_support_le_envelope B575 C575 3117467147 -
Nock.RedTeam.Batch575.formR_work_vs_majorant B575 C575 2596077745 -
Nock.RedTeam.Batch575.formR_work_vs_majorant._proof_1_1 B575 C575 473634815 -
Nock.RedTeam.Batch575.list_length_eq_one B575 C575 962345923 -
Nock.RedTeam.Batch575.natDegree_C'poly B575 C575 2047474192 -
Nock.RedTeam.Batch575.natDegree_C'poly._proof_1_1 B575 C575 3426529743 -
Nock.RedTeam.Batch575.natDegree_Tpoly B575 C575 3770247551 -
Nock.RedTeam.Batch575.natDegree_formRCounts_coeff B575 C575 2220506780 -
Nock.RedTeam.Batch575.natDegree_formRCounts_coeff._proof_1_13 B575 C575 2127658490 -
Nock.RedTeam.Batch575.natDegree_formRCounts_coeff._proof_1_14 B575 C575 1674051418 -
Nock.RedTeam.Batch575.natDegree_formRCounts_coeff._proof_1_15 B575 C575 2202526956 -
Nock.RedTeam.Batch575.natDegree_formRCounts_coeff._proof_1_16 B575 C575 978594812 -
Nock.RedTeam.Batch575.natDegree_formRCounts_coeff._proof_1_7 B575 C575 4073535012 -
Nock.RedTeam.Batch575.natDegree_formRPw_coeff B575 C575 3879980663 -
Nock.RedTeam.Batch575.natDegree_formRPw_coeff._proof_1_12 B575 C575 3472176156 -
Nock.RedTeam.Batch575.natDegree_formRPw_coeff._proof_1_13 B575 C575 3450003673 -
Nock.RedTeam.Batch575.natDegree_formRPw_coeff._proof_1_14 B575 C575 3962209038 -
Nock.RedTeam.Batch575.natDegree_formRPw_coeff._proof_1_15 B575 C575 2614661514 -
Nock.RedTeam.Batch575.natDegree_scale B575 C575 2279494421 -
Nock.RedTeam.Batch575.nodeCount B575 C575 1106012378 133854298
Nock.RedTeam.Batch575.nodeCount._f B575 C575 415629541 3862713361
Nock.RedTeam.Batch575.nodeCount._sunfold B575 C575 1106012378 2696717240
Nock.RedTeam.Batch575.nodeCount._unsafe_rec B575 C575 1106012378 2702060746
Nock.RedTeam.Batch575.nodeCount.eq_1 B575 C575 3116792390 -
Nock.RedTeam.Batch575.nodeCount.eq_2 B575 C575 2303551454 -
Nock.RedTeam.Batch575.nodeCount.eq_3 B575 C575 3437608237 -
Nock.RedTeam.Batch575.nodeCount.eq_4 B575 C575 2688067174 -
Nock.RedTeam.Batch575.nodeCount.eq_def B575 C575 2728955081 -
Nock.RedTeam.Batch575.paired_bracket B575 C575 79884844 -
Nock.RedTeam.Batch575.pw_not_load_bearing B575 B575 3057228289 -
Nock.RedTeam.Batch575.rpaths_eq_nil B575 C575 194934239 -
Nock.RedTeam.Batch575.rpaths_length B575 C575 1800957573 -
Nock.RedTeam.Batch575.rpaths_length._f B575 C575 1036633489 1549910939
Nock.RedTeam.Batch575.rpaths_length.match_1_1 B575 C575 3410202841 1182909447
Nock.RedTeam.Batch575.rpaths_singleton B575 C575 1236330360 -
Nock.RedTeam.Batch575.s2FailTree B575 B575 2351502989 2960739361
Nock.RedTeam.Batch575.s2FailTree.eq_1 B575 B575 873299979 -
Nock.RedTeam.Batch575.s2Fail_counts B575 B575 4034478929 -
Nock.RedTeam.Batch575.s2Fail_not_nested B575 B575 2910036652 -
Nock.RedTeam.Batch575.s2Fail_paired B575 B575 1225581373 -
Nock.RedTeam.Batch575.s2Fail_paths B575 B575 2738872327 -
Nock.RedTeam.Batch575.s2Fail_pw B575 B575 312690882 -
Nock.RedTeam.Batch575.s2Fail_relaxis B575 B575 3995106175 -
Nock.RedTeam.Batch575.s2Fail_unique B575 B575 423393017 -
Nock.RedTeam.Batch575.s2_nested_fails B575 B575 178420293 -
Nock.RedTeam.Batch575.s2_nested_fails.match_1_1 B575 B575 2508554441 55181087
Nock.RedTeam.Batch575.s2_nested_fails_with_pw B575 B575 895528188 -
Nock.RedTeam.Batch575.sameTs_c B575 B575 70975716 1294897761
Nock.RedTeam.Batch575.sameTs_c.eq_1 B575 B575 1105981947 -
Nock.RedTeam.Batch575.sameTs_m B575 B575 2546708756 4142234025
Nock.RedTeam.Batch575.sameTs_m.eq_1 B575 B575 2162863611 -
Nock.RedTeam.Batch575.scale B575 C575 2121760106 1079955503
Nock.RedTeam.Batch575.scale.eq_1 B575 C575 2313884604 -
Nock.RedTeam.Batch575.sumAddrP B575 C575 2166233548 1020100940
Nock.RedTeam.Batch575.sumAddrP.eq_1 B575 C575 3470665707 -
Nock.RedTeam.Batch575.sumAddrP_append B575 C575 2315743053 -
Nock.RedTeam.Batch575.sumAddrP_shift B575 C575 3283678752 -
Nock.RedTeam.Batch575.sumPowP B575 C575 2166233548 2568926105
Nock.RedTeam.Batch575.sumPowP.eq_1 B575 C575 3478179711 -
Nock.RedTeam.Batch575.sumPowP_append B575 C575 1858040146 -
Nock.RedTeam.Batch575.sumPowP_shift B575 C575 267733668 -
Nock.RedTeam.Batch575.unpaired_read_coeff B575 C575 4091934585 -
Nock.RedTeam.Batch575.unpaired_read_ne B575 C575 1974395588 -
Nock.RedTeam.Batch575.unpaired_verify_coeff B575 C575 3876990400 -
Nock.RedTeam.Batch575.unpaired_verify_ne B575 C575 2563215565 -
Nock.RedTeam.Batch575.vpaths_eq_nil B575 C575 1518893483 -
Nock.RedTeam.Batch575.vpaths_length B575 C575 2751318715 -
Nock.RedTeam.Batch575.vpaths_length._f B575 C575 3331836151 3017210363
Nock.RedTeam.Batch575.vpaths_length.match_1_1 B575 C575 3410202841 1182909447
Nock.RedTeam.Batch575.vpaths_singleton B575 C575 771981128 -"


def digestsAtBase : String := "Nock.NockVMROM.Thm54.DeployedStaging 204 880735740987659027
Nock.NockVMROM.Thm54.FormRAxisEvent 67 1522227421159118681
Nock.RedTeam.Batch363Thm54AcceptedContent 4 660077547883360179
Nock.RedTeam.Batch554Thm54PwFunctional 203 14119643418010899285
Nock.RedTeam.Batch555Thm54PwCertificate 107 9391227257882709315
Nock.RedTeam.Batch556Thm54PwEvent 29 16586981882241791328
Nock.RedTeam.Batch557Thm54RangeGadget 278 4271989939577676028
Nock.RedTeam.Batch558Thm54FormRJoin 29 9231959007272228881
Nock.RedTeam.Batch575Thm54FormRMtree 132 10524277566947421701
Nock.RedTeam.Batch576Thm54FormRNegatives 16 18337166840196162303
Nock.RedTeam.Batch577Thm54FormRCompleteness 38 2710332912347085039
Nock.RedTeam.Batch581Thm54FormREvent 12 12674802896832735829
Nock.RedTeam.Batch582Thm54FormRCompletenessHazard 14 15429469039719168227
Nock.RedTeam.Batch583Thm54DeployedStaging 14 15439857314584313401
Nock.RedTeam.Batch584Thm54StagingChronology 6 17538545429600134932
Nock.RedTeam.Batch619Thm54FormRReadSet 7 4515141408010865141
Nock.RedTeam.Batch620Thm54AtomRoundF1 3 5610398585759358928
Nock.RedTeam.Batch621Thm54FormRNumerals 1 6907034089448381614
Nock.RedTeam.Batch622Thm54FormRReviewRepairs 2 12286368471170011704
Nock.RedTeam.Batch624Thm54FormREventA4 16 4701637537874768968
Nock.RedTeam.Batch625Thm54FormREventStaging 7 8790191094244774103
Nock.RedTeam.Batch626Thm54FormREventNested 12 11517903969060239787
Nock.RedTeam.Batch627Thm54FormREventMirror 170 16373371886382006874
Nock.RedTeam.Batch628Thm54LambdaEventLift 18 9322825281001680018
Nock.RedTeam.Batch629Thm54LambdaEventFrontier 21 6084540173338267873
Nock.RedTeam.Batch633Thm54LambdaEventUnguarded 28 482236954834910062
Nock.RedTeam.Batch634Thm54LambdaEventImportCycle 20 3364290717984755863
Nock.RedTeam.Batch641Thm54LambdaEventGuarded 27 12771257767625506379
Nock.RedTeam.Batch646Thm54LambdaEventHostileForm 19 14706442605324895923"

/-- The digest: a fold of `mixHash` over the rows sorted by name. -/
def digestOf (rows : List (String × UInt64 × String)) : UInt64 :=
  rows.foldl (init := 7) fun acc (n, t, v) => mixHash (mixHash acc (hash n)) (mixHash t (hash v))

/-- The constants of the environment, by printed name. -/
def byName (env : Environment) : Std.HashMap String (Name × ConstantInfo) := Id.run do
  let mut m : Std.HashMap String (Name × ConstantInfo) := {}
  for (n, ci) in env.constants.map₁.toList do m := m.insert (toString n) (n, ci)
  return m

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

/-- The value hash a row records for a definition (`-` otherwise). -/
def defValue (ci : ConstantInfo) : String :=
  match ci with
  | .defnInfo d => toString d.value.hash
  | _ => "-"

/-- Check one row; `none` when it matches. -/
def checkRow (env : Environment) (tab : Std.HashMap String (Name × ConstantInfo))
    (row : String) : Option String :=
  match row.splitOn " " with
  | [n, _base, now, th, vh] =>
    match tab.get? n with
    | none => some s!"{n}: missing"
    | some (nm, ci) =>
      if toString ci.type.hash != th then some s!"{n}: type hash {ci.type.hash} ≠ {th}"
      else if defValue ci != "-" && defValue ci != vh then some s!"{n}: value hash changed"
      else if moduleOf env nm != modOfCode now then
        some s!"{n}: module {moduleOf env nm} ≠ {modOfCode now}"
      else none
  | _ => some s!"malformed row {row}"

/-! ## per name -/

run_cmd do
  let env ← getEnv
  let tab := byName env
  let rows := (namesAtBase.splitOn "\n").filter (· ≠ "")
  let mut moved : Nat := 0
  for r in rows do
    if let some err := checkRow env tab r then throwError "R1: {err}"
    match r.splitOn " " with
    | [_, b, a, _, _] => if b != a then moved := moved + 1
    | _ => pure ()
  logInfo m!"R1: {rows.length} names of Batch554/556/557/575/FormRAxisEvent: types unchanged, \
    definition values unchanged, {moved} moved to the recorded modules, the rest in place"

/-! ## per module, over all 29 modules -/

run_cmd do
  let env ← getEnv
  let tab := byName env
  let movedRows := ((namesAtBase.splitOn "\n").filter (· ≠ "")).filterMap fun r =>
    match r.splitOn " " with
    | [n, b, a, _, _] => if b != a then some (n, modOfCode b) else none
    | _ => none
  let movedMap : Std.HashMap String Name := movedRows.foldl (fun m (n, b) => m.insert n b) {}
  let bases := ((digestsAtBase.splitOn "\n").filter (· ≠ "")).filterMap fun r =>
    match r.splitOn " " with
    | [m, c, d] => some (m, c, d)
    | _ => none
  let mut groups : Std.HashMap String (List (String × UInt64 × String)) := {}

  -- (`formRLambdaEvent`, `restOf8`, `seedSlice_card_le`, `formRLambdaEvent_card_le`, with their


  let baseNames : Std.HashSet String := ((namesAtBase.splitOn "\n").filter (· ≠ "")).foldl
    (fun acc r => match r.splitOn " " with | n :: _ => acc.insert n | _ => acc) {}
  let added30 : List String :=
    ["Nock.NockVMROM.Thm54.FormRAxisEvent.formRLambdaEvent",
     "Nock.NockVMROM.Thm54.FormRAxisEvent.restOf8",
     "Nock.NockVMROM.Thm54.FormRAxisEvent.seedSlice_card_le"]
  let mut skipped : Array String := #[]
  for (s, (n, ci)) in tab.toList do
    if isPrivateName n then continue
    if moduleOf env n == `Nock.NockVMROM.Thm54.FormRAxisEvent ∧ ¬ baseNames.contains s ∧
        added30.any (fun pre => s.startsWith pre) then
      skipped := skipped.push s
      continue
    let base := (movedMap.get? s).getD (moduleOf env n)
    groups := groups.insert (toString base)
      ((s, ci.type.hash, defValue ci) :: groups.getD (toString base) [])
  let mut bad : Array String := #[]
  for (m, c, d) in bases do
    let rows := (groups.getD m []).toArray.qsort (fun a b => a.1 < b.1) |>.toList
    if toString rows.length != c ∨ toString (digestOf rows) != d then
      bad := bad.push s!"{m} {rows.length} {digestOf rows}"
  unless bad.isEmpty do throwError "R2: moved: {bad}"
  logInfo m!"R2: {bases.length} modules, public names and digests as recorded at bb42fcc1 \
    (thirtieth-move additions excluded: {skipped.qsort (· < ·)})"

/-! ## PC: the R1 checker rejects a wrong row -/

run_cmd do
  let env ← getEnv
  let tab := byName env
  let some (_, pw) := tab.get? "Nock.RedTeam.Batch575.formRPw" | throwError "PC: formRPw missing"
  let some (_, fc) := tab.get? "Nock.RedTeam.Batch575.formRCounts" | throwError "PC: missing"
  let bad := s!"Nock.RedTeam.Batch575.formRCounts B575 C575 {pw.type.hash} {defValue fc}"
  let good := s!"Nock.RedTeam.Batch575.formRCounts B575 C575 {fc.type.hash} {defValue fc}"
  unless (checkRow env tab good).isNone do throwError "PC: the true row is rejected"
  match checkRow env tab bad with
  | some e => logInfo m!"PC: a row with formRPw's type hash is rejected: {e}"
  | none => throwError "PC: the wrong row was accepted"

end Nock.RedTeam.Batch637
