/-
**`exec_e2e_J8`**, the end-to-end theorem of the executable verifier at the J-8 interface, as a
kernel-checked SKELETON.

  `Pr[ AccF … ∧ ¬ Nock.Jet.HoldsN d.c ] ≤ 2^-82`

at `JX := I.JJ npub tp hcap = plusJ (minusT (J8 d hd) I.R I.hfree) (Fin npub) tp hcap` (TieJ8G), with the instance
`I = ⟨XI170 XI0, hsh, …, d, …, R, hT, hσ, hfree⟩ : TieJ8G.Inst`, `d.Pb = PbOfX XI …`, `d.hN = XI.hN`, `d.ω = zv XI.hGen` (`DatX`).
`R` is ABSTRACT in the statement (a concrete `RJ8` makes `Fin (RJ8 …).ns'` unification run for minutes); the final instance is
`R := RJ8 XI d hd`, `hT := rfl`, `hσ := fun _ => rfl`, `hfree := hfree_J8 …`, which IS `Inst.ofRJ8 (XI170 XI0) …` (`inst_RJ8`, `rfl`).
`R0J.Holds = HoldsN d.c` is `rfl` through `rapJ`/`plusJ`/`minusT`/`J8` (`holds_JX`).

Part 1 `exec_e2e_J` (+ `hdagU_J`): the scratch port (generic `J`). Part 2 the J-8 instance and `exec_e2e_J8` (`hdagU` discharged by
`hdagU_J8` with `G := Gflat I (hsz_of_hops …)`, `gb := gbJ`). Part 3 `hRVU_X_of` (`hRVU_J8` + plumbing).

## BINDER LEDGER of `exec_e2e_J8`  (LABEL | discharged by / will be discharged by)
Section variables (they enter the statement):
- `XI0`, `hn32 : nD ≤ 32`                 | instance; `hn32` = `hn32_of_shape hsh` (kernel), kept as a variable for `ωS`
- `hsh : j8ShapeOk (XI170 XI0)`          | EXECUTED (verifier exe shape gate) + kernel Bool→Prop lemmas
- `D : DatX …`                           | construction: `DatX.ofData` builds it with `rfl` equations (= Inst.hd/hdN/hdω)
- `hdk : DatumOK D.d`                    | DATUM HYPOTHESIS (N1/N2 binders of nock's `soundJ8V_pointwise`); witness only at nock's
                                           `nvJet_in_regime` (InstJ8D), NOT yet at a `PbOfX` datum
- `R hT hσ hfree`                        | KERNEL: `RJ8`, `rfl`, `rfl`, `hfree_J8` (`inst_RJ8`)
- `npub`, `tp`, `hcap : I.Cap npub`      | construction; `hcap` a number (kernel, `card Ι = 1117`), pending
- `pr : PubRead JX`                      | construction, pending (`plusPR` with a canonicalising `rd`, = `Mof`)
- `dF`, `hNH`, `hpd`                     | numbers (`|H| = hN = 2^(k+1)`, `pre.size ≤ hN+1` = `hpd_of_shape`): kernel, pending
- `ders cmeta`, `hnum : NumOK`, `hops : HopsOK` | named hyps. `HopsOK` = hop 0 (`J8Chips`: EXECUTED + kernel `J8ChipsK`;
                                           TCB until it lands); `NumOK` = kroots ∈ {1,9,25,42,48,174}, krootsV ∈ {1,2}: DATUM ↔ instance
                                           (`decide` per program; enforced by hop 0)
- `cI`, `hm`                             | construction (layout), pending 
- `I0 I Ifin`, the `DecidableEq/Finite/SampleableType` instances, `enc md L sl0 sl1 m0 mf` | protocol parameters as in `exec_e2e_final`
Theorem binders:
- `hl : XI0.l = 170`                      | EXECUTED (exe; `exec_e2e_final` is at `XI170 XI0`)
- `encZ decZ hz`                          | statement parameters
- `hnq9 : nq = 9`                         | EXECUTED (instance number; shape checks only `nq % 3 = 0`) → `hnq` by `rfl`
- `hkd : colKind[c] < 3`                  | EXECUTED (pending a shape conjunct)
- `hblk hblkq`                            | KERNEL, pending (cr-tables `decide` per chip id, needs `cI`)
- `hpub hppt hgen`                        | construction of `cI`/`pr`, pending 
- `hnpub`, `hcI_col`, `hcI_pub`           | construction (layout of `cI`), pending [named hyps]
- `hrdT : RdSpec`                         | KERNEL, pending (`pr.rd` = `Mof` per chip)   [named hyp]
- `hn0 hn1`                               | EXECUTED (`nCoins = #[13,6]` is in the shape, `slotOfOk`) 
- `hSlotOK`                               | EXECUTED + kernel, pending (loader `ders`/`cmeta` literal check) 
- `hpre0`                                 | KERNEL, pending (`preKindOk` + chip `preprocessingIndex` ⊆ `preIdxJ8`, ~60 lines) 
- `hcur1`                                 | EXECUTED + kernel (`maskOk` + Lagrange) for the 3 masks; TCB `hpreJet` for the jet 
- `hRVU`                                  | KERNEL, pending (= `hRVU_X_of`: `hRVU_J8` [kernel] + `StmtP d` [DATUM
                                            HYPOTHESIS] + `InpLink`/`hids`/`hpJ`/`hpV` [datum↔instance, `decide` per program] + slot
                                            canonicity + coin tie `hχ` [kernel, pending] + `rd` plumbing `hrd` [needs `PubJ8P` canon lemma])
- `hmd hL`                                | construction (`rfl` by choosing `md`, `L` as the verifier's)
- `hd hEnc`                               | construction (`dF = 1 = XI0.d`); `encK_ok` (kernel)
- `hrate hF htoPoly hD hH hDg`            | KERNEL numbers, pending (the `_numbers` pattern: `tp_eq`, field card, digest card)
- `hnsC : ns ≤ 2^20`                      | EXECUTED (instance number)
- `Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig` | adversary, as in `exec_e2e_final`
Discharged here (kernel): `hshape` (= `hsh`), `hr` (`r_of_shape`), `hnq` (from `hnq9`), `hoff` (`hoff_J8`), `hns` (`rfl`),
`hHJ` (`hdom_J8`), `hdagU` (`hdagU_J8`), `hb` (`gb_indep`), `hm12` (`cap_m` + `cI`), `hnqC` (`nq = 9`).

## Non-vacuity (sketch; the full toy1 `example` is NOT written: toy1 exists in Lean only as pub data, not as an `ExecInst`)
Kernel today: `hsh` at `toyShape4` (`toyShape_ok`); `DatX` at `toyShape4` (`toyPb`, `DatX.ofData`); `R…hfree` (`inst_RJ8`);
`hEnc` (`encK_ok`); `InpLink` at toy1 (`inpLink_toy1`); `PubJ8P` at toy1 (`SP.toy1_rel`); slot / pub canonicity at toy1
(`toy1_slots_can`, `toy1_pub_can`); `StmtP ∧ PubP` and `DatumOK` separately at nock's witness (`stmt_pub_inhabited`, `datumOK_witness`).
Waiting: `HopsOK` (false at toyShape4's placeholder chips; holds only at a real J-8 instance via exe check), `hcur1`
(`maskOk`), `hSlotOK`, `hRVU`'s `hrd`, and ONE datum carrying `DatumOK ∧ StmtP` with `d.Pb = PbOfX XI …` (no joint witness).
-/
import NockvmE2E.Exec.E2EFinal
import NockvmE2E.Exec.E2EInstGen
import NockvmE2E.Exec.HdagU
import NockvmE2E.Exec.J8Shape
import NockvmE2E.J8.MinusT
import NockvmE2E.J8.Regroup
import NockvmE2E.J8.InstJ8W
import NockvmE2E.J8.RVUJ8
import NockvmE2E.J8.TieJ8G

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Part 1: `exec_e2e_J` at an abstract interface `J` (an unchanged copy) -/

namespace NockvmE2E.Exec.E2EJ8
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
  NockvmE2E.Exec.InstGen
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.J8 NockvmE2E.Exec.E2ELR

variable (XI0 : ExecInst) (hn32 : (XI170 XI0).nD ≤ 32)

set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD hn32
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))

variable [SampleableType KC]
variable (J : RapAirJ (ZMod NockvmE2E.Exec.p) KC) [NeZero J.r] (pr : PubRead J) (d : ℕ+)
  (hNH : friBound s1 d ≤ J.H.card) (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card)
  {nsK : ℕ} (G : Regroup (deepParamsJ J pr ωS (31 / 64) (friBound s1 d) hNH hpd).ns nsK) (gb : Fin 3 → KC)

set_option hygiene false in
local notation "PJ" => (deepParamsJ J pr ωS (31 / 64) (friBound s1 d) hNH hpd).regroup G gb
set_option hygiene false in
local notation "AJ" => (airJ J pr ωS (31 / 64) (friBound s1 d) hNH hpd).regroup G gb
set_option hygiene false in
local notation "R0P" => R0J J pr ωS (31 / 64) (friBound s1 d)
set_option hygiene false in
local notation "RestP" => RestJ J pr ωS (31 / 64) (friBound s1 d) hNH hpd
set_option hygiene false in
local notation "RestVP" => RestVJ J pr ωS (31 / 64) (friBound s1 d) hNH hpd

variable (cI : J.ι0 ≃ Fin (XI170 XI0).nc) {m : ℕ} (hm : m + 1 = (XI170 XI0).nc * J.r + (PJ).nq)

set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cI J.r hm

variable [DecidableEq ((PJ).statement (R0P) (RestP)).M0] [Finite ((PJ).statement (R0P) (RestP)).M0]
  [DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  [Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
  (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
variable [∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (enc : KC ↪ DgJ8)
  (md : PointMaskData (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD)) (ZMod NockvmE2E.Exec.p) DgJ8) (L : Fri.FriLeaves (ω := ωS) s1)
  {n0 n1 : ℕ} (sl0 : {i : Fin (extFrame J.Φ0 2).n // (extFrame J.Φ0 2).sampledAfter i = 0} ≃ Fin n0)
  (sl1 : {i : Fin (extFrame J.Φ0 2).n // (extFrame J.Φ0 2).sampledAfter i = 1} ≃ Fin n1)
  (m0 : ((PJ).statement (R0P) (RestP)).M0) (mf : (R0P).Mfin)

set_option hygiene false in
local notation "MC" => msC (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 4 s1 d (XI170 XI0).l DgJ8 enc md L (S := KC)
set_option hygiene false in
local notation "RM" => RapP.rapMask (extFrame J.Φ0 2) KC md.toRapMaskData ((PJ).statement (R0P) (RestP)).M0
  (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := KC) s1 d (XI170 XI0).l DgJ8 enc L
set_option hygiene false in
local notation "OPN" => OpenAll DgJ8 (merkleSkels (MC))
set_option hygiene false in
local notation "DA" => daOf (XI170 XI0) hn32 (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin DgJ8 md cI sl0 sl1 (PJ).ha (PJ).hz
  (single_az (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd).1
  (single_az (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd).2 m0 mf
set_option hygiene false in
local notation "EMBF" => fun (π : FlatProof) =>
  embedMsgs dgOf (MC) (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 d (XI170 XI0).l L enc))
    (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld
  SoundnessCoupling BadBound MerkleTreeMultiExtractability in
/-- **the J-8 shape**: the exec e2e figure `≤ 2^-82` at ANY interface `J` (the J-8 one is `plusJ (minusT J8 R hfree) …`), with the
decoders `daOf` and the opening facts plugged in. The binders are the remaining hypotheses (labelled in the binder list). -/
theorem exec_e2e_J {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    [Finite (NQuery (merkleSkels (MC)))]
    [SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
    -- [executed] the J-8 shape of the loaded instance (the verifier exe rejects otherwise)
    (hshape : J8Shape.j8ShapeOk (XI170 XI0) = true) (hl : XI0.l = 170)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    -- [construction] layout facts of `cI` against the instance
    (hr : J.r = (XI170 XI0).r) (hnq : (XI170 XI0).nq = (PJ).nq)
    (hkd : ∀ c < (XI170 XI0).nc, (XI170 XI0).colKind[c]! < 3)
    (hblk : ∀ c, (XI170 XI0).blockOf[(cI c).val]! = J.colRound0 c)
    (hblkq : ∀ q : Fin (PJ).nq, (XI170 XI0).blockOf[(XI170 XI0).nc + q.val]! = 3)
    (hpub : ∀ c, pr.pub c = true ↔ (XI170 XI0).colKind[(cI c).val]! = 2)
    (hppt : ∀ c, pr.pub c = true → pr.ppt c = toKV (XI170 XI0).ppt)
    (hoff : ∀ t k, J.off t k = zv (XI170 XI0).hGen ^ (k : ℕ))
    (hns : (PJ).ns = ((XI170 XI0).tabs.toList.map (fun t => t.chip.cons.size)).sum)
    (hHJ : J.H = (Finset.range (XI170 XI0).hN).image (fun i => zv (XI170 XI0).hShift * zv (XI170 XI0).hGen ^ i))
    (hgen : pr.gen = toKV VF.K3.gen)
    -- the DAG tie (output of `hdagU_of_tie`), the public twin
    (hdagU : ∀ (c0 : Block (extFrame J.Φ0 2) KC 0) (c1 : Block (extFrame J.Φ0 2) KC 1) (c2 : Block (extFrame J.Φ0 2) KC 2)
      (c3 : Block (extFrame J.Φ0 2) KC 3) (ζ : VF.K3) (vT : Array (Array VF.K3)),
      CanonIn (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) ζ vT →
      ∀ i : Fin (PJ).ns, (termsAt (XI170 XI0) (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) ζ vT)[i.1]? =
        some ((AJ).Cv (chiOfBlocks c0 c1 c2 c3) (toKV ζ) i (vTOfG (XI170 XI0) cI J.r vT)))
    (hRVU : ∀ (c0 : Block (extFrame J.Φ0 2) KC 0) (c1 : Block (extFrame J.Φ0 2) KC 1) (c2 : Block (extFrame J.Φ0 2) KC 2)
      (c3 : Block (extFrame J.Φ0 2) KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
      VShape (XI170 XI0) vT vQ →
      PubJ8P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf
        (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) (pubAt (XI170 XI0) vT) →
      (RestVP) m0 (finDecG (XI170 XI0) cI J.r (PJ).nq mf (deepMsg vT vQ)) (chiOfBlocks c0 c1 c2 c3))
    -- [kernel, `gb_indep`] independence of `gb` on the used coordinates
    (hb : ∀ c : Fin 3 → ZMod NockvmE2E.Exec.p, (∀ k, (∀ j, G.crd j ≠ k) → c k = 0) →
      ∑ k, algebraMap (ZMod NockvmE2E.Exec.p) KC (c k) * gb k = 0 → ∀ k, c k = 0)
    -- [construction] the mask data and leaves are the verifier's
    (hmd : md = mdX (XI170 XI0) (J8Shape.hn1_of_shape hshape) (PJ).colRoundX
      (rkP (XI170 XI0) (PJ) rfl hnq cI hblk hblkq) toyEncB)
    (hL : L = LX (XI170 XI0) hn32)
    (hd : d.val = XI0.d) (hEnc : EncOK enc)
    -- [numbers] the caps (from `J.cap_*`, the field, the instance numbers)
    (hrate : 64 * (2 ^ (∑ j, ((s1) j).val) * d.val) ≤ 2 ^ (XI170 XI0).nD)
    (hF : goldilocks ^ 3 ≤ Fintype.card KC) (hm12 : m + 1 ≤ 2 ^ 12)
    (htoPoly : (PJ).toPoly = udDecodeB ωS (31 / 64) (friBound s1 d))
    (hnsC : (PJ).ns ≤ 2 ^ 20) (hD : (PJ).D.card ≤ 2 ^ 32) (hH : (PJ).H.card ≤ 2 ^ 32) (hnqC : (PJ).nq + 1 ≤ 2 ^ 8)
    (hDg : goldilocks ^ 4 ≤ Nat.card DgJ8)
    -- [adversary] as in `exec_e2e_final`
    (Aflat : OracleComp (SuccinctSpecK DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC))
      (Option (Statement × Salt × FlatProof × W)))
    (Q_FS Q_H V Pn : ℕ) (hQFS : Q_FS ≤ 2 ^ 64) (hQH : Q_H ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
    (hFS : FsBound (Q := NQuery (merkleSkels (MC))) (∅ : (ofFn (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))).QueryCache)
      Q_FS (verifiedFS (trueGuards _) (embedAdv DgJ8 EMBF Aflat)))
    (hHq : IsQueryBoundP (embedAdv DgJ8 EMBF Aflat)
      (@isHashQuery (NQuery (merkleSkels (MC))) DgJ8 _ (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))) Q_H)
    (hterm : ∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (MC)).length) (op : OPN)
      (logs : Fin (merkleSkels (MC)).length → MerkleTreeExtractor.QueryLog (NQuery (merkleSkels (MC))) DgJ8),
      claimsQueryCount (mkClaims (merkleSkels (MC)) roots h op logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (MC))).nodeBudget tag ≤ Pn) :
    Pr{let g ← $ᵗ (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd);
       let o ← simulateQ (withTable g) Aflat}[
      match o with
      | none => False
      | some (z, salt, π, _) =>
        AccF XI0 hn32 (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin d enc md L encZ decZ
          (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 d (XI170 XI0).l L enc)) g (z, salt) π ∧ ¬ (R0P).Holds] ≤
      (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  have hpt := pt_J (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd cI hpub hppt hoff
  have U := uniLinksN_of_da (XI170 XI0) hn32 (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin d DgJ8 enc md L (NockvmE2E.Merkle.RapFriQ.PubJ8P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf)
    rfl hr hkd cI sl0 sl1
    (single_az (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd).1
    (single_az (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd).2 m0 mf dgOf
    (dsbC, dsmC s1 d (XI170 XI0).l L enc) hpt.1 hpt.2 hns hnq hdagU hRVU
    (hH_J (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd hHJ) rfl
    (hcw_J (XI170 XI0) J pr (ω := ωS) (31 / 64) (friBound s1 d) hNH hpd hgen)
  have O := opsU_of_layout (XI170 XI0) (PJ) rfl (AJ) hr hnq hkd cI hblk hblkq hpt.1 hpt.2 hm
  exact exec_e2e_final XI0 hn32 (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin d enc md L (NockvmE2E.Merkle.RapFriQ.PubJ8P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf) hl encZ decZ hz (DA)
    (vTOfG (XI170 XI0) cI J.r) toyEncB (rkP (XI170 XI0) (PJ) rfl hnq cI hblk hblkq) (J8Shape.hn1_of_shape hshape) hmd hL
    (NockvmE2E.Merkle.RapFriQ.pubSound_J8 _ (J8Shape.hmode_of_shape hshape)) U (colNG (XI170 XI0) cI) O (J8Shape.domLink_of_shape hshape) hd hEnc
    (rapInput_rapJ _ _) (hlink_regroup J pr ωS (31 / 64) (friBound s1 d) hNH hpd G gb hb) (by show 2 + 1 < 4; norm_num)
    (hRest_J J pr ωS (31 / 64) (friBound s1 d) hNH hpd) errJ (fun _ r => roundBound_rapJ_le _ _ _ r)
    hrate hF hm12 htoPoly hnsC hD hH hnqC errJ_le hDg Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig


set_option maxHeartbeats 4000000 in
/-- **output in the form `exec_e2e_J` takes**: `hdagU` from `hdagU_of_tie` + the shape bundle; the binders are those of the tie
obligations (`htie` the tie; `hcur0/hcur1/hpubJ/hslot/hdomt/htabS/htabX` layout facts; `hinj` from `paramsOk`). -/
theorem hdagU_J (hshape : J8Shape.j8ShapeOk (XI170 XI0) = true)
    (hns : nsK = ((XI170 XI0).tabs.toList.map (·.chip.cons.size)).sum)
    (tabX : Fin nsK → Fin (XI170 XI0).tabs.size) (tabJ : Fin (XI170 XI0).tabs.size → Fin J.T)
    (htabS : ∀ j, J.tabS j = tabJ (tabX (G.grp j)))
    (htabX : ∀ i : Fin nsK, (tabX i).1 = (DagSem.flatIdx ((XI170 XI0).tabs.toList.map (·.chip.cons.size)) i.1).1)
    (colJ pubJ : Fin (XI170 XI0).tabs.size → ℕ → J.ι0)
    (hcur0 : ∀ (t : Fin (XI170 XI0).tabs.size) c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub →
      (XI170 XI0).colKind[(XI170 XI0).tabs[t].col0 + c]! = 0 →
      J.pre (colJ t c) = none ∧ ∀ vT k, vTOfG (XI170 XI0) cI J.r vT (colJ t c, k) =
        toKV (vT[(XI170 XI0).tabs[t].col0 + c]!)[k.1]!)
    (hcur1 : ∀ (t : Fin (XI170 XI0).tabs.size) c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub →
      (XI170 XI0).colKind[(XI170 XI0).tabs[t].col0 + c]! = 1 →
      J.pre (colJ t c) = some (((List.range (XI170 XI0).pre[(XI170 XI0).tabs[t].col0 + c]!.size).map fun m =>
        Polynomial.monomial m (zv ((XI170 XI0).pre[(XI170 XI0).tabs[t].col0 + c]!)[m]!)).sum))
    (hpubJ : ∀ (t : Fin (XI170 XI0).tabs.size) s vT, s < (XI170 XI0).tabs[t].npub →
      vTOfG (XI170 XI0) cI J.r vT (pubJ t s, 0) =
        toKV (vT[(XI170 XI0).pubOf[(XI170 XI0).tabs[t].pubBase + s]!]!)[0]!)
    (hJr : J.r = 2) (hoff : ∀ t (k : Fin J.r), J.off t k = zv (XI170 XI0).hGen ^ k.1)
    (chalK : Coins J.Φ0 KC → ℕ → KC)
    (hslot : ∀ c0 c1 c2 c3, ∀ q < 19, toKV (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1))[q]! =
      chalK (restr 2 (chiOfBlocks c0 c1 c2 c3)) q)
    (hdom : J.H = (Finset.range (XI170 XI0).hN).image (fun i => zv (XI170 XI0).hShift * zv (XI170 XI0).hGen ^ i))
    (hdomt : ∀ t : Fin (XI170 XI0).tabs.size, J.Ht (tabJ t) =
      (Finset.range (XI170 XI0).tabs[t].hN).image (fun i => zv (XI170 XI0).hShift * zv (XI170 XI0).hGen ^ i))
    (hinj : Set.InjOn (fun i => zv (XI170 XI0).hShift * zv (XI170 XI0).hGen ^ i) (Finset.range (XI170 XI0).hN : Set ℕ))
    (htie : ∀ (i : Fin nsK) (χ : Coins J.Φ0 KC) (v val : J.ι0 × Fin J.r → KC),
      ∑ j ∈ Finset.univ.filter (fun j => G.grp j = i),
          gb (G.crd j) * MvPolynomial.aeval val (J.C χ (pr.rd (fun c => v (c, 0))) j) =
        (DagSem.evalDagK (XI170 XI0).tabs[tabX i].chip
          ⟨fun c => val (colJ (tabX i) c, 0), fun c => val (colJ (tabX i) c, ⟨1 % J.r, Nat.mod_lt _ (NeZero.pos _)⟩),
           fun s => HdagU.coord0 (v (pubJ (tabX i) s, 0)), chalK χ, (XI170 XI0).tabs[tabX i].chip.baseCols⟩)[
          (DagSem.flatIdx ((XI170 XI0).tabs.toList.map (·.chip.cons.size)) i.1).2]!) :
    ∀ (c0 : Block (extFrame J.Φ0 2) KC 0) (c1 : Block (extFrame J.Φ0 2) KC 1) (c2 : Block (extFrame J.Φ0 2) KC 2)
      (c3 : Block (extFrame J.Φ0 2) KC 3) (ζ : VF.K3) (vT : Array (Array VF.K3)),
      CanonIn (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) ζ vT →
      ∀ i : Fin (PJ).ns, (termsAt (XI170 XI0) (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) ζ vT)[i.1]? =
        some ((AJ).Cv (chiOfBlocks c0 c1 c2 c3) (toKV ζ) i (vTOfG (XI170 XI0) cI J.r vT)) := by
  obtain ⟨hread, hcanon, hpreC, hS, hle, hcolB, hpubB, hnpub, hkind, hr2⟩ := J8Shape.hdagU_shape_of_j8 hshape
  exact HdagU.hdagU_of_tie J pr ωS (31 / 64) (friBound s1 d) hNH hpd (XI170 XI0) G gb (blockEnc sl0) (blockEnc sl1)
    (vTOfG (XI170 XI0) cI J.r) hns tabX tabJ htabS htabX colJ pubJ hread hcanon hpreC hS hle hcolB hpubB hnpub hkind
    hcur0 hcur1 hpubJ hr2 hJr hoff chalK hslot hdom hdomt hinj htie

end NockvmE2E.Exec.E2EJ8

/-! ## Part 2: the J-8 instantiation at `I := Inst.ofRJ8 (XI170 XI0) …` (TieJ8G), `JX := I.JJ npub tp hcap`
(= `plusJ (minusT (J8 d hd) (RJ8 XI d hd) hfree_J8) (Fin npub) tp hcap`, `Inst.ofRJ8_Jm`, `rfl`) -/

namespace NockvmE2E.Exec.E2EJ8.J8X
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
  NockvmE2E.Exec.InstGen
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.J8 NockvmE2E.Exec.E2ELR
open NockvmE2E.Exec.E2EJ8
open NockvmE2E.J8.InstJ8 (Datum DatumOK J8 PbOfX PosX posX_of_shape hNof ω0 StmtP PubP)
open NockvmE2E.J8.TieJ8G (Inst HopsOK NumOK RdSpec Gflat hsz_of_hops gbJ hdagU_J8 hoff_J8 hdom_J8 colJ pubJ chalK)
open NockvmE2E.J8.InstJ8W (sigmaX RJ8 hfree_J8)

/-- the J-8 datum over a loaded instance `XI`: `d.Pb = PbOfX XI …` (uniform orbit `ω = zv XI.hGen`, `n_t = hN_t`), and the union
domain of the datum is the verifier's (`d.hN = XI.hN`, `d.ω = zv XI.hGen`). Always constructible with the three equations `rfl`
(`DatX.ofData`). These are exactly the arguments of `TieJ8G.Inst.ofRJ8` except `hdk`. -/
structure DatX (XI : ExecInst) (hsh : J8Shape.j8ShapeOk XI = true) where
  kroots : ℕ
  krootsV : ℕ
  Rt : ℕ → Nock.Jet.Autogen.Tpl
  regs : List ℕ
  ids : List ℕ
  idx : ℕ → ℕ
  rk : ℕ → ℕ × ℕ
  lay : Fin (hNof XI "jetChipJ8") → Nock.Jet.ChipJ8.PRow
  d : Datum
  hd : d.Pb = PbOfX XI hsh (posX_of_shape hsh) kroots krootsV Rt regs ids idx rk lay
  hdN : d.hN = XI.hN
  hdω : d.ω = ω0 XI

/-- `DatX` from the raw datum fields (the three equations are `rfl`) -/
def DatX.ofData (XI : ExecInst) (hsh : J8Shape.j8ShapeOk XI = true) (kroots krootsV : ℕ) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ) (lay : Fin (hNof XI "jetChipJ8") → Nock.Jet.ChipJ8.PRow)
    (base : Datum) : DatX XI hsh :=
  ⟨kroots, krootsV, Rt, regs, ids, idx, rk, lay,
    { base with Pb := PbOfX XI hsh (posX_of_shape hsh) kroots krootsV Rt regs ids idx rk lay, hN := XI.hN, ω := ω0 XI },
    rfl, rfl, rfl⟩

variable (XI0 : ExecInst) (hn32 : (XI170 XI0).nD ≤ 32) (hsh : J8Shape.j8ShapeOk (XI170 XI0) = true)

set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD hn32
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))

variable [SampleableType KC]
variable (D : DatX (XI170 XI0) hsh) (hdk : DatumOK D.d)
/- the table restriction is kept ABSTRACT (a concrete `RJ8 …` makes `Fin (RJ8 …).ns'` vs `Fin (minusT …).ns` unification run for
minutes, TieJ8G finding); the final instance is `R := RJ8 XI d hd`, `hT := rfl`, `hσ := fun _ => rfl`, `hfree := hfree_J8 …`
(= `Inst.ofRJ8`, see `exec_e2e_J8_RJ8` at the end). -/
variable (R : TabRestr (J8 D.d hdk)) (hT : R.T' = (XI170 XI0).tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigmaX (XI170 XI0) (Fin.cast hT t)) (hfree : (J8 D.d hdk).AccOn R.q)

set_option hygiene false in
local notation "IX" => (⟨XI170 XI0, hsh, posX_of_shape hsh, D.kroots, D.krootsV, D.Rt, D.regs, D.ids, D.idx, D.rk, D.lay, D.d, D.hd,
  hdk, D.hdN, D.hdω, R, hT, hσ, hfree⟩ : Inst)

variable (npub : ℕ) (tp : Fin (IX).Jm.T) (hcap : (IX).Cap npub)

set_option hygiene false in
local notation "JXn" => (IX).JJ npub tp hcap

/-- **`R0J.Holds = HoldsN c`**: `rfl` through `rapJ`, `plusJ`, `minusT` and `J8`. -/
theorem holds_JX (pr : PubRead JXn) (dF : ℕ+) :
    (R0J JXn pr ωS (31 / 64) (friBound s1 dF)).Holds = Nock.Jet.HoldsN D.d.c := rfl

variable (pr : PubRead JXn) (dF : ℕ+) (hNH : friBound s1 dF ≤ (JXn).H.card)
  (hpd : ∀ j c, (JXn).pre j = some c → c.natDegree ≤ (JXn).H.card)
  (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ)) (hnum : ∀ t, NumOK (IX).d (sigmaX (IX).XI t))
  (hops : HopsOK IX ders cmeta)

set_option hygiene false in
local notation "GX" => Gflat IX (hsz_of_hops IX ders cmeta hnum hops)
set_option hygiene false in
local notation "PJ" => (deepParamsJ JXn pr ωS (31 / 64) (friBound s1 dF) hNH hpd).regroup GX gbJ
set_option hygiene false in
local notation "AJ" => (airJ JXn pr ωS (31 / 64) (friBound s1 dF) hNH hpd).regroup GX gbJ
set_option hygiene false in
local notation "R0P" => R0J JXn pr ωS (31 / 64) (friBound s1 dF)
set_option hygiene false in
local notation "RestP" => RestJ JXn pr ωS (31 / 64) (friBound s1 dF) hNH hpd
set_option hygiene false in
local notation "RestVP" => RestVJ JXn pr ωS (31 / 64) (friBound s1 dF) hNH hpd

variable (cI : (JXn).ι0 ≃ Fin (XI170 XI0).nc) {m : ℕ} (hm : m + 1 = (XI170 XI0).nc * (JXn).r + (PJ).nq)

set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cI (JXn).r hm

variable [DecidableEq ((PJ).statement (R0P) (RestP)).M0] [Finite ((PJ).statement (R0P) (RestP)).M0]
  [DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  [Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
  (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
variable [∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (enc : KC ↪ DgJ8)
  (md : PointMaskData (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD)) (ZMod NockvmE2E.Exec.p) DgJ8) (L : Fri.FriLeaves (ω := ωS) s1)
  {n0 n1 : ℕ} (sl0 : {i : Fin (extFrame (JXn).Φ0 2).n // (extFrame (JXn).Φ0 2).sampledAfter i = 0} ≃ Fin n0)
  (sl1 : {i : Fin (extFrame (JXn).Φ0 2).n // (extFrame (JXn).Φ0 2).sampledAfter i = 1} ≃ Fin n1)
  (m0 : ((PJ).statement (R0P) (RestP)).M0) (mf : (R0P).Mfin)

set_option hygiene false in
local notation "MC" => msC (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 4 s1 dF (XI170 XI0).l DgJ8 enc md L (S := KC)
set_option hygiene false in
local notation "RM" => RapP.rapMask (extFrame (JXn).Φ0 2) KC md.toRapMaskData ((PJ).statement (R0P) (RestP)).M0
  (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := KC) s1 dF (XI170 XI0).l DgJ8 enc L
set_option hygiene false in
local notation "OPN" => OpenAll DgJ8 (merkleSkels (MC))
set_option hygiene false in
local notation "DA" => daOf (XI170 XI0) hn32 (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin DgJ8 md cI sl0 sl1 (PJ).ha (PJ).hz
  (single_az (XI170 XI0) JXn pr (ω := ωS) (31 / 64) (friBound s1 dF) hNH hpd).1
  (single_az (XI170 XI0) JXn pr (ω := ωS) (31 / 64) (friBound s1 dF) hNH hpd).2 m0 mf
set_option hygiene false in
local notation "EMBF" => fun (π : FlatProof) =>
  embedMsgs dgOf (MC) (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 dF (XI170 XI0).l L enc))
    (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList

include cI hm in
/-- `hm12` from the interface cap `cap_m` (`m + 1 = nc·r + nq = |ι0|·r + 3(d−1) ≤ 2^12`) -/
theorem hm12_X : m + 1 ≤ 2 ^ 12 := by
  have hc : Fintype.card (JXn).ι0 = (XI170 XI0).nc := by rw [Fintype.card_congr cI, Fintype.card_fin]
  have hcap' := (JXn).cap_m
  rw [hc] at hcap'
  rw [hm]
  exact hcap'

/-! ### Part 3: `hRVU` at `JX` from `hRVU_J8`.
`RestVJ` at `JX` is `PubP d (restr 2 χ) (pr.rd …) ∧ StmtP d` by `rfl`. The residue is the `rd` plumbing (`hrd`), the coin tie (`hχ`,
the J-8 form of `hslot`) and slot canonicity. FINDING (vacuity): `hRVU`'s premise (`VShape ∧ PubJ8P`) does NOT give canonical publics,
while `hRVU_J8` needs `hp : ∀ g ∈ pub, canon g`; so `hrd` is stated with a canonical witness `pub` (for a canonicalising reader `pr.rd`,
`pub := pubAt vT` reduced mod `p`; that needs a lemma `PubJ8P pub → PubJ8P (canon pub)`). -/
theorem hRVU_X_of (hS : StmtP D.d) (hlink : NockvmE2E.J8.RVUJ8.InpLink D.d (XI170 XI0).pubIn)
    (hids : ∀ id ∈ D.d.Pb.regs, id < NockvmE2E.J8.InstJ8.P)
    (hpJ : D.d.Pb.nJ = 0 → (XI170 XI0).pubLay.present[3]! = false)
    (hpV : D.d.Pb.krootsV = 0 → (XI170 XI0).pubLay.present[5]! = false)
    (hslots : ∀ (c0 : Block (extFrame (JXn).Φ0 2) KC 0) (c1 : Block (extFrame (JXn).Φ0 2) KC 1),
      ∀ s ∈ slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1), canon3 s)
    (hχ : ∀ (c0 : Block (extFrame (JXn).Φ0 2) KC 0) (c1 : Block (extFrame (JXn).Φ0 2) KC 1)
      (c2 : Block (extFrame (JXn).Φ0 2) KC 2) (c3 : Block (extFrame (JXn).Φ0 2) KC 3) (i : Fin 19),
      restr 2 (chiOfBlocks c0 c1 c2 c3) i =
        toKV (SP.coinsOf (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) (XI170 XI0).slotOf)[i.val]!)
    (hrd : ∀ (c0 : Block (extFrame (JXn).Φ0 2) KC 0) (c1 : Block (extFrame (JXn).Φ0 2) KC 1)
      (c2 : Block (extFrame (JXn).Φ0 2) KC 2) (c3 : Block (extFrame (JXn).Φ0 2) KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
      VShape (XI170 XI0) vT vQ →
      PubJ8P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf
        (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) (pubAt (XI170 XI0) vT) →
      ∃ pub : Array UInt64, (∀ g ∈ pub, canon g) ∧
        PubJ8P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf
          (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) pub ∧
        pr.rd (fun c => (finDecG (XI170 XI0) cI (JXn).r (PJ).nq mf (deepMsg vT vQ)).2.1 (c, 0)) =
          NockvmE2E.J8.RVUJ8.Mof (XI170 XI0).pubLay pub) :
    ∀ (c0 : Block (extFrame (JXn).Φ0 2) KC 0) (c1 : Block (extFrame (JXn).Φ0 2) KC 1)
      (c2 : Block (extFrame (JXn).Φ0 2) KC 2) (c3 : Block (extFrame (JXn).Φ0 2) KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
      VShape (XI170 XI0) vT vQ →
      PubJ8P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf
        (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) (pubAt (XI170 XI0) vT) →
      (RestVP) m0 (finDecG (XI170 XI0) cI (JXn).r (PJ).nq mf (deepMsg vT vQ)) (chiOfBlocks c0 c1 c2 c3) := by
  intro c0 c1 c2 c3 vT vQ hV hP
  obtain ⟨pub, hcan, hP', hrd'⟩ := hrd c0 c1 c2 c3 vT vQ hV hP
  refine ⟨?_, hS⟩
  show PubP D.d (restr 2 (chiOfBlocks c0 c1 c2 c3))
    (pr.rd (fun c => (finDecG (XI170 XI0) cI (JXn).r (PJ).nq mf (deepMsg vT vQ)).2.1 (c, 0)))
  rw [hrd']
  exact NockvmE2E.J8.RVUJ8.hRVU_J8 D.d hS _ hlink _ _ _ pub (hslots c0 c1) hcan hids hpJ hpV _ (hχ c0 c1 c2 c3) hP'

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld
  SoundnessCoupling BadBound MerkleTreeMultiExtractability in
set_option maxHeartbeats 4000000 in
/-- **`exec_e2e_J8`** (SKELETON): the executable verifier's end-to-end figure at the J-8 interface
`JX = I.JJ npub tp hcap`, `I = Inst.ofRJ8 (XI170 XI0) …` (`R := RJ8`, `d.Pb = PbOfX XI …`):
`Pr[AccF … ∧ ¬ HoldsN d.c] ≤ 2^-82`. `hdagU` is discharged by `hdagU_J8` (its named hypotheses are binders here).
Every binder carries its label; see the ledger at the top of the file. -/
theorem exec_e2e_J8 {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    [Finite (NQuery (merkleSkels (MC)))]
    [SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
    /- [executed] the verifier exe checks `l = 170` on the loaded instance (`exec_e2e_final` is stated at `XI170 XI0`) -/
    (hl : XI0.l = 170)
    /- [statement parameter] the statement/salt codec -/
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    /- [executed] instance number `nq = 9` (the shape only checks `nq % 3 = 0`; add/ne5/mat have `nq = 9`) -/
    (hnq9 : (XI170 XI0).nq = 9)
    /- [executed, pending a shape conjunct] the column kinds are `< 3` -/
    (hkd : ∀ c < (XI170 XI0).nc, (XI170 XI0).colKind[c]! < 3)
    /- [kernel, pending] the cr-tables against the loaded `blockOf` (`decide` per chip id; needs `cI`) -/
    (hblk : ∀ c, (XI170 XI0).blockOf[(cI c).val]! = (JXn).colRound0 c)
    (hblkq : ∀ q : Fin (PJ).nq, (XI170 XI0).blockOf[(XI170 XI0).nc + q.val]! = 3)
    /- [construction, pending] the column bijection `cI` and the reader `pr` (`plusPR`) against the instance -/
    (hpub : ∀ c, pr.pub c = true ↔ (XI170 XI0).colKind[(cI c).val]! = 2)
    (hppt : ∀ c, pr.pub c = true → pr.ppt c = toKV (XI170 XI0).ppt)
    (hgen : pr.gen = toKV VF.K3.gen)
    /- `hdagU` ← `hdagU_J8`; its named hypotheses: -/
    /- [construction] `npub` = the number of flat public columns -/
    (hnpub : npub = (XI170 XI0).pubOf.size)
    /- [kernel, pending `Mof` plumbing] what `pr.rd` hands each chip -/
    (hrdT : RdSpec IX npub tp hcap pr)
    /- [executed: `nCoins = #[13, 6]` is in the shape (`slotOfOk`)] -/
    (hn0 : (XI170 XI0).nCoins[0]! = n0) (hn1 : (XI170 XI0).nCoins[1]! = n1)
    /- [executed + kernel, pending: the loader's `ders`/`cmeta` literal check] -/
    (hSlotOK : ∀ χ : Coins (JXn).Φ0 KC,
      NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta (chalK (JXn).Φ0 sl0 sl1 χ)) (NockvmE2E.J8.TieJ8.χf χ))
    /- [construction, pending] the layout of `cI` -/
    (hcI_col : ∀ (t : Fin (XI170 XI0).tabs.size) c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub →
      ((cI (colJ IX npub tp hcap t c) : Fin (XI170 XI0).nc) : ℕ) = (XI170 XI0).tabs[t].col0 + c)
    (hcI_pub : ∀ (t : Fin (XI170 XI0).tabs.size) s, s < (XI170 XI0).tabs[t].npub →
      ((cI (pubJ IX npub tp hcap t s) : Fin (XI170 XI0).nc) : ℕ) = (XI170 XI0).pubOf[(XI170 XI0).tabs[t].pubBase + s]!)
    /- [kernel, pending (`preKindOk` + chip `preprocessingIndex` ⊆ `preIdxJ8`, ~60 lines)] kind-0 columns are not fixed -/
    (hpre0 : ∀ (t : Fin (XI170 XI0).tabs.size) c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub →
      (XI170 XI0).colKind[(XI170 XI0).tabs[t].col0 + c]! = 0 → (JXn).pre (colJ IX npub tp hcap t c) = none)
    /- [executed + kernel (`maskOk` + Lagrange) for the 3 masks; TCB `hpreJet` for the jet layout] the fixed columns -/
    (hcur1 : ∀ (t : Fin (XI170 XI0).tabs.size) c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub →
      (XI170 XI0).colKind[(XI170 XI0).tabs[t].col0 + c]! = 1 →
      (JXn).pre (colJ IX npub tp hcap t c) = some (((List.range (XI170 XI0).pre[(XI170 XI0).tabs[t].col0 + c]!.size).map fun m =>
        Polynomial.monomial m (zv ((XI170 XI0).pre[(XI170 XI0).tabs[t].col0 + c]!)[m]!)).sum))
    /- [kernel, pending rd plumbing] the public twin (`hRVU_X_of` reduces it to `hRVU_J8` + datum/rd facts) -/
    (hRVU : ∀ (c0 : Block (extFrame (JXn).Φ0 2) KC 0) (c1 : Block (extFrame (JXn).Φ0 2) KC 1)
      (c2 : Block (extFrame (JXn).Φ0 2) KC 2) (c3 : Block (extFrame (JXn).Φ0 2) KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
      VShape (XI170 XI0) vT vQ →
      PubJ8P (XI170 XI0).pubIn (XI170 XI0).pubLay (XI170 XI0).slotOf
        (slotsAt (XI170 XI0) (blockEnc sl0 c0) (blockEnc sl1 c1)) (pubAt (XI170 XI0) vT) →
      (RestVP) m0 (finDecG (XI170 XI0) cI (JXn).r (PJ).nq mf (deepMsg vT vQ)) (chiOfBlocks c0 c1 c2 c3))
    /- [construction] the mask data and leaves are the verifier's (choose `md`, `L` so; `rfl`) -/
    (hmd : md = mdX (XI170 XI0) (J8Shape.hn1_of_shape hsh) (PJ).colRoundX
      (rkP (XI170 XI0) (PJ) rfl (hnq9.trans rfl) cI hblk hblkq) toyEncB)
    (hL : L = LX (XI170 XI0) hn32)
    /- [construction] `dF = XI0.d` (`= 1`, `d_of_shape`); [kernel] `EncOK encK` (`encK_ok`) -/
    (hd : dF.val = XI0.d) (hEnc : EncOK enc)
    /- [kernel, pending: the `_numbers` pattern] the FRI/field caps -/
    (hrate : 64 * (2 ^ (∑ j, ((s1) j).val) * dF.val) ≤ 2 ^ (XI170 XI0).nD)
    (hF : goldilocks ^ 3 ≤ Fintype.card KC)
    (htoPoly : (PJ).toPoly = udDecodeB ωS (31 / 64) (friBound s1 dF))
    /- [executed] the loaded instance has at most `2^20` DAG constraints -/
    (hnsC : (PJ).ns ≤ 2 ^ 20)
    (hD : (PJ).D.card ≤ 2 ^ 32) (hH : (PJ).H.card ≤ 2 ^ 32)
    (hDg : goldilocks ^ 4 ≤ Nat.card DgJ8)
    /- [adversary] as in `exec_e2e_final` -/
    (Aflat : OracleComp (SuccinctSpecK DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC))
      (Option (Statement × Salt × FlatProof × W)))
    (Q_FS Q_H V Pn : ℕ) (hQFS : Q_FS ≤ 2 ^ 64) (hQH : Q_H ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
    (hFS : FsBound (Q := NQuery (merkleSkels (MC))) (∅ : (ofFn (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))).QueryCache)
      Q_FS (verifiedFS (trueGuards _) (embedAdv DgJ8 EMBF Aflat)))
    (hHq : IsQueryBoundP (embedAdv DgJ8 EMBF Aflat)
      (@isHashQuery (NQuery (merkleSkels (MC))) DgJ8 _ (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))) Q_H)
    (hterm : ∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (MC)).length) (op : OPN)
      (logs : Fin (merkleSkels (MC)).length → MerkleTreeExtractor.QueryLog (NQuery (merkleSkels (MC))) DgJ8),
      claimsQueryCount (mkClaims (merkleSkels (MC)) roots h op logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (MC))).nodeBudget tag ≤ Pn) :
    Pr{let g ← $ᵗ (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd);
       let o ← simulateQ (withTable g) Aflat}[
      match o with
      | none => False
      | some (z, salt, π, _) =>
        AccF XI0 hn32 (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin dF enc md L encZ decZ
          (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 dF (XI170 XI0).l L enc)) g (z, salt) π ∧ ¬ Nock.Jet.HoldsN D.d.c] ≤
      (2 ^ 82 : ℝ≥0∞)⁻¹ :=
  exec_e2e_J XI0 hn32 JXn pr dF hNH hpd GX gbJ cI hm I0 I Ifin enc md L sl0 sl1 m0 mf hsh hl encZ decZ hz
    (J8Shape.r_of_shape hsh).symm (hnq9.trans rfl) hkd hblk hblkq hpub hppt
    (fun t k => hoff_J8 IX npub tp hcap t k) rfl (hdom_J8 IX npub tp hcap) hgen
    (hdagU_J8 IX npub tp hcap hnpub pr ωS (31 / 64) (friBound s1 dF) hNH hpd ders cmeta hnum hops hrdT sl0 sl1 hn0 hn1
      hSlotOK cI hcI_col hcI_pub hpre0 hcur1)
    hRVU (fun c _ h => NockvmE2E.J8.gb_indep c h) hmd hL hd hEnc hrate hF
    (hm12_X (ders := ders) (cmeta := cmeta) (hnum := hnum) (hops := hops) (cI := cI) (hm := hm))
    htoPoly hnsC hD hH (by show 3 * (4 - 1) + 1 ≤ 2 ^ 8; norm_num) hDg Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig

/-- **the final instance is `Inst.ofRJ8`**: at `R := RJ8 XI d hd` (`hT := rfl`, `hσ := fun _ => rfl`, `hfree := hfree_J8 …`) the
instance of `exec_e2e_J8` IS `Inst.ofRJ8 (XI170 XI0) …` (`rfl`), so `exec_e2e_J8 … (RJ8 …) rfl (fun _ => rfl) (hfree_J8 …)` is the
theorem at `plusJ (minusT (J8 d hd) (RJ8 XI d hd) hfree_J8) (Fin npub) tp hcap` (`Inst.ofRJ8_Jm`). -/
theorem inst_RJ8 :
    (⟨XI170 XI0, hsh, posX_of_shape hsh, D.kroots, D.krootsV, D.Rt, D.regs, D.ids, D.idx, D.rk, D.lay, D.d, D.hd,
      hdk, D.hdN, D.hdω, RJ8 (XI170 XI0) D.d hdk, rfl, fun _ => rfl,
      hfree_J8 (XI170 XI0) hsh (posX_of_shape hsh) D.kroots D.krootsV D.Rt D.regs D.ids D.idx D.rk D.lay D.d D.hd hdk⟩ : Inst) =
      Inst.ofRJ8 (XI170 XI0) hsh (posX_of_shape hsh) D.kroots D.krootsV D.Rt D.regs D.ids D.idx D.rk D.lay D.d D.hd hdk D.hdN
        D.hdω := rfl

end NockvmE2E.Exec.E2EJ8.J8X

#print axioms NockvmE2E.Exec.E2EJ8.exec_e2e_J
#print axioms NockvmE2E.Exec.E2EJ8.J8X.hRVU_X_of
#print axioms NockvmE2E.Exec.E2EJ8.J8X.holds_JX
#print axioms NockvmE2E.Exec.E2EJ8.J8X.exec_e2e_J8
#print axioms NockvmE2E.Exec.E2EJ8.J8X.inst_RJ8
