/-
  NockvmE2E/Exec/E2ELinksRap.lean   (proof-only)
-/
import NockvmE2E.Exec.E2EEmbed
import NockvmE2E.Exec.SoundCover

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.E2ELR

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Rap NockvmE2E.Merkle NockvmE2E.Merkle.RapFriQ
open NockvmE2E.Exec.E2E

/-! ## 1. `termsAt`: the table terms as a function of (slots, ζ, vT) -/
section Terms
open NockvmE2E.Exec.VF

/-- the verifier's `slotsOf` as a function of the two coin-block limb lists -/
def slotsAt (XI : ExecInst) (l0 l1 : List ℕ) : Array VF.K3 :=
  XI.derived.toList.foldl (fun (slots : Array VF.K3) (be : Nat × Nat) => slots.push (VF.K3.pow slots[be.1]! be.2))
    (k3s l0 XI.nCoins[0]! ++ k3s l1 XI.nCoins[1]!)

/-- the verifier's public values as a function of `vT` -/
def pubAt (XI : ExecInst) (vT : Array (Array VF.K3)) : Array VF.G := XI.pubOf.map fun c => ((vT[c]!)[0]!).c0

/-- `curNxtOf` as a function of `ζ` and `vT` -/
def curNxtAt (XI : ExecInst) (ζ : VF.K3) (vT : Array (Array VF.K3)) : Array VF.K3 × Array VF.K3 :=
  (List.range XI.nc).foldl
    (fun (st : Array VF.K3 × Array VF.K3) c =>
      match XI.colKind[c]! with
      | 0 => (st.1.set! c (vT[c]!)[0]!, st.2.set! c (if XI.r ≥ 2 then (vT[c]!)[1]! else VF.K3.zero))
      | 1 => (st.1.set! c (VF.K3.hornerG XI.pre[c]! ζ), st.2.set! c (VF.K3.hornerG XI.pre[c]! (VF.K3.smul XI.hGen ζ)))
      | _ => st)
    (Array.replicate (XI.nc + XI.nq) VF.K3.zero, Array.replicate (XI.nc + XI.nq) VF.K3.zero)

/-- table `t`'s constraint values as a function of `(slots, ζ, vT)` -/
def tabCvAt (XI : ExecInst) (slots : Array VF.K3) (ζ : VF.K3) (vT : Array (Array VF.K3)) (t : TabInst) : Array VF.K3 :=
  evalDag t.chip { cur := (curNxtAt XI ζ vT).1.extract t.col0 (t.col0 + t.nc),
                   next := (curNxtAt XI ζ vT).2.extract t.col0 (t.col0 + t.nc),
                   pub := (pubAt XI vT).extract t.pubBase (t.pubBase + t.npub), chal := slots, bc := t.chip.baseCols }

/-- **`termsAt`**: the verifier's table terms `mult_t · cv_{t,i}` (in `KC`) as a function of `(slots, ζ, vT)` only (the `α` argument of `termsK` is unused) -/
noncomputable def termsAt (XI : ExecInst) (slots : Array VF.K3) (ζ : VF.K3) (vT : Array (Array VF.K3)) : List KC :=
  termsK VF.K3.zero (tabCvAt XI slots ζ vT) (multOf XI ζ) XI.tabs.toList

theorem slotsOf_eq (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) :
    slotsOf XI FS z π = slotsAt XI (chalsOf XI FS z π)[1]! (chalsOf XI FS z π)[2]! := rfl
theorem pubOfProof_eq (XI : ExecInst) (π : FlatProof) : pubOfProof XI π = pubAt XI π.vT := rfl
theorem curNxtOf_eq (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) :
    curNxtOf XI FS z π = curNxtAt XI (zetaOf XI FS z π) π.vT := rfl
theorem tabCv_eq (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) (t : TabInst) :
    tabCv XI FS z π t = tabCvAt XI (slotsOf XI FS z π) (zetaOf XI FS z π) π.vT t := rfl
/-- **the refactor**: `termsOfK` IS `termsAt` at the proof's own slots / ζ / vT (`rfl`; `Sound*.lean` untouched) -/
theorem termsOfK_eq (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) :
    termsOfK XI FS z π = termsAt XI (slotsOf XI FS z π) (zetaOf XI FS z π) π.vT := rfl

/-- canonical inputs of `termsAt` (what `A.Cv` needs to be a faithful reading of the `K3` arithmetic) -/
def CanonIn (slots : Array VF.K3) (ζ : VF.K3) (vT : Array (Array VF.K3)) : Prop :=
  (∀ s ∈ slots, canon3 s) ∧ canon3 ζ ∧ (∀ a ∈ vT, ∀ x ∈ a, canon3 x)

end Terms

/-! ## 2. generic split lemmas for the flat encoding of a compiled path -/
section Gen
open NockvmE2E.Merkle.Fri

variable {Dg : Type} [Finite Dg] [DecidableEq Dg] (dY : List ℕ → Dg) {Op : Type} [Finite Op] [DecidableEq Op]

/-- the decoders of the second mask of an append -/
def sndD : (a b : MRounds Dg) → MDec (a ++ b) → MDec b
  | [], _, ds => ds
  | ⟨_, .clear⟩ :: a, b, (_, ds) => sndD a b ds
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (_, ds) => sndD a b ds

/-- the flat encoding of round `a.length + i` of a compiled path of `a ++ b` is round `i` of its suffix -/
theorem getD_snd : (a b : MRounds Dg) → (ds : MDec (a ++ b)) → (ω : Op) →
    (p : (protocol (compiledRoundsK Dg Op (a ++ b))).tree.ExecutionPath) → (i : ℕ) →
    (encPathD _ (mDecs dY (a ++ b) ds ω) p).getD (a.length + i) [] =
      (encPathD _ (mDecs dY b (sndD a b ds) ω) (MA.sndK Dg Op a b p)).getD i []
  | [], _, _, _, _, _ => by simp [MA.sndK, sndD]
  | ⟨_, .clear⟩ :: a, b, (d, ds), ω, p, i => by
      have := getD_snd a b ds ω p.2.2 i
      simp only [List.length_cons, show a.length + 1 + i = (a.length + i) + 1 by omega]
      exact this
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (d, ds), ω, p, i => by
      have := getD_snd a b ds ω p.2.2 i
      simp only [List.length_cons, show a.length + 1 + i = (a.length + i) + 1 by omega]
      exact this

end Gen

section Closed

open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst

variable (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof) (hv : verifyFlat XI H FS zF π = true)

set_option hygiene false in
local notation "ωS" => smoothDomain XI.nD (nD_le_of_verify XI H FS zF π hv)
set_option hygiene false in
local notation "s1" => (fun _ : Fin (XI.k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ XI.nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ XI.nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec XI.k (ω := ωS) s1 XI.l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) KC)
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : KC ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ XI.nD)) B Dg) (L : Fri.FriLeaves (ω := ωS) s1)
variable (hdom : 2 ^ (∑ j, ((s1) j).val) * d.val ≤ 2 ^ XI.nD)
variable (Op : Type) [Finite Op] [DecidableEq Op]
variable (PR : Array VF.K3 → Array VF.G → Prop)

set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L (S := S)
set_option hygiene false in
local notation "PS" => P.statement R0 Rest
set_option hygiene false in
local notation "PL" => friPlan (ω := ωS) P A R0 Rest RestV e
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := S) s1 d XI.l Dg enc L


variable (decode : Op → OpenAll Dg (merkleSkels (MC)))
  {Op' : Type}

set_option quotPrecheck false in
set_option hygiene false in
local notation "PATH" => (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath
set_option hygiene false in
local notation "CHI" p => chiQ P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L
  (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op decode p)
set_option hygiene false in
local notation "FINM" p => finMQ P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L
  (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op decode p)

set_option hygiene false in
local notation "FM" => Fri.friMerkleMask s1 d XI.l L Dg enc

section Fri
variable (dY : List ℕ → Dg)

/-- the flat encoding of the challenge of the LAST (clear) round of a compiled FRI mask path -/
noncomputable def lastEnc : (i c : ℕ) → (h : i + c = XI.k) → (ds : MDec (FM i c h)) →
    (q : (protocol (compiledRoundsK Dg Op (FM i c h))).tree.ExecutionPath) → List ℕ
  | _, 0, _, ds, q => ds.1.encC q.2.1
  | i, c + 1, h, ds, q => lastEnc i.succ c (by omega) ds.2 q.2.2

theorem getD_last : (c i : ℕ) → (h : i + c = XI.k) → (ds : MDec (FM i c h)) → (ω : Op) →
    (q : (protocol (compiledRoundsK Dg Op (FM i c h))).tree.ExecutionPath) →
    (encPathD _ (mDecs dY (FM i c h) ds ω) q).getD c [] = lastEnc XI H FS zF π hv d Dg enc L Op i c h ds q
  | 0, _, _, _, _, _ => rfl
  | c + 1, i, h, ds, ω, q => by
      have := getD_last c i.succ (by omega) ds.2 ω q.2.2
      exact this

/-- the query-codec link at the last round (`i = k`, `c = 0`): an instance fact (π-, g-free) about the challenge codec of `midRound k`. -/
def XsCodec : Prop :=
  ∀ (h : XI.k + 0 = XI.k) (ds : MDec (FM XI.k 0 h)) (q : (protocol (compiledRoundsK Dg Op (FM XI.k 0 h))).tree.ExecutionPath)
    (j : Fin XI.l), (Fri.XsOf s1 d XI.l L Dg enc Op XI.k 0 h q j).val =
      homV.ψ XI.dShift * homV.ψ XI.dGen ^ ((lastEnc XI H FS zF π hv d Dg enc L Op XI.k 0 h ds q)[j.1]! % 2 ^ XI.nD)

theorem xs_iter (hX : XsCodec XI H FS zF π hv d Dg enc L Op) : (c i : ℕ) → (h : i + c = XI.k) → (ds : MDec (FM i c h)) →
    (q : (protocol (compiledRoundsK Dg Op (FM i c h))).tree.ExecutionPath) → (j : Fin XI.l) →
    (Fri.XsOf s1 d XI.l L Dg enc Op i c h q j).val =
      homV.ψ XI.dShift * homV.ψ XI.dGen ^ ((lastEnc XI H FS zF π hv d Dg enc L Op i c h ds q)[j.1]! % 2 ^ XI.nD)
  | 0, i, h, ds, q, j => by
      have hi : i = XI.k := by omega
      subst hi
      exact hX h ds q j
  | c + 1, i, h, ds, q, j => xs_iter hX c i.succ (by omega) ds.2 q.2.2 j

end Fri

section Proj
variable (pp : PATH)

/-- **the coin vector of `q0`** is the four block challenges of `pp` (rounds 1..4) written into the default coins -/
theorem chi_eq : (CHI pp) =
    setBlock 3 (pp.2.2.2.2.2.2.2.2.2.1 : Block Φ KC 3) (setBlock 2 (pp.2.2.2.2.2.2.2.1 : Block Φ KC 2)
     (setBlock 1 (pp.2.2.2.2.2.1 : Block Φ KC 1) (setBlock 0 (pp.2.2.2.1 : Block Φ KC 0) (fun _ => default)))) := rfl

/-- **the final (clear) message of `q0`** is round 5's message of `pp` -/
theorem finM_eq : (FINM pp) = pp.2.2.2.2.2.2.2.2.2.2.1 := rfl

theorem chi_at2 (i : Fin Φ.n) (h : Φ.sampledAfter i = 2) :
    (CHI pp) i = (pp.2.2.2.2.2.2.2.1 : Block Φ KC 2) ⟨i, h⟩ := by
  rw [chi_eq (hv := hv) (decode := decode)]; simp [setBlock, h]

theorem chi_at3 (i : Fin Φ.n) (h : Φ.sampledAfter i = 3) :
    (CHI pp) i = (pp.2.2.2.2.2.2.2.2.2.1 : Block Φ KC 3) ⟨i, h⟩ := by
  rw [chi_eq (hv := hv) (decode := decode)]; simp [setBlock, h]

variable {Yd : Type} 
/-- the flat encoding of round `3` / `4` challenges, read off the decoder tuple -/
example (dY : List ℕ → Dg) (ds : MDec (MC)) (ω0 : Op) :
    (encPathD _ (mDecs dY (MC) ds ω0) pp).getD 3 [] = ds.2.2.2.1.encC (pp.2.2.2.2.2.2.2.1 : Block Φ KC 2) := by
  rfl

/-- the flat encoding of round `8 + k` of `p` is the encoding of the query challenge: `getD_snd` (RAP prefix, 6 rounds), two clear
rounds (batch, FRI head), then `getD_last` -/
theorem enc_query (dY : List ℕ → Dg) (ds : MDec (MC)) (ω0 : Op) :
    (encPathD _ (mDecs dY (MC) ds ω0) pp).getD (8 + XI.k) [] =
      lastEnc XI H FS zF π hv d Dg enc L Op 0 XI.k (by omega) (sndD (RM) (BM) ds).2.2
        (MA.sndK Dg Op (RM) (BM) pp).2.2.2.2 := by
  have h6 : (RM).length = 6 := rfl
  have := getD_snd dY (RM) (BM) ds ω0 pp (XI.k + 2)
  rw [h6, show 6 + (XI.k + 2) = 8 + XI.k by omega] at this
  rw [this]
  have h2 := getD_last XI H FS zF π hv d Dg enc L Op dY XI.k 0 (by omega) (sndD (RM) (BM) ds).2.2 ω0
    (MA.sndK Dg Op (RM) (BM) pp).2.2.2.2
  rw [← h2]
  show (_ :: _ :: (encPathD _ _ _)).getD (XI.k + 2) [] = _
  rw [List.getD_cons_succ, List.getD_cons_succ]
  rfl

theorem pos_get (hok : FlatOk XI H FS zF π) (j : Fin XI.l) :
    π.pos[j.1]! = ((chalsOf XI FS zF π)[8 + XI.k]!)[j.1]! % 2 ^ XI.nD := by
  have hsz := (NockvmE2E.Exec.Cover.flat_shape XI H FS zF π hok).2
  have hp := flatOk_pos XI H FS zF π hok
  have hj : j.1 < π.pos.size := by rw [hsz]; exact j.2
  rw [getElem!_pos π.pos j.1 hj]
  have hj' : j.1 < ((chalsOf XI FS zF π)[8 + XI.k]!).length := by
    have := hj; rw [hp] at this; simpa using this
  simp only [hp, Array.getElem_map, List.getElem_toArray]
  rw [getElem!_pos _ j.1 hj']

/-- **`hxs`**: the audited query vector `xsC p` is the verifier's coset points at its positions -/
theorem hxs_of (hX : XsCodec XI H FS zF π hv d Dg enc L Op) (dY : List ℕ → Dg) (ds : MDec (MC)) (ω0 : Op)
    (hok : FlatOk XI H FS zF π)
    (hch : (chalsOf XI FS zF π)[8 + XI.k]! = (encPathD _ (mDecs dY (MC) ds ω0) pp).getD (8 + XI.k) []) (j : Fin XI.l) :
    (xsC P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op pp j).val =
      homV.ψ XI.dShift * homV.ψ XI.dGen ^ π.pos[j.1]! := by
  rw [pos_get XI H FS zF π hok j, hch, enc_query (hv := hv) (pp := pp) ..]
  exact xs_iter XI H FS zF π hv d Dg enc L Op hX XI.k 0 (by omega) _ _ j

end Proj

/-! ## 3. `UniLinks`: the instance-only facts (π-free, g-free, every proof/flat datum ∀-quantified) -/

/-- shape facts of `(vT, vQ)` read off `FlatOk` -/
def VShape (vT : Array (Array VF.K3)) (vQ : Array VF.K3) : Prop :=
  vT.size = XI.nc ∧ vQ.size = XI.nq ∧ ∀ c ∈ List.range XI.nc, (vT[c]!).size = V.vTLen XI c

/-- the coin vector of the four block challenges (what `q0P`'s RAP prefix writes) -/
def chiOfBlocks (c0 : Block Φ KC 0) (c1 : Block Φ KC 1) (c2 : Block Φ KC 2) (c3 : Block Φ KC 3) : Coins Φ KC :=
  setBlock 3 c3 (setBlock 2 c2 (setBlock 1 c1 (setBlock 0 c0 (fun _ => default))))

/-- **`UniLinks`**: every field is about the INSTANCE only (the codecs `ds`, the decoder `vTOf`, `P`, `A`, `XI`); the proof `π`
and the table `g` never occur: flat data (`vT`, `vQ`, `ζ`, `slots`, the encoded challenges) is universally quantified, the audited
challenges are universally quantified `c0..c3`. `ds` lists the decoders of the RAP prefix in order: `ds.1` (M0, clear), `ds.2.1 … ds.2.2.2.2.1`
(the four block-challenge codecs), `ds.2.2.2.2.2.1` (Mfin, clear). -/
structure UniLinks (dY : List ℕ → Dg) (ds : MDec (MC)) (vTOf : Array (Array VF.K3) → ι × Fin r → KC) : Prop where
  hPa : Φ.sampledAfter P.a = 2
  hPz : Φ.sampledAfter P.z = 3
  /-- α = the K3 of the limbs of block 2's challenge -/
  hαC : ∀ c : Block Φ KC 2, toKV (VF.K3.ofLimbs (ds.2.2.2.1.encC c)) = c ⟨P.a, hPa⟩
  /-- ζ = the K3 of the limbs of block 3's challenge -/
  hζC : ∀ c : Block Φ KC 3, toKV (VF.K3.ofLimbs (ds.2.2.2.2.1.encC c)) = c ⟨P.z, hPz⟩
  /-- the query codec -/
  hxsU : XsCodec XI H FS zF π hv d Dg enc L Op
  /-- the `Mfin` decoder reads `vQ` and `vT` -/
  hQU : ∀ vT vQ, VShape XI vT vQ → ∀ j : Fin P.nq, (ds.2.2.2.2.2.1.decM (deepMsg vT vQ)).2.2 j = toKV vQ[j.1]!
  hVT : ∀ vT vQ, VShape XI vT vQ → (ds.2.2.2.2.2.1.decM (deepMsg vT vQ)).2.1 = vTOf vT
  hlenU : ∀ slots ζ vT, (termsAt XI slots ζ vT).length = P.ns
  hdagU : ∀ (c0 : Block Φ KC 0) (c1 : Block Φ KC 1) (c2 : Block Φ KC 2) (c3 : Block Φ KC 3) (ζ : VF.K3) (vT : Array (Array VF.K3)),
    CanonIn (slotsAt XI (ds.2.1.encC c0) (ds.2.2.1.encC c1)) ζ vT →
    ∀ i : Fin P.ns, (termsAt XI (slotsAt XI (ds.2.1.encC c0) (ds.2.2.1.encC c1)) ζ vT)[i.1]? =
      some (A.Cv (chiOfBlocks c0 c1 c2 c3) (toKV ζ) i (vTOf vT))
  hptsU : ∀ (ζ : VF.K3) (ck : ι × Fin r), ∃ pt ∈ (openPts XI ζ).toList, toKV pt = A.pt ck.1 ck.2 (toKV ζ)
  hRVU : ∀ (c0 : Block Φ KC 0) (c1 : Block Φ KC 1) (c2 : Block Φ KC 2) (c3 : Block Φ KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
    VShape XI vT vQ →
    PR (slotsAt XI (ds.2.1.encC c0) (ds.2.2.1.encC c1)) (pubAt XI vT) →
    RestV (ds.1.decM []) (ds.2.2.2.2.2.1.decM (deepMsg vT vQ)) (chiOfBlocks c0 c1 c2 c3)
  hH : P.H = (Finset.range XI.hN).image (fun i => psiV XI.hShift * psiV XI.hGen ^ i)
  he : P.e = 3
  hnq : XI.nq = P.nq
  hcw : ∀ j : Fin P.nq, toKV VF.K3.gen ^ (j.1 % 3) = P.cw j


/-- the named hypothesis "`chalsOf = fs_chal_dec`" (B6-1b): the verifier's re-derived challenges are the encodings of `p`'s challenges -/
def ChalsDec (dY : List ℕ → Dg) (ds : MDec (MC)) (ω0 : Op) (pp : PATH) : Prop :=
  ∀ i, i < 9 + XI.k → roundNl XI i ≠ 0 →
    (chalsOf XI FS zF π)[i]! = (encPathD _ (mDecs dY (MC) ds ω0) pp).getD i []

theorem vshape_of_flat (hok : FlatOk XI H FS zF π) : VShape XI π.vT π.vQ := by
  obtain ⟨_, _, _, _, _, h6, h7, _⟩ := hok
  simp only [Bool.and_eq_true, beq_iff_eq] at h6
  exact ⟨h6.1.1.1, h6.1.1.2, fun c hc => by simpa using h7 c hc⟩

theorem k3s_congr (l l' : List ℕ) (n : ℕ) (h : n = 0 ∨ l = l') : k3s l n = k3s l' n := by
  rcases h with rfl | rfl <;> simp [k3s]

/-- the verifier's coin slots are `slotsAt` of the encodings of `p`'s block-0/1 challenges -/
theorem slots_link (dY : List ℕ → Dg) (ds : MDec (MC)) (ω0 : Op) (pp : PATH)
    (hch : ChalsDec XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op dY ds ω0 pp) :
    slotsOf XI FS zF π = slotsAt XI (ds.2.1.encC (pp.2.2.2.1 : Block Φ KC 0)) (ds.2.2.1.encC (pp.2.2.2.2.2.1 : Block Φ KC 1)) := by
  have e1 : (encPathD _ (mDecs dY (MC) ds ω0) pp).getD 1 [] = ds.2.1.encC (pp.2.2.2.1 : Block Φ KC 0) := rfl
  have e2 : (encPathD _ (mDecs dY (MC) ds ω0) pp).getD 2 [] = ds.2.2.1.encC (pp.2.2.2.2.2.1 : Block Φ KC 1) := rfl
  have c1 : (chalsOf XI FS zF π)[1]! = ds.2.1.encC (pp.2.2.2.1 : Block Φ KC 0) ∨ XI.nCoins[0]! = 0 := by
    by_cases h0 : XI.nCoins[0]! = 0
    · exact Or.inr h0
    · exact Or.inl (by rw [← e1]; exact hch 1 (by omega) (by simp [roundNl, h0]))
  have c2 : (chalsOf XI FS zF π)[2]! = ds.2.2.1.encC (pp.2.2.2.2.2.1 : Block Φ KC 1) ∨ XI.nCoins[1]! = 0 := by
    by_cases h0 : XI.nCoins[1]! = 0
    · exact Or.inr h0
    · exact Or.inl (by rw [← e2]; exact hch 2 (by omega) (by simp [roundNl, h0]))
  rw [slotsOf_eq]; unfold slotsAt
  rw [k3s_congr _ (ds.2.1.encC (pp.2.2.2.1 : Block Φ KC 0)) _ c1.symm, k3s_congr _ (ds.2.2.1.encC (pp.2.2.2.2.2.1 : Block Φ KC 1)) _ c2.symm]

section Deep
variable (pp : PATH) (dY : List ℕ → Dg) (ds : MDec (MC)) (ω0 : Op) (vTOf : Array (Array VF.K3) → ι × Fin r → KC)

/-- **`hα`, `hζ`, `hlen`, `hdag`, `hH`, `he`, `hnq`, `hcw`, `hQ` of `DeepLinkC`**, from `UniLinks`, `chalsOf = fs_chal_dec` and the `Mfin` message -/
theorem deepLinkC_of (U : UniLinks XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR dY ds vTOf) (hok : FlatOk XI H FS zF π)
    (hch : ChalsDec XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op dY ds ω0 pp)
    (hm5 : pp.2.2.2.2.2.2.2.2.2.2.1 = ds.2.2.2.2.2.1.decM (deepMsg π.vT π.vQ)) :
    DeepLinkC XI H FS zF π P A (CHI pp) ((CHI pp) P.a) ((CHI pp) P.z) (FINM pp).2.1 (FINM pp).2.2 := by
  have hc := allCanon_of_flatOk XI H FS zF π hok
  have hsh := vshape_of_flat XI H FS zF π hok
  have e3 : (encPathD _ (mDecs dY (MC) ds ω0) pp).getD 3 [] = ds.2.2.2.1.encC (pp.2.2.2.2.2.2.2.1 : Block Φ KC 2) := rfl
  have e4 : (encPathD _ (mDecs dY (MC) ds ω0) pp).getD 4 [] = ds.2.2.2.2.1.encC (pp.2.2.2.2.2.2.2.2.2.1 : Block Φ KC 3) := rfl
  have hslots := slots_link XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op dY ds ω0 pp hch
  have halpha : toKV (alphaOf XI FS zF π) = (CHI pp) P.a := by
    refine Eq.trans ?_ (chi_at2 (hv := hv) (decode := decode) (pp := pp) (i := P.a) (h := U.hPa)).symm
    refine Eq.trans ?_ (U.hαC (pp.2.2.2.2.2.2.2.1 : Block Φ KC 2))
    unfold alphaOf
    rw [hch 3 (by omega) (by simp [roundNl]), e3]
  have hzeta : toKV (zetaOf XI FS zF π) = (CHI pp) P.z := by
    refine Eq.trans ?_ (chi_at3 (hv := hv) (decode := decode) (pp := pp) (i := P.z) (h := U.hPz)).symm
    refine Eq.trans ?_ (U.hζC (pp.2.2.2.2.2.2.2.2.2.1 : Block Φ KC 3))
    unfold zetaOf
    rw [hch 4 (by omega) (by simp [roundNl]), e4]
  have hlen : (termsOfK XI FS zF π).length = P.ns := by rw [termsOfK_eq]; exact U.hlenU _ _ _
  have hVTq : (FINM pp).2.1 = vTOf π.vT := by rw [finM_eq (hv := hv) (decode := decode), hm5]; exact U.hVT _ _ hsh
  refine ⟨halpha, hzeta, hlen, ?_, U.hH, U.he, U.hnq, U.hcw, ?_⟩
  · intro i
    have hcan : CanonIn (slotsOf XI FS zF π) (zetaOf XI FS zF π) π.vT :=
      ⟨slotsOf_canon XI H FS zF π hok, canon3_zetaOf XI FS zF π hc.chal, (flatOk_limbs XI H FS zF π hok).1⟩
    rw [hslots] at hcan
    have h := U.hdagU (pp.2.2.2.1 : Block Φ KC 0) (pp.2.2.2.2.2.1 : Block Φ KC 1) (pp.2.2.2.2.2.2.2.1 : Block Φ KC 2)
      (pp.2.2.2.2.2.2.2.2.2.1 : Block Φ KC 3) (zetaOf XI FS zF π) π.vT hcan (Fin.cast hlen i)
    rw [← hslots, ← termsOfK_eq] at h
    rw [List.getElem?_eq_getElem (by simp)] at h
    have h' := Option.some.inj h
    rw [List.get_eq_getElem]
    simp only [Fin.val_cast] at h'
    rw [h', hVTq, ← hzeta, chi_eq (hv := hv) (decode := decode)]
    rfl
  · intro j
    rw [finM_eq (hv := hv) (decode := decode), hm5]
    exact (U.hQU _ _ hsh j).symm

/-- `hpts` of `ClosedLinksL` -/
theorem hpts_of (U : UniLinks XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR dY ds vTOf)
    (D : DeepLinkC XI H FS zF π P A (CHI pp) ((CHI pp) P.a) ((CHI pp) P.z) (FINM pp).2.1 (FINM pp).2.2) :
    ∀ ck : ι × Fin r, ∃ pt ∈ (openPts XI (zetaOf XI FS zF π)).toList, toKV pt = A.pt ck.1 ck.2 ((CHI pp) P.z) := by
  intro ck
  obtain ⟨pt, hm, h⟩ := U.hptsU (zetaOf XI FS zF π) ck
  exact ⟨pt, hm, by rw [h, D.hζ]⟩

/-- `hRV` of `ClosedLinksL` -/
theorem hRV_of (U : UniLinks XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR dY ds vTOf) (hok : FlatOk XI H FS zF π)
    (hch : ChalsDec XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op dY ds ω0 pp)
    (hm0 : pp.1 = ds.1.decM [])
    (hm5 : pp.2.2.2.2.2.2.2.2.2.2.1 = ds.2.2.2.2.2.1.decM (deepMsg π.vT π.vQ)) :
    PR (slotsOf XI FS zF π) (pubOfProof XI π) →
      RestV (MA.fstB Dg (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op decode pp)).1
        (FINM pp) (CHI pp) := by
  intro hP
  have hsh := vshape_of_flat XI H FS zF π hok
  rw [slots_link XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op dY ds ω0 pp hch, pubOfProof_eq] at hP
  have h := U.hRVU (pp.2.2.2.1 : Block Φ KC 0) (pp.2.2.2.2.2.1 : Block Φ KC 1) (pp.2.2.2.2.2.2.2.1 : Block Φ KC 2)
    (pp.2.2.2.2.2.2.2.2.2.1 : Block Φ KC 3) π.vT π.vQ hsh hP
  rw [← hm5] at h
  rw [← hm0] at h
  exact h

theorem roundNl_query (hok : FlatOk XI H FS zF π) : roundNl XI (8 + XI.k) ≠ 0 := by
  obtain ⟨_, _, h3, _⟩ := hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le] at h3
  have hl : 1 ≤ XI.l := h3.2
  have : roundNl XI (8 + XI.k) = XI.l := by
    unfold roundNl
    have h1 : (8 + XI.k == 1) = false := by simp; omega
    have h2 : (8 + XI.k == 2) = false := by simp; omega
    have h3 : (8 + XI.k == 3) = false := by simp; omega
    have h4 : (8 + XI.k == 4) = false := by simp; omega
    have h6 : (8 + XI.k == 6) = false := by simp; omega
    have h5 : (8 + XI.k == 5) = false := by simp; omega
    simp [h1, h2, h3, h4, h5, h6]
  omega

/-- the four RAP/DEEP fields of `ClosedLinksL` (`hxs hD hpts hRV`), stated exactly as there -/
structure RapLinks : Prop where
  hxs : ∀ j, (xsC P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op pp j).val =
      homV.ψ XI.dShift * homV.ψ XI.dGen ^ π.pos[j.1]!
  hD : DeepLinkC XI H FS zF π P A (CHI pp) ((CHI pp) P.a) ((CHI pp) P.z) (FINM pp).2.1 (FINM pp).2.2
  hpts : ∀ ck : ι × Fin r, ∃ pt ∈ (openPts XI (zetaOf XI FS zF π)).toList, toKV pt = A.pt ck.1 ck.2 ((CHI pp) P.z)
  hRV : PR (slotsOf XI FS zF π) (pubOfProof XI π) →
      RestV (MA.fstB Dg (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin 4 s1 d XI.l Dg enc md L Op decode pp)).1 (FINM pp) (CHI pp)

/-- ** main**: `hxs hα hζ hQ hlen hdag hpts hRV` (and `hH he hnq hcw`) of `ClosedLinksL` from `UniLinks` (instance facts), the named
hypotheses `chalsOf = fs_chal_dec` (`ChalsDec`) and the two clear messages of `p` (`hm0`, `hm5`: both hold for `p = pathOf z _ g (embedMsgs …)`) -/
theorem rapLinks_of_uni (U : UniLinks XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR dY ds vTOf) (hok : FlatOk XI H FS zF π)
    (hch : ChalsDec XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op dY ds ω0 pp)
    (hm0 : pp.1 = ds.1.decM [])
    (hm5 : pp.2.2.2.2.2.2.2.2.2.2.1 = ds.2.2.2.2.2.1.decM (deepMsg π.vT π.vQ)) :
    RapLinks XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR decode pp := by
  have D := deepLinkC_of XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR decode pp dY ds ω0 vTOf U hok hch hm5
  exact ⟨fun j => hxs_of XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op pp U.hxsU dY ds ω0 hok
      (hch _ (by omega) (roundNl_query XI H FS zF π hok)) j,
    D, hpts_of XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR decode pp dY ds vTOf U D,
    hRV_of XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR decode pp dY ds ω0 vTOf U hok hch hm0 hm5⟩

/-- **assembly**: the RAP/DEEP half of `ClosedLinksL` is replaced by `RapLinks` (the types agree on the nose; `hsel`, `hF` stay with B6-1b / ) -/
theorem closedLinksL_of_rap {Input Salt : Type} (z : Input × Salt)
    (L0 : NockvmE2E.Exec.Cover.ClosedLinksL XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin 4 d G Dg enc md L Op decode z pp
      PR)
    (R : RapLinks XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin d Dg enc md L Op PR decode pp) :
    NockvmE2E.Exec.Cover.ClosedLinksL XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin 4 d G Dg enc md L Op decode z pp
      PR :=
  { L0 with hxs := R.hxs, hD := R.hD, hpts := R.hpts, hRV := R.hRV }

/-- **the clear messages of the embedded path**: for `p = pathOf z _ g (embedMsgs … (msgsOf π))`, round 0 carries `decM []` and round 5 the decoded
`deepMsg` (`hm0`, `hm5` above) -/
theorem embed_msgs {Input : Type} (z : Input) (g : (k : Key Input PUnit (compiledRoundsK Dg Op (MC))) → k.Challenge)
    :
    (Emb.pathOf z (compiledRoundsK Dg Op (MC)) g (embedMsgs dY (MC) ds ω0 (msgsOf XI π).toList)).1 = ds.1.decM [] ∧
    (Emb.pathOf z (compiledRoundsK Dg Op (MC)) g (embedMsgs dY (MC) ds ω0 (msgsOf XI π).toList)).2.2.2.2.2.2.2.2.2.2.1 =
      ds.2.2.2.2.2.1.decM (deepMsg π.vT π.vQ) := by
  constructor
  · show ds.1.decM (((msgsOf XI π).toList).headD []) = _
    simp [msgsOf]
  · show ds.2.2.2.2.2.1.decM ((((msgsOf XI π).toList).tail.tail.tail.tail.tail).headD []) = _
    simp [msgsOf]

end Deep

/-! ## 4. non-vacuity (kernel) at `toyInstB` (`nD = 5`, columns of kinds 0/1/2, `nq = 3`, `r = 2`, no tables) and generic reuse -/
section NonVac
open NockvmE2E.Exec.V

/-- `termsAt` has the literal-instance values: no tables, no terms, so `hlenU`'s left side is `0` -/
example (slots : Array VF.K3) (ζ : VF.K3) (vT : Array (Array VF.K3)) : termsAt toyInstB slots ζ vT = [] := by
  simp [termsAt, termsK, toyInstB]
/-- the coin slots of the literal instance are empty (`nCoins = #[0, 0]`), for ANY block limbs: the zero-coin case of `slots_link` -/
example (l0 l1 : List ℕ) : slotsAt toyInstB l0 l1 = #[] := by
  simp [slotsAt, k3s, toyInstB]
/-- the premises of `hdagU` / `hRVU` are inhabited: canonical inputs and a `VShape`-conforming `(vT, vQ)` exist at the literal instance -/
example : CanonIn #[] VF.K3.zero #[] := ⟨fun _ h => by simp at h, canon3_zero, fun _ h => by simp at h⟩
example : VShape toyInstB (#[Array.replicate 2 VF.K3.zero, Array.replicate 2 VF.K3.zero, Array.replicate 1 VF.K3.zero])
    (Array.replicate 3 VF.K3.zero) := by
  refine ⟨by decide, by decide, ?_⟩
  decide +kernel
/-- the `Mfin` message codec's input is a nonempty class: `deepMsg` of a conforming `(vT, vQ)` has `3 * (2 + 2 + 1 + 3)` limbs -/
example : (deepMsg (#[Array.replicate 2 VF.K3.zero, Array.replicate 2 VF.K3.zero, Array.replicate 1 VF.K3.zero])
    (Array.replicate 3 VF.K3.zero)).length = 24 := by decide +kernel
/-- `hptsU`'s shape: both opened offsets of a column and the out-of-domain point are among the verifier's `openPts` (here `r = 2`, `hGen = 1`) -/
example (ζ : VF.K3) : VF.K3.mul ζ VF.K3.one ∈ (openPts toyInstB ζ).toList ∧ ζ ∈ (openPts toyInstB ζ).toList ∧
    toyInstB.ppt ∈ (openPts toyInstB ζ).toList := by
  refine ⟨?_, zeta_mem_openPts toyInstB ζ, ?_⟩ <;> simp [openPts, toyInstB, List.range_succ]
/-- `hxsU`'s target is satisfiable for EVERY position vector (the codec's decoded points exist): `xsOfPos` reused -/
theorem xs_target_nonvac (hn32 : XI.nD ≤ 32) (hshift : XI.dShift = 7) (hgen : psiV XI.dGen = ((zeta XI.nD : KCˣ) : KC))
    (pos : Fin XI.l → ℕ) :
    ∃ xs : Fin XI.l → ((smoothDomain XI.nD hn32).subdomain 0).toFinset,
      ∀ j, (xs j).val = homV.ψ XI.dShift * homV.ψ XI.dGen ^ pos j :=
  NockvmE2E.Exec.Cover.xsOfPos XI hn32 hshift hgen XI.l pos

end NonVac

#print axioms getD_snd
#print axioms getD_last
#print axioms xs_iter
#print axioms enc_query
#print axioms pos_get
#print axioms hxs_of
#print axioms slots_link
#print axioms deepLinkC_of
#print axioms hpts_of
#print axioms hRV_of
#print axioms rapLinks_of_uni
#print axioms closedLinksL_of_rap
#print axioms embed_msgs
#print axioms xs_target_nonvac
#print axioms chi_eq
#print axioms termsOfK_eq

end Closed
end NockvmE2E.Exec.E2ELR
