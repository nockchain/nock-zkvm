/-
  NockvmE2E/Exec/Tip5.lean

  Source (read only): the nockvm library, `Nock/Driver/Tip5.lean` (permutation, sponge, hash10; unchanged but for the
  namespace and `P`) and `Nock/Driver/Tip5Vectors.lean` (all 20 vectors, `decide +kernel`, no `native_decide`).  The FS key
  schedule follows `Nock/DriverJ8/TranscriptJ8.lean` (length-prefixed absorb chain over `hashVarlen`, then squeeze) and is
  stated over ArkLib's salted `Key` (the Merkle/ BCS compilation of `NockvmE2E/Merkle/Compiled.lean`).
-/
import NockvmE2E.Exec.Field
import ArkLib.Interaction.Oracle.Security.StateRestoration

set_option autoImplicit false

namespace NockvmE2E.Exec.Tip5

/-- The Goldilocks prime `2^64 - 2^32 + 1` (`PRIME`). -/
def P : Nat := 18446744069414584321
/-- `RATE`. -/
def RATE : Nat := 10
/-- `STATE_SIZE`. -/
def STATE : Nat := 16
/-- `DIGEST_LENGTH`. -/
def DIGLEN : Nat := 5
/-- `NUM_ROUNDS`. -/
def ROUNDS : Nat := 7
/-- `NUM_SPLIT_AND_LOOKUP`. -/
def SPLIT : Nat := 4
/-- `R = 2^64`, as an element of `Fp` it is `2^32 - 1` (`R_MOD_P`). -/
def Rm : Nat := 2 ^ 64 % P
/-- `R^-1 mod p` (`= R2` of `belt.rs`, as `R^3 = 1`). -/
def Rinv : Nat := 18446744065119617025

theorem Rm_eq : Rm = 4294967295 := by decide +kernel
theorem Rinv_spec : Rm * Rinv % P = 1 := by decide +kernel

/-- `LOOKUP_TABLE` (`mod.rs`). -/
def lookupTable : List Nat := [
    0, 7, 26, 63, 124, 215, 85, 254, 214, 228, 45, 185, 140, 173, 33, 240,
  29, 177, 176, 32, 8, 110, 87, 202, 204, 99, 150, 106, 230, 14, 235, 128,
  213, 239, 212, 138, 23, 130, 208, 6, 44, 71, 93, 116, 146, 189, 251, 81,
  199, 97, 38, 28, 73, 179, 95, 84, 152, 48, 35, 119, 49, 88, 242, 3,
  148, 169, 72, 120, 62, 161, 166, 83, 175, 191, 137, 19, 100, 129, 112, 55,
  221, 102, 218, 61, 151, 237, 68, 164, 17, 147, 46, 234, 203, 216, 22, 141,
  65, 57, 123, 12, 244, 54, 219, 231, 96, 77, 180, 154, 5, 253, 133, 165,
  98, 195, 205, 134, 245, 30, 9, 188, 59, 142, 186, 197, 181, 144, 92, 31,
  224, 163, 111, 74, 58, 69, 113, 196, 67, 246, 225, 10, 121, 50, 60, 157,
  90, 122, 2, 250, 101, 75, 178, 159, 24, 36, 201, 11, 243, 132, 198, 190,
  114, 233, 39, 52, 21, 209, 108, 238, 91, 187, 18, 104, 194, 37, 153, 34,
  200, 143, 126, 155, 236, 118, 64, 80, 172, 89, 94, 193, 135, 183, 86, 107,
  252, 13, 167, 206, 136, 220, 207, 103, 171, 160, 76, 182, 227, 217, 158, 56,
  174, 4, 66, 109, 139, 162, 184, 211, 249, 47, 125, 232, 117, 43, 16, 42,
  127, 20, 241, 25, 149, 105, 156, 51, 53, 168, 145, 247, 223, 79, 78, 226,
  15, 222, 82, 115, 70, 210, 27, 41, 1, 170, 40, 131, 192, 229, 248, 255]

/-- `ROUND_CONSTANTS` (`mod.rs`), `NUM_ROUNDS * STATE_SIZE = 112` entries. -/
def roundConstants : List Nat := [
    1332676891236936200, 16607633045354064669, 12746538998793080786, 15240351333789289931,
  10333439796058208418, 986873372968378050, 153505017314310505, 703086547770691416,
  8522628845961587962, 1727254290898686320, 199492491401196126, 2969174933639985366,
  1607536590362293391, 16971515075282501568, 15401316942841283351, 14178982151025681389,
  2916963588744282587, 5474267501391258599, 5350367839445462659, 7436373192934779388,
  12563531800071493891, 12265318129758141428, 6524649031155262053, 1388069597090660214,
  3049665785814990091, 5225141380721656276, 10399487208361035835, 6576713996114457203,
  12913805829885867278, 10299910245954679423, 12980779960345402499, 593670858850716490,
  12184128243723146967, 1315341360419235257, 9107195871057030023, 4354141752578294067,
  8824457881527486794, 14811586928506712910, 7768837314956434138, 2807636171572954860,
  9487703495117094125, 13452575580428891895, 14689488045617615844, 16144091782672017853,
  15471922440568867245, 17295382518415944107, 15054306047726632486, 5708955503115886019,
  9596017237020520842, 16520851172964236909, 8513472793890943175, 8503326067026609602,
  9402483918549940854, 8614816312698982446, 7744830563717871780, 14419404818700162041,
  8090742384565069824, 15547662568163517559, 17314710073626307254, 10008393716631058961,
  14480243402290327574, 13569194973291808551, 10573516815088946209, 15120483436559336219,
  3515151310595301563, 1095382462248757907, 5323307938514209350, 14204542692543834582,
  12448773944668684656, 13967843398310696452, 14838288394107326806, 13718313940616442191,
  15032565440414177483, 13769903572116157488, 17074377440395071208, 16931086385239297738,
  8723550055169003617, 590842605971518043, 16642348030861036090, 10708719298241282592,
  12766914315707517909, 11780889552403245587, 113183285481780712, 9019899125655375514,
  3300264967390964820, 12802381622653377935, 891063765000023873, 15939045541699412539,
  3240223189948727743, 4087221142360949772, 10980466041788253952, 18199914337033135244,
  7168108392363190150, 16860278046098150740, 13088202265571714855, 4712275036097525581,
  16338034078141228133, 1455012125527134274, 5024057780895012002, 9289161311673217186,
  9401110072402537104, 11919498251456187748, 4173156070774045271, 15647643457869530627,
  15642078237964257476, 1405048341078324037, 3059193199283698832, 1605012781983592984,
  7134876918849821827, 5796994175286958720, 7251651436095127661, 4565856221886323991]

/-- The first row of `MDS_MATRIX_I64`; row `i` is this row rotated right by `i`. -/
def mdsRow0 : List Nat := [
    61402, 17845, 26798, 59689, 12021, 40901, 41351, 27521,
  56951, 12034, 53865, 43244, 7454, 33823, 28750, 1108]

theorem lookupTable_length : lookupTable.length = 256 := by decide +kernel
theorem roundConstants_length : roundConstants.length = 112 := by decide +kernel
theorem mdsRow0_length : mdsRow0.length = 16 := by decide +kernel

/-- `MDS_MATRIX_I64[i][j]`. -/
def mds (i j : Nat) : Nat := mdsRow0.getD ((j + STATE - i % STATE) % STATE) 0

/-- The round constants times `R`, as the crate computes them in `permute`. -/
def rcMont (i j : Nat) : Nat := (roundConstants.getD (i * STATE + j) 0 * 2 ^ 64) % P

/-- `x ^ 7 mod p`. -/
def pow7 (x : Nat) : Nat :=
  let x2 := x * x % P
  let x4 := x2 * x2 % P
  x4 * x2 % P * x % P

/-- The byte-wise lookup of one lane: each of the 8 little-endian bytes through `LOOKUP_TABLE`. -/
def lookupLane (x : Nat) : Nat :=
  (List.range 8).foldl
    (fun acc k => acc + (lookupTable.getD ((x >>> (8 * k)) &&& 255) 0) <<< (8 * k)) 0

/-- `sbox_layer`. -/
def sboxLayer (s : List Nat) : List Nat :=
  (List.range STATE).map fun i => if i < SPLIT then lookupLane (s.getD i 0) else pow7 (s.getD i 0)

/-- `linear_layer`. -/
def linearLayer (s : List Nat) : List Nat :=
  (List.range STATE).map fun i =>
    (List.range STATE).foldl (fun acc j => acc + mds i j * s.getD j 0) 0 % P

/-- One round `i`. -/
def round (i : Nat) (s : List Nat) : List Nat :=
  let b := linearLayer (sboxLayer s)
  (List.range STATE).map fun j => (rcMont i j + b.getD j 0) % P

/-- `permute`. -/
def permute (s : List Nat) : List Nat := (List.range ROUNDS).foldl (fun st i => round i st) s

/-- `create_init_sponge_variable`. -/
def initVar : List Nat := List.replicate STATE 0
/-- `create_init_sponge_fixed`. -/
def initFixed : List Nat := List.replicate 10 0 ++ List.replicate 6 4294967295

/-- `montify`: `x * R mod p` (`mont_reduction (x * R2)`). -/
def montify (x : Nat) : Nat := x * Rm % P
/-- `mont_reduction`: `a * R^-1 mod p`. -/
def montRed (a : Nat) : Nat := a * Rinv % P

/-- `tip5_absorb_rate`: overwrite the rate with one block, then permute. -/
def absorbBlock (s : List Nat) (blk : List Nat) : List Nat := permute (blk ++ s.drop RATE)

/-- Absorb blocks of length `RATE` from a list, `fuel` blocks at most (structural). -/
def absorbFuel : Nat → List Nat → List Nat → List Nat
  | 0, s, _ => s
  | n + 1, s, l => if l.isEmpty then s else absorbFuel n (absorbBlock s (l.take RATE)) (l.drop RATE)

/-- `tip5_calc_digest`. -/
def digestOf (s : List Nat) : List Nat := (s.take DIGLEN).map montRed

/-- `tip5_pad_vecbelt`: append `[1, 0, .., 0]` up to a multiple of `RATE`. -/
def pad (inp : List Nat) : List Nat :=
  inp ++ [1] ++ List.replicate (RATE - inp.length % RATE - 1) 0

/-- **`hash_varlen`** (`hash.rs`): the Tip5 variable-length sponge hash of base-field limbs.
Precondition (the crate's `assert_all_based`): every limb `< p`. -/
def hashVarlen (inp : List Nat) : List Nat :=
  let blocks := (pad inp).map montify
  digestOf (absorbFuel (blocks.length / RATE + 1) initVar blocks)

/-- **`hash_10`** (`hash.rs`): the fixed-length hash of exactly ten limbs (`%fixed` sponge). -/
def hash10 (inp : List Nat) : List Nat :=
  digestOf (permute ((inp.map montify) ++ initFixed.drop RATE))

/-- All limbs are field elements. -/
def Based (l : List Nat) : Prop := ∀ x ∈ l, x < P

instance (l : List Nat) : Decidable (Based l) := by unfold Based; infer_instance


theorem tv_montify : montify 1 = 4294967295 ∧ montify 122 = 523986009990 ∧
    montify 127128129130 = 11055578874863858041 := by decide +kernel

theorem tv_montred : montRed 45157629471412822477200 = 10514079938160 ∧
    montRed 24583549534147014201149663878358805000 = 6813007285744613222 := by decide +kernel

theorem tv1_varlen : hashVarlen [] =
    [11048995573592393898, 6655187932135147625, 8573492257662932655, 4379820112787053727, 3881663824627898703] := by decide +kernel

theorem tv2_varlen : hashVarlen [2] =
    [8342164316692288712, 12061287490523852513, 4038969618836824144, 5830796451787599265, 468390350313364562] := by decide +kernel

theorem tv3_varlen : hashVarlen [5, 26] =
    [4045697570544439560, 13674194094340317530, 13743008867885290460, 6020910684025273897, 3362765570390427021] := by decide +kernel

theorem tv4_varlen : hashVarlen [1, 2448, 1, 0, 0, 0, 0, 0, 0, 0] =
    [12811986333282368874, 13601598673786067780, 3807788325936413287, 5511165615113400862, 11490077061305916457] := by decide +kernel

theorem tv5_varlen : hashVarlen [0] =
    [14200481387078929215, 15881046951003480491, 724470049182694108, 13621965870194770768, 329148162721599097] := by decide +kernel

theorem tv6_varlen : hashVarlen [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] =
    [12735212915971076565, 7789085617489624939, 4619502071071326909, 6036885477939560831, 2966144383908523453] := by decide +kernel

theorem tv7_varlen : hashVarlen [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] =
    [2490434595382276408, 14341343290673163516, 2491233006384873183, 15465041162987180922, 11815538018825610320] := by decide +kernel

theorem tv8_varlen : hashVarlen [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] =
    [6401004364544695452, 15125188253232391419, 11623071801923952913, 6200602763077970365, 6209893719295479298] := by decide +kernel

theorem tv9_varlen : hashVarlen [17, 1000020, 2000023, 3000026, 4000029, 5000032, 6000035, 7000038, 8000041, 9000044, 10000047, 11000050, 12000053, 13000056, 14000059, 15000062, 16000065, 17000068, 18000071, 19000074, 20000077, 21000080, 22000083, 23000086, 24000089] =
    [11926666801742104007, 16445744349730768989, 5201230381983307807, 2352322618159079616, 10639439611131708946] := by decide +kernel

theorem tv10_varlen : hashVarlen [18446744069414584320, 18446744069414584320, 18446744069414584320] =
    [2941425018396290597, 16115306305613659799, 11212249099595232631, 2156261626375181373, 7621636006685901516] := by decide +kernel

theorem tv11_varlen : hashVarlen [18446744069414584320, 18446744069414584320, 18446744069414584320, 18446744069414584320, 18446744069414584320, 18446744069414584320, 18446744069414584320, 18446744069414584320, 18446744069414584320, 18446744069414584320] =
    [6173927087780275107, 7837807287211762495, 3967068295064183439, 16415864766103194107, 10924932930283502995] := by decide +kernel

theorem tv12_varlen : hashVarlen [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] =
    [8382060958181788964, 16066061079560324702, 3333742567967315536, 12747105226626001924, 3378654714149291319] := by decide +kernel

theorem tv13_varlen : hashVarlen [0, 0, 0, 0, 0, 0, 0, 0, 0] =
    [10839871895809174654, 3638003660387364873, 5958660276711177896, 13756860651280221086, 16022507246831145802] := by decide +kernel

theorem tv14_hash10 : hash10 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] =
    [15056352079679291843, 7747109957227225216, 5953953536499948464, 9253444947603856218, 6415804733172141563] := by decide +kernel

theorem tv15_hash10 : hash10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] =
    [9769253258223299735, 16053759420056716001, 11946278425937256513, 206946406145412314, 2105714581349115951] := by decide +kernel

theorem tv16_hash10 : hash10 [18446744069414584320, 18446744069414584319, 18446744069414584318, 18446744069414584317, 18446744069414584316, 18446744069414584315, 18446744069414584314, 18446744069414584313, 18446744069414584312, 18446744069414584311] =
    [8438103062707176166, 1783408735107653822, 9164186108992092356, 143076692034823967, 1221638418688248272] := by decide +kernel

theorem tv_perm0 : permute (List.replicate 16 0) =
    [17324604900585909983, 3920346291276200650, 14291393908922830197, 8091744655277936893, 12970812709658306896, 10118522693556575834, 7227151872989822594, 1071132837964818999, 228472562367071834, 18366608707523360310, 11786497396049402957, 11071452717089019025, 16192546354706628500, 4464680096629294277, 18027980985287795659, 8310086468177043051] := by decide +kernel

theorem tv_permI : permute ((List.range 16).map (· * 123456789)) =
    [7845059332189812629, 389891752830224609, 14940023699877445952, 13428430919640799468, 1066306772968639113, 2429434136936771554, 2172668475697586422, 18096154523783046935, 5063687219633862947, 18320861355457920128, 17949348529699512050, 16177190744204535600, 13535375061276082474, 178620631396096651, 4555942227555842583, 4145154448494368017] := by decide +kernel


theorem P_eq : P = NockvmE2E.Exec.p := by decide +kernel

/-! ## The ROM instantiation: `tip5Oracle : Query → Dg` -/

/-- A digest: 5 Goldilocks limbs (`Dg`, `|Dg| ≥ p^4` in the plan's ROM model). -/
abbrev Dg : Type := Fin 5 → ZMod NockvmE2E.Exec.p

/-- The Tip5 digest of a limb list, as `Dg`. -/
def toDg (l : List Nat) : Dg := fun i => ((l.getD i.val 0 : Nat) : ZMod NockvmE2E.Exec.p)

/-- The random-oracle instance: a query, encoded as `< p` limbs by `enc`, answered by `hashVarlen`. -/
def tip5Oracle {Query : Type} (enc : Query → List Nat) (q : Query) : Dg := toDg (hashVarlen (enc q))

/-! ## FS key schedule over ArkLib's salted `Key` -/

section Schedule
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration

def tIni : Nat := 0x65326501   -- domain tags, `< 2^56`
def tAbs : Nat := 0x65326502
def tSqz : Nat := 0x65326503
def tIn : Nat := 0x65326504
def tMsg : Nat := 0x65326505

/-- Absorb `data` under tag `t` into the 5-limb chain state `s` (length-prefixed, as `absorbSt` in TranscriptJ8). -/
def absorb (s : List Nat) (t : Nat) (data : List Nat) : List Nat :=
  hashVarlen ([tAbs] ++ s ++ [t, data.length] ++ data)

/-- `n` limbs squeezed from state `s`: the first `n` of `H[tSqz] ++ s ++ [k]`, `k = 0, 1, ..`. -/
def squeeze (s : List Nat) (n : Nat) : List Nat :=
  ((List.range ((n + 4) / 5)).flatMap fun k => hashVarlen ([tSqz] ++ s ++ [k])).take n

variable {Input Salt : Type}

/-- The prover messages (each with its salt) recorded in a key, in round order. -/
def keyMsgs (encM : ∀ r : Round, r.Message → List Nat) (encS : Salt → List Nat) :
    {rounds : List Round} → Key Input Salt rounds → List (List Nat)
  | [], k => nomatch k
  | r :: _, .inl (_, m, s) => [encM r m ++ encS s]
  | r :: _, .inr (m, s, k) => (encM r m ++ encS s) :: keyMsgs encM encS k

/-- The FS chain state of a key: the input first, then each round's commitment in order (no later data is read). -/
def keyState (encI : Input → List Nat) (encM : ∀ r : Round, r.Message → List Nat) (encS : Salt → List Nat)
    {rounds : List Round} (k : Key Input Salt rounds) : List Nat :=
  (keyMsgs encM encS k).foldl (fun s m => absorb s tMsg m) (absorb (hashVarlen [tIni]) tIn (encI k.input))

/-- The FS oracle: the challenge addressed by `k`, decoded by `dec` from `nl k` squeezed limbs. -/
def fsChallenge (encI : Input → List Nat) (encM : ∀ r : Round, r.Message → List Nat) (encS : Salt → List Nat)
    {rounds : List Round} (nl : Key Input Salt rounds → Nat)
    (dec : (k : Key Input Salt rounds) → List Nat → k.Challenge) (k : Key Input Salt rounds) : k.Challenge :=
  dec k (squeeze (keyState encI encM encS k) (nl k))

end Schedule

end NockvmE2E.Exec.Tip5
