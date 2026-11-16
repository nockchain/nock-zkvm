/-
  Nock/Driver/Tip5.lean

  **Tip5 in Lean, executable.**

  * `permute`: per round, the S-box layer (first `4` lanes: the byte-wise `LOOKUP_TABLE`; the other
    `12`: `x^7`), the circulant MDS layer (`MDS_MATRIX_I64`, row `i` = row `0` rotated right by `i`),
    then `+ ROUND_CONSTANTS * R mod p` (the crate stores the constants un-Montgomeried and multiplies by
    `R = 2^64` at run time);
  * `hash10`: the fixed-length variant (`%fixed` initial capacity `2^32 - 1`), one block of 10.

  The state lives in the Montgomery representation exactly as in the crate, because the byte lookup is
  not a field operation.  Multiplications are plain `Nat` products reduced mod `p` (the crate's
  `bmul` / `bpow` are exact mod-`p` operations; `Based` inputs are a precondition of the crate,
  `debug_assert` there, a hypothesis here).

  Nothing is proved about the permutation: the random oracle is a NAMED assumption of the driver
  (`Nock/Driver/Transcript.lean`).  The port is checked against test vectors (`Tip5Vectors.lean`).
-/
set_option autoImplicit false

namespace Nock.Driver.Tip5

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

/-- `tip5_pad_vecbelt`: append `[1, 0,.., 0]` up to a multiple of `RATE`. -/
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

end Nock.Driver.Tip5
