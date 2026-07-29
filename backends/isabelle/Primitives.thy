(* This file provides the foundational definitions for the Isabelle/HOL backend. *)

theory Primitives
  imports
    Main
    "HOL-Library.Word" (* Integer bit operations and their syntax bundle *)
    (*"HOL-Library.String"
    "HOL-Library.Code_Char" *)
begin

unbundle bit_operations_syntax

(* Aeneas imports *)
(*
nitpick_params [off]
quickcheck_params [off] *)

(*** Result *)

datatype error =
    Failure
  | OutOfFuel

datatype 'a result =
    Ok 'a
  | Fail error

(** The result of one loop-body iteration.  The first type parameter is the
    state supplied to the next iteration; the second is the value returned by
    a break. *)
datatype ('state, 'break) control_flow =
    LoopContinue 'state
  | LoopBreak 'break

(** Rust loops need not terminate, whereas every Isabelle/HOL function is
    total.  We therefore keep the general loop fixed point abstract and expose
    its unfolding equation.  Terminating executions are characterized by this
    equation; divergent executions intentionally remain unspecified. *)
axiomatization loop ::
  "('state ⇒ (('state, 'break) control_flow) result) ⇒ 'state ⇒ 'break result"
where loop_unfold:
  "loop body state =
    (case body state of
       Fail e ⇒ Fail e
     | Ok (LoopContinue next) ⇒ loop body next
     | Ok (LoopBreak value) ⇒ Ok value)"

definition return :: "'a ⇒ 'a result" where
  "return x ≡ Ok x"

definition fail :: "error ⇒ 'a result" where
  "fail e ≡ Fail e"

fun bind :: "'a result ⇒ ('a ⇒ 'b result) ⇒ 'b result" (infixl ">>=" 55) where
  "bind (Fail e) f = Fail e"
| "bind (Ok x) f = f x"

(** Lift a well-formedness predicate through the result monad.  This is used
    by generated contracts for erased const-generic indices: a successful
    result must satisfy the predicate, while a failure carries no value to
    check. *)
fun result_wf :: "('a ⇒ bool) ⇒ 'a result ⇒ bool" where
  "result_wf P (Ok x) = P x"
| "result_wf P (Fail e) = True"

syntax
  "_do_bind" :: "[pttrn, 'a result, 'b result] ⇒ 'b result" 
    ("(2_ <- _;// _)" [0, 0, 10] 10)
translations
  "_do_bind x m e" ⇌ "CONST bind m (λx. e)"

(** Monadic assert *)
definition massert :: "bool ⇒ unit result" where
  "massert b ≡ if b then return () else fail Failure"

(** Unwrap a successful result (used for globals). Panics on failure. *)
primrec (nonexhaustive) get_result :: "'a result ⇒ 'a" where
  "get_result (Ok x) = x" (*
| "get_result (Fail e) = undefined" *)

(*** Misc *)

type_synonym string = String.string
type_synonym str = string
type_synonym char = char

(*
definition char_of_byte :: "Word.word8 ⇒ char" where
  "char_of_byte = Code_Char.char_of_byte" *)

definition core_mem_replace :: "'a ⇒ 'a ⇒ ('a × 'a)" where
  "core_mem_replace x y ≡ (x, y)"

definition bool_and :: "bool ⇒ bool ⇒ bool" where
  "bool_and x y ≡ x ∧ y"

definition bool_or :: "bool ⇒ bool ⇒ bool" where
  "bool_or x y ≡ x ∨ y"

definition bool_xor :: "bool ⇒ bool ⇒ bool" where
  "bool_xor x y ≡ x ≠ y"

record 'a mut_raw_ptr = mut_raw_ptr_v :: 'a
record 'a const_raw_ptr = const_raw_ptr_v :: 'a

(*** Scalars *)

(* We model all scalar types as 'int' and provide bounds-checking
   operations that return a 'result' type. *)

type_synonym i8 = int
type_synonym i16 = int
type_synonym i32 = int
type_synonym i64 = int
type_synonym i128 = int
type_synonym u8 = int
type_synonym u16 = int
type_synonym u32 = int
type_synonym u64 = int
type_synonym u128 = int
type_synonym isize = int
type_synonym usize = int

(* Min/Max constants *)
definition i8_min   :: int where "i8_min = -128"
definition i8_max   :: int where "i8_max = 127"
definition i16_min  :: int where "i16_min = -32768"
definition i16_max  :: int where "i16_max = 32767"
definition i32_min  :: int where "i32_min = -2147483648"
definition i32_max  :: int where "i32_max = 2147483647"
definition i64_min  :: int where "i64_min = -9223372036854775808"
definition i64_max  :: int where "i64_max = 9223372036854775807"
definition i128_min :: int where "i128_min = -170141183460469231731687303715884105728"
definition i128_max :: int where "i128_max = 170141183460469231731687303715884105727"
definition u8_min   :: int where "u8_min = 0"
definition u8_max   :: int where "u8_max = 255"
definition u16_min  :: int where "u16_min = 0"
definition u16_max  :: int where "u16_max = 65535"
definition u32_min  :: int where "u32_min = 0"
definition u32_max  :: int where "u32_max = 4294967295"
definition u64_min  :: int where "u64_min = 0"
definition u64_max  :: int where "u64_max = 18446744073709551615"
definition u128_min :: int where "u128_min = 0"
definition u128_max :: int where "u128_max = 340282366920938463463374607431768211455"

(* The Isabelle backend currently fixes Rust's target pointer width to 64 bits.
   Consequently, [isize] and [usize] have the same bounds and cast behaviour as
   [i64] and [u64], respectively.  Supporting another target requires making
   this width part of the extraction configuration. *)
definition isize_min :: int where "isize_min = -9223372036854775808"
definition isize_max :: int where "isize_max = 9223372036854775807"
definition usize_min :: int where "usize_min = 0"
definition usize_max :: int where "usize_max = 18446744073709551615"


datatype scalar_ty =
    Isize | I8 | I16 | I32 | I64 | I128 |
    Usize | U8 | U16 | U32 | U64 | U128

(* [isize] and [usize] are fixed to 64 bits, as documented above. *)
fun scalar_bits :: "scalar_ty ⇒ nat" where
  "scalar_bits Isize = 64"
| "scalar_bits I8 = 8"
| "scalar_bits I16 = 16"
| "scalar_bits I32 = 32"
| "scalar_bits I64 = 64"
| "scalar_bits I128 = 128"
| "scalar_bits Usize = 64"
| "scalar_bits U8 = 8"
| "scalar_bits U16 = 16"
| "scalar_bits U32 = 32"
| "scalar_bits U64 = 64"
| "scalar_bits U128 = 128"

fun scalar_is_signed :: "scalar_ty ⇒ bool" where
  "scalar_is_signed Isize = True"
| "scalar_is_signed I8 = True"
| "scalar_is_signed I16 = True"
| "scalar_is_signed I32 = True"
| "scalar_is_signed I64 = True"
| "scalar_is_signed I128 = True"
| "scalar_is_signed Usize = False"
| "scalar_is_signed U8 = False"
| "scalar_is_signed U16 = False"
| "scalar_is_signed U32 = False"
| "scalar_is_signed U64 = False"
| "scalar_is_signed U128 = False"

fun scalar_min :: "scalar_ty ⇒ int" where
  "scalar_min Isize = isize_min"
| "scalar_min I8 = i8_min"
| "scalar_min I16 = i16_min"
| "scalar_min I32 = i32_min"
| "scalar_min I64 = i64_min"
| "scalar_min I128 = i128_min"
| "scalar_min Usize = usize_min"
| "scalar_min U8 = u8_min"
| "scalar_min U16 = u16_min"
| "scalar_min U32 = u32_min"
| "scalar_min U64 = u64_min"
| "scalar_min U128 = u128_min"

fun scalar_max :: "scalar_ty ⇒ int" where
  "scalar_max Isize = isize_max"
| "scalar_max I8 = i8_max"
| "scalar_max I16 = i16_max"
| "scalar_max I32 = i32_max"
| "scalar_max I64 = i64_max"
| "scalar_max I128 = i128_max"
| "scalar_max Usize = usize_max"
| "scalar_max U8 = u8_max"
| "scalar_max U16 = u16_max"
| "scalar_max U32 = u32_max"
| "scalar_max U64 = u64_max"
| "scalar_max U128 = u128_max"

definition scalar_in_bounds :: "scalar_ty ⇒ int ⇒ bool" where
  "scalar_in_bounds ty x ≡ scalar_min ty ≤ x ∧ x ≤ scalar_max ty"

(* Smart constructors *)
definition mk_scalar :: "scalar_ty ⇒ int ⇒ int result" where
  "mk_scalar ty x ≡ if scalar_in_bounds ty x then return x else fail Failure"

definition mk_i8    :: "int ⇒ i8 result"    where "mk_i8 = mk_scalar I8"
definition mk_i16   :: "int ⇒ i16 result"   where "mk_i16 = mk_scalar I16"
definition mk_i32   :: "int ⇒ i32 result"   where "mk_i32 = mk_scalar I32"
definition mk_i64   :: "int ⇒ i64 result"   where "mk_i64 = mk_scalar I64"
definition mk_i128  :: "int ⇒ i128 result"  where "mk_i128 = mk_scalar I128"
definition mk_isize :: "int ⇒ isize result" where "mk_isize = mk_scalar Isize"
definition mk_u8    :: "int ⇒ u8 result"    where "mk_u8 = mk_scalar U8"
definition mk_u16   :: "int ⇒ u16 result"   where "mk_u16 = mk_scalar U16"
definition mk_u32   :: "int ⇒ u32 result"   where "mk_u32 = mk_scalar U32"
definition mk_u64   :: "int ⇒ u64 result"   where "mk_u64 = mk_scalar U64"
definition mk_u128  :: "int ⇒ u128 result"  where "mk_u128 = mk_scalar U128"
definition mk_usize :: "int ⇒ usize result" where "mk_usize = mk_scalar Usize"

(* Interpret an arbitrary integer at the fixed width and signedness of [ty]. *)
definition scalar_modulus :: "scalar_ty ⇒ int" where
  "scalar_modulus ty ≡ (2 :: int) ^ scalar_bits ty"

definition scalar_wrap :: "scalar_ty ⇒ int ⇒ int" where
  "scalar_wrap ty x ≡
    (let modulus = scalar_modulus ty;
         value = x mod modulus
     in if scalar_is_signed ty ∧ value ≥ modulus div 2
        then value - modulus
        else value)"

(* Isabelle's integer division rounds towards minus infinity, whereas Rust
   truncates towards zero.  Define the Rust operations explicitly. *)
definition scalar_trunc_div :: "int ⇒ int ⇒ int" where
  "scalar_trunc_div x y ≡
    (if (x < 0) = (y < 0)
     then abs x div abs y
     else -(abs x div abs y))"

definition scalar_trunc_rem :: "int ⇒ int ⇒ int" where
  "scalar_trunc_rem x y ≡ x - scalar_trunc_div x y * y"


(* Scalar operations *)
definition scalar_add :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_add ty x y ≡ mk_scalar ty (x + y)"
definition scalar_sub :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_sub ty x y ≡ mk_scalar ty (x - y)"
definition scalar_mul :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_mul ty x y ≡ mk_scalar ty (x * y)"
definition scalar_div :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_div ty x y ≡
    if y = 0 then fail Failure else mk_scalar ty (scalar_trunc_div x y)"
definition scalar_rem :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_rem ty x y ≡
    if y = 0 then fail Failure else mk_scalar ty (scalar_trunc_rem x y)"
definition scalar_neg :: "scalar_ty ⇒ int ⇒ int result" where
  "scalar_neg ty x ≡ mk_scalar ty (- x)"

(* Wrapping operations are pure in Aeneas' Pure IR, except division and
   remainder which can still fail on a zero divisor. *)
definition scalar_wrapping_add :: "scalar_ty ⇒ int ⇒ int ⇒ int" where
  "scalar_wrapping_add ty x y ≡ scalar_wrap ty (x + y)"
definition scalar_wrapping_sub :: "scalar_ty ⇒ int ⇒ int ⇒ int" where
  "scalar_wrapping_sub ty x y ≡ scalar_wrap ty (x - y)"
definition scalar_wrapping_mul :: "scalar_ty ⇒ int ⇒ int ⇒ int" where
  "scalar_wrapping_mul ty x y ≡ scalar_wrap ty (x * y)"
definition scalar_wrapping_neg :: "scalar_ty ⇒ int ⇒ int" where
  "scalar_wrapping_neg ty x ≡ scalar_wrap ty (- x)"
definition scalar_wrapping_div :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_wrapping_div ty x y ≡
    if y = 0 then fail Failure
    else return (scalar_wrap ty (scalar_trunc_div x y))"
definition scalar_wrapping_rem :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_wrapping_rem ty x y ≡
    if y = 0 then fail Failure
    else return (scalar_wrap ty (scalar_trunc_rem x y))"

(* Rust's overflowing_* operations return the wrapped value and an overflow
   flag.  The Pure checked operators use this same pair representation. *)
definition scalar_add_checked :: "scalar_ty ⇒ int ⇒ int ⇒ int × bool" where
  "scalar_add_checked ty x y ≡
    (let z = x + y in (scalar_wrap ty z, ¬ scalar_in_bounds ty z))"
definition scalar_sub_checked :: "scalar_ty ⇒ int ⇒ int ⇒ int × bool" where
  "scalar_sub_checked ty x y ≡
    (let z = x - y in (scalar_wrap ty z, ¬ scalar_in_bounds ty z))"
definition scalar_mul_checked :: "scalar_ty ⇒ int ⇒ int ⇒ int × bool" where
  "scalar_mul_checked ty x y ≡
    (let z = x * y in (scalar_wrap ty z, ¬ scalar_in_bounds ty z))"
(* Logic *)
definition scalar_lt :: "scalar_ty ⇒ int ⇒ int ⇒ bool" where
  "scalar_lt ty x y ≡ x < y"
definition scalar_le :: "scalar_ty ⇒ int ⇒ int ⇒ bool" where
  "scalar_le ty x y ≡ x ≤ y"
definition scalar_gt :: "scalar_ty ⇒ int ⇒ int ⇒ bool" where
  "scalar_gt ty x y ≡ x > y"
definition scalar_ge :: "scalar_ty ⇒ int ⇒ int ⇒ bool" where
  "scalar_ge ty x y ≡ x ≥ y"
definition scalar_eq :: "scalar_ty ⇒ int ⇒ int ⇒ bool" where
  "scalar_eq ty x y ≡ x = y"
definition scalar_ne :: "scalar_ty ⇒ int ⇒ int ⇒ bool" where
  "scalar_ne ty x y ≡ x ≠ y"

(* Bitwise operations are pure.  Wrapping the mathematical integer result is
   essential for signed types, whose representation is two's complement. *)
definition scalar_xor :: "scalar_ty ⇒ int ⇒ int ⇒ int" where
  "scalar_xor ty x y ≡ scalar_wrap ty (x XOR y)"
definition scalar_or :: "scalar_ty ⇒ int ⇒ int ⇒ int" where
  "scalar_or ty x y ≡ scalar_wrap ty (x OR y)"
definition scalar_and :: "scalar_ty ⇒ int ⇒ int ⇒ int" where
  "scalar_and ty x y ≡ scalar_wrap ty (x AND y)"
definition scalar_not :: "scalar_ty ⇒ int ⇒ int" where
  "scalar_not ty x ≡ scalar_wrap ty (NOT x)"

definition scalar_shift_in_bounds :: "scalar_ty ⇒ int ⇒ bool" where
  "scalar_shift_in_bounds ty n ≡ 0 ≤ n ∧ n < int (scalar_bits ty)"

definition scalar_shl :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_shl ty x n ≡
    if scalar_shift_in_bounds ty n
    then return (scalar_wrap ty (x * (2 :: int) ^ nat n))
    else fail Failure"

definition scalar_shr :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_shr ty x n ≡
    if scalar_shift_in_bounds ty n
    then return (scalar_wrap ty (x div (2 :: int) ^ nat n))
    else fail Failure"

definition scalar_wrapping_shift_amount :: "scalar_ty ⇒ int ⇒ nat" where
  "scalar_wrapping_shift_amount ty n ≡ nat (n mod int (scalar_bits ty))"

definition scalar_wrapping_shl :: "scalar_ty ⇒ int ⇒ int ⇒ int" where
  "scalar_wrapping_shl ty x n ≡
    scalar_wrap ty
      (x * (2 :: int) ^ scalar_wrapping_shift_amount ty n)"

definition scalar_wrapping_shr :: "scalar_ty ⇒ int ⇒ int ⇒ int" where
  "scalar_wrapping_shr ty x n ≡
    scalar_wrap ty
      (x div (2 :: int) ^ scalar_wrapping_shift_amount ty n)"

(* Rust integer casts never fail for a well-formed source scalar.  They first
   retain the low bits of the target width, then interpret those bits as a
   two's-complement number when the target is signed.  We keep a [result]
   return type because the Pure translation currently treats non-Lean casts as
   monadic. *)
definition scalar_cast :: "scalar_ty ⇒ scalar_ty ⇒ int ⇒ int result" where
  "scalar_cast _ tgt_ty x ≡ return (scalar_wrap tgt_ty x)"

definition scalar_cast_bool :: "scalar_ty ⇒ bool ⇒ int result" where
  "scalar_cast_bool _ b ≡ return (if b then 1 else 0)"

(* Helper for HOL4/Isabelle style casts (e.g., i32_of_u8) *)
definition i8_to_int    :: "i8 ⇒ int"    where "i8_to_int x = x"
definition i16_to_int   :: "i16 ⇒ int"   where "i16_to_int x = x"
definition i32_to_int   :: "i32 ⇒ int"   where "i32_to_int x = x"
definition i64_to_int   :: "i64 ⇒ int"   where "i64_to_int x = x"
definition i128_to_int  :: "i128 ⇒ int"  where "i128_to_int x = x"
definition isize_to_int :: "isize ⇒ int" where "isize_to_int x = x"
definition u8_to_int    :: "u8 ⇒ int"    where "u8_to_int x = x"
definition u16_to_int   :: "u16 ⇒ int"   where "u16_to_int x = x"
definition u32_to_int   :: "u32 ⇒ int"   where "u32_to_int x = x"
definition u64_to_int   :: "u64 ⇒ int"   where "u64_to_int x = x"
definition u128_to_int  :: "u128 ⇒ int"  where "u128_to_int x = x"
definition usize_to_int :: "usize ⇒ int" where "usize_to_int x = x"
definition bool_to_int :: "bool ⇒ int" where
  "bool_to_int x = (if x then 1 else 0)"

(* Comparisons (on the unwrapped 'int' types) *)
definition scalar_leb  :: "'a::order ⇒ 'a ⇒ bool" where "scalar_leb = (≤)"
definition scalar_ltb  :: "'a::linorder ⇒ 'a ⇒ bool" where "scalar_ltb = (<)"
definition scalar_geb  :: "'a::order ⇒ 'a ⇒ bool" where "scalar_geb = (≥)"
definition scalar_gtb  :: "'a::linorder ⇒ 'a ⇒ bool" where "scalar_gtb = (>)"

(*
definition scalar_eqb  :: "'a::eq ⇒ 'a ⇒ bool" where "scalar_eqb = (=)"
definition scalar_neqb :: "'a::eq ⇒ 'a ⇒ bool" where "scalar_neqb = (≠)" 
*)
definition scalar_eqb  :: "'a::order ⇒ 'a ⇒ bool" where "scalar_eqb = (=)"
definition scalar_neqb :: "'a::order ⇒ 'a ⇒ bool" where "scalar_neqb = (≠)" 

(* Neg Op *)
definition isize_neg :: "int ⇒ int result" where 
  "isize_neg = scalar_neg Isize"
definition i8_neg :: "int ⇒ int result" where 
  "i8_neg = scalar_neg I8"
definition i16_neg :: "int ⇒ int result" where 
  "i16_neg = scalar_neg I16"
definition i32_neg :: "int ⇒ int result" where 
  "i32_neg = scalar_neg I32"
definition i64_neg :: "int ⇒ int result" where 
  "i64_neg = scalar_neg I64"
definition i128_neg :: "int ⇒ int result" where 
  "i128_neg = scalar_neg I128"

(* Div Op *)
definition isize_div :: "int ⇒ int ⇒ int result" where 
  "isize_div = scalar_div Isize"
definition i8_div :: "int ⇒ int ⇒ int result" where 
  "i8_div = scalar_div I8"
definition i16_div :: "int ⇒ int ⇒ int result" where 
  "i16_div = scalar_div I16"
definition i32_div :: "int ⇒ int ⇒ int result" where 
  "i32_div = scalar_div I32"
definition i64_div :: "int ⇒ int ⇒ int result" where 
  "i64_div = scalar_div I64"
definition i128_div :: "int ⇒ int ⇒ int result" where 
  "i128_div = scalar_div I128"
definition usize_div :: "int ⇒ int ⇒ int result" where 
  "usize_div = scalar_div Usize"
definition u8_div :: "int ⇒ int ⇒ int result" where 
  "u8_div = scalar_div U8"
definition u16_div :: "int ⇒ int ⇒ int result" where 
  "u16_div = scalar_div U16"
definition u32_div :: "int ⇒ int ⇒ int result" where 
  "u32_div = scalar_div U32"
definition u64_div :: "int ⇒ int ⇒ int result" where 
  "u64_div = scalar_div U64"
definition u128_div :: "int ⇒ int ⇒ int result" where 
  "u128_div = scalar_div U128"

(* Rem Op *)
definition isize_rem :: "int ⇒ int ⇒ int result" where 
  "isize_rem = scalar_rem Isize"
definition i8_rem :: "int ⇒ int ⇒ int result" where 
  "i8_rem = scalar_rem I8"
definition i16_rem :: "int ⇒ int ⇒ int result" where 
  "i16_rem = scalar_rem I16"
definition i32_rem :: "int ⇒ int ⇒ int result" where 
  "i32_rem = scalar_rem I32"
definition i64_rem :: "int ⇒ int ⇒ int result" where 
  "i64_rem = scalar_rem I64"
definition i128_rem :: "int ⇒ int ⇒ int result" where 
  "i128_rem = scalar_rem I128"
definition usize_rem :: "int ⇒ int ⇒ int result" where 
  "usize_rem = scalar_rem Usize"
definition u8_rem :: "int ⇒ int ⇒ int result" where 
  "u8_rem = scalar_rem U8"
definition u16_rem :: "int ⇒ int ⇒ int result" where 
  "u16_rem = scalar_rem U16"
definition u32_rem :: "int ⇒ int ⇒ int result" where 
  "u32_rem = scalar_rem U32"
definition u64_rem :: "int ⇒ int ⇒ int result" where 
  "u64_rem = scalar_rem U64"
definition u128_rem :: "int ⇒ int ⇒ int result" where 
  "u128_rem = scalar_rem U128"

(* Add Op *)
definition isize_add :: "int ⇒ int ⇒ int result" where 
  "isize_add = scalar_add Isize"
definition i8_add :: "int ⇒ int ⇒ int result" where 
  "i8_add = scalar_add I8"
definition i16_add :: "int ⇒ int ⇒ int result" where 
  "i16_add = scalar_add I16"
definition i32_add :: "int ⇒ int ⇒ int result" where 
  "i32_add = scalar_add I32"
definition i64_add :: "int ⇒ int ⇒ int result" where 
  "i64_add = scalar_add I64"
definition i128_add :: "int ⇒ int ⇒ int result" where 
  "i128_add = scalar_add I128"
definition usize_add :: "int ⇒ int ⇒ int result" where 
  "usize_add = scalar_add Usize"
definition u8_add :: "int ⇒ int ⇒ int result" where 
  "u8_add = scalar_add U8"
definition u16_add :: "int ⇒ int ⇒ int result" where 
  "u16_add = scalar_add U16"
definition u32_add :: "int ⇒ int ⇒ int result" where 
  "u32_add = scalar_add U32"
definition u64_add :: "int ⇒ int ⇒ int result" where 
  "u64_add = scalar_add U64"
definition u128_add :: "int ⇒ int ⇒ int result" where 
  "u128_add = scalar_add U128"

(* Sub Op *)
definition isize_sub :: "int ⇒ int ⇒ int result" where 
  "isize_sub = scalar_sub Isize"
definition i8_sub :: "int ⇒ int ⇒ int result" where 
  "i8_sub = scalar_sub I8"
definition i16_sub :: "int ⇒ int ⇒ int result" where 
  "i16_sub = scalar_sub I16"
definition i32_sub :: "int ⇒ int ⇒ int result" where 
  "i32_sub = scalar_sub I32"
definition i64_sub :: "int ⇒ int ⇒ int result" where 
  "i64_sub = scalar_sub I64"
definition i128_sub :: "int ⇒ int ⇒ int result" where 
  "i128_sub = scalar_sub I128"
definition usize_sub :: "int ⇒ int ⇒ int result" where 
  "usize_sub = scalar_sub Usize"
definition u8_sub :: "int ⇒ int ⇒ int result" where 
  "u8_sub = scalar_sub U8"
definition u16_sub :: "int ⇒ int ⇒ int result" where 
  "u16_sub = scalar_sub U16"
definition u32_sub :: "int ⇒ int ⇒ int result" where 
  "u32_sub = scalar_sub U32"
definition u64_sub :: "int ⇒ int ⇒ int result" where 
  "u64_sub = scalar_sub U64"
definition u128_sub :: "int ⇒ int ⇒ int result" where 
  "u128_sub = scalar_sub U128"

(* Mul Op *)
definition isize_mul :: "int ⇒ int ⇒ int result" where 
  "isize_mul = scalar_mul Isize"
definition i8_mul :: "int ⇒ int ⇒ int result" where 
  "i8_mul = scalar_mul I8"
definition i16_mul :: "int ⇒ int ⇒ int result" where 
  "i16_mul = scalar_mul I16"
definition i32_mul :: "int ⇒ int ⇒ int result" where 
  "i32_mul = scalar_mul I32"
definition i64_mul :: "int ⇒ int ⇒ int result" where 
  "i64_mul = scalar_mul I64"
definition i128_mul :: "int ⇒ int ⇒ int result" where 
  "i128_mul = scalar_mul I128"
definition usize_mul :: "int ⇒ int ⇒ int result" where 
  "usize_mul = scalar_mul Usize"
definition u8_mul :: "int ⇒ int ⇒ int result" where 
  "u8_mul = scalar_mul U8"
definition u16_mul :: "int ⇒ int ⇒ int result" where 
  "u16_mul = scalar_mul U16"
definition u32_mul :: "int ⇒ int ⇒ int result" where 
  "u32_mul = scalar_mul U32"
definition u64_mul :: "int ⇒ int ⇒ int result" where 
  "u64_mul = scalar_mul U64"
definition u128_mul :: "int ⇒ int ⇒ int result" where 
  "u128_mul = scalar_mul U128"

(* Xor Op *)
definition u8_xor :: "int ⇒ int ⇒ int" where
  "u8_xor = scalar_xor U8"
definition u16_xor :: "int ⇒ int ⇒ int" where
  "u16_xor = scalar_xor U16"
definition u32_xor :: "int ⇒ int ⇒ int" where
  "u32_xor = scalar_xor U32"
definition u64_xor :: "int ⇒ int ⇒ int" where
  "u64_xor = scalar_xor U64"
definition u128_xor :: "int ⇒ int ⇒ int" where
  "u128_xor = scalar_xor U128"
definition usize_xor :: "int ⇒ int ⇒ int" where
  "usize_xor = scalar_xor Usize"
definition i8_xor :: "int ⇒ int ⇒ int" where
  "i8_xor = scalar_xor I8"
definition i16_xor :: "int ⇒ int ⇒ int" where
  "i16_xor = scalar_xor I16"
definition i32_xor :: "int ⇒ int ⇒ int" where
  "i32_xor = scalar_xor I32"
definition i64_xor :: "int ⇒ int ⇒ int" where
  "i64_xor = scalar_xor I64"
definition i128_xor :: "int ⇒ int ⇒ int" where
  "i128_xor = scalar_xor I128"
definition isize_xor :: "int ⇒ int ⇒ int" where
  "isize_xor = scalar_xor Isize"

(* Or Op *)
definition u8_or :: "int ⇒ int ⇒ int" where
  "u8_or = scalar_or U8"
definition u16_or :: "int ⇒ int ⇒ int" where
  "u16_or = scalar_or U16"
definition u32_or :: "int ⇒ int ⇒ int" where
  "u32_or = scalar_or U32"
definition u64_or :: "int ⇒ int ⇒ int" where
  "u64_or = scalar_or U64"
definition u128_or :: "int ⇒ int ⇒ int" where
  "u128_or = scalar_or U128"
definition usize_or :: "int ⇒ int ⇒ int" where
  "usize_or = scalar_or Usize"
definition i8_or :: "int ⇒ int ⇒ int" where
  "i8_or = scalar_or I8"
definition i16_or :: "int ⇒ int ⇒ int" where
  "i16_or = scalar_or I16"
definition i32_or :: "int ⇒ int ⇒ int" where
  "i32_or = scalar_or I32"
definition i64_or :: "int ⇒ int ⇒ int" where
  "i64_or = scalar_or I64"
definition i128_or :: "int ⇒ int ⇒ int" where
  "i128_or = scalar_or I128"
definition isize_or :: "int ⇒ int ⇒ int" where
  "isize_or = scalar_or Isize"

(* And Op *)
definition u8_and :: "int ⇒ int ⇒ int" where
  "u8_and = scalar_and U8"
definition u16_and :: "int ⇒ int ⇒ int" where
  "u16_and = scalar_and U16"
definition u32_and :: "int ⇒ int ⇒ int" where
  "u32_and = scalar_and U32"
definition u64_and :: "int ⇒ int ⇒ int" where
  "u64_and = scalar_and U64"
definition u128_and :: "int ⇒ int ⇒ int" where
  "u128_and = scalar_and U128"
definition usize_and :: "int ⇒ int ⇒ int" where
  "usize_and = scalar_and Usize"
definition i8_and :: "int ⇒ int ⇒ int" where
  "i8_and = scalar_and I8"
definition i16_and :: "int ⇒ int ⇒ int" where
  "i16_and = scalar_and I16"
definition i32_and :: "int ⇒ int ⇒ int" where
  "i32_and = scalar_and I32"
definition i64_and :: "int ⇒ int ⇒ int" where
  "i64_and = scalar_and I64"
definition i128_and :: "int ⇒ int ⇒ int" where
  "i128_and = scalar_and I128"
definition isize_and :: "int ⇒ int ⇒ int" where
  "isize_and = scalar_and Isize"

(* Shift Left Op *)
definition u8_shl :: "int ⇒ int ⇒ int result" where 
  "u8_shl = scalar_shl U8"
definition u16_shl :: "int ⇒ int ⇒ int result" where 
  "u16_shl = scalar_shl U16"
definition u32_shl :: "int ⇒ int ⇒ int result" where 
  "u32_shl = scalar_shl U32"
definition u64_shl :: "int ⇒ int ⇒ int result" where 
  "u64_shl = scalar_shl U64"
definition u128_shl :: "int ⇒ int ⇒ int result" where 
  "u128_shl = scalar_shl U128"
definition usize_shl :: "int ⇒ int ⇒ int result" where 
  "usize_shl = scalar_shl Usize"
definition i8_shl :: "int ⇒ int ⇒ int result" where 
  "i8_shl = scalar_shl I8"
definition i16_shl :: "int ⇒ int ⇒ int result" where 
  "i16_shl = scalar_shl I16"
definition i32_shl :: "int ⇒ int ⇒ int result" where 
  "i32_shl = scalar_shl I32"
definition i64_shl :: "int ⇒ int ⇒ int result" where 
  "i64_shl = scalar_shl I64"
definition i128_shl :: "int ⇒ int ⇒ int result" where 
  "i128_shl = scalar_shl I128"
definition isize_shl :: "int ⇒ int ⇒ int result" where 
  "isize_shl = scalar_shl Isize"

(* Shift Right Op *)
definition u8_shr :: "int ⇒ int ⇒ int result" where 
  "u8_shr = scalar_shr U8"
definition u16_shr :: "int ⇒ int ⇒ int result" where 
  "u16_shr = scalar_shr U16"
definition u32_shr :: "int ⇒ int ⇒ int result" where 
  "u32_shr = scalar_shr U32"
definition u64_shr :: "int ⇒ int ⇒ int result" where 
  "u64_shr = scalar_shr U64"
definition u128_shr :: "int ⇒ int ⇒ int result" where 
  "u128_shr = scalar_shr U128"
definition usize_shr :: "int ⇒ int ⇒ int result" where 
  "usize_shr = scalar_shr Usize"
definition i8_shr :: "int ⇒ int ⇒ int result" where 
  "i8_shr = scalar_shr I8"
definition i16_shr :: "int ⇒ int ⇒ int result" where 
  "i16_shr = scalar_shr I16"
definition i32_shr :: "int ⇒ int ⇒ int result" where 
  "i32_shr = scalar_shr I32"
definition i64_shr :: "int ⇒ int ⇒ int result" where 
  "i64_shr = scalar_shr I64"
definition i128_shr :: "int ⇒ int ⇒ int result" where 
  "i128_shr = scalar_shr I128"
definition isize_shr :: "int ⇒ int ⇒ int result" where 
  "isize_shr = scalar_shr Isize"

(* Not Op *)
definition u8_not :: "int ⇒ int" where
  "u8_not = scalar_not U8"
definition u16_not :: "int ⇒ int" where
  "u16_not = scalar_not U16"
definition u32_not :: "int ⇒ int" where
  "u32_not = scalar_not U32"
definition u64_not :: "int ⇒ int" where
  "u64_not = scalar_not U64"
definition u128_not :: "int ⇒ int" where
  "u128_not = scalar_not U128"
definition usize_not :: "int ⇒ int" where
  "usize_not = scalar_not Usize"
definition i8_not :: "int ⇒ int" where
  "i8_not = scalar_not I8"
definition i16_not :: "int ⇒ int" where
  "i16_not = scalar_not I16"
definition i32_not :: "int ⇒ int" where
  "i32_not = scalar_not I32"
definition i64_not :: "int ⇒ int" where
  "i64_not = scalar_not I64"
definition i128_not :: "int ⇒ int" where
  "i128_not = scalar_not I128"
definition isize_not :: "int ⇒ int" where
  "isize_not = scalar_not Isize"

(* Less Than Op *)
definition u8_lt :: "int ⇒ int ⇒ bool" where 
  "u8_lt = scalar_lt U8"
definition u16_lt :: "int ⇒ int ⇒ bool" where 
  "u16_lt = scalar_lt U16"
definition u32_lt :: "int ⇒ int ⇒ bool" where 
  "u32_lt = scalar_lt U32"
definition u64_lt :: "int ⇒ int ⇒ bool" where 
  "u64_lt = scalar_lt U64"
definition u128_lt :: "int ⇒ int ⇒ bool" where 
  "u128_lt = scalar_lt U128"
definition usize_lt :: "int ⇒ int ⇒ bool" where 
  "usize_lt = scalar_lt Usize"
definition i8_lt :: "int ⇒ int ⇒ bool" where 
  "i8_lt = scalar_lt I8"
definition i16_lt :: "int ⇒ int ⇒ bool" where 
  "i16_lt = scalar_lt I16"
definition i32_lt :: "int ⇒ int ⇒ bool" where 
  "i32_lt = scalar_lt I32"
definition i64_lt :: "int ⇒ int ⇒ bool" where 
  "i64_lt = scalar_lt I64"
definition i128_lt :: "int ⇒ int ⇒ bool" where 
  "i128_lt = scalar_lt I128"
definition isize_lt :: "int ⇒ int ⇒ bool" where 
  "isize_lt = scalar_lt Isize"

(* Less and Equal Op *)
definition u8_le :: "int ⇒ int ⇒ bool" where 
  "u8_le = scalar_le U8"
definition u16_le :: "int ⇒ int ⇒ bool" where 
  "u16_le = scalar_le U16"
definition u32_le :: "int ⇒ int ⇒ bool" where 
  "u32_le = scalar_le U32"
definition u64_le :: "int ⇒ int ⇒ bool" where 
  "u64_le = scalar_le U64"
definition u128_le :: "int ⇒ int ⇒ bool" where 
  "u128_le = scalar_le U128"
definition usize_le :: "int ⇒ int ⇒ bool" where 
  "usize_le = scalar_le Usize"
definition i8_le :: "int ⇒ int ⇒ bool" where 
  "i8_le = scalar_le I8"
definition i16_le :: "int ⇒ int ⇒ bool" where 
  "i16_le = scalar_le I16"
definition i32_le :: "int ⇒ int ⇒ bool" where 
  "i32_le = scalar_le I32"
definition i64_le :: "int ⇒ int ⇒ bool" where 
  "i64_le = scalar_le I64"
definition i128_le :: "int ⇒ int ⇒ bool" where 
  "i128_le = scalar_le I128"
definition isize_le :: "int ⇒ int ⇒ bool" where 
  "isize_le = scalar_le Isize"

(* Greater Than Op *)
definition u8_gt :: "int ⇒ int ⇒ bool" where 
  "u8_gt = scalar_gt U8"
definition u16_gt :: "int ⇒ int ⇒ bool" where 
  "u16_gt = scalar_gt U16"
definition u32_gt :: "int ⇒ int ⇒ bool" where 
  "u32_gt = scalar_gt U32"
definition u64_gt :: "int ⇒ int ⇒ bool" where 
  "u64_gt = scalar_gt U64"
definition u128_gt :: "int ⇒ int ⇒ bool" where 
  "u128_gt = scalar_gt U128"
definition usize_gt :: "int ⇒ int ⇒ bool" where 
  "usize_gt = scalar_gt Usize"
definition i8_gt :: "int ⇒ int ⇒ bool" where 
  "i8_gt = scalar_gt I8"
definition i16_gt :: "int ⇒ int ⇒ bool" where 
  "i16_gt = scalar_gt I16"
definition i32_gt :: "int ⇒ int ⇒ bool" where 
  "i32_gt = scalar_gt I32"
definition i64_gt :: "int ⇒ int ⇒ bool" where 
  "i64_gt = scalar_gt I64"
definition i128_gt :: "int ⇒ int ⇒ bool" where 
  "i128_gt = scalar_gt I128"
definition isize_gt :: "int ⇒ int ⇒ bool" where 
  "isize_gt = scalar_gt Isize"

(* Greater and Equal Op *)
definition u8_ge :: "int ⇒ int ⇒ bool" where 
  "u8_ge = scalar_ge U8"
definition u16_ge :: "int ⇒ int ⇒ bool" where 
  "u16_ge = scalar_ge U16"
definition u32_ge :: "int ⇒ int ⇒ bool" where 
  "u32_ge = scalar_ge U32"
definition u64_ge :: "int ⇒ int ⇒ bool" where 
  "u64_ge = scalar_ge U64"
definition u128_ge :: "int ⇒ int ⇒ bool" where 
  "u128_ge = scalar_ge U128"
definition usize_ge :: "int ⇒ int ⇒ bool" where 
  "usize_ge = scalar_ge Usize"
definition i8_ge :: "int ⇒ int ⇒ bool" where 
  "i8_ge = scalar_ge I8"
definition i16_ge :: "int ⇒ int ⇒ bool" where 
  "i16_ge = scalar_ge I16"
definition i32_ge :: "int ⇒ int ⇒ bool" where 
  "i32_ge = scalar_ge I32"
definition i64_ge :: "int ⇒ int ⇒ bool" where 
  "i64_ge = scalar_ge I64"
definition i128_ge :: "int ⇒ int ⇒ bool" where 
  "i128_ge = scalar_ge I128"
definition isize_ge :: "int ⇒ int ⇒ bool" where 
  "isize_ge = scalar_ge Isize"

(* Equal Op *)
definition u8_eq :: "int ⇒ int ⇒ bool" where 
  "u8_eq = scalar_eq U8"
definition u16_eq :: "int ⇒ int ⇒ bool" where 
  "u16_eq = scalar_eq U16"
definition u32_eq :: "int ⇒ int ⇒ bool" where 
  "u32_eq = scalar_eq U32"
definition u64_eq :: "int ⇒ int ⇒ bool" where 
  "u64_eq = scalar_eq U64"
definition u128_eq :: "int ⇒ int ⇒ bool" where 
  "u128_eq = scalar_eq U128"
definition usize_eq :: "int ⇒ int ⇒ bool" where 
  "usize_eq = scalar_eq Usize"
definition i8_eq :: "int ⇒ int ⇒ bool" where 
  "i8_eq = scalar_eq I8"
definition i16_eq :: "int ⇒ int ⇒ bool" where 
  "i16_eq = scalar_eq I16"
definition i32_eq :: "int ⇒ int ⇒ bool" where 
  "i32_eq = scalar_eq I32"
definition i64_eq :: "int ⇒ int ⇒ bool" where 
  "i64_eq = scalar_eq I64"
definition i128_eq :: "int ⇒ int ⇒ bool" where 
  "i128_eq = scalar_eq I128"
definition isize_eq :: "int ⇒ int ⇒ bool" where 
  "isize_eq = scalar_eq Isize"

(* Not Equal Op *)
definition u8_ne :: "int ⇒ int ⇒ bool" where 
  "u8_ne = scalar_ne U8"
definition u16_ne :: "int ⇒ int ⇒ bool" where 
  "u16_ne = scalar_ne U16"
definition u32_ne :: "int ⇒ int ⇒ bool" where 
  "u32_ne = scalar_ne U32"
definition u64_ne :: "int ⇒ int ⇒ bool" where 
  "u64_ne = scalar_ne U64"
definition u128_ne :: "int ⇒ int ⇒ bool" where 
  "u128_ne = scalar_ne U128"
definition usize_ne :: "int ⇒ int ⇒ bool" where 
  "usize_ne = scalar_ne Usize"
definition i8_ne :: "int ⇒ int ⇒ bool" where 
  "i8_ne = scalar_ne I8"
definition i16_ne :: "int ⇒ int ⇒ bool" where 
  "i16_ne = scalar_ne I16"
definition i32_ne :: "int ⇒ int ⇒ bool" where 
  "i32_ne = scalar_ne I32"
definition i64_ne :: "int ⇒ int ⇒ bool" where 
  "i64_ne = scalar_ne I64"
definition i128_ne :: "int ⇒ int ⇒ bool" where 
  "i128_ne = scalar_ne I128"
definition isize_ne :: "int ⇒ int ⇒ bool" where 
  "isize_ne = scalar_ne Isize"

(** Small utility *)
definition usize_to_nat :: "usize ⇒ nat" where
  "usize_to_nat x = (if x < 0 then 0 else nat x)"

(** Constants *)
definition core_num_U8_MIN :: u32 where
  "core_num_U8_MIN = u8_min"

definition core_num_U16_MIN :: u32 where
  "core_num_U16_MIN = u16_min"

definition core_num_U32_MIN :: u32 where
  "core_num_U32_MIN = u32_min"

definition core_num_U64_MIN :: u64 where
  "core_num_U64_MIN = u64_min"

definition core_num_U128_MIN :: u128 where
  "core_num_U128_MIN = u64_min" 

axiomatization core_num_Usize_MIN :: usize

definition core_num_I8_MIN :: i32 where
  "core_num_I8_MIN = i8_min"

definition core_num_I16_MIN :: i32 where
  "core_num_I16_MIN = i16_min"

definition core_num_I32_MIN :: i32 where
  "core_num_I32_MIN = i32_min"

definition core_num_I64_MIN :: i64 where
  "core_num_I64_MIN = i64_min"

definition core_num_I128_MIN :: i128 where
  "core_num_I128_MIN = i64_min" 

axiomatization core_num_Isize_MIN :: isize

definition core_num_U8_MAX :: u32 where
  "core_num_U8_MAX = u8_max"

definition core_num_U16_MAX :: u32 where
  "core_num_U16_MAX = u16_max"

definition core_num_U32_MAX :: u32 where
  "core_num_U32_MAX = u32_max"

definition core_num_U64_MAX :: u64 where
  "core_num_U64_MAX = u64_max"

definition core_num_U128_MAX :: u128 where
  "core_num_U128_MAX = u64_max"

axiomatization core_num_Usize_MAX :: usize 

definition core_num_I8_MAX :: i32 where
  "core_num_I8_MAX = i8_max"

definition core_num_I16_MAX :: i32 where
  "core_num_I16_MAX = i16_max"

definition core_num_I32_MAX :: i32 where
  "core_num_I32_MAX = i32_max"

definition core_num_I64_MAX :: i64 where
  "core_num_I64_MAX = i64_max"

definition core_num_I128_MAX :: i128 where
  "core_num_I128_MAX = i64_max"

axiomatization core_num_Isize_MAX :: isize

(*** core *)

(** Trait declaration: [core::clone::Clone] *)
record 'self core_clone_Clone =
  core_clone_Clone_clone :: "'self ⇒ 'self result"
  core_clone_Clone_clone_from :: "'self ⇒ 'self ⇒ 'self result"

definition core_clone_impls_CloneUsize_clone :: "usize ⇒ usize" where "core_clone_impls_CloneUsize_clone x = x"
(* ... other scalar clone impls ... *)

definition core_clone_CloneUsize :: "usize core_clone_Clone" where
  "core_clone_CloneUsize = (|
    core_clone_Clone_clone = (λx. return (core_clone_impls_CloneUsize_clone x)),
    core_clone_Clone_clone_from = (λ _ y. return y)
  |)"
(* ... other scalar clone instances ... *)
axiomatization core_clone_CloneI8 :: "i8 core_clone_Clone"
axiomatization core_clone_CloneU32 :: "u32 core_clone_Clone"
(* ... *)

record 'self core_marker_Copy =
  cloneInst :: "'self core_clone_Clone"

(*
definition core_marker_CopyU8 :: "u8 core_marker_Copy" where
  "core_marker_CopyU8 = (| cloneInst = core_clone_CloneU8 |)" *)
(* ... other scalar copy instances ... *)
axiomatization core_marker_CopyI8 :: "i8 core_marker_Copy"
axiomatization core_marker_CopyU32 :: "u32 core_marker_Copy"
(* ... *)

(** [core::option::{core::option::Option<T>}::unwrap] *)
fun core_option_Option_unwrap :: "'a option ⇒ 'a result" where
  "core_option_Option_unwrap (Some x) = (Ok x)" |
  "core_option_Option_unwrap None = Fail Failure"

(*** core::ops *)

(* Trait declaration: [core::ops::index::Index] *)
record ('self, 'idx, 'output) core_ops_index_Index =
  core_ops_index_Index_index :: "'self ⇒ 'idx ⇒ 'output result"

(* Trait declaration: [core::ops::index::IndexMut] *)
record ('self, 'idx, 'output) core_ops_index_IndexMut =
  core_ops_index_IndexMut_indexInst :: "('self, 'idx, 'output) core_ops_index_Index"
  core_ops_index_IndexMut_index_mut :: "'self ⇒ 'idx ⇒ ('output × ('output ⇒ 'self)) result"

(* Trait declaration [core::ops::deref::Deref] *)
record ('self, 'target) core_ops_deref_Deref =
  core_ops_deref_Deref_deref :: "'self ⇒ 'target result"

(* Trait declaration [core::ops::deref::DerefMut] *)
record ('self, 'target) core_ops_deref_DerefMut =
  core_ops_deref_DerefMut_derefInst :: "('self, 'target) core_ops_deref_Deref"
  core_ops_deref_DerefMut_deref_mut :: "'self ⇒ ('target × ('target ⇒ 'self)) result"

record 'a core_ops_range_Range =
  core_ops_range_Range_start :: 'a
  core_ops_range_Range_end_' :: 'a

(*** [alloc] *)

definition alloc_boxed_Box_deref :: "'a ⇒ 'a" where "alloc_boxed_Box_deref x = x"
definition alloc_boxed_Box_deref_mut :: "'a ⇒ 'a × ('a ⇒ 'a)" where
  "alloc_boxed_Box_deref_mut x = (x, (λy. y))"

definition alloc_boxed_Box_coreopsDerefInst :: "'a ⇒ ('a, 'a) core_ops_deref_Deref" where
  "alloc_boxed_Box_coreopsDerefInst _ = (|
    core_ops_deref_Deref_deref = (λx. Ok (alloc_boxed_Box_deref x))
  |)"

(* Names used by the builtin trait-instance table. *)
definition core_ops_deref_DerefBoxInst ::
  "('a, 'a) core_ops_deref_Deref" where
  "core_ops_deref_DerefBoxInst = (|
    core_ops_deref_Deref_deref = λx. return (alloc_boxed_Box_deref x)
  |)"

definition core_ops_deref_DerefBoxMutInst ::
  "('a, 'a) core_ops_deref_DerefMut" where
  "core_ops_deref_DerefBoxMutInst = (|
    core_ops_deref_DerefMut_derefInst = core_ops_deref_DerefBoxInst,
    core_ops_deref_DerefMut_deref_mut =
      λx. return (alloc_boxed_Box_deref_mut x)
  |)"


(*** Arrays / Slices / Vectors *)

(* We model arrays, slices and vectors as lists.  Rust's array length and the
   usize upper bound are not part of the Isabelle type, so operations which
   may observe a malformed value remain total and report [Failure]. *)
type_synonym 'a array = "'a list"
type_synonym 'a slice = "'a list"
type_synonym 'a alloc_vec_Vec = "'a list"

(** The length index of a Rust array is erased from its Isabelle type.  The
    generated semantic contracts use [array_wf n xs] to recover the source
    invariant at the proposition level. *)
definition array_wf :: "usize ⇒ 'a array ⇒ bool" where
  "array_wf n xs ⟷
    0 ≤ n ∧ n ≤ usize_max ∧ int (length xs) = n"

(* Arrays *)
definition mk_array :: "usize ⇒ 'a list ⇒ 'a array" where
  "mk_array _ xs = xs"
definition array_repeat :: "usize ⇒ 'a ⇒ 'a array" where
  "array_repeat n x = replicate (nat n) x"

(* Array lengths are erased from Isabelle types but remain explicit term
   arguments at call sites.  The primitive interfaces therefore accept the
   length and may use it for consistency checks in future refinements. *)
definition array_index_usize ::
  "usize ⇒ 'a array ⇒ usize ⇒ 'a result" where
  "array_index_usize _ a i =
    (if 0 ≤ i ∧ i < int (length a)
     then return (a ! nat i)
     else fail Failure)"

definition array_update_usize ::
  "usize ⇒ 'a array ⇒ usize ⇒ 'a ⇒ 'a array result" where
  "array_update_usize _ a i x =
    (if 0 ≤ i ∧ i < int (length a)
     then return (list_update a (nat i) x)
     else fail Failure)"

definition array_update ::
  "'a array ⇒ usize ⇒ 'a ⇒ 'a array" where
  "array_update a i x =
    (if 0 ≤ i ∧ i < int (length a)
     then list_update a (nat i) x
     else a)"

definition array_index_mut_usize ::
  "usize ⇒ 'a array ⇒ usize ⇒ ('a × ('a ⇒ 'a array)) result" where
  "array_index_mut_usize _ a i =
    (if 0 ≤ i ∧ i < int (length a)
     then return (a ! nat i, array_update a i)
     else fail Failure)"

(* Slices *)
definition slice_len :: "'a slice ⇒ usize" where
  "slice_len s =
    (let n = int (length s) in if n ≤ usize_max then n else 0)"

definition slice_index_usize :: "'a slice ⇒ usize ⇒ 'a result" where
  "slice_index_usize s i =
    (if 0 ≤ i ∧ i < int (length s)
     then return (s ! nat i)
     else fail Failure)"

definition slice_update_usize ::
  "'a slice ⇒ usize ⇒ 'a ⇒ 'a slice result" where
  "slice_update_usize s i x =
    (if 0 ≤ i ∧ i < int (length s)
     then return (list_update s (nat i) x)
     else fail Failure)"

definition slice_update ::
  "'a slice ⇒ usize ⇒ 'a ⇒ 'a slice" where
  "slice_update s i x =
    (if 0 ≤ i ∧ i < int (length s)
     then list_update s (nat i) x
     else s)"

definition slice_index_mut_usize :: "'a slice ⇒ usize ⇒ ('a × ('a ⇒ 'a slice)) result" where
  "slice_index_mut_usize s i =
    (if 0 ≤ i ∧ i < int (length s)
     then return (s ! nat i, slice_update s i)
     else fail Failure)"

(* Subslices *)
definition array_to_slice :: "usize ⇒ 'a array ⇒ 'a slice" where
  "array_to_slice _ a = a"
definition array_from_slice :: "'a array ⇒ 'a slice ⇒ 'a array" where "array_from_slice _ s = s"

definition array_to_slice_mut ::
  "usize ⇒ 'a array ⇒ 'a slice × ('a slice ⇒ 'a array)" where
  "array_to_slice_mut n a = (array_to_slice n a, array_from_slice a)"

definition slice_range_valid ::
  "usize core_ops_range_Range ⇒ 'a slice ⇒ bool" where
  "slice_range_valid r s ⟷
    0 ≤ core_ops_range_Range_start r ∧
    core_ops_range_Range_start r ≤ core_ops_range_Range_end_' r ∧
    core_ops_range_Range_end_' r ≤ int (length s)"

definition slice_subslice ::
  "'a slice ⇒ usize core_ops_range_Range ⇒ 'a slice result" where
  "slice_subslice s r =
    (if slice_range_valid r s then
       return
         (take (nat (core_ops_range_Range_end_' r -
                     core_ops_range_Range_start r))
           (drop (nat (core_ops_range_Range_start r)) s))
     else fail Failure)"

definition slice_replace_range ::
  "'a slice ⇒ usize core_ops_range_Range ⇒ 'a slice ⇒ 'a slice" where
  "slice_replace_range s r ns =
    (if slice_range_valid r s ∧
        int (length ns) =
          core_ops_range_Range_end_' r - core_ops_range_Range_start r
     then
       take (nat (core_ops_range_Range_start r)) s @
       ns @
       drop (nat (core_ops_range_Range_end_' r)) s
     else s)"

definition slice_update_subslice ::
  "'a slice ⇒ usize core_ops_range_Range ⇒ 'a slice ⇒ 'a slice result" where
  "slice_update_subslice s r ns =
    (if slice_range_valid r s ∧
        int (length ns) =
          core_ops_range_Range_end_' r - core_ops_range_Range_start r
     then return (slice_replace_range s r ns)
     else fail Failure)"

definition array_subslice ::
  "'a array ⇒ usize core_ops_range_Range ⇒ 'a slice result" where
  "array_subslice a r = slice_subslice a r"

definition array_update_subslice ::
  "'a array ⇒ usize core_ops_range_Range ⇒ 'a slice ⇒ 'a array result" where
  "array_update_subslice a r ns = slice_update_subslice a r ns"

(* Vectors *)
definition alloc_vec_Vec_to_list :: "'a alloc_vec_Vec ⇒ 'a list" where
  "alloc_vec_Vec_to_list v = v"

definition alloc_vec_Vec_length :: "'a alloc_vec_Vec ⇒ int" where
  "alloc_vec_Vec_length v = int (length v)"

definition alloc_vec_Vec_new :: "'a alloc_vec_Vec" where
  "alloc_vec_Vec_new = []"

(* [Vec::len] is registered as [-canFail -lift], hence it must be a pure
   [usize], not a [usize result]. *)
definition alloc_vec_Vec_len :: "'a alloc_vec_Vec ⇒ usize" where
  "alloc_vec_Vec_len v =
    (let n = int (length v) in if n ≤ usize_max then n else 0)"

definition alloc_vec_Vec_push :: "'a alloc_vec_Vec ⇒ 'a ⇒ ('a alloc_vec_Vec) result" where
  "alloc_vec_Vec_push v x =
    (let l = v @ [x] in
     if int (length l) ≤ usize_max then return l else fail OutOfFuel)"

definition alloc_vec_Vec_insert :: "'a alloc_vec_Vec ⇒ usize ⇒ 'a ⇒ ('a alloc_vec_Vec) result" where
  "alloc_vec_Vec_insert v i x =
    (if 0 ≤ i ∧ i < int (length v)
     then return (list_update v (nat i) x)
     else fail Failure)"

definition alloc_vec_Vec_index_usize ::
  "'a alloc_vec_Vec ⇒ usize ⇒ 'a result" where
  "alloc_vec_Vec_index_usize v i =
    (if 0 ≤ i ∧ i < int (length v)
     then return (v ! nat i)
     else fail Failure)"

definition alloc_vec_Vec_update_usize ::
  "'a alloc_vec_Vec ⇒ usize ⇒ 'a ⇒ 'a alloc_vec_Vec result" where
  "alloc_vec_Vec_update_usize v i x =
    (if 0 ≤ i ∧ i < int (length v)
     then return (list_update v (nat i) x)
     else fail Failure)"

definition alloc_vec_Vec_update ::
  "'a alloc_vec_Vec ⇒ usize ⇒ 'a ⇒ 'a alloc_vec_Vec" where
  "alloc_vec_Vec_update v i x =
    (if 0 ≤ i ∧ i < int (length v)
     then list_update v (nat i) x
     else v)"

definition alloc_vec_Vec_index_mut_usize :: "'a alloc_vec_Vec ⇒ usize ⇒ ('a × ('a ⇒ 'a alloc_vec_Vec)) result" where
  "alloc_vec_Vec_index_mut_usize v i =
    (if 0 ≤ i ∧ i < int (length v)
     then return (v ! nat i, alloc_vec_Vec_update v i)
     else fail Failure)"

definition alloc_vec_Vec_with_capacity ::
  "usize ⇒ 'a alloc_vec_Vec" where
  "alloc_vec_Vec_with_capacity _ = alloc_vec_Vec_new"

definition alloc_vec_Vec_deref ::
  "'a alloc_vec_Vec ⇒ 'a slice" where
  "alloc_vec_Vec_deref v = v"

definition alloc_vec_Vec_deref_mut ::
  "'a alloc_vec_Vec ⇒ 'a slice × ('a slice ⇒ 'a alloc_vec_Vec)" where
  "alloc_vec_Vec_deref_mut v = (v, λs. s)"

definition core_slice_Slice_reverse ::
  "'a slice ⇒ 'a slice" where
  "core_slice_Slice_reverse s = rev s"

fun alloc_slice_Slice_to_vec ::
  "'a core_clone_Clone ⇒ 'a slice ⇒ 'a alloc_vec_Vec result" where
  "alloc_slice_Slice_to_vec clone_inst [] = return []"
| "alloc_slice_Slice_to_vec clone_inst (x # xs) =
    (core_clone_Clone_clone clone_inst x >>= (λy.
     alloc_slice_Slice_to_vec clone_inst xs >>= (λys.
     return (y # ys))))"

(* Trait declaration: [core::slice::index::private_slice_index::Sealed] *)
record 'self core_slice_index_private_slice_index_Sealed =
  core_slice_index_private_slice_index_Sealed_dummy :: unit

(* Trait declaration: [core::slice::index::SliceIndex] *)
record ('self, 'T, 'output) core_slice_index_SliceIndex =
  sealedInst :: "'self core_slice_index_private_slice_index_Sealed"
  core_slice_index_SliceIndex_get :: "'self ⇒ 'T ⇒ 'output option result"
  core_slice_index_SliceIndex_get_mut :: "'self ⇒ 'T ⇒ ('output option × ('output option ⇒ 'T)) result"
  core_slice_index_SliceIndex_get_unchecked :: "'self ⇒ 'T const_raw_ptr ⇒ 'output const_raw_ptr result"
  core_slice_index_SliceIndex_get_unchecked_mut :: "'self ⇒ 'T mut_raw_ptr ⇒ 'output mut_raw_ptr result"
  core_slice_index_SliceIndex_index :: "'self ⇒ 'T ⇒ 'output result"
  core_slice_index_SliceIndex_index_mut :: "'self ⇒ 'T ⇒ ('output × ('output ⇒ 'T)) result"

(* [core::slice::[T]::get/get_mut] and the Index/IndexMut methods. *)
definition core_slice_Slice_get ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex ⇒
   'a slice ⇒ 'idx ⇒ 'output option result" where
  "core_slice_Slice_get inst s i =
    core_slice_index_SliceIndex_get inst i s"

definition core_slice_Slice_get_mut ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex ⇒
   'a slice ⇒ 'idx ⇒
   ('output option × ('output option ⇒ 'a slice)) result" where
  "core_slice_Slice_get_mut inst s i =
    core_slice_index_SliceIndex_get_mut inst i s"

definition core_slice_index_Slice_index ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex ⇒
   'a slice ⇒ 'idx ⇒ 'output result" where
  "core_slice_index_Slice_index inst s i =
    core_slice_index_SliceIndex_index inst i s"

definition core_slice_index_Slice_index_mut ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex ⇒
   'a slice ⇒ 'idx ⇒ ('output × ('output ⇒ 'a slice)) result" where
  "core_slice_index_Slice_index_mut inst s i =
    core_slice_index_SliceIndex_index_mut inst i s"

(* [SliceIndex<Range<usize>, [T]>]. *)
definition core_slice_index_SliceIndexRangeUsizeSlice_get ::
  "usize core_ops_range_Range ⇒ 'a slice ⇒ 'a slice option result" where
  "core_slice_index_SliceIndexRangeUsizeSlice_get r s =
    (if slice_range_valid r s
     then slice_subslice s r >>= (λss. return (Some ss))
     else return None)"

definition core_slice_index_SliceIndexRangeUsizeSlice_get_mut ::
  "usize core_ops_range_Range ⇒ 'a slice ⇒
   ('a slice option × ('a slice option ⇒ 'a slice)) result" where
  "core_slice_index_SliceIndexRangeUsizeSlice_get_mut r s =
    (if slice_range_valid r s then
       slice_subslice s r >>= (λss.
       return
         (Some ss,
          λnss. case nss of
             None ⇒ s
           | Some ys ⇒ slice_replace_range s r ys))
     else return (None, λ_. s))"

definition core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked ::
  "usize core_ops_range_Range ⇒
   'a slice const_raw_ptr ⇒ 'a slice const_raw_ptr result" where
  "core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked _ _ =
    fail Failure"

definition core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked_mut ::
  "usize core_ops_range_Range ⇒
   'a slice mut_raw_ptr ⇒ 'a slice mut_raw_ptr result" where
  "core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked_mut _ _ =
    fail Failure"

definition core_slice_index_SliceIndexRangeUsizeSlice_index ::
  "usize core_ops_range_Range ⇒ 'a slice ⇒ 'a slice result" where
  "core_slice_index_SliceIndexRangeUsizeSlice_index r s =
    slice_subslice s r"

definition core_slice_index_SliceIndexRangeUsizeSlice_index_mut ::
  "usize core_ops_range_Range ⇒ 'a slice ⇒
   ('a slice × ('a slice ⇒ 'a slice)) result" where
  "core_slice_index_SliceIndexRangeUsizeSlice_index_mut r s =
    (slice_subslice s r >>= (λss.
     return (ss, slice_replace_range s r)))"

definition core_slice_index_private_slice_index_SealedRangeUsizeInst
  :: "usize core_ops_range_Range core_slice_index_private_slice_index_Sealed"
  where "core_slice_index_private_slice_index_SealedRangeUsizeInst =
    (| core_slice_index_private_slice_index_Sealed_dummy = () |)"

definition core_slice_index_SliceIndexRangeUsizeSliceInst ::
  "(usize core_ops_range_Range, 'a slice, 'a slice)
   core_slice_index_SliceIndex" where
  "core_slice_index_SliceIndexRangeUsizeSliceInst = (|
    sealedInst = core_slice_index_private_slice_index_SealedRangeUsizeInst,
    core_slice_index_SliceIndex_get = core_slice_index_SliceIndexRangeUsizeSlice_get,
    core_slice_index_SliceIndex_get_mut = core_slice_index_SliceIndexRangeUsizeSlice_get_mut,
    core_slice_index_SliceIndex_get_unchecked = core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked,
    core_slice_index_SliceIndex_get_unchecked_mut = core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked_mut,
    core_slice_index_SliceIndex_index = core_slice_index_SliceIndexRangeUsizeSlice_index,
    core_slice_index_SliceIndex_index_mut = core_slice_index_SliceIndexRangeUsizeSlice_index_mut
  |)"

(* Slice and array Index/IndexMut instances. *)
definition core_ops_index_IndexSliceInst ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex ⇒
   ('a slice, 'idx, 'output) core_ops_index_Index" where
  "core_ops_index_IndexSliceInst inst = (|
    core_ops_index_Index_index = core_slice_index_Slice_index inst
  |)"

definition core_ops_index_IndexMutSliceInst ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex ⇒
   ('a slice, 'idx, 'output) core_ops_index_IndexMut" where
  "core_ops_index_IndexMutSliceInst inst = (|
    core_ops_index_IndexMut_indexInst = core_ops_index_IndexSliceInst inst,
    core_ops_index_IndexMut_index_mut = core_slice_index_Slice_index_mut inst
  |)"

definition core_array_Array_index ::
  "usize ⇒ ('a slice, 'idx, 'output) core_ops_index_Index ⇒
   'a array ⇒ 'idx ⇒ 'output result" where
  "core_array_Array_index _ inst a i =
    core_ops_index_Index_index inst a i"

definition core_array_Array_index_mut ::
  "usize ⇒ ('a slice, 'idx, 'output) core_ops_index_IndexMut ⇒
   'a array ⇒ 'idx ⇒ ('output × ('output ⇒ 'a array)) result" where
  "core_array_Array_index_mut _ inst a i =
    core_ops_index_IndexMut_index_mut inst a i"

definition core_ops_index_IndexArrayInst ::
  "usize ⇒ ('a slice, 'idx, 'output) core_ops_index_Index ⇒
   ('a array, 'idx, 'output) core_ops_index_Index" where
  "core_ops_index_IndexArrayInst n inst = (|
    core_ops_index_Index_index = core_array_Array_index n inst
  |)"

definition core_ops_index_IndexMutArrayInst ::
  "usize ⇒ ('a slice, 'idx, 'output) core_ops_index_IndexMut ⇒
   ('a array, 'idx, 'output) core_ops_index_IndexMut" where
  "core_ops_index_IndexMutArrayInst n inst = (|
    core_ops_index_IndexMut_indexInst =
      core_ops_index_IndexArrayInst n
        (core_ops_index_IndexMut_indexInst inst),
    core_ops_index_IndexMut_index_mut = core_array_Array_index_mut n inst
  |)"

(* [SliceIndex<usize, [T]>]. *)
definition core_slice_index_usize_get ::
  "usize ⇒ 'a slice ⇒ 'a option result" where
  "core_slice_index_usize_get i s =
    return
      (if 0 ≤ i ∧ i < int (length s)
       then Some (s ! nat i)
       else None)"

definition core_slice_index_usize_get_mut ::
  "usize ⇒ 'a slice ⇒ ('a option × ('a option ⇒ 'a slice)) result" where
  "core_slice_index_usize_get_mut i s =
    return
      (if 0 ≤ i ∧ i < int (length s)
       then
         (Some (s ! nat i),
          λx. case x of None ⇒ s | Some y ⇒ slice_update s i y)
       else (None, λ_. s))"

definition core_slice_index_usize_get_unchecked ::
  "usize ⇒ 'a slice const_raw_ptr ⇒ 'a const_raw_ptr result" where
  "core_slice_index_usize_get_unchecked _ _ = fail Failure"

definition core_slice_index_usize_get_unchecked_mut ::
  "usize ⇒ 'a slice mut_raw_ptr ⇒ 'a mut_raw_ptr result" where
  "core_slice_index_usize_get_unchecked_mut _ _ = fail Failure"

definition core_slice_index_usize_index ::
  "usize ⇒ 'a slice ⇒ 'a result" where
  "core_slice_index_usize_index i s = slice_index_usize s i"

definition core_slice_index_usize_index_mut ::
  "usize ⇒ 'a slice ⇒ ('a × ('a ⇒ 'a slice)) result" where
  "core_slice_index_usize_index_mut i s = slice_index_mut_usize s i"

definition core_slice_index_private_slice_index_SealedUsizeInst ::
  "usize core_slice_index_private_slice_index_Sealed" where
  "core_slice_index_private_slice_index_SealedUsizeInst =
    (| core_slice_index_private_slice_index_Sealed_dummy = () |)"

definition core_slice_index_SliceIndexUsizeSliceInst ::
  "(usize, 'a slice, 'a) core_slice_index_SliceIndex" where
  "core_slice_index_SliceIndexUsizeSliceInst = (|
    sealedInst = core_slice_index_private_slice_index_SealedUsizeInst,
    core_slice_index_SliceIndex_get = core_slice_index_usize_get,
    core_slice_index_SliceIndex_get_mut = core_slice_index_usize_get_mut,
    core_slice_index_SliceIndex_get_unchecked =
      core_slice_index_usize_get_unchecked,
    core_slice_index_SliceIndex_get_unchecked_mut =
      core_slice_index_usize_get_unchecked_mut,
    core_slice_index_SliceIndex_index = core_slice_index_usize_index,
    core_slice_index_SliceIndex_index_mut = core_slice_index_usize_index_mut
  |)"

(* Vec uses the same list representation as Slice, so generic indexing can
   delegate directly to the supplied SliceIndex implementation. *)
definition alloc_vec_Vec_index ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex ⇒
   'a alloc_vec_Vec ⇒ 'idx ⇒ 'output result" where
  "alloc_vec_Vec_index inst v i =
    core_slice_index_SliceIndex_index inst i v"

definition alloc_vec_Vec_index_mut ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex ⇒
   'a alloc_vec_Vec ⇒ 'idx ⇒
   ('output × ('output ⇒ 'a alloc_vec_Vec)) result" where
  "alloc_vec_Vec_index_mut inst v i =
    core_slice_index_SliceIndex_index_mut inst i v"

definition alloc_vec_Vec_IndexInst ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex ⇒
   ('a alloc_vec_Vec, 'idx, 'output) core_ops_index_Index" where
  "alloc_vec_Vec_IndexInst inst = (|
    core_ops_index_Index_index = alloc_vec_Vec_index inst
  |)"

definition alloc_vec_Vec_IndexMutInst ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex ⇒
   ('a alloc_vec_Vec, 'idx, 'output) core_ops_index_IndexMut" where
  "alloc_vec_Vec_IndexMutInst inst = (|
    core_ops_index_IndexMut_indexInst = alloc_vec_Vec_IndexInst inst,
    core_ops_index_IndexMut_index_mut = alloc_vec_Vec_index_mut inst
  |)"

definition core_ops_deref_DerefVecInst ::
  "('a alloc_vec_Vec, 'a slice) core_ops_deref_Deref" where
  "core_ops_deref_DerefVecInst = (|
    core_ops_deref_Deref_deref = λv. return (alloc_vec_Vec_deref v)
  |)"

definition core_ops_deref_DerefMutVecInst ::
  "('a alloc_vec_Vec, 'a slice) core_ops_deref_DerefMut" where
  "core_ops_deref_DerefMutVecInst = (|
    core_ops_deref_DerefMut_derefInst = core_ops_deref_DerefVecInst,
    core_ops_deref_DerefMut_deref_mut =
      λv. return (alloc_vec_Vec_deref_mut v)
  |)"

definition alloc_vec_DerefVec ::
  "('a alloc_vec_Vec, 'a slice) core_ops_deref_Deref" where
  "alloc_vec_DerefVec = core_ops_deref_DerefVecInst"

definition alloc_vec_DerefMutVec ::
  "('a alloc_vec_Vec, 'a slice) core_ops_deref_DerefMut" where
  "alloc_vec_DerefMutVec = core_ops_deref_DerefMutVecInst"

end
