(* This file provides the foundational definitions for the Isabelle/HOL backend. *)

theory Primitives
  imports
    Main
    "HOL-Library.Word" (* For eventual bitwise ops *)
    (*"HOL-Library.String"
    "HOL-Library.Code_Char" *)
begin

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

definition return :: "'a ⇒ 'a result" where
  "return x ≡ Ok x"

definition fail :: "error ⇒ 'a result" where
  "fail e ≡ Fail e"

fun bind :: "'a result ⇒ ('a ⇒ 'b result) ⇒ 'b result" (infixl ">>=" 55) where
  "bind (Fail e) f = Fail e"
| "bind (Ok x) f = f x"

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
type_synonym char = char

(*
definition char_of_byte :: "Word.word8 ⇒ char" where
  "char_of_byte = Code_Char.char_of_byte" *)

definition core_mem_replace :: "'a ⇒ 'a ⇒ ('a × 'a)" where
  "core_mem_replace x y ≡ (x, x)"

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

definition usize_min :: int where "usize_min = 0"

axiomatization isize_min :: int and isize_max :: int and usize_max :: int
where
  isize_min_bound: "isize_min ≤ i32_min" and
  isize_max_bound: "i32_max ≤ isize_max" and
  usize_min_bound: "usize_min = 0" and
  usize_max_bound: "u32_max ≤ usize_max"


datatype scalar_ty =
    Isize | I8 | I16 | I32 | I64 | I128 |
    Usize | U8 | U16 | U32 | U64 | U128

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


(* Scalar operations *)
definition scalar_add :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_add ty x y ≡ mk_scalar ty (x + y)"
definition scalar_sub :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_sub ty x y ≡ mk_scalar ty (x - y)"
definition scalar_mul :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_mul ty x y ≡ mk_scalar ty (x * y)"
definition scalar_div :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_div ty x y ≡ if y = 0 then fail Failure else mk_scalar ty (x div y)"
definition scalar_rem :: "scalar_ty ⇒ int ⇒ int ⇒ int result" where
  "scalar_rem ty x y ≡ if y = 0 then fail Failure else mk_scalar ty (x mod y)"
definition scalar_neg :: "scalar_ty ⇒ int ⇒ int result" where
  "scalar_neg ty x ≡ mk_scalar ty (- x)"
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

(* Axiomatized bitwise operations *)
axiomatization scalar_xor :: "scalar_ty ⇒ int ⇒ int ⇒ int result"
axiomatization scalar_or  :: "scalar_ty ⇒ int ⇒ int ⇒ int result"
axiomatization scalar_and :: "scalar_ty ⇒ int ⇒ int ⇒ int result"
axiomatization scalar_shl :: "scalar_ty ⇒ scalar_ty ⇒ int ⇒ int ⇒ int result"
axiomatization scalar_shr :: "scalar_ty ⇒ scalar_ty ⇒ int ⇒ int ⇒ int result"
axiomatization scalar_not :: "scalar_ty ⇒ int ⇒ int result"

(* Casts *)
definition scalar_cast :: "scalar_ty ⇒ scalar_ty ⇒ int ⇒ int result" where
  "scalar_cast _ tgt_ty x ≡ mk_scalar tgt_ty x"

definition scalar_cast_bool :: "scalar_ty ⇒ bool ⇒ int result" where
  "scalar_cast_bool tgt_ty b ≡ mk_scalar tgt_ty (if b then 1 else 0)"

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
definition u8_xor :: "int ⇒ int ⇒ int result" where 
  "u8_xor = scalar_xor U8"
definition u16_xor :: "int ⇒ int ⇒ int result" where 
  "u16_xor = scalar_xor U16"
definition u32_xor :: "int ⇒ int ⇒ int result" where 
  "u32_xor = scalar_xor U32"
definition u64_xor :: "int ⇒ int ⇒ int result" where 
  "u64_xor = scalar_xor U64"
definition u128_xor :: "int ⇒ int ⇒ int result" where 
  "u128_xor = scalar_xor U128"
definition usize_xor :: "int ⇒ int ⇒ int result" where 
  "usize_xor = scalar_xor Usize"
definition i8_xor :: "int ⇒ int ⇒ int result" where 
  "i8_xor = scalar_xor I8"
definition i16_xor :: "int ⇒ int ⇒ int result" where 
  "i16_xor = scalar_xor I16"
definition i32_xor :: "int ⇒ int ⇒ int result" where 
  "i32_xor = scalar_xor I32"
definition i64_xor :: "int ⇒ int ⇒ int result" where 
  "i64_xor = scalar_xor I64"
definition i128_xor :: "int ⇒ int ⇒ int result" where 
  "i128_xor = scalar_xor I128"
definition isize_xor :: "int ⇒ int ⇒ int result" where 
  "isize_xor = scalar_xor Isize"

(* Or Op *)
definition u8_or :: "int ⇒ int ⇒ int result" where 
  "u8_or = scalar_or U8"
definition u16_or :: "int ⇒ int ⇒ int result" where 
  "u16_or = scalar_or U16"
definition u32_or :: "int ⇒ int ⇒ int result" where 
  "u32_or = scalar_or U32"
definition u64_or :: "int ⇒ int ⇒ int result" where 
  "u64_or = scalar_or U64"
definition u128_or :: "int ⇒ int ⇒ int result" where 
  "u128_or = scalar_or U128"
definition usize_or :: "int ⇒ int ⇒ int result" where 
  "usize_or = scalar_or Usize"
definition i8_or :: "int ⇒ int ⇒ int result" where 
  "i8_or = scalar_or I8"
definition i16_or :: "int ⇒ int ⇒ int result" where 
  "i16_or = scalar_or I16"
definition i32_or :: "int ⇒ int ⇒ int result" where 
  "i32_or = scalar_or I32"
definition i64_or :: "int ⇒ int ⇒ int result" where 
  "i64_or = scalar_or I64"
definition i128_or :: "int ⇒ int ⇒ int result" where 
  "i128_or = scalar_or I128"
definition isize_or :: "int ⇒ int ⇒ int result" where 
  "isize_or = scalar_or Isize"

(* And Op *)
definition u8_and :: "int ⇒ int ⇒ int result" where 
  "u8_and = scalar_and U8"
definition u16_and :: "int ⇒ int ⇒ int result" where 
  "u16_and = scalar_and U16"
definition u32_and :: "int ⇒ int ⇒ int result" where 
  "u32_and = scalar_and U32"
definition u64_and :: "int ⇒ int ⇒ int result" where 
  "u64_and = scalar_and U64"
definition u128_and :: "int ⇒ int ⇒ int result" where 
  "u128_and = scalar_and U128"
definition usize_and :: "int ⇒ int ⇒ int result" where 
  "usize_and = scalar_and Usize"
definition i8_and :: "int ⇒ int ⇒ int result" where 
  "i8_and = scalar_and I8"
definition i16_and :: "int ⇒ int ⇒ int result" where 
  "i16_and = scalar_and I16"
definition i32_and :: "int ⇒ int ⇒ int result" where 
  "i32_and = scalar_and I32"
definition i64_and :: "int ⇒ int ⇒ int result" where 
  "i64_and = scalar_and I64"
definition i128_and :: "int ⇒ int ⇒ int result" where 
  "i128_and = scalar_and I128"
definition isize_and :: "int ⇒ int ⇒ int result" where 
  "isize_and = scalar_and Isize"

(* Shift Left Op *)
definition u8_shl :: "int ⇒ int ⇒ int result" where 
  "u8_shl = scalar_shl U8 U8"
definition u16_shl :: "int ⇒ int ⇒ int result" where 
  "u16_shl = scalar_shl U16 U8"
definition u32_shl :: "int ⇒ int ⇒ int result" where 
  "u32_shl = scalar_shl U32 U8"
definition u64_shl :: "int ⇒ int ⇒ int result" where 
  "u64_shl = scalar_shl U64 U8"
definition u128_shl :: "int ⇒ int ⇒ int result" where 
  "u128_shl = scalar_shl U128 U8"
definition usize_shl :: "int ⇒ int ⇒ int result" where 
  "usize_shl = scalar_shl Usize U8"
definition i8_shl :: "int ⇒ int ⇒ int result" where 
  "i8_shl = scalar_shl I8 U8"
definition i16_shl :: "int ⇒ int ⇒ int result" where 
  "i16_shl = scalar_shl I16 U8"
definition i32_shl :: "int ⇒ int ⇒ int result" where 
  "i32_shl = scalar_shl I32 U8"
definition i64_shl :: "int ⇒ int ⇒ int result" where 
  "i64_shl = scalar_shl I64 U8"
definition i128_shl :: "int ⇒ int ⇒ int result" where 
  "i128_shl = scalar_shl I128 U8"
definition isize_shl :: "int ⇒ int ⇒ int result" where 
  "isize_shl = scalar_shl Isize U8"

(* Shift Right Op *)
definition u8_shr :: "int ⇒ int ⇒ int result" where 
  "u8_shr = scalar_shr U8 U8"
definition u16_shr :: "int ⇒ int ⇒ int result" where 
  "u16_shr = scalar_shr U16 U8"
definition u32_shr :: "int ⇒ int ⇒ int result" where 
  "u32_shr = scalar_shr U32 U8"
definition u64_shr :: "int ⇒ int ⇒ int result" where 
  "u64_shr = scalar_shr U64 U8"
definition u128_shr :: "int ⇒ int ⇒ int result" where 
  "u128_shr = scalar_shr U128 U8"
definition usize_shr :: "int ⇒ int ⇒ int result" where 
  "usize_shr = scalar_shr Usize U8"
definition i8_shr :: "int ⇒ int ⇒ int result" where 
  "i8_shr = scalar_shr I8 U8"
definition i16_shr :: "int ⇒ int ⇒ int result" where 
  "i16_shr = scalar_shr I16 U8"
definition i32_shr :: "int ⇒ int ⇒ int result" where 
  "i32_shr = scalar_shr I32 I8"
definition i64_shr :: "int ⇒ int ⇒ int result" where 
  "i64_shr = scalar_shr I64 U8"
definition i128_shr :: "int ⇒ int ⇒ int result" where 
  "i128_shr = scalar_shr I128 U8"
definition isize_shr :: "int ⇒ int ⇒ int result" where 
  "isize_shr = scalar_shr Isize U8"

(* Not Op *)
definition u8_not :: "int ⇒ int result" where 
  "u8_not = scalar_not U8"
definition u16_not :: "int ⇒ int result" where 
  "u16_not = scalar_not U16"
definition u32_not :: "int ⇒ int result" where 
  "u32_not = scalar_not U32"
definition u64_not :: "int ⇒ int result" where 
  "u64_not = scalar_not U64"
definition u128_not :: "int ⇒ int result" where 
  "u128_not = scalar_not U128"
definition usize_not :: "int ⇒ int result" where 
  "usize_not = scalar_not Usize"
definition i8_not :: "int ⇒ int result" where 
  "i8_not = scalar_not I8"
definition i16_not :: "int ⇒ int result" where 
  "i16_not = scalar_not I16"
definition i32_not :: "int ⇒ int result" where 
  "i32_not = scalar_not I32"
definition i64_not :: "int ⇒ int result" where 
  "i64_not = scalar_not I64"
definition i128_not :: "int ⇒ int result" where 
  "i128_not = scalar_not I128"
definition isize_not :: "int ⇒ int result" where 
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
  core_ops_range_Range_end_ :: 'a

(*** [alloc] *)

definition alloc_boxed_Box_deref :: "'a ⇒ 'a" where "alloc_boxed_Box_deref x = x"
definition alloc_boxed_Box_deref_mut :: "'a ⇒ 'a × ('a ⇒ 'a)" where
  "alloc_boxed_Box_deref_mut x = (x, (λy. y))"

definition alloc_boxed_Box_coreopsDerefInst :: "'a ⇒ ('a, 'a) core_ops_deref_Deref" where
  "alloc_boxed_Box_coreopsDerefInst _ = (|
    core_ops_deref_Deref_deref = (λx. Ok (alloc_boxed_Box_deref x))
  |)"

(*
definition alloc_boxed_Box_coreopsDerefMutInst :: "'a ⇒ ('a, 'a) core_ops_deref_DerefMut" where
  "alloc_boxed_Box_coreopsDerefMutInst x = (|
    core_ops_deref_DerefMut_derefInst = alloc_boxed_Box_coreopsDerefInst (),
    core_ops_deref_DerefMut_deref_mut = (λx. Ok (alloc_boxed_Box_deref_mut x))
  |)" *)


(*** Arrays / Slices / Vectors *)

(* We model all of these as simple lists for now *)
type_synonym 'a array = "'a list"
type_synonym 'a slice = "'a list"
type_synonym 'a alloc_vec_Vec = "'a list"

(* Arrays *)
axiomatization mk_array :: "usize ⇒ 'a list ⇒ 'a array result"
axiomatization array_repeat :: "usize ⇒ 'a ⇒ 'a array result"
axiomatization array_index_usize :: "'a array ⇒ usize ⇒ 'a result"
axiomatization array_update_usize :: "'a array ⇒ usize ⇒ 'a ⇒ 'a array result"

axiomatization array_index_mut_usize :: "'a array ⇒ usize ⇒ ('a × ('a ⇒ 'a array)) result"
(*
primrec (nonexhaustive) array_index_mut_usize :: "'a array ⇒ usize ⇒ ('a × ('a ⇒ 'a array)) result" where
  "array_index_mut_usize a i = (
    array_index_usize a i >>= (λx.
    return (x, (λnx. (case array_update_usize a i nx of Ok a' ⇒ a'))) 
  ))" *)
(* | Fail e ⇒ undefined (* Or panics *) *)

(* Slices *)
definition slice_len :: "'a slice ⇒ usize" where
  "slice_len s = (let n = of_nat (length s) in if  n ≤ usize_max then n else 0  )" (* Should be safe *)
axiomatization slice_index_usize :: "'a slice ⇒ usize ⇒ 'a result"
axiomatization slice_update_usize :: "'a slice ⇒ usize ⇒ 'a ⇒ 'a slice result"

definition slice_index_mut_usize :: "'a slice ⇒ usize ⇒ ('a × ('a ⇒ 'a slice)) result" where
  "slice_index_mut_usize s i = (
    slice_index_usize s i >>= (λx.
    return (x, (λnx. (case slice_update_usize s i nx of Ok s' ⇒ s' | Fail e ⇒ undefined)))
  ))"

(* Subslices *)
definition array_to_slice :: "'a array ⇒ 'a slice" where "array_to_slice a = a"
definition array_from_slice :: "'a array ⇒ 'a slice ⇒ 'a array" where "array_from_slice _ s = s"

definition array_to_slice_mut :: "'a array ⇒ 'a slice × ('a slice ⇒ 'a array)" where
  "array_to_slice_mut a = (array_to_slice a, array_from_slice a)"

axiomatization array_subslice :: "'a array ⇒ 'a core_ops_range_Range ⇒ 'a slice result"
axiomatization array_update_subslice :: "'a array ⇒ 'a core_ops_range_Range ⇒ 'a slice ⇒ 'a array result"
axiomatization slice_subslice :: "'a slice ⇒ 'a core_ops_range_Range ⇒ 'a slice result"
axiomatization slice_update_subslice :: "'a slice ⇒ 'a core_ops_range_Range ⇒ 'a slice ⇒ 'a slice result"

(* Vectors *)
definition alloc_vec_Vec_to_list :: "'a alloc_vec_Vec ⇒ 'a list" where "alloc_vec_Vec_to_list v = v"
definition alloc_vec_Vec_length :: "'a alloc_vec_Vec ⇒ int" where "alloc_vec_Vec_length v = of_nat (length v)"
definition alloc_vec_Vec_new :: "'a alloc_vec_Vec" where "alloc_vec_Vec_new = []"

definition alloc_vec_Vec_len :: "'a alloc_vec_Vec ⇒ usize result" where
  "alloc_vec_Vec_len v = mk_usize (of_nat (length v))"

definition alloc_vec_Vec_push :: "'a alloc_vec_Vec ⇒ 'a ⇒ ('a alloc_vec_Vec) result" where
  "alloc_vec_Vec_push v x = (
    let l = v @ [x] in
    if of_nat (length l) ≤ usize_max then return l else fail OutOfFuel
  )"

definition alloc_vec_Vec_insert :: "'a alloc_vec_Vec ⇒ usize ⇒ 'a ⇒ ('a alloc_vec_Vec) result" where
  "alloc_vec_Vec_insert v i x = (
    if i < of_nat (length v) then return (list_update v (nat i) x)
    else fail Failure
  )"

axiomatization alloc_vec_Vec_index_usize :: "'a alloc_vec_Vec ⇒ usize ⇒ 'a result"
axiomatization alloc_vec_Vec_update_usize :: "'a alloc_vec_Vec ⇒ usize ⇒ 'a ⇒ 'a alloc_vec_Vec result"

definition alloc_vec_Vec_index_mut_usize :: "'a alloc_vec_Vec ⇒ usize ⇒ ('a × ('a ⇒ 'a alloc_vec_Vec)) result" where
  "alloc_vec_Vec_index_mut_usize v i = (
    alloc_vec_Vec_index_usize v i >>= (λx.
    return (x, (λnx. (case alloc_vec_Vec_update_usize v i nx of Ok v' ⇒ v' | Fail e ⇒ undefined)))
  ))"

(* Trait declaration: [core::slice::index::private_slice_index::Sealed] *)
type_synonym 'self core_slice_index_private_slice_index_Sealed = unit

(* Trait declaration: [core::slice::index::SliceIndex] *)
record ('self, 'T, 'output) core_slice_index_SliceIndex =
  core_slice_index_SliceIndex_sealedInst :: "'self core_slice_index_private_slice_index_Sealed"
  core_slice_index_SliceIndex_get :: "'self ⇒ 'T ⇒ 'output option result"
  core_slice_index_SliceIndex_get_mut :: "'self ⇒ 'T ⇒ ('output option × ('output option ⇒ 'T)) result"
  core_slice_index_SliceIndex_get_unchecked :: "'self ⇒ 'T const_raw_ptr ⇒ 'output const_raw_ptr result"
  core_slice_index_SliceIndex_get_unchecked_mut :: "'self ⇒ 'T mut_raw_ptr ⇒ 'output mut_raw_ptr result"
  core_slice_index_SliceIndex_index :: "'self ⇒ 'T ⇒ 'output result"
  core_slice_index_SliceIndex_index_mut :: "'self ⇒ 'T ⇒ ('output × ('output ⇒ 'T)) result"

(* ... All the SliceIndex implementations ... *)
(* This part is highly complex and depends on many axioms. *)
(* We'll provide axioms and instances similar to Coq. *)

axiomatization core_slice_index_Slice_index
  :: "('idx, 'a slice, 'output) core_slice_index_SliceIndex ⇒ 'a slice ⇒ 'idx ⇒ 'output result"
axiomatization core_slice_index_Slice_index_mut
  :: "('idx, 'a slice, 'output) core_slice_index_SliceIndex ⇒ 'a slice ⇒ 'idx ⇒ ('output × ('output ⇒ 'a slice)) result"

axiomatization core_slice_index_SliceIndexRangeUsizeSlice_get
  :: "'a core_ops_range_Range ⇒ 'a slice ⇒ 'a slice option result"
axiomatization core_slice_index_SliceIndexRangeUsizeSlice_get_mut
  :: "'a core_ops_range_Range ⇒ 'a slice ⇒ ('a slice option × ('a slice option ⇒ 'a slice)) result"
axiomatization core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked
  :: "'a core_ops_range_Range ⇒ 'a slice const_raw_ptr ⇒ 'a slice const_raw_ptr result"
axiomatization core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked_mut
  :: "'a core_ops_range_Range ⇒ 'a mut_raw_ptr ⇒ 'a mut_raw_ptr result"
axiomatization core_slice_index_SliceIndexRangeUsizeSlice_index
  :: "'a core_ops_range_Range ⇒ 'a slice ⇒ 'a slice result"
axiomatization core_slice_index_SliceIndexRangeUsizeSlice_index_mut
  :: "'a core_ops_range_Range ⇒ 'a slice ⇒ ('a slice × ('a slice ⇒ 'a slice)) result"

definition core_slice_index_private_slice_index_SealedRangeUsizeInst
  :: "usize core_ops_range_Range core_slice_index_private_slice_index_Sealed"
  where "core_slice_index_private_slice_index_SealedRangeUsizeInst = ()"

(*
definition core_slice_index_SliceIndexRangeUsizeSliceInst :: "'a ⇒ (usize core_ops_range_Range, 'a slice, 'a slice) core_slice_index_SliceIndex"
  where "core_slice_index_SliceIndexRangeUsizeSliceInst _ = (|
    core_slice_index_SliceIndex_sealedInst = core_slice_index_private_slice_index_SealedRangeUsizeInst,
    core_slice_index_SliceIndex_get = core_slice_index_SliceIndexRangeUsizeSlice_get,
    core_slice_index_SliceIndex_get_mut = core_slice_index_SliceIndexRangeUsizeSlice_get_mut,
    core_slice_index_SliceIndex_get_unchecked = core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked,
    core_slice_index_SliceIndex_get_unchecked_mut = core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked_mut,
    core_slice_index_SliceIndex_index = core_slice_index_SliceIndexRangeUsizeSlice_index,
    core_slice_index_SliceIndex_index_mut = core_slice_index_SliceIndexRangeUsizeSlice_index_mut
  |)" *)

(* ... and so on for all trait impls ... *)
(* This is a representative subset. *)

end