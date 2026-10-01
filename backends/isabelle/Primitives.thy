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

(** [Diverge] represents a non-terminating computation.  It is the bottom
    element of the flat order used to define recursive functions and loops
    as least fixed points (see [partial_function (result)] below), following
    the [Result.div] constructor of the Lean backend. *)
datatype 'a result =
    Ok 'a
  | Fail error
  | Diverge

definition return :: "'a \<Rightarrow> 'a result" where
  "return x \<equiv> Ok x"

definition fail :: "error \<Rightarrow> 'a result" where
  "fail e \<equiv> Fail e"

fun bind :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> 'b result" (infixl ">>=" 55) where
  "bind (Fail e) f = Fail e"
| "bind (Ok x) f = f x"
| "bind Diverge f = Diverge"

(** Lift a well-formedness predicate through the result monad.  This is used
    by generated contracts for erased const-generic indices: a successful
    result must satisfy the predicate, while a failure carries no value to
    check. *)
fun result_wf :: "('a \<Rightarrow> bool) \<Rightarrow> 'a result \<Rightarrow> bool" where
  "result_wf P (Ok x) = P x"
| "result_wf P (Fail e) = True"
| "result_wf P Diverge = True"

syntax
  "_do_bind" :: "[pttrn, 'a result, 'b result] \<Rightarrow> 'b result" 
    ("(2_ <- _;// _)" [0, 0, 10] 10)
translations
  "_do_bind x m e" \<rightleftharpoons> "CONST bind m (\<lambda>x. e)"

(** Monadic assert *)
definition massert :: "bool \<Rightarrow> unit result" where
  "massert b \<equiv> if b then return () else fail Failure"

(** Unwrap a successful result (used for globals). Panics on failure. *)
primrec (nonexhaustive) get_result :: "'a result \<Rightarrow> 'a" where
  "get_result (Ok x) = x" (*
| "get_result (Fail e) = undefined" *)

(*** Partial functions over the result monad

   Recursive Rust functions and loop bodies need not terminate, whereas every
   Isabelle/HOL definition must be total.  We therefore define them as least
   fixed points in the flat order whose bottom element is [Diverge], using
   Isabelle's [partial_function] command with a dedicated mode [result].  A
   non-terminating execution denotes [Diverge]; terminating executions are
   characterised by the unfolding equations ([f.simps]) that the command
   proves.  This mirrors [partial_fixpoint] in the Lean backend. *)

abbreviation "result_ord \<equiv> flat_ord Diverge"
abbreviation "mono_result \<equiv> monotone (fun_ord result_ord) result_ord"

interpretation result:
  partial_function_definitions "flat_ord Diverge" "flat_lub Diverge"
  rewrites "flat_lub Diverge {} \<equiv> Diverge"
  by (rule flat_interpretation) (simp add: flat_lub_def)

declaration \<open>Partial_Function.init "result" @{term result.fixp_fun}
  @{term result.mono_body} @{thm result.fixp_rule_uc} @{thm result.fixp_induct_uc}
  NONE\<close>

lemma result_bind_mono [partial_function_mono]:
  assumes mf: "mono_result B" and mg: "\<And>y. mono_result (\<lambda>f. C y f)"
  shows "mono_result (\<lambda>f. bind (B f) (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b result" assume fg: "fun_ord result_ord f g"
  with mf have "result_ord (B f) (B g)" by (rule monotoneD[of _ _ _ f g])
  then have "result_ord (bind (B f) (\<lambda>y. C y f)) (bind (B g) (\<lambda>y. C y f))"
    unfolding flat_ord_def by auto
  also from mg have "\<And>y'. result_ord (C y' f) (C y' g)"
    by (rule monotoneD) (rule fg)
  then have "result_ord (bind (B g) (\<lambda>y'. C y' f)) (bind (B g) (\<lambda>y'. C y' g))"
    unfolding flat_ord_def by (cases "B g") auto
  finally (result.leq_trans)
  show "result_ord (bind (B f) (\<lambda>y. C y f)) (bind (B g) (\<lambda>y. C y g))" .
qed

(** Monotonicity through tuple destructuring in bind continuations
    ([(x, y) <- m; e] is [bind m (\<lambda>(x, y). e)]). *)
lemma result_case_prod_mono [partial_function_mono]:
  assumes "\<And>a b. mono_result (\<lambda>f. C a b f)"
  shows "mono_result (\<lambda>f. case p of (a, b) \<Rightarrow> C a b f)"
  using assms by (cases p) simp

(** The result of one loop-body iteration.  The first type parameter is the
    state supplied to the next iteration; the second is the value returned by
    a break. *)
datatype ('state, 'break) control_flow =
    LoopContinue 'state
  | LoopBreak 'break

(** Rust loops need not terminate, whereas every Isabelle/HOL function is
    total.  The loop combinator is therefore the least fixed point of its
    one-step unfolding in the result monad: a loop that never breaks or fails
    denotes [Diverge]. *)
partial_function (result) loop ::
  "('state \<Rightarrow> (('state, 'break) control_flow) result) \<Rightarrow> 'state \<Rightarrow> 'break result"
where
  "loop body state =
    (r <- body state;
     case r of
       LoopContinue next \<Rightarrow> loop body next
     | LoopBreak value \<Rightarrow> Ok value)"

(** The unfolding equation of the loop combinator, in the form used by the
    translation: a body that fails propagates the failure, a body that breaks
    returns the break value, and a body that continues iterates. *)
lemma loop_unfold:
  "loop body state =
    (case body state of
       Fail e \<Rightarrow> Fail e
     | Diverge \<Rightarrow> Diverge
     | Ok (LoopContinue next) \<Rightarrow> loop body next
     | Ok (LoopBreak value) \<Rightarrow> Ok value)"
  by (subst loop.simps) (cases "body state", auto split: control_flow.split)

(*** Misc *)

type_synonym string = String.string
type_synonym str = string
type_synonym char = char

(*
definition char_of_byte :: "Word.word8 \<Rightarrow> char" where
  "char_of_byte = Code_Char.char_of_byte" *)

definition core_mem_replace :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a)" where
  "core_mem_replace x y \<equiv> (x, y)"

definition bool_and :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "bool_and x y \<equiv> x \<and> y"

definition bool_or :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "bool_or x y \<equiv> x \<or> y"

definition bool_xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "bool_xor x y \<equiv> x \<noteq> y"

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
fun scalar_bits :: "scalar_ty \<Rightarrow> nat" where
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

fun scalar_is_signed :: "scalar_ty \<Rightarrow> bool" where
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

fun scalar_min :: "scalar_ty \<Rightarrow> int" where
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

fun scalar_max :: "scalar_ty \<Rightarrow> int" where
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

definition scalar_in_bounds :: "scalar_ty \<Rightarrow> int \<Rightarrow> bool" where
  "scalar_in_bounds ty x \<equiv> scalar_min ty \<le> x \<and> x \<le> scalar_max ty"

(* Smart constructors *)
definition mk_scalar :: "scalar_ty \<Rightarrow> int \<Rightarrow> int result" where
  "mk_scalar ty x \<equiv> if scalar_in_bounds ty x then return x else fail Failure"

definition mk_i8    :: "int \<Rightarrow> i8 result"    where "mk_i8 = mk_scalar I8"
definition mk_i16   :: "int \<Rightarrow> i16 result"   where "mk_i16 = mk_scalar I16"
definition mk_i32   :: "int \<Rightarrow> i32 result"   where "mk_i32 = mk_scalar I32"
definition mk_i64   :: "int \<Rightarrow> i64 result"   where "mk_i64 = mk_scalar I64"
definition mk_i128  :: "int \<Rightarrow> i128 result"  where "mk_i128 = mk_scalar I128"
definition mk_isize :: "int \<Rightarrow> isize result" where "mk_isize = mk_scalar Isize"
definition mk_u8    :: "int \<Rightarrow> u8 result"    where "mk_u8 = mk_scalar U8"
definition mk_u16   :: "int \<Rightarrow> u16 result"   where "mk_u16 = mk_scalar U16"
definition mk_u32   :: "int \<Rightarrow> u32 result"   where "mk_u32 = mk_scalar U32"
definition mk_u64   :: "int \<Rightarrow> u64 result"   where "mk_u64 = mk_scalar U64"
definition mk_u128  :: "int \<Rightarrow> u128 result"  where "mk_u128 = mk_scalar U128"
definition mk_usize :: "int \<Rightarrow> usize result" where "mk_usize = mk_scalar Usize"

(* Interpret an arbitrary integer at the fixed width and signedness of [ty]. *)
definition scalar_modulus :: "scalar_ty \<Rightarrow> int" where
  "scalar_modulus ty \<equiv> (2 :: int) ^ scalar_bits ty"

definition scalar_wrap :: "scalar_ty \<Rightarrow> int \<Rightarrow> int" where
  "scalar_wrap ty x \<equiv>
    (let modulus = scalar_modulus ty;
         value = x mod modulus
     in if scalar_is_signed ty \<and> value \<ge> modulus div 2
        then value - modulus
        else value)"

(* Isabelle's integer division rounds towards minus infinity, whereas Rust
   truncates towards zero.  Define the Rust operations explicitly. *)
definition scalar_trunc_div :: "int \<Rightarrow> int \<Rightarrow> int" where
  "scalar_trunc_div x y \<equiv>
    (if (x < 0) = (y < 0)
     then abs x div abs y
     else -(abs x div abs y))"

definition scalar_trunc_rem :: "int \<Rightarrow> int \<Rightarrow> int" where
  "scalar_trunc_rem x y \<equiv> x - scalar_trunc_div x y * y"


(* Scalar operations *)
definition scalar_add :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int result" where
  "scalar_add ty x y \<equiv> mk_scalar ty (x + y)"
definition scalar_sub :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int result" where
  "scalar_sub ty x y \<equiv> mk_scalar ty (x - y)"
definition scalar_mul :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int result" where
  "scalar_mul ty x y \<equiv> mk_scalar ty (x * y)"
definition scalar_div :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int result" where
  "scalar_div ty x y \<equiv>
    if y = 0 then fail Failure else mk_scalar ty (scalar_trunc_div x y)"
definition scalar_rem :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int result" where
  "scalar_rem ty x y \<equiv>
    if y = 0 then fail Failure else mk_scalar ty (scalar_trunc_rem x y)"
definition scalar_neg :: "scalar_ty \<Rightarrow> int \<Rightarrow> int result" where
  "scalar_neg ty x \<equiv> mk_scalar ty (- x)"

(* Wrapping operations are pure in Aeneas' Pure IR, except division and
   remainder which can still fail on a zero divisor. *)
definition scalar_wrapping_add :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "scalar_wrapping_add ty x y \<equiv> scalar_wrap ty (x + y)"
definition scalar_wrapping_sub :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "scalar_wrapping_sub ty x y \<equiv> scalar_wrap ty (x - y)"
definition scalar_wrapping_mul :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "scalar_wrapping_mul ty x y \<equiv> scalar_wrap ty (x * y)"
definition scalar_wrapping_neg :: "scalar_ty \<Rightarrow> int \<Rightarrow> int" where
  "scalar_wrapping_neg ty x \<equiv> scalar_wrap ty (- x)"
definition scalar_wrapping_div :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int result" where
  "scalar_wrapping_div ty x y \<equiv>
    if y = 0 then fail Failure
    else return (scalar_wrap ty (scalar_trunc_div x y))"
definition scalar_wrapping_rem :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int result" where
  "scalar_wrapping_rem ty x y \<equiv>
    if y = 0 then fail Failure
    else return (scalar_wrap ty (scalar_trunc_rem x y))"

(* Rust's overflowing_* operations return the wrapped value and an overflow
   flag.  The Pure checked operators use this same pair representation. *)
definition scalar_add_checked :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> bool" where
  "scalar_add_checked ty x y \<equiv>
    (let z = x + y in (scalar_wrap ty z, \<not> scalar_in_bounds ty z))"
definition scalar_sub_checked :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> bool" where
  "scalar_sub_checked ty x y \<equiv>
    (let z = x - y in (scalar_wrap ty z, \<not> scalar_in_bounds ty z))"
definition scalar_mul_checked :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> bool" where
  "scalar_mul_checked ty x y \<equiv>
    (let z = x * y in (scalar_wrap ty z, \<not> scalar_in_bounds ty z))"
(* Logic *)
definition scalar_lt :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "scalar_lt ty x y \<equiv> x < y"
definition scalar_le :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "scalar_le ty x y \<equiv> x \<le> y"
definition scalar_gt :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "scalar_gt ty x y \<equiv> x > y"
definition scalar_ge :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "scalar_ge ty x y \<equiv> x \<ge> y"
definition scalar_eq :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "scalar_eq ty x y \<equiv> x = y"
definition scalar_ne :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "scalar_ne ty x y \<equiv> x \<noteq> y"

(* Bitwise operations are pure.  Wrapping the mathematical integer result is
   essential for signed types, whose representation is two's complement. *)
definition scalar_xor :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "scalar_xor ty x y \<equiv> scalar_wrap ty (x XOR y)"
definition scalar_or :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "scalar_or ty x y \<equiv> scalar_wrap ty (x OR y)"
definition scalar_and :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "scalar_and ty x y \<equiv> scalar_wrap ty (x AND y)"
definition scalar_not :: "scalar_ty \<Rightarrow> int \<Rightarrow> int" where
  "scalar_not ty x \<equiv> scalar_wrap ty (NOT x)"

definition scalar_shift_in_bounds :: "scalar_ty \<Rightarrow> int \<Rightarrow> bool" where
  "scalar_shift_in_bounds ty n \<equiv> 0 \<le> n \<and> n < int (scalar_bits ty)"

definition scalar_shl :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int result" where
  "scalar_shl ty x n \<equiv>
    if scalar_shift_in_bounds ty n
    then return (scalar_wrap ty (x * (2 :: int) ^ nat n))
    else fail Failure"

definition scalar_shr :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int result" where
  "scalar_shr ty x n \<equiv>
    if scalar_shift_in_bounds ty n
    then return (scalar_wrap ty (x div (2 :: int) ^ nat n))
    else fail Failure"

definition scalar_wrapping_shift_amount :: "scalar_ty \<Rightarrow> int \<Rightarrow> nat" where
  "scalar_wrapping_shift_amount ty n \<equiv> nat (n mod int (scalar_bits ty))"

definition scalar_wrapping_shl :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "scalar_wrapping_shl ty x n \<equiv>
    scalar_wrap ty
      (x * (2 :: int) ^ scalar_wrapping_shift_amount ty n)"

definition scalar_wrapping_shr :: "scalar_ty \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "scalar_wrapping_shr ty x n \<equiv>
    scalar_wrap ty
      (x div (2 :: int) ^ scalar_wrapping_shift_amount ty n)"

(* Rust integer casts never fail for a well-formed source scalar.  They first
   retain the low bits of the target width, then interpret those bits as a
   two's-complement number when the target is signed.  We keep a [result]
   return type because the Pure translation currently treats non-Lean casts as
   monadic. *)
definition scalar_cast :: "scalar_ty \<Rightarrow> scalar_ty \<Rightarrow> int \<Rightarrow> int result" where
  "scalar_cast _ tgt_ty x \<equiv> return (scalar_wrap tgt_ty x)"

definition scalar_cast_bool :: "scalar_ty \<Rightarrow> bool \<Rightarrow> int result" where
  "scalar_cast_bool _ b \<equiv> return (if b then 1 else 0)"

(* Helper for HOL4/Isabelle style casts (e.g., i32_of_u8) *)
definition i8_to_int    :: "i8 \<Rightarrow> int"    where "i8_to_int x = x"
definition i16_to_int   :: "i16 \<Rightarrow> int"   where "i16_to_int x = x"
definition i32_to_int   :: "i32 \<Rightarrow> int"   where "i32_to_int x = x"
definition i64_to_int   :: "i64 \<Rightarrow> int"   where "i64_to_int x = x"
definition i128_to_int  :: "i128 \<Rightarrow> int"  where "i128_to_int x = x"
definition isize_to_int :: "isize \<Rightarrow> int" where "isize_to_int x = x"
definition u8_to_int    :: "u8 \<Rightarrow> int"    where "u8_to_int x = x"
definition u16_to_int   :: "u16 \<Rightarrow> int"   where "u16_to_int x = x"
definition u32_to_int   :: "u32 \<Rightarrow> int"   where "u32_to_int x = x"
definition u64_to_int   :: "u64 \<Rightarrow> int"   where "u64_to_int x = x"
definition u128_to_int  :: "u128 \<Rightarrow> int"  where "u128_to_int x = x"
definition usize_to_int :: "usize \<Rightarrow> int" where "usize_to_int x = x"
definition bool_to_int :: "bool \<Rightarrow> int" where
  "bool_to_int x = (if x then 1 else 0)"

(* Comparisons (on the unwrapped 'int' types) *)
definition scalar_leb  :: "'a::order \<Rightarrow> 'a \<Rightarrow> bool" where "scalar_leb = (\<le>)"
definition scalar_ltb  :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> bool" where "scalar_ltb = (<)"
definition scalar_geb  :: "'a::order \<Rightarrow> 'a \<Rightarrow> bool" where "scalar_geb = (\<ge>)"
definition scalar_gtb  :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> bool" where "scalar_gtb = (>)"

(*
definition scalar_eqb  :: "'a::eq \<Rightarrow> 'a \<Rightarrow> bool" where "scalar_eqb = (=)"
definition scalar_neqb :: "'a::eq \<Rightarrow> 'a \<Rightarrow> bool" where "scalar_neqb = (\<noteq>)" 
*)
definition scalar_eqb  :: "'a::order \<Rightarrow> 'a \<Rightarrow> bool" where "scalar_eqb = (=)"
definition scalar_neqb :: "'a::order \<Rightarrow> 'a \<Rightarrow> bool" where "scalar_neqb = (\<noteq>)" 

(* Neg Op *)
definition isize_neg :: "int \<Rightarrow> int result" where 
  "isize_neg = scalar_neg Isize"
definition i8_neg :: "int \<Rightarrow> int result" where 
  "i8_neg = scalar_neg I8"
definition i16_neg :: "int \<Rightarrow> int result" where 
  "i16_neg = scalar_neg I16"
definition i32_neg :: "int \<Rightarrow> int result" where 
  "i32_neg = scalar_neg I32"
definition i64_neg :: "int \<Rightarrow> int result" where 
  "i64_neg = scalar_neg I64"
definition i128_neg :: "int \<Rightarrow> int result" where 
  "i128_neg = scalar_neg I128"

(* Div Op *)
definition isize_div :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "isize_div = scalar_div Isize"
definition i8_div :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i8_div = scalar_div I8"
definition i16_div :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i16_div = scalar_div I16"
definition i32_div :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i32_div = scalar_div I32"
definition i64_div :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i64_div = scalar_div I64"
definition i128_div :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i128_div = scalar_div I128"
definition usize_div :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "usize_div = scalar_div Usize"
definition u8_div :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u8_div = scalar_div U8"
definition u16_div :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u16_div = scalar_div U16"
definition u32_div :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u32_div = scalar_div U32"
definition u64_div :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u64_div = scalar_div U64"
definition u128_div :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u128_div = scalar_div U128"

(* Rem Op *)
definition isize_rem :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "isize_rem = scalar_rem Isize"
definition i8_rem :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i8_rem = scalar_rem I8"
definition i16_rem :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i16_rem = scalar_rem I16"
definition i32_rem :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i32_rem = scalar_rem I32"
definition i64_rem :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i64_rem = scalar_rem I64"
definition i128_rem :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i128_rem = scalar_rem I128"
definition usize_rem :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "usize_rem = scalar_rem Usize"
definition u8_rem :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u8_rem = scalar_rem U8"
definition u16_rem :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u16_rem = scalar_rem U16"
definition u32_rem :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u32_rem = scalar_rem U32"
definition u64_rem :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u64_rem = scalar_rem U64"
definition u128_rem :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u128_rem = scalar_rem U128"

(* Add Op *)
definition isize_add :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "isize_add = scalar_add Isize"
definition i8_add :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i8_add = scalar_add I8"
definition i16_add :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i16_add = scalar_add I16"
definition i32_add :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i32_add = scalar_add I32"
definition i64_add :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i64_add = scalar_add I64"
definition i128_add :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i128_add = scalar_add I128"
definition usize_add :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "usize_add = scalar_add Usize"
definition u8_add :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u8_add = scalar_add U8"
definition u16_add :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u16_add = scalar_add U16"
definition u32_add :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u32_add = scalar_add U32"
definition u64_add :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u64_add = scalar_add U64"
definition u128_add :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u128_add = scalar_add U128"

(* Sub Op *)
definition isize_sub :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "isize_sub = scalar_sub Isize"
definition i8_sub :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i8_sub = scalar_sub I8"
definition i16_sub :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i16_sub = scalar_sub I16"
definition i32_sub :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i32_sub = scalar_sub I32"
definition i64_sub :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i64_sub = scalar_sub I64"
definition i128_sub :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i128_sub = scalar_sub I128"
definition usize_sub :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "usize_sub = scalar_sub Usize"
definition u8_sub :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u8_sub = scalar_sub U8"
definition u16_sub :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u16_sub = scalar_sub U16"
definition u32_sub :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u32_sub = scalar_sub U32"
definition u64_sub :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u64_sub = scalar_sub U64"
definition u128_sub :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u128_sub = scalar_sub U128"

(* Mul Op *)
definition isize_mul :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "isize_mul = scalar_mul Isize"
definition i8_mul :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i8_mul = scalar_mul I8"
definition i16_mul :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i16_mul = scalar_mul I16"
definition i32_mul :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i32_mul = scalar_mul I32"
definition i64_mul :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i64_mul = scalar_mul I64"
definition i128_mul :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i128_mul = scalar_mul I128"
definition usize_mul :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "usize_mul = scalar_mul Usize"
definition u8_mul :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u8_mul = scalar_mul U8"
definition u16_mul :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u16_mul = scalar_mul U16"
definition u32_mul :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u32_mul = scalar_mul U32"
definition u64_mul :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u64_mul = scalar_mul U64"
definition u128_mul :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u128_mul = scalar_mul U128"

(* Xor Op *)
definition u8_xor :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u8_xor = scalar_xor U8"
definition u16_xor :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u16_xor = scalar_xor U16"
definition u32_xor :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u32_xor = scalar_xor U32"
definition u64_xor :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u64_xor = scalar_xor U64"
definition u128_xor :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u128_xor = scalar_xor U128"
definition usize_xor :: "int \<Rightarrow> int \<Rightarrow> int" where
  "usize_xor = scalar_xor Usize"
definition i8_xor :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i8_xor = scalar_xor I8"
definition i16_xor :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i16_xor = scalar_xor I16"
definition i32_xor :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i32_xor = scalar_xor I32"
definition i64_xor :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i64_xor = scalar_xor I64"
definition i128_xor :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i128_xor = scalar_xor I128"
definition isize_xor :: "int \<Rightarrow> int \<Rightarrow> int" where
  "isize_xor = scalar_xor Isize"

(* Or Op *)
definition u8_or :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u8_or = scalar_or U8"
definition u16_or :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u16_or = scalar_or U16"
definition u32_or :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u32_or = scalar_or U32"
definition u64_or :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u64_or = scalar_or U64"
definition u128_or :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u128_or = scalar_or U128"
definition usize_or :: "int \<Rightarrow> int \<Rightarrow> int" where
  "usize_or = scalar_or Usize"
definition i8_or :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i8_or = scalar_or I8"
definition i16_or :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i16_or = scalar_or I16"
definition i32_or :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i32_or = scalar_or I32"
definition i64_or :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i64_or = scalar_or I64"
definition i128_or :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i128_or = scalar_or I128"
definition isize_or :: "int \<Rightarrow> int \<Rightarrow> int" where
  "isize_or = scalar_or Isize"

(* And Op *)
definition u8_and :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u8_and = scalar_and U8"
definition u16_and :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u16_and = scalar_and U16"
definition u32_and :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u32_and = scalar_and U32"
definition u64_and :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u64_and = scalar_and U64"
definition u128_and :: "int \<Rightarrow> int \<Rightarrow> int" where
  "u128_and = scalar_and U128"
definition usize_and :: "int \<Rightarrow> int \<Rightarrow> int" where
  "usize_and = scalar_and Usize"
definition i8_and :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i8_and = scalar_and I8"
definition i16_and :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i16_and = scalar_and I16"
definition i32_and :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i32_and = scalar_and I32"
definition i64_and :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i64_and = scalar_and I64"
definition i128_and :: "int \<Rightarrow> int \<Rightarrow> int" where
  "i128_and = scalar_and I128"
definition isize_and :: "int \<Rightarrow> int \<Rightarrow> int" where
  "isize_and = scalar_and Isize"

(* Shift Left Op *)
definition u8_shl :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u8_shl = scalar_shl U8"
definition u16_shl :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u16_shl = scalar_shl U16"
definition u32_shl :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u32_shl = scalar_shl U32"
definition u64_shl :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u64_shl = scalar_shl U64"
definition u128_shl :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u128_shl = scalar_shl U128"
definition usize_shl :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "usize_shl = scalar_shl Usize"
definition i8_shl :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i8_shl = scalar_shl I8"
definition i16_shl :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i16_shl = scalar_shl I16"
definition i32_shl :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i32_shl = scalar_shl I32"
definition i64_shl :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i64_shl = scalar_shl I64"
definition i128_shl :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i128_shl = scalar_shl I128"
definition isize_shl :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "isize_shl = scalar_shl Isize"

(* Shift Right Op *)
definition u8_shr :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u8_shr = scalar_shr U8"
definition u16_shr :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u16_shr = scalar_shr U16"
definition u32_shr :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u32_shr = scalar_shr U32"
definition u64_shr :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u64_shr = scalar_shr U64"
definition u128_shr :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "u128_shr = scalar_shr U128"
definition usize_shr :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "usize_shr = scalar_shr Usize"
definition i8_shr :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i8_shr = scalar_shr I8"
definition i16_shr :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i16_shr = scalar_shr I16"
definition i32_shr :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i32_shr = scalar_shr I32"
definition i64_shr :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i64_shr = scalar_shr I64"
definition i128_shr :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "i128_shr = scalar_shr I128"
definition isize_shr :: "int \<Rightarrow> int \<Rightarrow> int result" where 
  "isize_shr = scalar_shr Isize"

(* Not Op *)
definition u8_not :: "int \<Rightarrow> int" where
  "u8_not = scalar_not U8"
definition u16_not :: "int \<Rightarrow> int" where
  "u16_not = scalar_not U16"
definition u32_not :: "int \<Rightarrow> int" where
  "u32_not = scalar_not U32"
definition u64_not :: "int \<Rightarrow> int" where
  "u64_not = scalar_not U64"
definition u128_not :: "int \<Rightarrow> int" where
  "u128_not = scalar_not U128"
definition usize_not :: "int \<Rightarrow> int" where
  "usize_not = scalar_not Usize"
definition i8_not :: "int \<Rightarrow> int" where
  "i8_not = scalar_not I8"
definition i16_not :: "int \<Rightarrow> int" where
  "i16_not = scalar_not I16"
definition i32_not :: "int \<Rightarrow> int" where
  "i32_not = scalar_not I32"
definition i64_not :: "int \<Rightarrow> int" where
  "i64_not = scalar_not I64"
definition i128_not :: "int \<Rightarrow> int" where
  "i128_not = scalar_not I128"
definition isize_not :: "int \<Rightarrow> int" where
  "isize_not = scalar_not Isize"

(* Less Than Op *)
definition u8_lt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u8_lt = scalar_lt U8"
definition u16_lt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u16_lt = scalar_lt U16"
definition u32_lt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u32_lt = scalar_lt U32"
definition u64_lt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u64_lt = scalar_lt U64"
definition u128_lt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u128_lt = scalar_lt U128"
definition usize_lt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "usize_lt = scalar_lt Usize"
definition i8_lt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i8_lt = scalar_lt I8"
definition i16_lt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i16_lt = scalar_lt I16"
definition i32_lt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i32_lt = scalar_lt I32"
definition i64_lt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i64_lt = scalar_lt I64"
definition i128_lt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i128_lt = scalar_lt I128"
definition isize_lt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "isize_lt = scalar_lt Isize"

(* Less and Equal Op *)
definition u8_le :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u8_le = scalar_le U8"
definition u16_le :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u16_le = scalar_le U16"
definition u32_le :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u32_le = scalar_le U32"
definition u64_le :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u64_le = scalar_le U64"
definition u128_le :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u128_le = scalar_le U128"
definition usize_le :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "usize_le = scalar_le Usize"
definition i8_le :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i8_le = scalar_le I8"
definition i16_le :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i16_le = scalar_le I16"
definition i32_le :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i32_le = scalar_le I32"
definition i64_le :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i64_le = scalar_le I64"
definition i128_le :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i128_le = scalar_le I128"
definition isize_le :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "isize_le = scalar_le Isize"

(* Greater Than Op *)
definition u8_gt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u8_gt = scalar_gt U8"
definition u16_gt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u16_gt = scalar_gt U16"
definition u32_gt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u32_gt = scalar_gt U32"
definition u64_gt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u64_gt = scalar_gt U64"
definition u128_gt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u128_gt = scalar_gt U128"
definition usize_gt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "usize_gt = scalar_gt Usize"
definition i8_gt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i8_gt = scalar_gt I8"
definition i16_gt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i16_gt = scalar_gt I16"
definition i32_gt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i32_gt = scalar_gt I32"
definition i64_gt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i64_gt = scalar_gt I64"
definition i128_gt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i128_gt = scalar_gt I128"
definition isize_gt :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "isize_gt = scalar_gt Isize"

(* Greater and Equal Op *)
definition u8_ge :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u8_ge = scalar_ge U8"
definition u16_ge :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u16_ge = scalar_ge U16"
definition u32_ge :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u32_ge = scalar_ge U32"
definition u64_ge :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u64_ge = scalar_ge U64"
definition u128_ge :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u128_ge = scalar_ge U128"
definition usize_ge :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "usize_ge = scalar_ge Usize"
definition i8_ge :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i8_ge = scalar_ge I8"
definition i16_ge :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i16_ge = scalar_ge I16"
definition i32_ge :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i32_ge = scalar_ge I32"
definition i64_ge :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i64_ge = scalar_ge I64"
definition i128_ge :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i128_ge = scalar_ge I128"
definition isize_ge :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "isize_ge = scalar_ge Isize"

(* Equal Op *)
definition u8_eq :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u8_eq = scalar_eq U8"
definition u16_eq :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u16_eq = scalar_eq U16"
definition u32_eq :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u32_eq = scalar_eq U32"
definition u64_eq :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u64_eq = scalar_eq U64"
definition u128_eq :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u128_eq = scalar_eq U128"
definition usize_eq :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "usize_eq = scalar_eq Usize"
definition i8_eq :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i8_eq = scalar_eq I8"
definition i16_eq :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i16_eq = scalar_eq I16"
definition i32_eq :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i32_eq = scalar_eq I32"
definition i64_eq :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i64_eq = scalar_eq I64"
definition i128_eq :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i128_eq = scalar_eq I128"
definition isize_eq :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "isize_eq = scalar_eq Isize"

(* Not Equal Op *)
definition u8_ne :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u8_ne = scalar_ne U8"
definition u16_ne :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u16_ne = scalar_ne U16"
definition u32_ne :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u32_ne = scalar_ne U32"
definition u64_ne :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u64_ne = scalar_ne U64"
definition u128_ne :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "u128_ne = scalar_ne U128"
definition usize_ne :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "usize_ne = scalar_ne Usize"
definition i8_ne :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i8_ne = scalar_ne I8"
definition i16_ne :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i16_ne = scalar_ne I16"
definition i32_ne :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i32_ne = scalar_ne I32"
definition i64_ne :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i64_ne = scalar_ne I64"
definition i128_ne :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "i128_ne = scalar_ne I128"
definition isize_ne :: "int \<Rightarrow> int \<Rightarrow> bool" where 
  "isize_ne = scalar_ne Isize"

(** Small utility *)
definition usize_to_nat :: "usize \<Rightarrow> nat" where
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
  core_clone_Clone_clone :: "'self \<Rightarrow> 'self result"
  core_clone_Clone_clone_from :: "'self \<Rightarrow> 'self \<Rightarrow> 'self result"

definition core_clone_impls_CloneUsize_clone :: "usize \<Rightarrow> usize" where "core_clone_impls_CloneUsize_clone x = x"
(* ... other scalar clone impls ... *)

definition core_clone_CloneUsize :: "usize core_clone_Clone" where
  "core_clone_CloneUsize = (|
    core_clone_Clone_clone = (\<lambda>x. return (core_clone_impls_CloneUsize_clone x)),
    core_clone_Clone_clone_from = (\<lambda> _ y. return y)
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
fun core_option_Option_unwrap :: "'a option \<Rightarrow> 'a result" where
  "core_option_Option_unwrap (Some x) = (Ok x)" |
  "core_option_Option_unwrap None = Fail Failure"

(*** core::ops *)

(* Trait declaration: [core::ops::index::Index] *)
record ('self, 'idx, 'output) core_ops_index_Index =
  core_ops_index_Index_index :: "'self \<Rightarrow> 'idx \<Rightarrow> 'output result"

(* Trait declaration: [core::ops::index::IndexMut] *)
record ('self, 'idx, 'output) core_ops_index_IndexMut =
  core_ops_index_IndexMut_indexInst :: "('self, 'idx, 'output) core_ops_index_Index"
  core_ops_index_IndexMut_index_mut :: "'self \<Rightarrow> 'idx \<Rightarrow> ('output \<times> ('output \<Rightarrow> 'self)) result"

(* Trait declaration [core::ops::deref::Deref] *)
record ('self, 'target) core_ops_deref_Deref =
  core_ops_deref_Deref_deref :: "'self \<Rightarrow> 'target result"

(* Trait declaration [core::ops::deref::DerefMut] *)
record ('self, 'target) core_ops_deref_DerefMut =
  core_ops_deref_DerefMut_derefInst :: "('self, 'target) core_ops_deref_Deref"
  core_ops_deref_DerefMut_deref_mut :: "'self \<Rightarrow> ('target \<times> ('target \<Rightarrow> 'self)) result"

record 'a core_ops_range_Range =
  core_ops_range_Range_start :: 'a
  core_ops_range_Range_end_' :: 'a

(*** [alloc] *)

definition alloc_boxed_Box_deref :: "'a \<Rightarrow> 'a" where "alloc_boxed_Box_deref x = x"
definition alloc_boxed_Box_deref_mut :: "'a \<Rightarrow> 'a \<times> ('a \<Rightarrow> 'a)" where
  "alloc_boxed_Box_deref_mut x = (x, (\<lambda>y. y))"

definition alloc_boxed_Box_coreopsDerefInst :: "'a \<Rightarrow> ('a, 'a) core_ops_deref_Deref" where
  "alloc_boxed_Box_coreopsDerefInst _ = (|
    core_ops_deref_Deref_deref = (\<lambda>x. Ok (alloc_boxed_Box_deref x))
  |)"

(* Names used by the builtin trait-instance table. *)
definition core_ops_deref_DerefBoxInst ::
  "('a, 'a) core_ops_deref_Deref" where
  "core_ops_deref_DerefBoxInst = (|
    core_ops_deref_Deref_deref = \<lambda>x. return (alloc_boxed_Box_deref x)
  |)"

definition core_ops_deref_DerefBoxMutInst ::
  "('a, 'a) core_ops_deref_DerefMut" where
  "core_ops_deref_DerefBoxMutInst = (|
    core_ops_deref_DerefMut_derefInst = core_ops_deref_DerefBoxInst,
    core_ops_deref_DerefMut_deref_mut =
      \<lambda>x. return (alloc_boxed_Box_deref_mut x)
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
definition array_wf :: "usize \<Rightarrow> 'a array \<Rightarrow> bool" where
  "array_wf n xs \<longleftrightarrow>
    0 \<le> n \<and> n \<le> usize_max \<and> int (length xs) = n"

(* Arrays *)
definition mk_array :: "usize \<Rightarrow> 'a list \<Rightarrow> 'a array" where
  "mk_array _ xs = xs"
definition array_repeat :: "usize \<Rightarrow> 'a \<Rightarrow> 'a array" where
  "array_repeat n x = replicate (nat n) x"

(* Array lengths are erased from Isabelle types but remain explicit term
   arguments at call sites.  The primitive interfaces therefore accept the
   length and may use it for consistency checks in future refinements. *)
definition array_index_usize ::
  "usize \<Rightarrow> 'a array \<Rightarrow> usize \<Rightarrow> 'a result" where
  "array_index_usize _ a i =
    (if 0 \<le> i \<and> i < int (length a)
     then return (a ! nat i)
     else fail Failure)"

definition array_update_usize ::
  "usize \<Rightarrow> 'a array \<Rightarrow> usize \<Rightarrow> 'a \<Rightarrow> 'a array result" where
  "array_update_usize _ a i x =
    (if 0 \<le> i \<and> i < int (length a)
     then return (list_update a (nat i) x)
     else fail Failure)"

definition array_update ::
  "'a array \<Rightarrow> usize \<Rightarrow> 'a \<Rightarrow> 'a array" where
  "array_update a i x =
    (if 0 \<le> i \<and> i < int (length a)
     then list_update a (nat i) x
     else a)"

definition array_index_mut_usize ::
  "usize \<Rightarrow> 'a array \<Rightarrow> usize \<Rightarrow> ('a \<times> ('a \<Rightarrow> 'a array)) result" where
  "array_index_mut_usize _ a i =
    (if 0 \<le> i \<and> i < int (length a)
     then return (a ! nat i, array_update a i)
     else fail Failure)"

(* Slices *)
definition slice_len :: "'a slice \<Rightarrow> usize" where
  "slice_len s =
    (let n = int (length s) in if n \<le> usize_max then n else 0)"

definition slice_index_usize :: "'a slice \<Rightarrow> usize \<Rightarrow> 'a result" where
  "slice_index_usize s i =
    (if 0 \<le> i \<and> i < int (length s)
     then return (s ! nat i)
     else fail Failure)"

definition slice_update_usize ::
  "'a slice \<Rightarrow> usize \<Rightarrow> 'a \<Rightarrow> 'a slice result" where
  "slice_update_usize s i x =
    (if 0 \<le> i \<and> i < int (length s)
     then return (list_update s (nat i) x)
     else fail Failure)"

definition slice_update ::
  "'a slice \<Rightarrow> usize \<Rightarrow> 'a \<Rightarrow> 'a slice" where
  "slice_update s i x =
    (if 0 \<le> i \<and> i < int (length s)
     then list_update s (nat i) x
     else s)"

definition slice_index_mut_usize :: "'a slice \<Rightarrow> usize \<Rightarrow> ('a \<times> ('a \<Rightarrow> 'a slice)) result" where
  "slice_index_mut_usize s i =
    (if 0 \<le> i \<and> i < int (length s)
     then return (s ! nat i, slice_update s i)
     else fail Failure)"

(* Subslices *)
definition array_to_slice :: "usize \<Rightarrow> 'a array \<Rightarrow> 'a slice" where
  "array_to_slice _ a = a"
definition array_from_slice :: "'a array \<Rightarrow> 'a slice \<Rightarrow> 'a array" where "array_from_slice _ s = s"

definition array_to_slice_mut ::
  "usize \<Rightarrow> 'a array \<Rightarrow> 'a slice \<times> ('a slice \<Rightarrow> 'a array)" where
  "array_to_slice_mut n a = (array_to_slice n a, array_from_slice a)"

definition slice_range_valid ::
  "usize core_ops_range_Range \<Rightarrow> 'a slice \<Rightarrow> bool" where
  "slice_range_valid r s \<longleftrightarrow>
    0 \<le> core_ops_range_Range_start r \<and>
    core_ops_range_Range_start r \<le> core_ops_range_Range_end_' r \<and>
    core_ops_range_Range_end_' r \<le> int (length s)"

definition slice_subslice ::
  "'a slice \<Rightarrow> usize core_ops_range_Range \<Rightarrow> 'a slice result" where
  "slice_subslice s r =
    (if slice_range_valid r s then
       return
         (take (nat (core_ops_range_Range_end_' r -
                     core_ops_range_Range_start r))
           (drop (nat (core_ops_range_Range_start r)) s))
     else fail Failure)"

definition slice_replace_range ::
  "'a slice \<Rightarrow> usize core_ops_range_Range \<Rightarrow> 'a slice \<Rightarrow> 'a slice" where
  "slice_replace_range s r ns =
    (if slice_range_valid r s \<and>
        int (length ns) =
          core_ops_range_Range_end_' r - core_ops_range_Range_start r
     then
       take (nat (core_ops_range_Range_start r)) s @
       ns @
       drop (nat (core_ops_range_Range_end_' r)) s
     else s)"

definition slice_update_subslice ::
  "'a slice \<Rightarrow> usize core_ops_range_Range \<Rightarrow> 'a slice \<Rightarrow> 'a slice result" where
  "slice_update_subslice s r ns =
    (if slice_range_valid r s \<and>
        int (length ns) =
          core_ops_range_Range_end_' r - core_ops_range_Range_start r
     then return (slice_replace_range s r ns)
     else fail Failure)"

definition array_subslice ::
  "'a array \<Rightarrow> usize core_ops_range_Range \<Rightarrow> 'a slice result" where
  "array_subslice a r = slice_subslice a r"

definition array_update_subslice ::
  "'a array \<Rightarrow> usize core_ops_range_Range \<Rightarrow> 'a slice \<Rightarrow> 'a array result" where
  "array_update_subslice a r ns = slice_update_subslice a r ns"

(* Vectors *)
definition alloc_vec_Vec_to_list :: "'a alloc_vec_Vec \<Rightarrow> 'a list" where
  "alloc_vec_Vec_to_list v = v"

definition alloc_vec_Vec_length :: "'a alloc_vec_Vec \<Rightarrow> int" where
  "alloc_vec_Vec_length v = int (length v)"

definition alloc_vec_Vec_new :: "'a alloc_vec_Vec" where
  "alloc_vec_Vec_new = []"

(* [Vec::len] is registered as [-canFail -lift], hence it must be a pure
   [usize], not a [usize result]. *)
definition alloc_vec_Vec_len :: "'a alloc_vec_Vec \<Rightarrow> usize" where
  "alloc_vec_Vec_len v =
    (let n = int (length v) in if n \<le> usize_max then n else 0)"

definition alloc_vec_Vec_push :: "'a alloc_vec_Vec \<Rightarrow> 'a \<Rightarrow> ('a alloc_vec_Vec) result" where
  "alloc_vec_Vec_push v x =
    (let l = v @ [x] in
     if int (length l) \<le> usize_max then return l else fail OutOfFuel)"

definition alloc_vec_Vec_insert :: "'a alloc_vec_Vec \<Rightarrow> usize \<Rightarrow> 'a \<Rightarrow> ('a alloc_vec_Vec) result" where
  "alloc_vec_Vec_insert v i x =
    (if 0 \<le> i \<and> i < int (length v)
     then return (list_update v (nat i) x)
     else fail Failure)"

definition alloc_vec_Vec_index_usize ::
  "'a alloc_vec_Vec \<Rightarrow> usize \<Rightarrow> 'a result" where
  "alloc_vec_Vec_index_usize v i =
    (if 0 \<le> i \<and> i < int (length v)
     then return (v ! nat i)
     else fail Failure)"

definition alloc_vec_Vec_update_usize ::
  "'a alloc_vec_Vec \<Rightarrow> usize \<Rightarrow> 'a \<Rightarrow> 'a alloc_vec_Vec result" where
  "alloc_vec_Vec_update_usize v i x =
    (if 0 \<le> i \<and> i < int (length v)
     then return (list_update v (nat i) x)
     else fail Failure)"

definition alloc_vec_Vec_update ::
  "'a alloc_vec_Vec \<Rightarrow> usize \<Rightarrow> 'a \<Rightarrow> 'a alloc_vec_Vec" where
  "alloc_vec_Vec_update v i x =
    (if 0 \<le> i \<and> i < int (length v)
     then list_update v (nat i) x
     else v)"

definition alloc_vec_Vec_index_mut_usize :: "'a alloc_vec_Vec \<Rightarrow> usize \<Rightarrow> ('a \<times> ('a \<Rightarrow> 'a alloc_vec_Vec)) result" where
  "alloc_vec_Vec_index_mut_usize v i =
    (if 0 \<le> i \<and> i < int (length v)
     then return (v ! nat i, alloc_vec_Vec_update v i)
     else fail Failure)"

definition alloc_vec_Vec_with_capacity ::
  "usize \<Rightarrow> 'a alloc_vec_Vec" where
  "alloc_vec_Vec_with_capacity _ = alloc_vec_Vec_new"

definition alloc_vec_Vec_deref ::
  "'a alloc_vec_Vec \<Rightarrow> 'a slice" where
  "alloc_vec_Vec_deref v = v"

definition alloc_vec_Vec_deref_mut ::
  "'a alloc_vec_Vec \<Rightarrow> 'a slice \<times> ('a slice \<Rightarrow> 'a alloc_vec_Vec)" where
  "alloc_vec_Vec_deref_mut v = (v, \<lambda>s. s)"

definition core_slice_Slice_reverse ::
  "'a slice \<Rightarrow> 'a slice" where
  "core_slice_Slice_reverse s = rev s"

fun alloc_slice_Slice_to_vec ::
  "'a core_clone_Clone \<Rightarrow> 'a slice \<Rightarrow> 'a alloc_vec_Vec result" where
  "alloc_slice_Slice_to_vec clone_inst [] = return []"
| "alloc_slice_Slice_to_vec clone_inst (x # xs) =
    (core_clone_Clone_clone clone_inst x >>= (\<lambda>y.
     alloc_slice_Slice_to_vec clone_inst xs >>= (\<lambda>ys.
     return (y # ys))))"

(* Trait declaration: [core::slice::index::private_slice_index::Sealed] *)
record 'self core_slice_index_private_slice_index_Sealed =
  core_slice_index_private_slice_index_Sealed_dummy :: unit

(* Trait declaration: [core::slice::index::SliceIndex] *)
record ('self, 'T, 'output) core_slice_index_SliceIndex =
  sealedInst :: "'self core_slice_index_private_slice_index_Sealed"
  core_slice_index_SliceIndex_get :: "'self \<Rightarrow> 'T \<Rightarrow> 'output option result"
  core_slice_index_SliceIndex_get_mut :: "'self \<Rightarrow> 'T \<Rightarrow> ('output option \<times> ('output option \<Rightarrow> 'T)) result"
  core_slice_index_SliceIndex_get_unchecked :: "'self \<Rightarrow> 'T const_raw_ptr \<Rightarrow> 'output const_raw_ptr result"
  core_slice_index_SliceIndex_get_unchecked_mut :: "'self \<Rightarrow> 'T mut_raw_ptr \<Rightarrow> 'output mut_raw_ptr result"
  core_slice_index_SliceIndex_index :: "'self \<Rightarrow> 'T \<Rightarrow> 'output result"
  core_slice_index_SliceIndex_index_mut :: "'self \<Rightarrow> 'T \<Rightarrow> ('output \<times> ('output \<Rightarrow> 'T)) result"

(* [core::slice::[T]::get/get_mut] and the Index/IndexMut methods. *)
definition core_slice_Slice_get ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex \<Rightarrow>
   'a slice \<Rightarrow> 'idx \<Rightarrow> 'output option result" where
  "core_slice_Slice_get inst s i =
    core_slice_index_SliceIndex_get inst i s"

definition core_slice_Slice_get_mut ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex \<Rightarrow>
   'a slice \<Rightarrow> 'idx \<Rightarrow>
   ('output option \<times> ('output option \<Rightarrow> 'a slice)) result" where
  "core_slice_Slice_get_mut inst s i =
    core_slice_index_SliceIndex_get_mut inst i s"

definition core_slice_index_Slice_index ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex \<Rightarrow>
   'a slice \<Rightarrow> 'idx \<Rightarrow> 'output result" where
  "core_slice_index_Slice_index inst s i =
    core_slice_index_SliceIndex_index inst i s"

definition core_slice_index_Slice_index_mut ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex \<Rightarrow>
   'a slice \<Rightarrow> 'idx \<Rightarrow> ('output \<times> ('output \<Rightarrow> 'a slice)) result" where
  "core_slice_index_Slice_index_mut inst s i =
    core_slice_index_SliceIndex_index_mut inst i s"

(* [SliceIndex<Range<usize>, [T]>]. *)
definition core_slice_index_SliceIndexRangeUsizeSlice_get ::
  "usize core_ops_range_Range \<Rightarrow> 'a slice \<Rightarrow> 'a slice option result" where
  "core_slice_index_SliceIndexRangeUsizeSlice_get r s =
    (if slice_range_valid r s
     then slice_subslice s r >>= (\<lambda>ss. return (Some ss))
     else return None)"

definition core_slice_index_SliceIndexRangeUsizeSlice_get_mut ::
  "usize core_ops_range_Range \<Rightarrow> 'a slice \<Rightarrow>
   ('a slice option \<times> ('a slice option \<Rightarrow> 'a slice)) result" where
  "core_slice_index_SliceIndexRangeUsizeSlice_get_mut r s =
    (if slice_range_valid r s then
       slice_subslice s r >>= (\<lambda>ss.
       return
         (Some ss,
          \<lambda>nss. case nss of
             None \<Rightarrow> s
           | Some ys \<Rightarrow> slice_replace_range s r ys))
     else return (None, \<lambda>_. s))"

definition core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked ::
  "usize core_ops_range_Range \<Rightarrow>
   'a slice const_raw_ptr \<Rightarrow> 'a slice const_raw_ptr result" where
  "core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked _ _ =
    fail Failure"

definition core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked_mut ::
  "usize core_ops_range_Range \<Rightarrow>
   'a slice mut_raw_ptr \<Rightarrow> 'a slice mut_raw_ptr result" where
  "core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked_mut _ _ =
    fail Failure"

definition core_slice_index_SliceIndexRangeUsizeSlice_index ::
  "usize core_ops_range_Range \<Rightarrow> 'a slice \<Rightarrow> 'a slice result" where
  "core_slice_index_SliceIndexRangeUsizeSlice_index r s =
    slice_subslice s r"

definition core_slice_index_SliceIndexRangeUsizeSlice_index_mut ::
  "usize core_ops_range_Range \<Rightarrow> 'a slice \<Rightarrow>
   ('a slice \<times> ('a slice \<Rightarrow> 'a slice)) result" where
  "core_slice_index_SliceIndexRangeUsizeSlice_index_mut r s =
    (slice_subslice s r >>= (\<lambda>ss.
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
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex \<Rightarrow>
   ('a slice, 'idx, 'output) core_ops_index_Index" where
  "core_ops_index_IndexSliceInst inst = (|
    core_ops_index_Index_index = core_slice_index_Slice_index inst
  |)"

definition core_ops_index_IndexMutSliceInst ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex \<Rightarrow>
   ('a slice, 'idx, 'output) core_ops_index_IndexMut" where
  "core_ops_index_IndexMutSliceInst inst = (|
    core_ops_index_IndexMut_indexInst = core_ops_index_IndexSliceInst inst,
    core_ops_index_IndexMut_index_mut = core_slice_index_Slice_index_mut inst
  |)"

definition core_array_Array_index ::
  "usize \<Rightarrow> ('a slice, 'idx, 'output) core_ops_index_Index \<Rightarrow>
   'a array \<Rightarrow> 'idx \<Rightarrow> 'output result" where
  "core_array_Array_index _ inst a i =
    core_ops_index_Index_index inst a i"

definition core_array_Array_index_mut ::
  "usize \<Rightarrow> ('a slice, 'idx, 'output) core_ops_index_IndexMut \<Rightarrow>
   'a array \<Rightarrow> 'idx \<Rightarrow> ('output \<times> ('output \<Rightarrow> 'a array)) result" where
  "core_array_Array_index_mut _ inst a i =
    core_ops_index_IndexMut_index_mut inst a i"

definition core_ops_index_IndexArrayInst ::
  "usize \<Rightarrow> ('a slice, 'idx, 'output) core_ops_index_Index \<Rightarrow>
   ('a array, 'idx, 'output) core_ops_index_Index" where
  "core_ops_index_IndexArrayInst n inst = (|
    core_ops_index_Index_index = core_array_Array_index n inst
  |)"

definition core_ops_index_IndexMutArrayInst ::
  "usize \<Rightarrow> ('a slice, 'idx, 'output) core_ops_index_IndexMut \<Rightarrow>
   ('a array, 'idx, 'output) core_ops_index_IndexMut" where
  "core_ops_index_IndexMutArrayInst n inst = (|
    core_ops_index_IndexMut_indexInst =
      core_ops_index_IndexArrayInst n
        (core_ops_index_IndexMut_indexInst inst),
    core_ops_index_IndexMut_index_mut = core_array_Array_index_mut n inst
  |)"

(* [SliceIndex<usize, [T]>]. *)
definition core_slice_index_usize_get ::
  "usize \<Rightarrow> 'a slice \<Rightarrow> 'a option result" where
  "core_slice_index_usize_get i s =
    return
      (if 0 \<le> i \<and> i < int (length s)
       then Some (s ! nat i)
       else None)"

definition core_slice_index_usize_get_mut ::
  "usize \<Rightarrow> 'a slice \<Rightarrow> ('a option \<times> ('a option \<Rightarrow> 'a slice)) result" where
  "core_slice_index_usize_get_mut i s =
    return
      (if 0 \<le> i \<and> i < int (length s)
       then
         (Some (s ! nat i),
          \<lambda>x. case x of None \<Rightarrow> s | Some y \<Rightarrow> slice_update s i y)
       else (None, \<lambda>_. s))"

definition core_slice_index_usize_get_unchecked ::
  "usize \<Rightarrow> 'a slice const_raw_ptr \<Rightarrow> 'a const_raw_ptr result" where
  "core_slice_index_usize_get_unchecked _ _ = fail Failure"

definition core_slice_index_usize_get_unchecked_mut ::
  "usize \<Rightarrow> 'a slice mut_raw_ptr \<Rightarrow> 'a mut_raw_ptr result" where
  "core_slice_index_usize_get_unchecked_mut _ _ = fail Failure"

definition core_slice_index_usize_index ::
  "usize \<Rightarrow> 'a slice \<Rightarrow> 'a result" where
  "core_slice_index_usize_index i s = slice_index_usize s i"

definition core_slice_index_usize_index_mut ::
  "usize \<Rightarrow> 'a slice \<Rightarrow> ('a \<times> ('a \<Rightarrow> 'a slice)) result" where
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
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex \<Rightarrow>
   'a alloc_vec_Vec \<Rightarrow> 'idx \<Rightarrow> 'output result" where
  "alloc_vec_Vec_index inst v i =
    core_slice_index_SliceIndex_index inst i v"

definition alloc_vec_Vec_index_mut ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex \<Rightarrow>
   'a alloc_vec_Vec \<Rightarrow> 'idx \<Rightarrow>
   ('output \<times> ('output \<Rightarrow> 'a alloc_vec_Vec)) result" where
  "alloc_vec_Vec_index_mut inst v i =
    core_slice_index_SliceIndex_index_mut inst i v"

definition alloc_vec_Vec_IndexInst ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex \<Rightarrow>
   ('a alloc_vec_Vec, 'idx, 'output) core_ops_index_Index" where
  "alloc_vec_Vec_IndexInst inst = (|
    core_ops_index_Index_index = alloc_vec_Vec_index inst
  |)"

definition alloc_vec_Vec_IndexMutInst ::
  "('idx, 'a slice, 'output) core_slice_index_SliceIndex \<Rightarrow>
   ('a alloc_vec_Vec, 'idx, 'output) core_ops_index_IndexMut" where
  "alloc_vec_Vec_IndexMutInst inst = (|
    core_ops_index_IndexMut_indexInst = alloc_vec_Vec_IndexInst inst,
    core_ops_index_IndexMut_index_mut = alloc_vec_Vec_index_mut inst
  |)"

definition core_ops_deref_DerefVecInst ::
  "('a alloc_vec_Vec, 'a slice) core_ops_deref_Deref" where
  "core_ops_deref_DerefVecInst = (|
    core_ops_deref_Deref_deref = \<lambda>v. return (alloc_vec_Vec_deref v)
  |)"

definition core_ops_deref_DerefMutVecInst ::
  "('a alloc_vec_Vec, 'a slice) core_ops_deref_DerefMut" where
  "core_ops_deref_DerefMutVecInst = (|
    core_ops_deref_DerefMut_derefInst = core_ops_deref_DerefVecInst,
    core_ops_deref_DerefMut_deref_mut =
      \<lambda>v. return (alloc_vec_Vec_deref_mut v)
  |)"

definition alloc_vec_DerefVec ::
  "('a alloc_vec_Vec, 'a slice) core_ops_deref_Deref" where
  "alloc_vec_DerefVec = core_ops_deref_DerefVecInst"

definition alloc_vec_DerefMutVec ::
  "('a alloc_vec_Vec, 'a slice) core_ops_deref_DerefMut" where
  "alloc_vec_DerefMutVec = core_ops_deref_DerefMutVecInst"

end
