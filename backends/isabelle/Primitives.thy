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

(** The function package uses this congruence rule when collecting recursive
    calls beneath a monadic bind.  The continuation is evaluated only when the
    first computation succeeds, so its termination assumptions may use the
    equation [m = Ok x]. *)
lemma result_bind_cong [fundef_cong]:
  assumes "m = m'" and "\<And>x. m' = Ok x \<Longrightarrow> f x = g x"
  shows "bind m f = bind m' g"
  using assms by (cases m') auto

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

(* Admissibility of "every successful result satisfies P", which gives the
   induction rule [f.fixp_induct] for every function defined with
   [partial_function (result)]: to prove [P x y] from [f x = Ok y] it
   suffices to prove it for one unfolding of the body, assuming it for the
   recursive calls. *)
lemma result_admissible:
  "result.admissible (\<lambda>(f :: 'a \<Rightarrow> 'b result). \<forall>x y. f x = Ok y \<longrightarrow> P x y)"
proof (rule ccpo.admissibleI)
  fix A :: "('a \<Rightarrow> 'b result) set"
  assume ch: "Complete_Partial_Order.chain result.le_fun A"
    and IH: "\<forall>f\<in>A. \<forall>x y. f x = Ok y \<longrightarrow> P x y"
  from ch have ch': "\<And>x. Complete_Partial_Order.chain result_ord {y. \<exists>f\<in>A. y = f x}"
    by (rule chain_fun)
  show "\<forall>x y. result.lub_fun A x = Ok y \<longrightarrow> P x y"
  proof (intro allI impI)
    fix x y assume "result.lub_fun A x = Ok y"
    from flat_lub_in_chain[OF ch' this[unfolded fun_lub_def]]
    have "Ok y \<in> {y. \<exists>f\<in>A. y = f x}" by simp
    then have "\<exists>f\<in>A. f x = Ok y" by auto
    with IH show "P x y" by auto
  qed
qed

lemma fixp_induct_result:
  fixes F :: "'c \<Rightarrow> 'c" and
    U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a result" and
    C :: "('b \<Rightarrow> 'a result) \<Rightarrow> 'c" and
    P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono: "\<And>x. mono_result (\<lambda>f. U (F (C f)) x)"
  assumes eq: "f \<equiv> C (ccpo.fixp (fun_lub (flat_lub Diverge)) (fun_ord result_ord) (\<lambda>f. U (F (C f))))"
  assumes inverse2: "\<And>f. U (C f) = f"
  assumes step: "\<And>f x y. (\<And>x y. U f x = Ok y \<Longrightarrow> P x y) \<Longrightarrow> U (F f) x = Ok y \<Longrightarrow> P x y"
  assumes defined: "U f x = Ok y"
  shows "P x y"
  using step defined result.fixp_induct_uc[of U F C, OF mono eq inverse2 result_admissible]
  unfolding fun_lub_def flat_lub_def by (auto 9 2)

declaration \<open>Partial_Function.init "result" @{term result.fixp_fun}
  @{term result.mono_body} @{thm result.fixp_rule_uc} @{thm result.fixp_induct_uc}
  (SOME @{thm fixp_induct_result})\<close>

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

(** The Rust never type [!].  Aeneas prints it as [Never].  Every HOL type is
    inhabited, so an abstract type is the closest encoding: no closed term of
    type [Never] is ever produced by a translated program, but the type itself
    cannot be empty. *)
typedecl Never

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

definition core_num_Usize_MIN :: usize where "core_num_Usize_MIN = usize_min"
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

definition core_num_Isize_MIN :: isize where "core_num_Isize_MIN = isize_min"
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

definition core_num_Usize_MAX :: usize where "core_num_Usize_MAX = usize_max"
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

definition core_num_Isize_MAX :: isize where "core_num_Isize_MAX = isize_max"
(*** core *)

(** Trait declaration: [core::convert::From].  Aeneas passes trait evidence as
    an explicit dictionary, with the target type first and the source type
    second. *)
record ('self, 'source) core_convert_From =
  from_' :: "'source \<Rightarrow> 'self result"

(** The blanket [Into] implementation delegates to its [From] dictionary. *)
definition core_convert_Into_Blanket_into ::
  "('u, 't) core_convert_From \<Rightarrow> 't \<Rightarrow> 'u result" where
  "core_convert_Into_Blanket_into from_inst x = from_' from_inst x"

(** Widening conversion from [u16] to [u32]. *)
definition core_convert_num_FromU32U16_from :: "u16 \<Rightarrow> u32 result" where
  "core_convert_num_FromU32U16_from x = scalar_cast U16 U32 x"

definition core_convert_FromU32U16 :: "(u32, u16) core_convert_From" where
  "core_convert_FromU32U16 = (|
    from_' = core_convert_num_FromU32U16_from
  |)"

(** Trait declaration: [core::clone::Clone] *)
record 'self core_clone_Clone =
  core_clone_Clone_clone :: "'self \<Rightarrow> 'self result"
  core_clone_Clone_clone_from :: "'self \<Rightarrow> 'self \<Rightarrow> 'self result"

(* [Clone] and [Copy] instances for the machine integers: cloning is the
   identity. *)
definition core_clone_impls_CloneI8_clone :: "i8 \<Rightarrow> i8" where
  "core_clone_impls_CloneI8_clone x = x"
definition core_clone_impls_CloneI8_clone_from :: "i8 \<Rightarrow> i8 \<Rightarrow> i8" where
  "core_clone_impls_CloneI8_clone_from _ y = y"
definition core_clone_CloneI8 :: "i8 core_clone_Clone" where
  "core_clone_CloneI8 = (|
    core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition core_clone_impls_CloneI16_clone :: "i16 \<Rightarrow> i16" where
  "core_clone_impls_CloneI16_clone x = x"
definition core_clone_impls_CloneI16_clone_from :: "i16 \<Rightarrow> i16 \<Rightarrow> i16" where
  "core_clone_impls_CloneI16_clone_from _ y = y"
definition core_clone_CloneI16 :: "i16 core_clone_Clone" where
  "core_clone_CloneI16 = (|
    core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition core_clone_impls_CloneI32_clone :: "i32 \<Rightarrow> i32" where
  "core_clone_impls_CloneI32_clone x = x"
definition core_clone_impls_CloneI32_clone_from :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" where
  "core_clone_impls_CloneI32_clone_from _ y = y"
definition core_clone_CloneI32 :: "i32 core_clone_Clone" where
  "core_clone_CloneI32 = (|
    core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition core_clone_impls_CloneI64_clone :: "i64 \<Rightarrow> i64" where
  "core_clone_impls_CloneI64_clone x = x"
definition core_clone_impls_CloneI64_clone_from :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" where
  "core_clone_impls_CloneI64_clone_from _ y = y"
definition core_clone_CloneI64 :: "i64 core_clone_Clone" where
  "core_clone_CloneI64 = (|
    core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition core_clone_impls_CloneI128_clone :: "i128 \<Rightarrow> i128" where
  "core_clone_impls_CloneI128_clone x = x"
definition core_clone_impls_CloneI128_clone_from :: "i128 \<Rightarrow> i128 \<Rightarrow> i128" where
  "core_clone_impls_CloneI128_clone_from _ y = y"
definition core_clone_CloneI128 :: "i128 core_clone_Clone" where
  "core_clone_CloneI128 = (|
    core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition core_clone_impls_CloneIsize_clone :: "isize \<Rightarrow> isize" where
  "core_clone_impls_CloneIsize_clone x = x"
definition core_clone_impls_CloneIsize_clone_from :: "isize \<Rightarrow> isize \<Rightarrow> isize" where
  "core_clone_impls_CloneIsize_clone_from _ y = y"
definition core_clone_CloneIsize :: "isize core_clone_Clone" where
  "core_clone_CloneIsize = (|
    core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition core_clone_impls_CloneU8_clone :: "u8 \<Rightarrow> u8" where
  "core_clone_impls_CloneU8_clone x = x"
definition core_clone_impls_CloneU8_clone_from :: "u8 \<Rightarrow> u8 \<Rightarrow> u8" where
  "core_clone_impls_CloneU8_clone_from _ y = y"
definition core_clone_CloneU8 :: "u8 core_clone_Clone" where
  "core_clone_CloneU8 = (|
    core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition core_clone_impls_CloneU16_clone :: "u16 \<Rightarrow> u16" where
  "core_clone_impls_CloneU16_clone x = x"
definition core_clone_impls_CloneU16_clone_from :: "u16 \<Rightarrow> u16 \<Rightarrow> u16" where
  "core_clone_impls_CloneU16_clone_from _ y = y"
definition core_clone_CloneU16 :: "u16 core_clone_Clone" where
  "core_clone_CloneU16 = (|
    core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition core_clone_impls_CloneU32_clone :: "u32 \<Rightarrow> u32" where
  "core_clone_impls_CloneU32_clone x = x"
definition core_clone_impls_CloneU32_clone_from :: "u32 \<Rightarrow> u32 \<Rightarrow> u32" where
  "core_clone_impls_CloneU32_clone_from _ y = y"
definition core_clone_CloneU32 :: "u32 core_clone_Clone" where
  "core_clone_CloneU32 = (|
    core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition core_clone_impls_CloneU64_clone :: "u64 \<Rightarrow> u64" where
  "core_clone_impls_CloneU64_clone x = x"
definition core_clone_impls_CloneU64_clone_from :: "u64 \<Rightarrow> u64 \<Rightarrow> u64" where
  "core_clone_impls_CloneU64_clone_from _ y = y"
definition core_clone_CloneU64 :: "u64 core_clone_Clone" where
  "core_clone_CloneU64 = (|
    core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition core_clone_impls_CloneU128_clone :: "u128 \<Rightarrow> u128" where
  "core_clone_impls_CloneU128_clone x = x"
definition core_clone_impls_CloneU128_clone_from :: "u128 \<Rightarrow> u128 \<Rightarrow> u128" where
  "core_clone_impls_CloneU128_clone_from _ y = y"
definition core_clone_CloneU128 :: "u128 core_clone_Clone" where
  "core_clone_CloneU128 = (|
    core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition core_clone_impls_CloneUsize_clone :: "usize \<Rightarrow> usize" where
  "core_clone_impls_CloneUsize_clone x = x"
definition core_clone_impls_CloneUsize_clone_from :: "usize \<Rightarrow> usize \<Rightarrow> usize" where
  "core_clone_impls_CloneUsize_clone_from _ y = y"
definition core_clone_CloneUsize :: "usize core_clone_Clone" where
  "core_clone_CloneUsize = (|
    core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"

record 'self core_marker_Copy =
  cloneInst :: "'self core_clone_Clone"

definition core_marker_CopyI8 :: "i8 core_marker_Copy" where
  "core_marker_CopyI8 = (| cloneInst = core_clone_CloneI8 |)"
definition core_marker_CopyI16 :: "i16 core_marker_Copy" where
  "core_marker_CopyI16 = (| cloneInst = core_clone_CloneI16 |)"
definition core_marker_CopyI32 :: "i32 core_marker_Copy" where
  "core_marker_CopyI32 = (| cloneInst = core_clone_CloneI32 |)"
definition core_marker_CopyI64 :: "i64 core_marker_Copy" where
  "core_marker_CopyI64 = (| cloneInst = core_clone_CloneI64 |)"
definition core_marker_CopyI128 :: "i128 core_marker_Copy" where
  "core_marker_CopyI128 = (| cloneInst = core_clone_CloneI128 |)"
definition core_marker_CopyIsize :: "isize core_marker_Copy" where
  "core_marker_CopyIsize = (| cloneInst = core_clone_CloneIsize |)"
definition core_marker_CopyU8 :: "u8 core_marker_Copy" where
  "core_marker_CopyU8 = (| cloneInst = core_clone_CloneU8 |)"
definition core_marker_CopyU16 :: "u16 core_marker_Copy" where
  "core_marker_CopyU16 = (| cloneInst = core_clone_CloneU16 |)"
definition core_marker_CopyU32 :: "u32 core_marker_Copy" where
  "core_marker_CopyU32 = (| cloneInst = core_clone_CloneU32 |)"
definition core_marker_CopyU64 :: "u64 core_marker_Copy" where
  "core_marker_CopyU64 = (| cloneInst = core_clone_CloneU64 |)"
definition core_marker_CopyU128 :: "u128 core_marker_Copy" where
  "core_marker_CopyU128 = (| cloneInst = core_clone_CloneU128 |)"
definition core_marker_CopyUsize :: "usize core_marker_Copy" where
  "core_marker_CopyUsize = (| cloneInst = core_clone_CloneUsize |)"

(* Checked arithmetic ([checked_add], ...): [None] on overflow or division
   by zero, following [core::num::{INT}::checked_*]. *)
definition scalar_checked_op :: "scalar_ty \<Rightarrow> int result \<Rightarrow> int option" where
  "scalar_checked_op ty r = (case r of Ok v \<Rightarrow> Some v | _ \<Rightarrow> None)"

(* Number of leading zero bits of the unsigned bit pattern of a value. *)
definition scalar_leading_zeros :: "scalar_ty \<Rightarrow> int \<Rightarrow> u32" where
  "scalar_leading_zeros ty x =
    (let u = x mod scalar_modulus ty; b = scalar_bits ty in
     int (b - (LEAST n. u < 2 ^ n)))"

definition I8_checked_add :: "i8 \<Rightarrow> i8 \<Rightarrow> i8 option" where
  "I8_checked_add x y = scalar_checked_op I8 (scalar_add I8 x y)"
definition I8_checked_sub :: "i8 \<Rightarrow> i8 \<Rightarrow> i8 option" where
  "I8_checked_sub x y = scalar_checked_op I8 (scalar_sub I8 x y)"
definition I8_checked_mul :: "i8 \<Rightarrow> i8 \<Rightarrow> i8 option" where
  "I8_checked_mul x y = scalar_checked_op I8 (scalar_mul I8 x y)"
definition I8_checked_div :: "i8 \<Rightarrow> i8 \<Rightarrow> i8 option" where
  "I8_checked_div x y = scalar_checked_op I8 (scalar_div I8 x y)"
definition I8_checked_rem :: "i8 \<Rightarrow> i8 \<Rightarrow> i8 option" where
  "I8_checked_rem x y = scalar_checked_op I8 (scalar_rem I8 x y)"
definition core_num_I8_leading_zeros :: "i8 \<Rightarrow> u32" where
  "core_num_I8_leading_zeros x = scalar_leading_zeros I8 x"
definition I16_checked_add :: "i16 \<Rightarrow> i16 \<Rightarrow> i16 option" where
  "I16_checked_add x y = scalar_checked_op I16 (scalar_add I16 x y)"
definition I16_checked_sub :: "i16 \<Rightarrow> i16 \<Rightarrow> i16 option" where
  "I16_checked_sub x y = scalar_checked_op I16 (scalar_sub I16 x y)"
definition I16_checked_mul :: "i16 \<Rightarrow> i16 \<Rightarrow> i16 option" where
  "I16_checked_mul x y = scalar_checked_op I16 (scalar_mul I16 x y)"
definition I16_checked_div :: "i16 \<Rightarrow> i16 \<Rightarrow> i16 option" where
  "I16_checked_div x y = scalar_checked_op I16 (scalar_div I16 x y)"
definition I16_checked_rem :: "i16 \<Rightarrow> i16 \<Rightarrow> i16 option" where
  "I16_checked_rem x y = scalar_checked_op I16 (scalar_rem I16 x y)"
definition core_num_I16_leading_zeros :: "i16 \<Rightarrow> u32" where
  "core_num_I16_leading_zeros x = scalar_leading_zeros I16 x"
definition I32_checked_add :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" where
  "I32_checked_add x y = scalar_checked_op I32 (scalar_add I32 x y)"
definition I32_checked_sub :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" where
  "I32_checked_sub x y = scalar_checked_op I32 (scalar_sub I32 x y)"
definition I32_checked_mul :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" where
  "I32_checked_mul x y = scalar_checked_op I32 (scalar_mul I32 x y)"
definition I32_checked_div :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" where
  "I32_checked_div x y = scalar_checked_op I32 (scalar_div I32 x y)"
definition I32_checked_rem :: "i32 \<Rightarrow> i32 \<Rightarrow> i32 option" where
  "I32_checked_rem x y = scalar_checked_op I32 (scalar_rem I32 x y)"
definition core_num_I32_leading_zeros :: "i32 \<Rightarrow> u32" where
  "core_num_I32_leading_zeros x = scalar_leading_zeros I32 x"
definition I64_checked_add :: "i64 \<Rightarrow> i64 \<Rightarrow> i64 option" where
  "I64_checked_add x y = scalar_checked_op I64 (scalar_add I64 x y)"
definition I64_checked_sub :: "i64 \<Rightarrow> i64 \<Rightarrow> i64 option" where
  "I64_checked_sub x y = scalar_checked_op I64 (scalar_sub I64 x y)"
definition I64_checked_mul :: "i64 \<Rightarrow> i64 \<Rightarrow> i64 option" where
  "I64_checked_mul x y = scalar_checked_op I64 (scalar_mul I64 x y)"
definition I64_checked_div :: "i64 \<Rightarrow> i64 \<Rightarrow> i64 option" where
  "I64_checked_div x y = scalar_checked_op I64 (scalar_div I64 x y)"
definition I64_checked_rem :: "i64 \<Rightarrow> i64 \<Rightarrow> i64 option" where
  "I64_checked_rem x y = scalar_checked_op I64 (scalar_rem I64 x y)"
definition core_num_I64_leading_zeros :: "i64 \<Rightarrow> u32" where
  "core_num_I64_leading_zeros x = scalar_leading_zeros I64 x"
definition I128_checked_add :: "i128 \<Rightarrow> i128 \<Rightarrow> i128 option" where
  "I128_checked_add x y = scalar_checked_op I128 (scalar_add I128 x y)"
definition I128_checked_sub :: "i128 \<Rightarrow> i128 \<Rightarrow> i128 option" where
  "I128_checked_sub x y = scalar_checked_op I128 (scalar_sub I128 x y)"
definition I128_checked_mul :: "i128 \<Rightarrow> i128 \<Rightarrow> i128 option" where
  "I128_checked_mul x y = scalar_checked_op I128 (scalar_mul I128 x y)"
definition I128_checked_div :: "i128 \<Rightarrow> i128 \<Rightarrow> i128 option" where
  "I128_checked_div x y = scalar_checked_op I128 (scalar_div I128 x y)"
definition I128_checked_rem :: "i128 \<Rightarrow> i128 \<Rightarrow> i128 option" where
  "I128_checked_rem x y = scalar_checked_op I128 (scalar_rem I128 x y)"
definition core_num_I128_leading_zeros :: "i128 \<Rightarrow> u32" where
  "core_num_I128_leading_zeros x = scalar_leading_zeros I128 x"
definition Isize_checked_add :: "isize \<Rightarrow> isize \<Rightarrow> isize option" where
  "Isize_checked_add x y = scalar_checked_op Isize (scalar_add Isize x y)"
definition Isize_checked_sub :: "isize \<Rightarrow> isize \<Rightarrow> isize option" where
  "Isize_checked_sub x y = scalar_checked_op Isize (scalar_sub Isize x y)"
definition Isize_checked_mul :: "isize \<Rightarrow> isize \<Rightarrow> isize option" where
  "Isize_checked_mul x y = scalar_checked_op Isize (scalar_mul Isize x y)"
definition Isize_checked_div :: "isize \<Rightarrow> isize \<Rightarrow> isize option" where
  "Isize_checked_div x y = scalar_checked_op Isize (scalar_div Isize x y)"
definition Isize_checked_rem :: "isize \<Rightarrow> isize \<Rightarrow> isize option" where
  "Isize_checked_rem x y = scalar_checked_op Isize (scalar_rem Isize x y)"
definition core_num_Isize_leading_zeros :: "isize \<Rightarrow> u32" where
  "core_num_Isize_leading_zeros x = scalar_leading_zeros Isize x"
definition U8_checked_add :: "u8 \<Rightarrow> u8 \<Rightarrow> u8 option" where
  "U8_checked_add x y = scalar_checked_op U8 (scalar_add U8 x y)"
definition U8_checked_sub :: "u8 \<Rightarrow> u8 \<Rightarrow> u8 option" where
  "U8_checked_sub x y = scalar_checked_op U8 (scalar_sub U8 x y)"
definition U8_checked_mul :: "u8 \<Rightarrow> u8 \<Rightarrow> u8 option" where
  "U8_checked_mul x y = scalar_checked_op U8 (scalar_mul U8 x y)"
definition U8_checked_div :: "u8 \<Rightarrow> u8 \<Rightarrow> u8 option" where
  "U8_checked_div x y = scalar_checked_op U8 (scalar_div U8 x y)"
definition U8_checked_rem :: "u8 \<Rightarrow> u8 \<Rightarrow> u8 option" where
  "U8_checked_rem x y = scalar_checked_op U8 (scalar_rem U8 x y)"
definition core_num_U8_leading_zeros :: "u8 \<Rightarrow> u32" where
  "core_num_U8_leading_zeros x = scalar_leading_zeros U8 x"
definition U16_checked_add :: "u16 \<Rightarrow> u16 \<Rightarrow> u16 option" where
  "U16_checked_add x y = scalar_checked_op U16 (scalar_add U16 x y)"
definition U16_checked_sub :: "u16 \<Rightarrow> u16 \<Rightarrow> u16 option" where
  "U16_checked_sub x y = scalar_checked_op U16 (scalar_sub U16 x y)"
definition U16_checked_mul :: "u16 \<Rightarrow> u16 \<Rightarrow> u16 option" where
  "U16_checked_mul x y = scalar_checked_op U16 (scalar_mul U16 x y)"
definition U16_checked_div :: "u16 \<Rightarrow> u16 \<Rightarrow> u16 option" where
  "U16_checked_div x y = scalar_checked_op U16 (scalar_div U16 x y)"
definition U16_checked_rem :: "u16 \<Rightarrow> u16 \<Rightarrow> u16 option" where
  "U16_checked_rem x y = scalar_checked_op U16 (scalar_rem U16 x y)"
definition core_num_U16_leading_zeros :: "u16 \<Rightarrow> u32" where
  "core_num_U16_leading_zeros x = scalar_leading_zeros U16 x"
definition U32_checked_add :: "u32 \<Rightarrow> u32 \<Rightarrow> u32 option" where
  "U32_checked_add x y = scalar_checked_op U32 (scalar_add U32 x y)"
definition U32_checked_sub :: "u32 \<Rightarrow> u32 \<Rightarrow> u32 option" where
  "U32_checked_sub x y = scalar_checked_op U32 (scalar_sub U32 x y)"
definition U32_checked_mul :: "u32 \<Rightarrow> u32 \<Rightarrow> u32 option" where
  "U32_checked_mul x y = scalar_checked_op U32 (scalar_mul U32 x y)"
definition U32_checked_div :: "u32 \<Rightarrow> u32 \<Rightarrow> u32 option" where
  "U32_checked_div x y = scalar_checked_op U32 (scalar_div U32 x y)"
definition U32_checked_rem :: "u32 \<Rightarrow> u32 \<Rightarrow> u32 option" where
  "U32_checked_rem x y = scalar_checked_op U32 (scalar_rem U32 x y)"
definition core_num_U32_leading_zeros :: "u32 \<Rightarrow> u32" where
  "core_num_U32_leading_zeros x = scalar_leading_zeros U32 x"
definition U64_checked_add :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" where
  "U64_checked_add x y = scalar_checked_op U64 (scalar_add U64 x y)"
definition U64_checked_sub :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" where
  "U64_checked_sub x y = scalar_checked_op U64 (scalar_sub U64 x y)"
definition U64_checked_mul :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" where
  "U64_checked_mul x y = scalar_checked_op U64 (scalar_mul U64 x y)"
definition U64_checked_div :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" where
  "U64_checked_div x y = scalar_checked_op U64 (scalar_div U64 x y)"
definition U64_checked_rem :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" where
  "U64_checked_rem x y = scalar_checked_op U64 (scalar_rem U64 x y)"
definition core_num_U64_leading_zeros :: "u64 \<Rightarrow> u32" where
  "core_num_U64_leading_zeros x = scalar_leading_zeros U64 x"
definition U128_checked_add :: "u128 \<Rightarrow> u128 \<Rightarrow> u128 option" where
  "U128_checked_add x y = scalar_checked_op U128 (scalar_add U128 x y)"
definition U128_checked_sub :: "u128 \<Rightarrow> u128 \<Rightarrow> u128 option" where
  "U128_checked_sub x y = scalar_checked_op U128 (scalar_sub U128 x y)"
definition U128_checked_mul :: "u128 \<Rightarrow> u128 \<Rightarrow> u128 option" where
  "U128_checked_mul x y = scalar_checked_op U128 (scalar_mul U128 x y)"
definition U128_checked_div :: "u128 \<Rightarrow> u128 \<Rightarrow> u128 option" where
  "U128_checked_div x y = scalar_checked_op U128 (scalar_div U128 x y)"
definition U128_checked_rem :: "u128 \<Rightarrow> u128 \<Rightarrow> u128 option" where
  "U128_checked_rem x y = scalar_checked_op U128 (scalar_rem U128 x y)"
definition core_num_U128_leading_zeros :: "u128 \<Rightarrow> u32" where
  "core_num_U128_leading_zeros x = scalar_leading_zeros U128 x"
definition Usize_checked_add :: "usize \<Rightarrow> usize \<Rightarrow> usize option" where
  "Usize_checked_add x y = scalar_checked_op Usize (scalar_add Usize x y)"
definition Usize_checked_sub :: "usize \<Rightarrow> usize \<Rightarrow> usize option" where
  "Usize_checked_sub x y = scalar_checked_op Usize (scalar_sub Usize x y)"
definition Usize_checked_mul :: "usize \<Rightarrow> usize \<Rightarrow> usize option" where
  "Usize_checked_mul x y = scalar_checked_op Usize (scalar_mul Usize x y)"
definition Usize_checked_div :: "usize \<Rightarrow> usize \<Rightarrow> usize option" where
  "Usize_checked_div x y = scalar_checked_op Usize (scalar_div Usize x y)"
definition Usize_checked_rem :: "usize \<Rightarrow> usize \<Rightarrow> usize option" where
  "Usize_checked_rem x y = scalar_checked_op Usize (scalar_rem Usize x y)"
definition core_num_Usize_leading_zeros :: "usize \<Rightarrow> u32" where
  "core_num_Usize_leading_zeros x = scalar_leading_zeros Usize x"

(* Wrapping arithmetic ([wrapping_add], ...): reduce modulo 2^bits. *)
definition core_num_I8_wrapping_add :: "i8 \<Rightarrow> i8 \<Rightarrow> i8" where
  "core_num_I8_wrapping_add x y = scalar_wrapping_add I8 x y"
definition core_num_I8_wrapping_sub :: "i8 \<Rightarrow> i8 \<Rightarrow> i8" where
  "core_num_I8_wrapping_sub x y = scalar_wrapping_sub I8 x y"
definition core_num_I8_wrapping_mul :: "i8 \<Rightarrow> i8 \<Rightarrow> i8" where
  "core_num_I8_wrapping_mul x y = scalar_wrapping_mul I8 x y"
definition core_num_I8_wrapping_neg :: "i8 \<Rightarrow> i8" where
  "core_num_I8_wrapping_neg x = scalar_wrapping_neg I8 x"
definition core_num_I8_wrapping_shl :: "i8 \<Rightarrow> u32 \<Rightarrow> i8" where
  "core_num_I8_wrapping_shl x n = scalar_wrapping_shl I8 x n"
definition core_num_I8_wrapping_shr :: "i8 \<Rightarrow> u32 \<Rightarrow> i8" where
  "core_num_I8_wrapping_shr x n = scalar_wrapping_shr I8 x n"
definition core_num_I16_wrapping_add :: "i16 \<Rightarrow> i16 \<Rightarrow> i16" where
  "core_num_I16_wrapping_add x y = scalar_wrapping_add I16 x y"
definition core_num_I16_wrapping_sub :: "i16 \<Rightarrow> i16 \<Rightarrow> i16" where
  "core_num_I16_wrapping_sub x y = scalar_wrapping_sub I16 x y"
definition core_num_I16_wrapping_mul :: "i16 \<Rightarrow> i16 \<Rightarrow> i16" where
  "core_num_I16_wrapping_mul x y = scalar_wrapping_mul I16 x y"
definition core_num_I16_wrapping_neg :: "i16 \<Rightarrow> i16" where
  "core_num_I16_wrapping_neg x = scalar_wrapping_neg I16 x"
definition core_num_I16_wrapping_shl :: "i16 \<Rightarrow> u32 \<Rightarrow> i16" where
  "core_num_I16_wrapping_shl x n = scalar_wrapping_shl I16 x n"
definition core_num_I16_wrapping_shr :: "i16 \<Rightarrow> u32 \<Rightarrow> i16" where
  "core_num_I16_wrapping_shr x n = scalar_wrapping_shr I16 x n"
definition core_num_I32_wrapping_add :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" where
  "core_num_I32_wrapping_add x y = scalar_wrapping_add I32 x y"
definition core_num_I32_wrapping_sub :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" where
  "core_num_I32_wrapping_sub x y = scalar_wrapping_sub I32 x y"
definition core_num_I32_wrapping_mul :: "i32 \<Rightarrow> i32 \<Rightarrow> i32" where
  "core_num_I32_wrapping_mul x y = scalar_wrapping_mul I32 x y"
definition core_num_I32_wrapping_neg :: "i32 \<Rightarrow> i32" where
  "core_num_I32_wrapping_neg x = scalar_wrapping_neg I32 x"
definition core_num_I32_wrapping_shl :: "i32 \<Rightarrow> u32 \<Rightarrow> i32" where
  "core_num_I32_wrapping_shl x n = scalar_wrapping_shl I32 x n"
definition core_num_I32_wrapping_shr :: "i32 \<Rightarrow> u32 \<Rightarrow> i32" where
  "core_num_I32_wrapping_shr x n = scalar_wrapping_shr I32 x n"
definition core_num_I64_wrapping_add :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" where
  "core_num_I64_wrapping_add x y = scalar_wrapping_add I64 x y"
definition core_num_I64_wrapping_sub :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" where
  "core_num_I64_wrapping_sub x y = scalar_wrapping_sub I64 x y"
definition core_num_I64_wrapping_mul :: "i64 \<Rightarrow> i64 \<Rightarrow> i64" where
  "core_num_I64_wrapping_mul x y = scalar_wrapping_mul I64 x y"
definition core_num_I64_wrapping_neg :: "i64 \<Rightarrow> i64" where
  "core_num_I64_wrapping_neg x = scalar_wrapping_neg I64 x"
definition core_num_I64_wrapping_shl :: "i64 \<Rightarrow> u32 \<Rightarrow> i64" where
  "core_num_I64_wrapping_shl x n = scalar_wrapping_shl I64 x n"
definition core_num_I64_wrapping_shr :: "i64 \<Rightarrow> u32 \<Rightarrow> i64" where
  "core_num_I64_wrapping_shr x n = scalar_wrapping_shr I64 x n"
definition core_num_I128_wrapping_add :: "i128 \<Rightarrow> i128 \<Rightarrow> i128" where
  "core_num_I128_wrapping_add x y = scalar_wrapping_add I128 x y"
definition core_num_I128_wrapping_sub :: "i128 \<Rightarrow> i128 \<Rightarrow> i128" where
  "core_num_I128_wrapping_sub x y = scalar_wrapping_sub I128 x y"
definition core_num_I128_wrapping_mul :: "i128 \<Rightarrow> i128 \<Rightarrow> i128" where
  "core_num_I128_wrapping_mul x y = scalar_wrapping_mul I128 x y"
definition core_num_I128_wrapping_neg :: "i128 \<Rightarrow> i128" where
  "core_num_I128_wrapping_neg x = scalar_wrapping_neg I128 x"
definition core_num_I128_wrapping_shl :: "i128 \<Rightarrow> u32 \<Rightarrow> i128" where
  "core_num_I128_wrapping_shl x n = scalar_wrapping_shl I128 x n"
definition core_num_I128_wrapping_shr :: "i128 \<Rightarrow> u32 \<Rightarrow> i128" where
  "core_num_I128_wrapping_shr x n = scalar_wrapping_shr I128 x n"
definition core_num_Isize_wrapping_add :: "isize \<Rightarrow> isize \<Rightarrow> isize" where
  "core_num_Isize_wrapping_add x y = scalar_wrapping_add Isize x y"
definition core_num_Isize_wrapping_sub :: "isize \<Rightarrow> isize \<Rightarrow> isize" where
  "core_num_Isize_wrapping_sub x y = scalar_wrapping_sub Isize x y"
definition core_num_Isize_wrapping_mul :: "isize \<Rightarrow> isize \<Rightarrow> isize" where
  "core_num_Isize_wrapping_mul x y = scalar_wrapping_mul Isize x y"
definition core_num_Isize_wrapping_neg :: "isize \<Rightarrow> isize" where
  "core_num_Isize_wrapping_neg x = scalar_wrapping_neg Isize x"
definition core_num_Isize_wrapping_shl :: "isize \<Rightarrow> u32 \<Rightarrow> isize" where
  "core_num_Isize_wrapping_shl x n = scalar_wrapping_shl Isize x n"
definition core_num_Isize_wrapping_shr :: "isize \<Rightarrow> u32 \<Rightarrow> isize" where
  "core_num_Isize_wrapping_shr x n = scalar_wrapping_shr Isize x n"
definition core_num_U8_wrapping_add :: "u8 \<Rightarrow> u8 \<Rightarrow> u8" where
  "core_num_U8_wrapping_add x y = scalar_wrapping_add U8 x y"
definition core_num_U8_wrapping_sub :: "u8 \<Rightarrow> u8 \<Rightarrow> u8" where
  "core_num_U8_wrapping_sub x y = scalar_wrapping_sub U8 x y"
definition core_num_U8_wrapping_mul :: "u8 \<Rightarrow> u8 \<Rightarrow> u8" where
  "core_num_U8_wrapping_mul x y = scalar_wrapping_mul U8 x y"
definition core_num_U8_wrapping_neg :: "u8 \<Rightarrow> u8" where
  "core_num_U8_wrapping_neg x = scalar_wrapping_neg U8 x"
definition core_num_U8_wrapping_shl :: "u8 \<Rightarrow> u32 \<Rightarrow> u8" where
  "core_num_U8_wrapping_shl x n = scalar_wrapping_shl U8 x n"
definition core_num_U8_wrapping_shr :: "u8 \<Rightarrow> u32 \<Rightarrow> u8" where
  "core_num_U8_wrapping_shr x n = scalar_wrapping_shr U8 x n"
definition core_num_U16_wrapping_add :: "u16 \<Rightarrow> u16 \<Rightarrow> u16" where
  "core_num_U16_wrapping_add x y = scalar_wrapping_add U16 x y"
definition core_num_U16_wrapping_sub :: "u16 \<Rightarrow> u16 \<Rightarrow> u16" where
  "core_num_U16_wrapping_sub x y = scalar_wrapping_sub U16 x y"
definition core_num_U16_wrapping_mul :: "u16 \<Rightarrow> u16 \<Rightarrow> u16" where
  "core_num_U16_wrapping_mul x y = scalar_wrapping_mul U16 x y"
definition core_num_U16_wrapping_neg :: "u16 \<Rightarrow> u16" where
  "core_num_U16_wrapping_neg x = scalar_wrapping_neg U16 x"
definition core_num_U16_wrapping_shl :: "u16 \<Rightarrow> u32 \<Rightarrow> u16" where
  "core_num_U16_wrapping_shl x n = scalar_wrapping_shl U16 x n"
definition core_num_U16_wrapping_shr :: "u16 \<Rightarrow> u32 \<Rightarrow> u16" where
  "core_num_U16_wrapping_shr x n = scalar_wrapping_shr U16 x n"
definition core_num_U32_wrapping_add :: "u32 \<Rightarrow> u32 \<Rightarrow> u32" where
  "core_num_U32_wrapping_add x y = scalar_wrapping_add U32 x y"
definition core_num_U32_wrapping_sub :: "u32 \<Rightarrow> u32 \<Rightarrow> u32" where
  "core_num_U32_wrapping_sub x y = scalar_wrapping_sub U32 x y"
definition core_num_U32_wrapping_mul :: "u32 \<Rightarrow> u32 \<Rightarrow> u32" where
  "core_num_U32_wrapping_mul x y = scalar_wrapping_mul U32 x y"
definition core_num_U32_wrapping_neg :: "u32 \<Rightarrow> u32" where
  "core_num_U32_wrapping_neg x = scalar_wrapping_neg U32 x"
definition core_num_U32_wrapping_shl :: "u32 \<Rightarrow> u32 \<Rightarrow> u32" where
  "core_num_U32_wrapping_shl x n = scalar_wrapping_shl U32 x n"
definition core_num_U32_wrapping_shr :: "u32 \<Rightarrow> u32 \<Rightarrow> u32" where
  "core_num_U32_wrapping_shr x n = scalar_wrapping_shr U32 x n"
definition core_num_U64_wrapping_add :: "u64 \<Rightarrow> u64 \<Rightarrow> u64" where
  "core_num_U64_wrapping_add x y = scalar_wrapping_add U64 x y"
definition core_num_U64_wrapping_sub :: "u64 \<Rightarrow> u64 \<Rightarrow> u64" where
  "core_num_U64_wrapping_sub x y = scalar_wrapping_sub U64 x y"
definition core_num_U64_wrapping_mul :: "u64 \<Rightarrow> u64 \<Rightarrow> u64" where
  "core_num_U64_wrapping_mul x y = scalar_wrapping_mul U64 x y"
definition core_num_U64_wrapping_neg :: "u64 \<Rightarrow> u64" where
  "core_num_U64_wrapping_neg x = scalar_wrapping_neg U64 x"
definition core_num_U64_wrapping_shl :: "u64 \<Rightarrow> u32 \<Rightarrow> u64" where
  "core_num_U64_wrapping_shl x n = scalar_wrapping_shl U64 x n"
definition core_num_U64_wrapping_shr :: "u64 \<Rightarrow> u32 \<Rightarrow> u64" where
  "core_num_U64_wrapping_shr x n = scalar_wrapping_shr U64 x n"
definition core_num_U128_wrapping_add :: "u128 \<Rightarrow> u128 \<Rightarrow> u128" where
  "core_num_U128_wrapping_add x y = scalar_wrapping_add U128 x y"
definition core_num_U128_wrapping_sub :: "u128 \<Rightarrow> u128 \<Rightarrow> u128" where
  "core_num_U128_wrapping_sub x y = scalar_wrapping_sub U128 x y"
definition core_num_U128_wrapping_mul :: "u128 \<Rightarrow> u128 \<Rightarrow> u128" where
  "core_num_U128_wrapping_mul x y = scalar_wrapping_mul U128 x y"
definition core_num_U128_wrapping_neg :: "u128 \<Rightarrow> u128" where
  "core_num_U128_wrapping_neg x = scalar_wrapping_neg U128 x"
definition core_num_U128_wrapping_shl :: "u128 \<Rightarrow> u32 \<Rightarrow> u128" where
  "core_num_U128_wrapping_shl x n = scalar_wrapping_shl U128 x n"
definition core_num_U128_wrapping_shr :: "u128 \<Rightarrow> u32 \<Rightarrow> u128" where
  "core_num_U128_wrapping_shr x n = scalar_wrapping_shr U128 x n"
definition core_num_Usize_wrapping_add :: "usize \<Rightarrow> usize \<Rightarrow> usize" where
  "core_num_Usize_wrapping_add x y = scalar_wrapping_add Usize x y"
definition core_num_Usize_wrapping_sub :: "usize \<Rightarrow> usize \<Rightarrow> usize" where
  "core_num_Usize_wrapping_sub x y = scalar_wrapping_sub Usize x y"
definition core_num_Usize_wrapping_mul :: "usize \<Rightarrow> usize \<Rightarrow> usize" where
  "core_num_Usize_wrapping_mul x y = scalar_wrapping_mul Usize x y"
definition core_num_Usize_wrapping_neg :: "usize \<Rightarrow> usize" where
  "core_num_Usize_wrapping_neg x = scalar_wrapping_neg Usize x"
definition core_num_Usize_wrapping_shl :: "usize \<Rightarrow> u32 \<Rightarrow> usize" where
  "core_num_Usize_wrapping_shl x n = scalar_wrapping_shl Usize x n"
definition core_num_Usize_wrapping_shr :: "usize \<Rightarrow> u32 \<Rightarrow> usize" where
  "core_num_Usize_wrapping_shr x n = scalar_wrapping_shr Usize x n"

(* Byte-level encodings of the machine integers: [to_le_bytes], [to_be_bytes],
   [from_le_bytes], [from_be_bytes].  A value is first reduced to its
   unsigned bit pattern; the result is a list of [bits/8] bytes. *)
definition scalar_to_le_bytes :: "scalar_ty \<Rightarrow> int \<Rightarrow> u8 list" where
  "scalar_to_le_bytes ty x =
    (let n = scalar_bits ty div 8; u = x mod scalar_modulus ty in
     map (\<lambda>k. (u div (256 ^ k)) mod 256) [0..<n])"

definition scalar_to_be_bytes :: "scalar_ty \<Rightarrow> int \<Rightarrow> u8 list" where
  "scalar_to_be_bytes ty x = rev (scalar_to_le_bytes ty x)"

definition scalar_from_le_bytes :: "scalar_ty \<Rightarrow> u8 list \<Rightarrow> int" where
  "scalar_from_le_bytes ty bs =
    scalar_wrap ty (\<Sum>k < length bs. (bs ! k) * 256 ^ k)"

definition scalar_from_be_bytes :: "scalar_ty \<Rightarrow> u8 list \<Rightarrow> int" where
  "scalar_from_be_bytes ty bs = scalar_from_le_bytes ty (rev bs)"

definition core_num_I8_to_le_bytes :: "i8 \<Rightarrow> u8 list" where
  "core_num_I8_to_le_bytes x = scalar_to_le_bytes I8 x"
definition core_num_I8_to_be_bytes :: "i8 \<Rightarrow> u8 list" where
  "core_num_I8_to_be_bytes x = scalar_to_be_bytes I8 x"
definition core_num_I8_from_le_bytes :: "u8 list \<Rightarrow> i8" where
  "core_num_I8_from_le_bytes bs = scalar_from_le_bytes I8 bs"
definition core_num_I8_from_be_bytes :: "u8 list \<Rightarrow> i8" where
  "core_num_I8_from_be_bytes bs = scalar_from_be_bytes I8 bs"
definition core_num_I16_to_le_bytes :: "i16 \<Rightarrow> u8 list" where
  "core_num_I16_to_le_bytes x = scalar_to_le_bytes I16 x"
definition core_num_I16_to_be_bytes :: "i16 \<Rightarrow> u8 list" where
  "core_num_I16_to_be_bytes x = scalar_to_be_bytes I16 x"
definition core_num_I16_from_le_bytes :: "u8 list \<Rightarrow> i16" where
  "core_num_I16_from_le_bytes bs = scalar_from_le_bytes I16 bs"
definition core_num_I16_from_be_bytes :: "u8 list \<Rightarrow> i16" where
  "core_num_I16_from_be_bytes bs = scalar_from_be_bytes I16 bs"
definition core_num_I32_to_le_bytes :: "i32 \<Rightarrow> u8 list" where
  "core_num_I32_to_le_bytes x = scalar_to_le_bytes I32 x"
definition core_num_I32_to_be_bytes :: "i32 \<Rightarrow> u8 list" where
  "core_num_I32_to_be_bytes x = scalar_to_be_bytes I32 x"
definition core_num_I32_from_le_bytes :: "u8 list \<Rightarrow> i32" where
  "core_num_I32_from_le_bytes bs = scalar_from_le_bytes I32 bs"
definition core_num_I32_from_be_bytes :: "u8 list \<Rightarrow> i32" where
  "core_num_I32_from_be_bytes bs = scalar_from_be_bytes I32 bs"
definition core_num_I64_to_le_bytes :: "i64 \<Rightarrow> u8 list" where
  "core_num_I64_to_le_bytes x = scalar_to_le_bytes I64 x"
definition core_num_I64_to_be_bytes :: "i64 \<Rightarrow> u8 list" where
  "core_num_I64_to_be_bytes x = scalar_to_be_bytes I64 x"
definition core_num_I64_from_le_bytes :: "u8 list \<Rightarrow> i64" where
  "core_num_I64_from_le_bytes bs = scalar_from_le_bytes I64 bs"
definition core_num_I64_from_be_bytes :: "u8 list \<Rightarrow> i64" where
  "core_num_I64_from_be_bytes bs = scalar_from_be_bytes I64 bs"
definition core_num_I128_to_le_bytes :: "i128 \<Rightarrow> u8 list" where
  "core_num_I128_to_le_bytes x = scalar_to_le_bytes I128 x"
definition core_num_I128_to_be_bytes :: "i128 \<Rightarrow> u8 list" where
  "core_num_I128_to_be_bytes x = scalar_to_be_bytes I128 x"
definition core_num_I128_from_le_bytes :: "u8 list \<Rightarrow> i128" where
  "core_num_I128_from_le_bytes bs = scalar_from_le_bytes I128 bs"
definition core_num_I128_from_be_bytes :: "u8 list \<Rightarrow> i128" where
  "core_num_I128_from_be_bytes bs = scalar_from_be_bytes I128 bs"
definition core_num_Isize_to_le_bytes :: "isize \<Rightarrow> u8 list" where
  "core_num_Isize_to_le_bytes x = scalar_to_le_bytes Isize x"
definition core_num_Isize_to_be_bytes :: "isize \<Rightarrow> u8 list" where
  "core_num_Isize_to_be_bytes x = scalar_to_be_bytes Isize x"
definition core_num_Isize_from_le_bytes :: "u8 list \<Rightarrow> isize" where
  "core_num_Isize_from_le_bytes bs = scalar_from_le_bytes Isize bs"
definition core_num_Isize_from_be_bytes :: "u8 list \<Rightarrow> isize" where
  "core_num_Isize_from_be_bytes bs = scalar_from_be_bytes Isize bs"
definition core_num_U8_to_le_bytes :: "u8 \<Rightarrow> u8 list" where
  "core_num_U8_to_le_bytes x = scalar_to_le_bytes U8 x"
definition core_num_U8_to_be_bytes :: "u8 \<Rightarrow> u8 list" where
  "core_num_U8_to_be_bytes x = scalar_to_be_bytes U8 x"
definition core_num_U8_from_le_bytes :: "u8 list \<Rightarrow> u8" where
  "core_num_U8_from_le_bytes bs = scalar_from_le_bytes U8 bs"
definition core_num_U8_from_be_bytes :: "u8 list \<Rightarrow> u8" where
  "core_num_U8_from_be_bytes bs = scalar_from_be_bytes U8 bs"
definition core_num_U16_to_le_bytes :: "u16 \<Rightarrow> u8 list" where
  "core_num_U16_to_le_bytes x = scalar_to_le_bytes U16 x"
definition core_num_U16_to_be_bytes :: "u16 \<Rightarrow> u8 list" where
  "core_num_U16_to_be_bytes x = scalar_to_be_bytes U16 x"
definition core_num_U16_from_le_bytes :: "u8 list \<Rightarrow> u16" where
  "core_num_U16_from_le_bytes bs = scalar_from_le_bytes U16 bs"
definition core_num_U16_from_be_bytes :: "u8 list \<Rightarrow> u16" where
  "core_num_U16_from_be_bytes bs = scalar_from_be_bytes U16 bs"
definition core_num_U32_to_le_bytes :: "u32 \<Rightarrow> u8 list" where
  "core_num_U32_to_le_bytes x = scalar_to_le_bytes U32 x"
definition core_num_U32_to_be_bytes :: "u32 \<Rightarrow> u8 list" where
  "core_num_U32_to_be_bytes x = scalar_to_be_bytes U32 x"
definition core_num_U32_from_le_bytes :: "u8 list \<Rightarrow> u32" where
  "core_num_U32_from_le_bytes bs = scalar_from_le_bytes U32 bs"
definition core_num_U32_from_be_bytes :: "u8 list \<Rightarrow> u32" where
  "core_num_U32_from_be_bytes bs = scalar_from_be_bytes U32 bs"
definition core_num_U64_to_le_bytes :: "u64 \<Rightarrow> u8 list" where
  "core_num_U64_to_le_bytes x = scalar_to_le_bytes U64 x"
definition core_num_U64_to_be_bytes :: "u64 \<Rightarrow> u8 list" where
  "core_num_U64_to_be_bytes x = scalar_to_be_bytes U64 x"
definition core_num_U64_from_le_bytes :: "u8 list \<Rightarrow> u64" where
  "core_num_U64_from_le_bytes bs = scalar_from_le_bytes U64 bs"
definition core_num_U64_from_be_bytes :: "u8 list \<Rightarrow> u64" where
  "core_num_U64_from_be_bytes bs = scalar_from_be_bytes U64 bs"
definition core_num_U128_to_le_bytes :: "u128 \<Rightarrow> u8 list" where
  "core_num_U128_to_le_bytes x = scalar_to_le_bytes U128 x"
definition core_num_U128_to_be_bytes :: "u128 \<Rightarrow> u8 list" where
  "core_num_U128_to_be_bytes x = scalar_to_be_bytes U128 x"
definition core_num_U128_from_le_bytes :: "u8 list \<Rightarrow> u128" where
  "core_num_U128_from_le_bytes bs = scalar_from_le_bytes U128 bs"
definition core_num_U128_from_be_bytes :: "u8 list \<Rightarrow> u128" where
  "core_num_U128_from_be_bytes bs = scalar_from_be_bytes U128 bs"
definition core_num_Usize_to_le_bytes :: "usize \<Rightarrow> u8 list" where
  "core_num_Usize_to_le_bytes x = scalar_to_le_bytes Usize x"
definition core_num_Usize_to_be_bytes :: "usize \<Rightarrow> u8 list" where
  "core_num_Usize_to_be_bytes x = scalar_to_be_bytes Usize x"
definition core_num_Usize_from_le_bytes :: "u8 list \<Rightarrow> usize" where
  "core_num_Usize_from_le_bytes bs = scalar_from_le_bytes Usize bs"
definition core_num_Usize_from_be_bytes :: "u8 list \<Rightarrow> usize" where
  "core_num_Usize_from_be_bytes bs = scalar_from_be_bytes Usize bs"

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

(* [core::ops::range::RangeTo]: [..end] *)
record 'a core_ops_range_RangeTo =
  core_ops_range_RangeTo_end_' :: 'a

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


(*** core::cmp *)

datatype core_cmp_Ordering =
    core_cmp_Ordering_Less
  | core_cmp_Ordering_Equal
  | core_cmp_Ordering_Greater

(* Trait declaration: [core::cmp::PartialEq] *)
record ('self, 'rhs) core_cmp_PartialEq =
  core_cmp_PartialEq_eq :: "'self \<Rightarrow> 'rhs \<Rightarrow> bool result"
  core_cmp_PartialEq_ne :: "'self \<Rightarrow> 'rhs \<Rightarrow> bool result"

(* Default implementation of [PartialEq::ne], used to fill the record field of
   implementations that do not override it. *)
definition core_cmp_PartialEq_ne_default_body ::
  "('self \<Rightarrow> 'rhs \<Rightarrow> bool result) \<Rightarrow> 'self \<Rightarrow> 'rhs \<Rightarrow> bool result" where
  "core_cmp_PartialEq_ne_default_body eq x y = (b <- eq x y; Ok (\<not> b))"
definition core_cmp_PartialEq_ne_default ::
  "('self, 'rhs) core_cmp_PartialEq \<Rightarrow> 'self \<Rightarrow> 'rhs \<Rightarrow> bool result" where
  "core_cmp_PartialEq_ne_default inst = core_cmp_PartialEq_ne_default_body (core_cmp_PartialEq_eq inst)"

(* Trait declaration: [core::cmp::PartialOrd] *)
record ('self, 'rhs) core_cmp_PartialOrd =
  partialEqInst :: "('self, 'rhs) core_cmp_PartialEq"
  core_cmp_PartialOrd_partial_cmp :: "'self \<Rightarrow> 'rhs \<Rightarrow> (core_cmp_Ordering option) result"
  core_cmp_PartialOrd_lt :: "'self \<Rightarrow> 'rhs \<Rightarrow> bool result"
  core_cmp_PartialOrd_le :: "'self \<Rightarrow> 'rhs \<Rightarrow> bool result"
  core_cmp_PartialOrd_gt :: "'self \<Rightarrow> 'rhs \<Rightarrow> bool result"
  core_cmp_PartialOrd_ge :: "'self \<Rightarrow> 'rhs \<Rightarrow> bool result"

(* Default implementations of the comparison methods in terms of [partial_cmp]. *)
definition core_cmp_PartialOrd_lt_default_body ::
  "('self \<Rightarrow> 'rhs \<Rightarrow> (core_cmp_Ordering option) result) \<Rightarrow> 'self \<Rightarrow> 'rhs \<Rightarrow> bool result" where
  "core_cmp_PartialOrd_lt_default_body pc x y = (c <- pc x y; Ok (c = Some core_cmp_Ordering_Less))"
definition core_cmp_PartialOrd_lt_default ::
  "('self, 'rhs) core_cmp_PartialOrd \<Rightarrow> 'self \<Rightarrow> 'rhs \<Rightarrow> bool result" where
  "core_cmp_PartialOrd_lt_default inst = core_cmp_PartialOrd_lt_default_body (core_cmp_PartialOrd_partial_cmp inst)"
definition core_cmp_PartialOrd_le_default_body ::
  "('self \<Rightarrow> 'rhs \<Rightarrow> (core_cmp_Ordering option) result) \<Rightarrow> 'self \<Rightarrow> 'rhs \<Rightarrow> bool result" where
  "core_cmp_PartialOrd_le_default_body pc x y =
    (c <- pc x y; Ok (c = Some core_cmp_Ordering_Less \<or> c = Some core_cmp_Ordering_Equal))"
definition core_cmp_PartialOrd_le_default ::
  "('self, 'rhs) core_cmp_PartialOrd \<Rightarrow> 'self \<Rightarrow> 'rhs \<Rightarrow> bool result" where
  "core_cmp_PartialOrd_le_default inst = core_cmp_PartialOrd_le_default_body (core_cmp_PartialOrd_partial_cmp inst)"
definition core_cmp_PartialOrd_gt_default_body ::
  "('self \<Rightarrow> 'rhs \<Rightarrow> (core_cmp_Ordering option) result) \<Rightarrow> 'self \<Rightarrow> 'rhs \<Rightarrow> bool result" where
  "core_cmp_PartialOrd_gt_default_body pc x y = (c <- pc x y; Ok (c = Some core_cmp_Ordering_Greater))"
definition core_cmp_PartialOrd_gt_default ::
  "('self, 'rhs) core_cmp_PartialOrd \<Rightarrow> 'self \<Rightarrow> 'rhs \<Rightarrow> bool result" where
  "core_cmp_PartialOrd_gt_default inst = core_cmp_PartialOrd_gt_default_body (core_cmp_PartialOrd_partial_cmp inst)"
definition core_cmp_PartialOrd_ge_default_body ::
  "('self \<Rightarrow> 'rhs \<Rightarrow> (core_cmp_Ordering option) result) \<Rightarrow> 'self \<Rightarrow> 'rhs \<Rightarrow> bool result" where
  "core_cmp_PartialOrd_ge_default_body pc x y =
    (c <- pc x y; Ok (c = Some core_cmp_Ordering_Greater \<or> c = Some core_cmp_Ordering_Equal))"
definition core_cmp_PartialOrd_ge_default ::
  "('self, 'rhs) core_cmp_PartialOrd \<Rightarrow> 'self \<Rightarrow> 'rhs \<Rightarrow> bool result" where
  "core_cmp_PartialOrd_ge_default inst = core_cmp_PartialOrd_ge_default_body (core_cmp_PartialOrd_partial_cmp inst)"

(* Comparison of machine integers (all represented by [int]). *)
definition scalar_partial_cmp :: "int \<Rightarrow> int \<Rightarrow> core_cmp_Ordering option" where
  "scalar_partial_cmp x y =
    Some (if x < y then core_cmp_Ordering_Less
          else if x = y then core_cmp_Ordering_Equal
          else core_cmp_Ordering_Greater)"

definition core_cmp_impls_PartialEqI8_eq :: "i8 \<Rightarrow> i8 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqI8_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqI8_ne :: "i8 \<Rightarrow> i8 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqI8_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqI8 :: "(i8, i8) core_cmp_PartialEq" where
  "core_cmp_PartialEqI8 = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqI8_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqI8_ne |)"
definition core_cmp_impls_PartialOrdI8_partial_cmp ::
  "i8 \<Rightarrow> i8 \<Rightarrow> (core_cmp_Ordering option) result" where
  "core_cmp_impls_PartialOrdI8_partial_cmp x y = Ok (scalar_partial_cmp x y)"
definition core_cmp_impls_PartialOrdI8_lt :: "i8 \<Rightarrow> i8 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI8_lt x y = Ok (x < y)"
definition core_cmp_impls_PartialOrdI8_le :: "i8 \<Rightarrow> i8 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI8_le x y = Ok (x \<le> y)"
definition core_cmp_impls_PartialOrdI8_gt :: "i8 \<Rightarrow> i8 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI8_gt x y = Ok (x > y)"
definition core_cmp_impls_PartialOrdI8_ge :: "i8 \<Rightarrow> i8 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI8_ge x y = Ok (x \<ge> y)"
definition core_cmp_PartialOrdI8 :: "(i8, i8) core_cmp_PartialOrd" where
  "core_cmp_PartialOrdI8 = (|
    partialEqInst = core_cmp_PartialEqI8,
    core_cmp_PartialOrd_partial_cmp = core_cmp_impls_PartialOrdI8_partial_cmp,
    core_cmp_PartialOrd_lt = core_cmp_impls_PartialOrdI8_lt,
    core_cmp_PartialOrd_le = core_cmp_impls_PartialOrdI8_le,
    core_cmp_PartialOrd_gt = core_cmp_impls_PartialOrdI8_gt,
    core_cmp_PartialOrd_ge = core_cmp_impls_PartialOrdI8_ge |)"

definition core_cmp_impls_PartialEqI16_eq :: "i16 \<Rightarrow> i16 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqI16_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqI16_ne :: "i16 \<Rightarrow> i16 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqI16_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqI16 :: "(i16, i16) core_cmp_PartialEq" where
  "core_cmp_PartialEqI16 = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqI16_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqI16_ne |)"
definition core_cmp_impls_PartialOrdI16_partial_cmp ::
  "i16 \<Rightarrow> i16 \<Rightarrow> (core_cmp_Ordering option) result" where
  "core_cmp_impls_PartialOrdI16_partial_cmp x y = Ok (scalar_partial_cmp x y)"
definition core_cmp_impls_PartialOrdI16_lt :: "i16 \<Rightarrow> i16 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI16_lt x y = Ok (x < y)"
definition core_cmp_impls_PartialOrdI16_le :: "i16 \<Rightarrow> i16 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI16_le x y = Ok (x \<le> y)"
definition core_cmp_impls_PartialOrdI16_gt :: "i16 \<Rightarrow> i16 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI16_gt x y = Ok (x > y)"
definition core_cmp_impls_PartialOrdI16_ge :: "i16 \<Rightarrow> i16 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI16_ge x y = Ok (x \<ge> y)"
definition core_cmp_PartialOrdI16 :: "(i16, i16) core_cmp_PartialOrd" where
  "core_cmp_PartialOrdI16 = (|
    partialEqInst = core_cmp_PartialEqI16,
    core_cmp_PartialOrd_partial_cmp = core_cmp_impls_PartialOrdI16_partial_cmp,
    core_cmp_PartialOrd_lt = core_cmp_impls_PartialOrdI16_lt,
    core_cmp_PartialOrd_le = core_cmp_impls_PartialOrdI16_le,
    core_cmp_PartialOrd_gt = core_cmp_impls_PartialOrdI16_gt,
    core_cmp_PartialOrd_ge = core_cmp_impls_PartialOrdI16_ge |)"

definition core_cmp_impls_PartialEqI32_eq :: "i32 \<Rightarrow> i32 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqI32_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqI32_ne :: "i32 \<Rightarrow> i32 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqI32_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqI32 :: "(i32, i32) core_cmp_PartialEq" where
  "core_cmp_PartialEqI32 = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqI32_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqI32_ne |)"
definition core_cmp_impls_PartialOrdI32_partial_cmp ::
  "i32 \<Rightarrow> i32 \<Rightarrow> (core_cmp_Ordering option) result" where
  "core_cmp_impls_PartialOrdI32_partial_cmp x y = Ok (scalar_partial_cmp x y)"
definition core_cmp_impls_PartialOrdI32_lt :: "i32 \<Rightarrow> i32 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI32_lt x y = Ok (x < y)"
definition core_cmp_impls_PartialOrdI32_le :: "i32 \<Rightarrow> i32 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI32_le x y = Ok (x \<le> y)"
definition core_cmp_impls_PartialOrdI32_gt :: "i32 \<Rightarrow> i32 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI32_gt x y = Ok (x > y)"
definition core_cmp_impls_PartialOrdI32_ge :: "i32 \<Rightarrow> i32 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI32_ge x y = Ok (x \<ge> y)"
definition core_cmp_PartialOrdI32 :: "(i32, i32) core_cmp_PartialOrd" where
  "core_cmp_PartialOrdI32 = (|
    partialEqInst = core_cmp_PartialEqI32,
    core_cmp_PartialOrd_partial_cmp = core_cmp_impls_PartialOrdI32_partial_cmp,
    core_cmp_PartialOrd_lt = core_cmp_impls_PartialOrdI32_lt,
    core_cmp_PartialOrd_le = core_cmp_impls_PartialOrdI32_le,
    core_cmp_PartialOrd_gt = core_cmp_impls_PartialOrdI32_gt,
    core_cmp_PartialOrd_ge = core_cmp_impls_PartialOrdI32_ge |)"

definition core_cmp_impls_PartialEqI64_eq :: "i64 \<Rightarrow> i64 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqI64_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqI64_ne :: "i64 \<Rightarrow> i64 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqI64_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqI64 :: "(i64, i64) core_cmp_PartialEq" where
  "core_cmp_PartialEqI64 = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqI64_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqI64_ne |)"
definition core_cmp_impls_PartialOrdI64_partial_cmp ::
  "i64 \<Rightarrow> i64 \<Rightarrow> (core_cmp_Ordering option) result" where
  "core_cmp_impls_PartialOrdI64_partial_cmp x y = Ok (scalar_partial_cmp x y)"
definition core_cmp_impls_PartialOrdI64_lt :: "i64 \<Rightarrow> i64 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI64_lt x y = Ok (x < y)"
definition core_cmp_impls_PartialOrdI64_le :: "i64 \<Rightarrow> i64 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI64_le x y = Ok (x \<le> y)"
definition core_cmp_impls_PartialOrdI64_gt :: "i64 \<Rightarrow> i64 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI64_gt x y = Ok (x > y)"
definition core_cmp_impls_PartialOrdI64_ge :: "i64 \<Rightarrow> i64 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI64_ge x y = Ok (x \<ge> y)"
definition core_cmp_PartialOrdI64 :: "(i64, i64) core_cmp_PartialOrd" where
  "core_cmp_PartialOrdI64 = (|
    partialEqInst = core_cmp_PartialEqI64,
    core_cmp_PartialOrd_partial_cmp = core_cmp_impls_PartialOrdI64_partial_cmp,
    core_cmp_PartialOrd_lt = core_cmp_impls_PartialOrdI64_lt,
    core_cmp_PartialOrd_le = core_cmp_impls_PartialOrdI64_le,
    core_cmp_PartialOrd_gt = core_cmp_impls_PartialOrdI64_gt,
    core_cmp_PartialOrd_ge = core_cmp_impls_PartialOrdI64_ge |)"

definition core_cmp_impls_PartialEqI128_eq :: "i128 \<Rightarrow> i128 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqI128_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqI128_ne :: "i128 \<Rightarrow> i128 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqI128_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqI128 :: "(i128, i128) core_cmp_PartialEq" where
  "core_cmp_PartialEqI128 = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqI128_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqI128_ne |)"
definition core_cmp_impls_PartialOrdI128_partial_cmp ::
  "i128 \<Rightarrow> i128 \<Rightarrow> (core_cmp_Ordering option) result" where
  "core_cmp_impls_PartialOrdI128_partial_cmp x y = Ok (scalar_partial_cmp x y)"
definition core_cmp_impls_PartialOrdI128_lt :: "i128 \<Rightarrow> i128 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI128_lt x y = Ok (x < y)"
definition core_cmp_impls_PartialOrdI128_le :: "i128 \<Rightarrow> i128 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI128_le x y = Ok (x \<le> y)"
definition core_cmp_impls_PartialOrdI128_gt :: "i128 \<Rightarrow> i128 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI128_gt x y = Ok (x > y)"
definition core_cmp_impls_PartialOrdI128_ge :: "i128 \<Rightarrow> i128 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdI128_ge x y = Ok (x \<ge> y)"
definition core_cmp_PartialOrdI128 :: "(i128, i128) core_cmp_PartialOrd" where
  "core_cmp_PartialOrdI128 = (|
    partialEqInst = core_cmp_PartialEqI128,
    core_cmp_PartialOrd_partial_cmp = core_cmp_impls_PartialOrdI128_partial_cmp,
    core_cmp_PartialOrd_lt = core_cmp_impls_PartialOrdI128_lt,
    core_cmp_PartialOrd_le = core_cmp_impls_PartialOrdI128_le,
    core_cmp_PartialOrd_gt = core_cmp_impls_PartialOrdI128_gt,
    core_cmp_PartialOrd_ge = core_cmp_impls_PartialOrdI128_ge |)"

definition core_cmp_impls_PartialEqIsize_eq :: "isize \<Rightarrow> isize \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqIsize_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqIsize_ne :: "isize \<Rightarrow> isize \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqIsize_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqIsize :: "(isize, isize) core_cmp_PartialEq" where
  "core_cmp_PartialEqIsize = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqIsize_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqIsize_ne |)"
definition core_cmp_impls_PartialOrdIsize_partial_cmp ::
  "isize \<Rightarrow> isize \<Rightarrow> (core_cmp_Ordering option) result" where
  "core_cmp_impls_PartialOrdIsize_partial_cmp x y = Ok (scalar_partial_cmp x y)"
definition core_cmp_impls_PartialOrdIsize_lt :: "isize \<Rightarrow> isize \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdIsize_lt x y = Ok (x < y)"
definition core_cmp_impls_PartialOrdIsize_le :: "isize \<Rightarrow> isize \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdIsize_le x y = Ok (x \<le> y)"
definition core_cmp_impls_PartialOrdIsize_gt :: "isize \<Rightarrow> isize \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdIsize_gt x y = Ok (x > y)"
definition core_cmp_impls_PartialOrdIsize_ge :: "isize \<Rightarrow> isize \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdIsize_ge x y = Ok (x \<ge> y)"
definition core_cmp_PartialOrdIsize :: "(isize, isize) core_cmp_PartialOrd" where
  "core_cmp_PartialOrdIsize = (|
    partialEqInst = core_cmp_PartialEqIsize,
    core_cmp_PartialOrd_partial_cmp = core_cmp_impls_PartialOrdIsize_partial_cmp,
    core_cmp_PartialOrd_lt = core_cmp_impls_PartialOrdIsize_lt,
    core_cmp_PartialOrd_le = core_cmp_impls_PartialOrdIsize_le,
    core_cmp_PartialOrd_gt = core_cmp_impls_PartialOrdIsize_gt,
    core_cmp_PartialOrd_ge = core_cmp_impls_PartialOrdIsize_ge |)"

definition core_cmp_impls_PartialEqU8_eq :: "u8 \<Rightarrow> u8 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqU8_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqU8_ne :: "u8 \<Rightarrow> u8 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqU8_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqU8 :: "(u8, u8) core_cmp_PartialEq" where
  "core_cmp_PartialEqU8 = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqU8_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqU8_ne |)"
definition core_cmp_impls_PartialOrdU8_partial_cmp ::
  "u8 \<Rightarrow> u8 \<Rightarrow> (core_cmp_Ordering option) result" where
  "core_cmp_impls_PartialOrdU8_partial_cmp x y = Ok (scalar_partial_cmp x y)"
definition core_cmp_impls_PartialOrdU8_lt :: "u8 \<Rightarrow> u8 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU8_lt x y = Ok (x < y)"
definition core_cmp_impls_PartialOrdU8_le :: "u8 \<Rightarrow> u8 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU8_le x y = Ok (x \<le> y)"
definition core_cmp_impls_PartialOrdU8_gt :: "u8 \<Rightarrow> u8 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU8_gt x y = Ok (x > y)"
definition core_cmp_impls_PartialOrdU8_ge :: "u8 \<Rightarrow> u8 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU8_ge x y = Ok (x \<ge> y)"
definition core_cmp_PartialOrdU8 :: "(u8, u8) core_cmp_PartialOrd" where
  "core_cmp_PartialOrdU8 = (|
    partialEqInst = core_cmp_PartialEqU8,
    core_cmp_PartialOrd_partial_cmp = core_cmp_impls_PartialOrdU8_partial_cmp,
    core_cmp_PartialOrd_lt = core_cmp_impls_PartialOrdU8_lt,
    core_cmp_PartialOrd_le = core_cmp_impls_PartialOrdU8_le,
    core_cmp_PartialOrd_gt = core_cmp_impls_PartialOrdU8_gt,
    core_cmp_PartialOrd_ge = core_cmp_impls_PartialOrdU8_ge |)"

definition core_cmp_impls_PartialEqU16_eq :: "u16 \<Rightarrow> u16 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqU16_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqU16_ne :: "u16 \<Rightarrow> u16 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqU16_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqU16 :: "(u16, u16) core_cmp_PartialEq" where
  "core_cmp_PartialEqU16 = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqU16_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqU16_ne |)"
definition core_cmp_impls_PartialOrdU16_partial_cmp ::
  "u16 \<Rightarrow> u16 \<Rightarrow> (core_cmp_Ordering option) result" where
  "core_cmp_impls_PartialOrdU16_partial_cmp x y = Ok (scalar_partial_cmp x y)"
definition core_cmp_impls_PartialOrdU16_lt :: "u16 \<Rightarrow> u16 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU16_lt x y = Ok (x < y)"
definition core_cmp_impls_PartialOrdU16_le :: "u16 \<Rightarrow> u16 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU16_le x y = Ok (x \<le> y)"
definition core_cmp_impls_PartialOrdU16_gt :: "u16 \<Rightarrow> u16 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU16_gt x y = Ok (x > y)"
definition core_cmp_impls_PartialOrdU16_ge :: "u16 \<Rightarrow> u16 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU16_ge x y = Ok (x \<ge> y)"
definition core_cmp_PartialOrdU16 :: "(u16, u16) core_cmp_PartialOrd" where
  "core_cmp_PartialOrdU16 = (|
    partialEqInst = core_cmp_PartialEqU16,
    core_cmp_PartialOrd_partial_cmp = core_cmp_impls_PartialOrdU16_partial_cmp,
    core_cmp_PartialOrd_lt = core_cmp_impls_PartialOrdU16_lt,
    core_cmp_PartialOrd_le = core_cmp_impls_PartialOrdU16_le,
    core_cmp_PartialOrd_gt = core_cmp_impls_PartialOrdU16_gt,
    core_cmp_PartialOrd_ge = core_cmp_impls_PartialOrdU16_ge |)"

definition core_cmp_impls_PartialEqU32_eq :: "u32 \<Rightarrow> u32 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqU32_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqU32_ne :: "u32 \<Rightarrow> u32 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqU32_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqU32 :: "(u32, u32) core_cmp_PartialEq" where
  "core_cmp_PartialEqU32 = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqU32_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqU32_ne |)"
definition core_cmp_impls_PartialOrdU32_partial_cmp ::
  "u32 \<Rightarrow> u32 \<Rightarrow> (core_cmp_Ordering option) result" where
  "core_cmp_impls_PartialOrdU32_partial_cmp x y = Ok (scalar_partial_cmp x y)"
definition core_cmp_impls_PartialOrdU32_lt :: "u32 \<Rightarrow> u32 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU32_lt x y = Ok (x < y)"
definition core_cmp_impls_PartialOrdU32_le :: "u32 \<Rightarrow> u32 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU32_le x y = Ok (x \<le> y)"
definition core_cmp_impls_PartialOrdU32_gt :: "u32 \<Rightarrow> u32 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU32_gt x y = Ok (x > y)"
definition core_cmp_impls_PartialOrdU32_ge :: "u32 \<Rightarrow> u32 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU32_ge x y = Ok (x \<ge> y)"
definition core_cmp_PartialOrdU32 :: "(u32, u32) core_cmp_PartialOrd" where
  "core_cmp_PartialOrdU32 = (|
    partialEqInst = core_cmp_PartialEqU32,
    core_cmp_PartialOrd_partial_cmp = core_cmp_impls_PartialOrdU32_partial_cmp,
    core_cmp_PartialOrd_lt = core_cmp_impls_PartialOrdU32_lt,
    core_cmp_PartialOrd_le = core_cmp_impls_PartialOrdU32_le,
    core_cmp_PartialOrd_gt = core_cmp_impls_PartialOrdU32_gt,
    core_cmp_PartialOrd_ge = core_cmp_impls_PartialOrdU32_ge |)"

definition core_cmp_impls_PartialEqU64_eq :: "u64 \<Rightarrow> u64 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqU64_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqU64_ne :: "u64 \<Rightarrow> u64 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqU64_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqU64 :: "(u64, u64) core_cmp_PartialEq" where
  "core_cmp_PartialEqU64 = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqU64_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqU64_ne |)"
definition core_cmp_impls_PartialOrdU64_partial_cmp ::
  "u64 \<Rightarrow> u64 \<Rightarrow> (core_cmp_Ordering option) result" where
  "core_cmp_impls_PartialOrdU64_partial_cmp x y = Ok (scalar_partial_cmp x y)"
definition core_cmp_impls_PartialOrdU64_lt :: "u64 \<Rightarrow> u64 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU64_lt x y = Ok (x < y)"
definition core_cmp_impls_PartialOrdU64_le :: "u64 \<Rightarrow> u64 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU64_le x y = Ok (x \<le> y)"
definition core_cmp_impls_PartialOrdU64_gt :: "u64 \<Rightarrow> u64 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU64_gt x y = Ok (x > y)"
definition core_cmp_impls_PartialOrdU64_ge :: "u64 \<Rightarrow> u64 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU64_ge x y = Ok (x \<ge> y)"
definition core_cmp_PartialOrdU64 :: "(u64, u64) core_cmp_PartialOrd" where
  "core_cmp_PartialOrdU64 = (|
    partialEqInst = core_cmp_PartialEqU64,
    core_cmp_PartialOrd_partial_cmp = core_cmp_impls_PartialOrdU64_partial_cmp,
    core_cmp_PartialOrd_lt = core_cmp_impls_PartialOrdU64_lt,
    core_cmp_PartialOrd_le = core_cmp_impls_PartialOrdU64_le,
    core_cmp_PartialOrd_gt = core_cmp_impls_PartialOrdU64_gt,
    core_cmp_PartialOrd_ge = core_cmp_impls_PartialOrdU64_ge |)"

definition core_cmp_impls_PartialEqU128_eq :: "u128 \<Rightarrow> u128 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqU128_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqU128_ne :: "u128 \<Rightarrow> u128 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqU128_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqU128 :: "(u128, u128) core_cmp_PartialEq" where
  "core_cmp_PartialEqU128 = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqU128_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqU128_ne |)"
definition core_cmp_impls_PartialOrdU128_partial_cmp ::
  "u128 \<Rightarrow> u128 \<Rightarrow> (core_cmp_Ordering option) result" where
  "core_cmp_impls_PartialOrdU128_partial_cmp x y = Ok (scalar_partial_cmp x y)"
definition core_cmp_impls_PartialOrdU128_lt :: "u128 \<Rightarrow> u128 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU128_lt x y = Ok (x < y)"
definition core_cmp_impls_PartialOrdU128_le :: "u128 \<Rightarrow> u128 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU128_le x y = Ok (x \<le> y)"
definition core_cmp_impls_PartialOrdU128_gt :: "u128 \<Rightarrow> u128 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU128_gt x y = Ok (x > y)"
definition core_cmp_impls_PartialOrdU128_ge :: "u128 \<Rightarrow> u128 \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdU128_ge x y = Ok (x \<ge> y)"
definition core_cmp_PartialOrdU128 :: "(u128, u128) core_cmp_PartialOrd" where
  "core_cmp_PartialOrdU128 = (|
    partialEqInst = core_cmp_PartialEqU128,
    core_cmp_PartialOrd_partial_cmp = core_cmp_impls_PartialOrdU128_partial_cmp,
    core_cmp_PartialOrd_lt = core_cmp_impls_PartialOrdU128_lt,
    core_cmp_PartialOrd_le = core_cmp_impls_PartialOrdU128_le,
    core_cmp_PartialOrd_gt = core_cmp_impls_PartialOrdU128_gt,
    core_cmp_PartialOrd_ge = core_cmp_impls_PartialOrdU128_ge |)"

definition core_cmp_impls_PartialEqUsize_eq :: "usize \<Rightarrow> usize \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqUsize_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqUsize_ne :: "usize \<Rightarrow> usize \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqUsize_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqUsize :: "(usize, usize) core_cmp_PartialEq" where
  "core_cmp_PartialEqUsize = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqUsize_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqUsize_ne |)"
definition core_cmp_impls_PartialOrdUsize_partial_cmp ::
  "usize \<Rightarrow> usize \<Rightarrow> (core_cmp_Ordering option) result" where
  "core_cmp_impls_PartialOrdUsize_partial_cmp x y = Ok (scalar_partial_cmp x y)"
definition core_cmp_impls_PartialOrdUsize_lt :: "usize \<Rightarrow> usize \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdUsize_lt x y = Ok (x < y)"
definition core_cmp_impls_PartialOrdUsize_le :: "usize \<Rightarrow> usize \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdUsize_le x y = Ok (x \<le> y)"
definition core_cmp_impls_PartialOrdUsize_gt :: "usize \<Rightarrow> usize \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdUsize_gt x y = Ok (x > y)"
definition core_cmp_impls_PartialOrdUsize_ge :: "usize \<Rightarrow> usize \<Rightarrow> bool result" where
  "core_cmp_impls_PartialOrdUsize_ge x y = Ok (x \<ge> y)"
definition core_cmp_PartialOrdUsize :: "(usize, usize) core_cmp_PartialOrd" where
  "core_cmp_PartialOrdUsize = (|
    partialEqInst = core_cmp_PartialEqUsize,
    core_cmp_PartialOrd_partial_cmp = core_cmp_impls_PartialOrdUsize_partial_cmp,
    core_cmp_PartialOrd_lt = core_cmp_impls_PartialOrdUsize_lt,
    core_cmp_PartialOrd_le = core_cmp_impls_PartialOrdUsize_le,
    core_cmp_PartialOrd_gt = core_cmp_impls_PartialOrdUsize_gt,
    core_cmp_PartialOrd_ge = core_cmp_impls_PartialOrdUsize_ge |)"

(*** core::ops::function *)

(* Trait declarations: [core::ops::function::FnOnce], [FnMut], [Fn].  The
   associated type [Output] is a type parameter. *)
record ('self, 'args, 'output) core_ops_function_FnOnce =
  core_ops_function_FnOnce_call_once :: "'self \<Rightarrow> 'args \<Rightarrow> 'output result"

record ('self, 'args, 'output) core_ops_function_FnMut =
  fnOnceInst :: "('self, 'args, 'output) core_ops_function_FnOnce"
  core_ops_function_FnMut_call_mut :: "'self \<Rightarrow> 'args \<Rightarrow> ('output \<times> 'self) result"

record ('self, 'args, 'output) core_ops_function_Fn =
  fnMutInst :: "('self, 'args, 'output) core_ops_function_FnMut"
  core_ops_function_Fn_call :: "'self \<Rightarrow> 'args \<Rightarrow> 'output result"

(*** core::clone (default method) *)

(* Default implementation of [Clone::clone_from]: ignore the old value and
   clone the source. *)
definition core_clone_Clone_clone_from_default_body ::
  "('self \<Rightarrow> 'self result) \<Rightarrow> 'self \<Rightarrow> 'self \<Rightarrow> 'self result" where
  "core_clone_Clone_clone_from_default_body clone _ source = clone source"
definition core_clone_Clone_clone_from_default ::
  "'self core_clone_Clone \<Rightarrow> 'self \<Rightarrow> 'self \<Rightarrow> 'self result" where
  "core_clone_Clone_clone_from_default inst = core_clone_Clone_clone_from_default_body (core_clone_Clone_clone inst)"

(*** core::result, core::ops::control_flow, core::convert *)

datatype ('t, 'e) core_result_Result =
    core_result_Result_Ok 't
  | core_result_Result_Err 'e

datatype ('b, 'c) core_ops_control_flow_ControlFlow =
    core_ops_control_flow_ControlFlow_Continue 'c
  | core_ops_control_flow_ControlFlow_Break 'b

typedecl core_num_error_TryFromIntError

(* [impl From<T> for T] *)
definition core_convert_FromSame_from :: "'t \<Rightarrow> 't" where
  "core_convert_FromSame_from x = x"

definition core_convert_FromSame :: "('t, 't) core_convert_From" where
  "core_convert_FromSame = (| from_' = (\<lambda>x. Ok x) |)"

(* [Result::map_err] *)
definition core_result_Result_map_err ::
  "('o, 'e, 'f) core_ops_function_FnOnce \<Rightarrow> ('t, 'e) core_result_Result \<Rightarrow> 'o \<Rightarrow>
   ('t, 'f) core_result_Result result" where
  "core_result_Result_map_err inst x f =
    (case x of
       core_result_Result_Ok v \<Rightarrow> Ok (core_result_Result_Ok v)
     | core_result_Result_Err e \<Rightarrow>
         (e' <- core_ops_function_FnOnce_call_once inst f e;
          Ok (core_result_Result_Err e')))"

(* [impl Try for Result<T, E>]::branch *)
definition core_result_Result_Insts_CoreOpsTry_branch ::
  "('t, 'e) core_result_Result \<Rightarrow>
   ((Never, 'e) core_result_Result, 't) core_ops_control_flow_ControlFlow result" where
  "core_result_Result_Insts_CoreOpsTry_branch x =
    (case x of
       core_result_Result_Ok v \<Rightarrow> Ok (core_ops_control_flow_ControlFlow_Continue v)
     | core_result_Result_Err e \<Rightarrow>
         Ok (core_ops_control_flow_ControlFlow_Break (core_result_Result_Err e)))"

(* [impl FromResidual<Result<!, E>> for Result<T, F>]::from_residual *)
definition core_result_Result_Insts_CoreOpsTryFromResidual_from_residual ::
  "('f, 'e) core_convert_From \<Rightarrow> (Never, 'e) core_result_Result \<Rightarrow>
   ('t, 'f) core_result_Result result" where
  "core_result_Result_Insts_CoreOpsTryFromResidual_from_residual inst r =
    (case r of
       core_result_Result_Ok _ \<Rightarrow> Fail Failure
     | core_result_Result_Err e \<Rightarrow>
         (v <- from_' inst e; Ok (core_result_Result_Err v)))"

(* [TryFrom<SRC> for DST]::try_from for integer types: succeeds iff the value
   fits in the destination type. *)
definition scalar_try_from :: "scalar_ty \<Rightarrow> int \<Rightarrow> (int, core_num_error_TryFromIntError) core_result_Result result" where
  "scalar_try_from ty x =
    Ok (if scalar_in_bounds ty x then core_result_Result_Ok x
        else core_result_Result_Err undefined)"
definition core_convert_num_TryFromI8I16_try_from :: "i16 \<Rightarrow> (i8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI8I16_try_from x = scalar_try_from I8 x"
definition core_convert_num_TryFromI8I32_try_from :: "i32 \<Rightarrow> (i8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI8I32_try_from x = scalar_try_from I8 x"
definition core_convert_num_TryFromI8I64_try_from :: "i64 \<Rightarrow> (i8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI8I64_try_from x = scalar_try_from I8 x"
definition core_convert_num_TryFromI8I128_try_from :: "i128 \<Rightarrow> (i8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI8I128_try_from x = scalar_try_from I8 x"
definition core_convert_num_TryFromI8Isize_try_from :: "isize \<Rightarrow> (i8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI8Isize_try_from x = scalar_try_from I8 x"
definition core_convert_num_TryFromI8U8_try_from :: "u8 \<Rightarrow> (i8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI8U8_try_from x = scalar_try_from I8 x"
definition core_convert_num_TryFromI8U16_try_from :: "u16 \<Rightarrow> (i8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI8U16_try_from x = scalar_try_from I8 x"
definition core_convert_num_TryFromI8U32_try_from :: "u32 \<Rightarrow> (i8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI8U32_try_from x = scalar_try_from I8 x"
definition core_convert_num_TryFromI8U64_try_from :: "u64 \<Rightarrow> (i8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI8U64_try_from x = scalar_try_from I8 x"
definition core_convert_num_TryFromI8U128_try_from :: "u128 \<Rightarrow> (i8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI8U128_try_from x = scalar_try_from I8 x"
definition core_convert_num_TryFromI8Usize_try_from :: "usize \<Rightarrow> (i8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI8Usize_try_from x = scalar_try_from I8 x"
definition core_convert_num_TryFromI16I8_try_from :: "i8 \<Rightarrow> (i16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI16I8_try_from x = scalar_try_from I16 x"
definition core_convert_num_TryFromI16I32_try_from :: "i32 \<Rightarrow> (i16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI16I32_try_from x = scalar_try_from I16 x"
definition core_convert_num_TryFromI16I64_try_from :: "i64 \<Rightarrow> (i16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI16I64_try_from x = scalar_try_from I16 x"
definition core_convert_num_TryFromI16I128_try_from :: "i128 \<Rightarrow> (i16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI16I128_try_from x = scalar_try_from I16 x"
definition core_convert_num_TryFromI16Isize_try_from :: "isize \<Rightarrow> (i16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI16Isize_try_from x = scalar_try_from I16 x"
definition core_convert_num_TryFromI16U8_try_from :: "u8 \<Rightarrow> (i16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI16U8_try_from x = scalar_try_from I16 x"
definition core_convert_num_TryFromI16U16_try_from :: "u16 \<Rightarrow> (i16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI16U16_try_from x = scalar_try_from I16 x"
definition core_convert_num_TryFromI16U32_try_from :: "u32 \<Rightarrow> (i16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI16U32_try_from x = scalar_try_from I16 x"
definition core_convert_num_TryFromI16U64_try_from :: "u64 \<Rightarrow> (i16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI16U64_try_from x = scalar_try_from I16 x"
definition core_convert_num_TryFromI16U128_try_from :: "u128 \<Rightarrow> (i16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI16U128_try_from x = scalar_try_from I16 x"
definition core_convert_num_TryFromI16Usize_try_from :: "usize \<Rightarrow> (i16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI16Usize_try_from x = scalar_try_from I16 x"
definition core_convert_num_TryFromI32I8_try_from :: "i8 \<Rightarrow> (i32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI32I8_try_from x = scalar_try_from I32 x"
definition core_convert_num_TryFromI32I16_try_from :: "i16 \<Rightarrow> (i32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI32I16_try_from x = scalar_try_from I32 x"
definition core_convert_num_TryFromI32I64_try_from :: "i64 \<Rightarrow> (i32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI32I64_try_from x = scalar_try_from I32 x"
definition core_convert_num_TryFromI32I128_try_from :: "i128 \<Rightarrow> (i32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI32I128_try_from x = scalar_try_from I32 x"
definition core_convert_num_TryFromI32Isize_try_from :: "isize \<Rightarrow> (i32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI32Isize_try_from x = scalar_try_from I32 x"
definition core_convert_num_TryFromI32U8_try_from :: "u8 \<Rightarrow> (i32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI32U8_try_from x = scalar_try_from I32 x"
definition core_convert_num_TryFromI32U16_try_from :: "u16 \<Rightarrow> (i32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI32U16_try_from x = scalar_try_from I32 x"
definition core_convert_num_TryFromI32U32_try_from :: "u32 \<Rightarrow> (i32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI32U32_try_from x = scalar_try_from I32 x"
definition core_convert_num_TryFromI32U64_try_from :: "u64 \<Rightarrow> (i32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI32U64_try_from x = scalar_try_from I32 x"
definition core_convert_num_TryFromI32U128_try_from :: "u128 \<Rightarrow> (i32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI32U128_try_from x = scalar_try_from I32 x"
definition core_convert_num_TryFromI32Usize_try_from :: "usize \<Rightarrow> (i32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI32Usize_try_from x = scalar_try_from I32 x"
definition core_convert_num_TryFromI64I8_try_from :: "i8 \<Rightarrow> (i64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI64I8_try_from x = scalar_try_from I64 x"
definition core_convert_num_TryFromI64I16_try_from :: "i16 \<Rightarrow> (i64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI64I16_try_from x = scalar_try_from I64 x"
definition core_convert_num_TryFromI64I32_try_from :: "i32 \<Rightarrow> (i64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI64I32_try_from x = scalar_try_from I64 x"
definition core_convert_num_TryFromI64I128_try_from :: "i128 \<Rightarrow> (i64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI64I128_try_from x = scalar_try_from I64 x"
definition core_convert_num_TryFromI64Isize_try_from :: "isize \<Rightarrow> (i64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI64Isize_try_from x = scalar_try_from I64 x"
definition core_convert_num_TryFromI64U8_try_from :: "u8 \<Rightarrow> (i64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI64U8_try_from x = scalar_try_from I64 x"
definition core_convert_num_TryFromI64U16_try_from :: "u16 \<Rightarrow> (i64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI64U16_try_from x = scalar_try_from I64 x"
definition core_convert_num_TryFromI64U32_try_from :: "u32 \<Rightarrow> (i64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI64U32_try_from x = scalar_try_from I64 x"
definition core_convert_num_TryFromI64U64_try_from :: "u64 \<Rightarrow> (i64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI64U64_try_from x = scalar_try_from I64 x"
definition core_convert_num_TryFromI64U128_try_from :: "u128 \<Rightarrow> (i64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI64U128_try_from x = scalar_try_from I64 x"
definition core_convert_num_TryFromI64Usize_try_from :: "usize \<Rightarrow> (i64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI64Usize_try_from x = scalar_try_from I64 x"
definition core_convert_num_TryFromI128I8_try_from :: "i8 \<Rightarrow> (i128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI128I8_try_from x = scalar_try_from I128 x"
definition core_convert_num_TryFromI128I16_try_from :: "i16 \<Rightarrow> (i128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI128I16_try_from x = scalar_try_from I128 x"
definition core_convert_num_TryFromI128I32_try_from :: "i32 \<Rightarrow> (i128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI128I32_try_from x = scalar_try_from I128 x"
definition core_convert_num_TryFromI128I64_try_from :: "i64 \<Rightarrow> (i128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI128I64_try_from x = scalar_try_from I128 x"
definition core_convert_num_TryFromI128Isize_try_from :: "isize \<Rightarrow> (i128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI128Isize_try_from x = scalar_try_from I128 x"
definition core_convert_num_TryFromI128U8_try_from :: "u8 \<Rightarrow> (i128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI128U8_try_from x = scalar_try_from I128 x"
definition core_convert_num_TryFromI128U16_try_from :: "u16 \<Rightarrow> (i128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI128U16_try_from x = scalar_try_from I128 x"
definition core_convert_num_TryFromI128U32_try_from :: "u32 \<Rightarrow> (i128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI128U32_try_from x = scalar_try_from I128 x"
definition core_convert_num_TryFromI128U64_try_from :: "u64 \<Rightarrow> (i128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI128U64_try_from x = scalar_try_from I128 x"
definition core_convert_num_TryFromI128U128_try_from :: "u128 \<Rightarrow> (i128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI128U128_try_from x = scalar_try_from I128 x"
definition core_convert_num_TryFromI128Usize_try_from :: "usize \<Rightarrow> (i128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromI128Usize_try_from x = scalar_try_from I128 x"
definition core_convert_num_TryFromIsizeI8_try_from :: "i8 \<Rightarrow> (isize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromIsizeI8_try_from x = scalar_try_from Isize x"
definition core_convert_num_TryFromIsizeI16_try_from :: "i16 \<Rightarrow> (isize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromIsizeI16_try_from x = scalar_try_from Isize x"
definition core_convert_num_TryFromIsizeI32_try_from :: "i32 \<Rightarrow> (isize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromIsizeI32_try_from x = scalar_try_from Isize x"
definition core_convert_num_TryFromIsizeI64_try_from :: "i64 \<Rightarrow> (isize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromIsizeI64_try_from x = scalar_try_from Isize x"
definition core_convert_num_TryFromIsizeI128_try_from :: "i128 \<Rightarrow> (isize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromIsizeI128_try_from x = scalar_try_from Isize x"
definition core_convert_num_TryFromIsizeU8_try_from :: "u8 \<Rightarrow> (isize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromIsizeU8_try_from x = scalar_try_from Isize x"
definition core_convert_num_TryFromIsizeU16_try_from :: "u16 \<Rightarrow> (isize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromIsizeU16_try_from x = scalar_try_from Isize x"
definition core_convert_num_TryFromIsizeU32_try_from :: "u32 \<Rightarrow> (isize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromIsizeU32_try_from x = scalar_try_from Isize x"
definition core_convert_num_TryFromIsizeU64_try_from :: "u64 \<Rightarrow> (isize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromIsizeU64_try_from x = scalar_try_from Isize x"
definition core_convert_num_TryFromIsizeU128_try_from :: "u128 \<Rightarrow> (isize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromIsizeU128_try_from x = scalar_try_from Isize x"
definition core_convert_num_TryFromIsizeUsize_try_from :: "usize \<Rightarrow> (isize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromIsizeUsize_try_from x = scalar_try_from Isize x"
definition core_convert_num_TryFromU8I8_try_from :: "i8 \<Rightarrow> (u8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU8I8_try_from x = scalar_try_from U8 x"
definition core_convert_num_TryFromU8I16_try_from :: "i16 \<Rightarrow> (u8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU8I16_try_from x = scalar_try_from U8 x"
definition core_convert_num_TryFromU8I32_try_from :: "i32 \<Rightarrow> (u8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU8I32_try_from x = scalar_try_from U8 x"
definition core_convert_num_TryFromU8I64_try_from :: "i64 \<Rightarrow> (u8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU8I64_try_from x = scalar_try_from U8 x"
definition core_convert_num_TryFromU8I128_try_from :: "i128 \<Rightarrow> (u8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU8I128_try_from x = scalar_try_from U8 x"
definition core_convert_num_TryFromU8Isize_try_from :: "isize \<Rightarrow> (u8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU8Isize_try_from x = scalar_try_from U8 x"
definition core_convert_num_TryFromU8U16_try_from :: "u16 \<Rightarrow> (u8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU8U16_try_from x = scalar_try_from U8 x"
definition core_convert_num_TryFromU8U32_try_from :: "u32 \<Rightarrow> (u8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU8U32_try_from x = scalar_try_from U8 x"
definition core_convert_num_TryFromU8U64_try_from :: "u64 \<Rightarrow> (u8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU8U64_try_from x = scalar_try_from U8 x"
definition core_convert_num_TryFromU8U128_try_from :: "u128 \<Rightarrow> (u8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU8U128_try_from x = scalar_try_from U8 x"
definition core_convert_num_TryFromU8Usize_try_from :: "usize \<Rightarrow> (u8, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU8Usize_try_from x = scalar_try_from U8 x"
definition core_convert_num_TryFromU16I8_try_from :: "i8 \<Rightarrow> (u16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU16I8_try_from x = scalar_try_from U16 x"
definition core_convert_num_TryFromU16I16_try_from :: "i16 \<Rightarrow> (u16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU16I16_try_from x = scalar_try_from U16 x"
definition core_convert_num_TryFromU16I32_try_from :: "i32 \<Rightarrow> (u16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU16I32_try_from x = scalar_try_from U16 x"
definition core_convert_num_TryFromU16I64_try_from :: "i64 \<Rightarrow> (u16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU16I64_try_from x = scalar_try_from U16 x"
definition core_convert_num_TryFromU16I128_try_from :: "i128 \<Rightarrow> (u16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU16I128_try_from x = scalar_try_from U16 x"
definition core_convert_num_TryFromU16Isize_try_from :: "isize \<Rightarrow> (u16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU16Isize_try_from x = scalar_try_from U16 x"
definition core_convert_num_TryFromU16U8_try_from :: "u8 \<Rightarrow> (u16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU16U8_try_from x = scalar_try_from U16 x"
definition core_convert_num_TryFromU16U32_try_from :: "u32 \<Rightarrow> (u16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU16U32_try_from x = scalar_try_from U16 x"
definition core_convert_num_TryFromU16U64_try_from :: "u64 \<Rightarrow> (u16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU16U64_try_from x = scalar_try_from U16 x"
definition core_convert_num_TryFromU16U128_try_from :: "u128 \<Rightarrow> (u16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU16U128_try_from x = scalar_try_from U16 x"
definition core_convert_num_TryFromU16Usize_try_from :: "usize \<Rightarrow> (u16, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU16Usize_try_from x = scalar_try_from U16 x"
definition core_convert_num_TryFromU32I8_try_from :: "i8 \<Rightarrow> (u32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU32I8_try_from x = scalar_try_from U32 x"
definition core_convert_num_TryFromU32I16_try_from :: "i16 \<Rightarrow> (u32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU32I16_try_from x = scalar_try_from U32 x"
definition core_convert_num_TryFromU32I32_try_from :: "i32 \<Rightarrow> (u32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU32I32_try_from x = scalar_try_from U32 x"
definition core_convert_num_TryFromU32I64_try_from :: "i64 \<Rightarrow> (u32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU32I64_try_from x = scalar_try_from U32 x"
definition core_convert_num_TryFromU32I128_try_from :: "i128 \<Rightarrow> (u32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU32I128_try_from x = scalar_try_from U32 x"
definition core_convert_num_TryFromU32Isize_try_from :: "isize \<Rightarrow> (u32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU32Isize_try_from x = scalar_try_from U32 x"
definition core_convert_num_TryFromU32U8_try_from :: "u8 \<Rightarrow> (u32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU32U8_try_from x = scalar_try_from U32 x"
definition core_convert_num_TryFromU32U16_try_from :: "u16 \<Rightarrow> (u32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU32U16_try_from x = scalar_try_from U32 x"
definition core_convert_num_TryFromU32U64_try_from :: "u64 \<Rightarrow> (u32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU32U64_try_from x = scalar_try_from U32 x"
definition core_convert_num_TryFromU32U128_try_from :: "u128 \<Rightarrow> (u32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU32U128_try_from x = scalar_try_from U32 x"
definition core_convert_num_TryFromU32Usize_try_from :: "usize \<Rightarrow> (u32, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU32Usize_try_from x = scalar_try_from U32 x"
definition core_convert_num_TryFromU64I8_try_from :: "i8 \<Rightarrow> (u64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU64I8_try_from x = scalar_try_from U64 x"
definition core_convert_num_TryFromU64I16_try_from :: "i16 \<Rightarrow> (u64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU64I16_try_from x = scalar_try_from U64 x"
definition core_convert_num_TryFromU64I32_try_from :: "i32 \<Rightarrow> (u64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU64I32_try_from x = scalar_try_from U64 x"
definition core_convert_num_TryFromU64I64_try_from :: "i64 \<Rightarrow> (u64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU64I64_try_from x = scalar_try_from U64 x"
definition core_convert_num_TryFromU64I128_try_from :: "i128 \<Rightarrow> (u64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU64I128_try_from x = scalar_try_from U64 x"
definition core_convert_num_TryFromU64Isize_try_from :: "isize \<Rightarrow> (u64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU64Isize_try_from x = scalar_try_from U64 x"
definition core_convert_num_TryFromU64U8_try_from :: "u8 \<Rightarrow> (u64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU64U8_try_from x = scalar_try_from U64 x"
definition core_convert_num_TryFromU64U16_try_from :: "u16 \<Rightarrow> (u64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU64U16_try_from x = scalar_try_from U64 x"
definition core_convert_num_TryFromU64U32_try_from :: "u32 \<Rightarrow> (u64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU64U32_try_from x = scalar_try_from U64 x"
definition core_convert_num_TryFromU64U128_try_from :: "u128 \<Rightarrow> (u64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU64U128_try_from x = scalar_try_from U64 x"
definition core_convert_num_TryFromU64Usize_try_from :: "usize \<Rightarrow> (u64, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU64Usize_try_from x = scalar_try_from U64 x"
definition core_convert_num_TryFromU128I8_try_from :: "i8 \<Rightarrow> (u128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU128I8_try_from x = scalar_try_from U128 x"
definition core_convert_num_TryFromU128I16_try_from :: "i16 \<Rightarrow> (u128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU128I16_try_from x = scalar_try_from U128 x"
definition core_convert_num_TryFromU128I32_try_from :: "i32 \<Rightarrow> (u128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU128I32_try_from x = scalar_try_from U128 x"
definition core_convert_num_TryFromU128I64_try_from :: "i64 \<Rightarrow> (u128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU128I64_try_from x = scalar_try_from U128 x"
definition core_convert_num_TryFromU128I128_try_from :: "i128 \<Rightarrow> (u128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU128I128_try_from x = scalar_try_from U128 x"
definition core_convert_num_TryFromU128Isize_try_from :: "isize \<Rightarrow> (u128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU128Isize_try_from x = scalar_try_from U128 x"
definition core_convert_num_TryFromU128U8_try_from :: "u8 \<Rightarrow> (u128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU128U8_try_from x = scalar_try_from U128 x"
definition core_convert_num_TryFromU128U16_try_from :: "u16 \<Rightarrow> (u128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU128U16_try_from x = scalar_try_from U128 x"
definition core_convert_num_TryFromU128U32_try_from :: "u32 \<Rightarrow> (u128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU128U32_try_from x = scalar_try_from U128 x"
definition core_convert_num_TryFromU128U64_try_from :: "u64 \<Rightarrow> (u128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU128U64_try_from x = scalar_try_from U128 x"
definition core_convert_num_TryFromU128Usize_try_from :: "usize \<Rightarrow> (u128, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromU128Usize_try_from x = scalar_try_from U128 x"
definition core_convert_num_TryFromUsizeI8_try_from :: "i8 \<Rightarrow> (usize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromUsizeI8_try_from x = scalar_try_from Usize x"
definition core_convert_num_TryFromUsizeI16_try_from :: "i16 \<Rightarrow> (usize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromUsizeI16_try_from x = scalar_try_from Usize x"
definition core_convert_num_TryFromUsizeI32_try_from :: "i32 \<Rightarrow> (usize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromUsizeI32_try_from x = scalar_try_from Usize x"
definition core_convert_num_TryFromUsizeI64_try_from :: "i64 \<Rightarrow> (usize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromUsizeI64_try_from x = scalar_try_from Usize x"
definition core_convert_num_TryFromUsizeI128_try_from :: "i128 \<Rightarrow> (usize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromUsizeI128_try_from x = scalar_try_from Usize x"
definition core_convert_num_TryFromUsizeIsize_try_from :: "isize \<Rightarrow> (usize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromUsizeIsize_try_from x = scalar_try_from Usize x"
definition core_convert_num_TryFromUsizeU8_try_from :: "u8 \<Rightarrow> (usize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromUsizeU8_try_from x = scalar_try_from Usize x"
definition core_convert_num_TryFromUsizeU16_try_from :: "u16 \<Rightarrow> (usize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromUsizeU16_try_from x = scalar_try_from Usize x"
definition core_convert_num_TryFromUsizeU32_try_from :: "u32 \<Rightarrow> (usize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromUsizeU32_try_from x = scalar_try_from Usize x"
definition core_convert_num_TryFromUsizeU64_try_from :: "u64 \<Rightarrow> (usize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromUsizeU64_try_from x = scalar_try_from Usize x"
definition core_convert_num_TryFromUsizeU128_try_from :: "u128 \<Rightarrow> (usize, core_num_error_TryFromIntError) core_result_Result result" where
  "core_convert_num_TryFromUsizeU128_try_from x = scalar_try_from Usize x"

(*** core::option *)

definition core_option_Option_is_none :: "'t option \<Rightarrow> bool" where
  "core_option_Option_is_none x = (x = None)"

definition core_option_Option_is_some :: "'t option \<Rightarrow> bool" where
  "core_option_Option_is_some x = (x \<noteq> None)"

fun core_option_Option_ok_or :: "'t option \<Rightarrow> 'e \<Rightarrow> ('t, 'e) core_result_Result result" where
  "core_option_Option_ok_or (Some v) e = Ok (core_result_Result_Ok v)"
| "core_option_Option_ok_or None e = Ok (core_result_Result_Err e)"

(* [impl Clone for Option<T>] *)
definition core_option_CloneOption_clone ::
  "'t core_clone_Clone \<Rightarrow> 't option \<Rightarrow> 't option result" where
  "core_option_CloneOption_clone inst x =
    (case x of
       None \<Rightarrow> Ok None
     | Some v \<Rightarrow> (v' <- core_clone_Clone_clone inst v; Ok (Some v')))"

definition core_option_CloneOption :: "'t core_clone_Clone \<Rightarrow> ('t option) core_clone_Clone" where
  "core_option_CloneOption inst = (|
    core_clone_Clone_clone = core_option_CloneOption_clone inst,
    core_clone_Clone_clone_from =
      core_clone_Clone_clone_from_default_body (core_option_CloneOption_clone inst) |)"

(*** core::ops::range::RangeInclusive *)

record 'idx core_ops_range_RangeInclusive =
  core_ops_range_RangeInclusive_start :: 'idx
  core_ops_range_RangeInclusive_end_' :: 'idx
  core_ops_range_RangeInclusive_exhausted :: bool

definition core_ops_range_RangeInclusive_new ::
  "'idx \<Rightarrow> 'idx \<Rightarrow> 'idx core_ops_range_RangeInclusive result" where
  "core_ops_range_RangeInclusive_new s e =
    Ok (| core_ops_range_RangeInclusive_start = s,
          core_ops_range_RangeInclusive_end_' = e,
          core_ops_range_RangeInclusive_exhausted = False |)"

(* [RangeInclusive::contains]: [start <= item && item <= end], using the
   [PartialOrd<Idx, U>] and [PartialOrd<U, Idx>] dictionaries. *)
definition core_ops_range_RangeInclusive_contains ::
  "('idx, 'idx) core_cmp_PartialOrd \<Rightarrow> ('idx, 'u) core_cmp_PartialOrd \<Rightarrow>
   ('u, 'idx) core_cmp_PartialOrd \<Rightarrow> 'idx core_ops_range_RangeInclusive \<Rightarrow> 'u \<Rightarrow> bool result" where
  "core_ops_range_RangeInclusive_contains _ inst1 inst2 r x =
    (b1 <- core_cmp_PartialOrd_le inst1 (core_ops_range_RangeInclusive_start r) x;
     if b1 then core_cmp_PartialOrd_le inst2 x (core_ops_range_RangeInclusive_end_' r)
     else Ok False)"

(*** alloc::vec (continued) *)

definition alloc_vec_Vec_clear :: "'a alloc_vec_Vec \<Rightarrow> 'a alloc_vec_Vec" where
  "alloc_vec_Vec_clear _ = []"

(* [alloc::vec::from_elem]: [vec![x; n]] *)
definition alloc_vec_from_elem :: "'a core_clone_Clone \<Rightarrow> 'a \<Rightarrow> usize \<Rightarrow> 'a alloc_vec_Vec result" where
  "alloc_vec_from_elem _ x n = Ok (replicate (nat n) x)"

(* [Vec::extend_from_slice]: clone the elements of the slice onto the vector.
   Cloning is modelled as the identity (the [Clone] dictionary is ignored),
   which is exact for [Copy] data. *)
definition alloc_vec_Vec_extend_from_slice ::
  "'a core_clone_Clone \<Rightarrow> 'a alloc_vec_Vec \<Rightarrow> 'a slice \<Rightarrow> 'a alloc_vec_Vec result" where
  "alloc_vec_Vec_extend_from_slice _ v s =
    (let l = v @ s in
     if int (length l) \<le> usize_max then Ok l else Fail Failure)"

(*** core::slice (continued) *)

(* [<[T]>::copy_from_slice]: panics unless both slices have the same length. *)
definition core_slice_Slice_copy_from_slice ::
  "'a core_marker_Copy \<Rightarrow> 'a slice \<Rightarrow> 'a slice \<Rightarrow> 'a slice result" where
  "core_slice_Slice_copy_from_slice _ s src =
    (if length s = length src then Ok src else Fail Failure)"

(* Shared slice iterator: the slice and the index of the next element. *)
record 'a core_slice_iter_Iter =
  core_slice_iter_Iter_slice :: "'a slice"
  core_slice_iter_Iter_i :: usize

definition core_slice_iter_IteratorSliceIter_next ::
  "'a core_slice_iter_Iter \<Rightarrow> ('a option \<times> 'a core_slice_iter_Iter) result" where
  "core_slice_iter_IteratorSliceIter_next it =
    (let s = core_slice_iter_Iter_slice it; i = core_slice_iter_Iter_i it in
     if 0 \<le> i \<and> i < int (length s)
     then Ok (Some (s ! nat i), it (| core_slice_iter_Iter_i := i + 1 |))
     else Ok (None, it))"

definition alloc_vec_IntoIteratorSharedVec_into_iter ::
  "'a alloc_vec_Vec \<Rightarrow> 'a core_slice_iter_Iter result" where
  "alloc_vec_IntoIteratorSharedVec_into_iter v =
    Ok (| core_slice_iter_Iter_slice = v, core_slice_iter_Iter_i = 0 |)"

(* [SliceIndex<RangeTo<usize>, [T]>]: [s[..end]] *)
definition slice_range_to_valid :: "usize core_ops_range_RangeTo \<Rightarrow> 'a slice \<Rightarrow> bool" where
  "slice_range_to_valid r s =
    (0 \<le> core_ops_range_RangeTo_end_' r \<and> core_ops_range_RangeTo_end_' r \<le> int (length s))"

definition slice_range_to_prefix :: "usize core_ops_range_RangeTo \<Rightarrow> 'a slice \<Rightarrow> 'a slice" where
  "slice_range_to_prefix r s = take (nat (core_ops_range_RangeTo_end_' r)) s"

definition slice_range_to_replace :: "usize core_ops_range_RangeTo \<Rightarrow> 'a slice \<Rightarrow> 'a slice \<Rightarrow> 'a slice" where
  "slice_range_to_replace r s ys = ys @ drop (nat (core_ops_range_RangeTo_end_' r)) s"

definition core_slice_index_SliceIndexRangeToUsizeSlice_get ::
  "usize core_ops_range_RangeTo \<Rightarrow> 'a slice \<Rightarrow> 'a slice option result" where
  "core_slice_index_SliceIndexRangeToUsizeSlice_get r s =
    Ok (if slice_range_to_valid r s then Some (slice_range_to_prefix r s) else None)"

definition core_slice_index_SliceIndexRangeToUsizeSlice_get_mut ::
  "usize core_ops_range_RangeTo \<Rightarrow> 'a slice \<Rightarrow>
   ('a slice option \<times> ('a slice option \<Rightarrow> 'a slice)) result" where
  "core_slice_index_SliceIndexRangeToUsizeSlice_get_mut r s =
    (if slice_range_to_valid r s then
       Ok (Some (slice_range_to_prefix r s),
           \<lambda>nss. case nss of None \<Rightarrow> s | Some ys \<Rightarrow> slice_range_to_replace r s ys)
     else Ok (None, \<lambda>_. s))"

definition core_slice_index_SliceIndexRangeToUsizeSlice_get_unchecked ::
  "usize core_ops_range_RangeTo \<Rightarrow> 'a slice const_raw_ptr \<Rightarrow> 'a slice const_raw_ptr result" where
  "core_slice_index_SliceIndexRangeToUsizeSlice_get_unchecked _ _ = Fail Failure"

definition core_slice_index_SliceIndexRangeToUsizeSlice_get_unchecked_mut ::
  "usize core_ops_range_RangeTo \<Rightarrow> 'a slice mut_raw_ptr \<Rightarrow> 'a slice mut_raw_ptr result" where
  "core_slice_index_SliceIndexRangeToUsizeSlice_get_unchecked_mut _ _ = Fail Failure"

definition core_slice_index_SliceIndexRangeToUsizeSlice_index ::
  "usize core_ops_range_RangeTo \<Rightarrow> 'a slice \<Rightarrow> 'a slice result" where
  "core_slice_index_SliceIndexRangeToUsizeSlice_index r s =
    (if slice_range_to_valid r s then Ok (slice_range_to_prefix r s) else Fail Failure)"

definition core_slice_index_SliceIndexRangeToUsizeSlice_index_mut ::
  "usize core_ops_range_RangeTo \<Rightarrow> 'a slice \<Rightarrow> ('a slice \<times> ('a slice \<Rightarrow> 'a slice)) result" where
  "core_slice_index_SliceIndexRangeToUsizeSlice_index_mut r s =
    (if slice_range_to_valid r s
     then Ok (slice_range_to_prefix r s, slice_range_to_replace r s)
     else Fail Failure)"

definition core_slice_index_private_slice_index_SealedRangeToUsizeInst
  :: "usize core_ops_range_RangeTo core_slice_index_private_slice_index_Sealed"
  where "core_slice_index_private_slice_index_SealedRangeToUsizeInst =
    (| core_slice_index_private_slice_index_Sealed_dummy = () |)"

definition core_slice_index_SliceIndexRangeToUsizeSliceInst ::
  "(usize core_ops_range_RangeTo, 'a slice, 'a slice) core_slice_index_SliceIndex" where
  "core_slice_index_SliceIndexRangeToUsizeSliceInst = (|
    sealedInst = core_slice_index_private_slice_index_SealedRangeToUsizeInst,
    core_slice_index_SliceIndex_get = core_slice_index_SliceIndexRangeToUsizeSlice_get,
    core_slice_index_SliceIndex_get_mut = core_slice_index_SliceIndexRangeToUsizeSlice_get_mut,
    core_slice_index_SliceIndex_get_unchecked = core_slice_index_SliceIndexRangeToUsizeSlice_get_unchecked,
    core_slice_index_SliceIndex_get_unchecked_mut = core_slice_index_SliceIndexRangeToUsizeSlice_get_unchecked_mut,
    core_slice_index_SliceIndex_index = core_slice_index_SliceIndexRangeToUsizeSlice_index,
    core_slice_index_SliceIndex_index_mut = core_slice_index_SliceIndexRangeToUsizeSlice_index_mut
  |)"


(*** Trait objects *)

(* HOL has no existential types, so a trait object ([dyn Trait]) is an
   abstract value built by the uninterpreted constructor [dyn_mk] from a
   dictionary and a value.  Such values cannot be inspected: this is enough
   for the formatting machinery below, whose models ignore their arguments,
   but not for calling methods on trait objects. *)
typedecl dyn
consts dyn_mk :: "'inst \<Rightarrow> 'self \<Rightarrow> dyn"

(*** core::fmt

   A simplistic model, following the Lean backend: the formatter is abstract
   and every formatting operation succeeds without changing it. *)

typedecl core_fmt_Formatter
type_synonym core_fmt_Error = unit
type_synonym core_fmt_Arguments = unit
type_synonym core_fmt_rt_Argument = unit

type_synonym fmt_result = "((unit, core_fmt_Error) core_result_Result \<times> core_fmt_Formatter) result"

definition fmt_ok :: "core_fmt_Formatter \<Rightarrow> fmt_result" where
  "fmt_ok f = Ok (core_result_Result_Ok (), f)"

(* Trait declarations: [core::fmt::Debug], [Display], [LowerHex] *)
record 'self core_fmt_Debug =
  core_fmt_Debug_fmt :: "'self \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result"
record 'self core_fmt_Display =
  core_fmt_Display_fmt :: "'self \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result"
record 'self core_fmt_LowerHex =
  core_fmt_LowerHex_fmt :: "'self \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result"

(* Formatter methods *)
definition core_fmt_Formatter_write_str :: "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_write_str f _ = fmt_ok f"
definition core_fmt_Formatter_write_fmt :: "core_fmt_Formatter \<Rightarrow> core_fmt_Arguments \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_write_fmt f _ = fmt_ok f"
definition core_fmt_Formatter_debug_struct_fields_finish ::
  "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> str slice \<Rightarrow> dyn slice \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_debug_struct_fields_finish f _ _ _ = fmt_ok f"
definition core_fmt_Formatter_debug_tuple_fields_finish ::
  "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> dyn slice \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_debug_tuple_fields_finish f _ _ = fmt_ok f"
definition core_fmt_Formatter_debug_struct_field1_finish ::
  "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_debug_struct_field1_finish f _ _ _ = fmt_ok f"
definition core_fmt_Formatter_debug_tuple_field1_finish ::
  "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_debug_tuple_field1_finish f _ _ = fmt_ok f"
definition core_fmt_Formatter_debug_struct_field2_finish ::
  "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_debug_struct_field2_finish f _ _ _ _ _ = fmt_ok f"
definition core_fmt_Formatter_debug_tuple_field2_finish ::
  "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> dyn \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_debug_tuple_field2_finish f _ _ _ = fmt_ok f"
definition core_fmt_Formatter_debug_struct_field3_finish ::
  "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_debug_struct_field3_finish f _ _ _ _ _ _ _ = fmt_ok f"
definition core_fmt_Formatter_debug_tuple_field3_finish ::
  "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> dyn \<Rightarrow> dyn \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_debug_tuple_field3_finish f _ _ _ _ = fmt_ok f"
definition core_fmt_Formatter_debug_struct_field4_finish ::
  "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_debug_struct_field4_finish f _ _ _ _ _ _ _ _ _ = fmt_ok f"
definition core_fmt_Formatter_debug_tuple_field4_finish ::
  "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> dyn \<Rightarrow> dyn \<Rightarrow> dyn \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_debug_tuple_field4_finish f _ _ _ _ _ = fmt_ok f"
definition core_fmt_Formatter_debug_struct_field5_finish ::
  "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_debug_struct_field5_finish f _ _ _ _ _ _ _ _ _ _ _ = fmt_ok f"
definition core_fmt_Formatter_debug_tuple_field5_finish ::
  "core_fmt_Formatter \<Rightarrow> str \<Rightarrow> dyn \<Rightarrow> dyn \<Rightarrow> dyn \<Rightarrow> dyn \<Rightarrow> dyn \<Rightarrow> fmt_result" where
  "core_fmt_Formatter_debug_tuple_field5_finish f _ _ _ _ _ _ = fmt_ok f"

(* Debug instances *)
definition core_fmt_DebugShared_fmt :: "'t core_fmt_Debug \<Rightarrow> 't \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_DebugShared_fmt inst x f = core_fmt_Debug_fmt inst x f"
definition core_fmt_DebugShared :: "'t core_fmt_Debug \<Rightarrow> 't core_fmt_Debug" where
  "core_fmt_DebugShared inst = (| core_fmt_Debug_fmt = core_fmt_DebugShared_fmt inst |)"
definition core_fmt_DebugUnit_fmt :: "unit \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_DebugUnit_fmt _ f = fmt_ok f"
definition core_fmt_DebugUnit :: "unit core_fmt_Debug" where
  "core_fmt_DebugUnit = (| core_fmt_Debug_fmt = core_fmt_DebugUnit_fmt |)"
definition core_fmt_DebugBool_fmt :: "bool \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_DebugBool_fmt _ f = fmt_ok f"
definition core_fmt_DebugBool :: "bool core_fmt_Debug" where
  "core_fmt_DebugBool = (| core_fmt_Debug_fmt = core_fmt_DebugBool_fmt |)"
definition alloc_vec_DebugVec_fmt :: "'t core_fmt_Debug \<Rightarrow> 't alloc_vec_Vec \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "alloc_vec_DebugVec_fmt _ _ f = fmt_ok f"
definition core_fmt_DebugVec :: "'t core_fmt_Debug \<Rightarrow> ('t alloc_vec_Vec) core_fmt_Debug" where
  "core_fmt_DebugVec inst = (| core_fmt_Debug_fmt = alloc_vec_DebugVec_fmt inst |)"
definition core_array_DebugArray_fmt :: "usize \<Rightarrow> 't core_fmt_Debug \<Rightarrow> 't array \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_array_DebugArray_fmt _ _ _ f = fmt_ok f"
definition core_fmt_DebugArray :: "usize \<Rightarrow> 't core_fmt_Debug \<Rightarrow> ('t array) core_fmt_Debug" where
  "core_fmt_DebugArray n inst = (| core_fmt_Debug_fmt = core_array_DebugArray_fmt n inst |)"
definition core_slice_DebugSlice_fmt :: "'t core_fmt_Debug \<Rightarrow> 't slice \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_slice_DebugSlice_fmt _ _ f = fmt_ok f"
definition core_fmt_DebugSlice :: "'t core_fmt_Debug \<Rightarrow> ('t slice) core_fmt_Debug" where
  "core_fmt_DebugSlice inst = (| core_fmt_Debug_fmt = core_slice_DebugSlice_fmt inst |)"
definition core_fmt_num_DebugI8_fmt :: "i8 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_DebugI8_fmt _ f = fmt_ok f"
definition core_fmt_DebugI8 :: "i8 core_fmt_Debug" where
  "core_fmt_DebugI8 = (| core_fmt_Debug_fmt = core_fmt_num_DebugI8_fmt |)"
definition core_fmt_num_imp_DisplayI8_fmt :: "i8 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_imp_DisplayI8_fmt _ f = fmt_ok f"
definition core_fmt_DisplayI8 :: "i8 core_fmt_Display" where
  "core_fmt_DisplayI8 = (| core_fmt_Display_fmt = core_fmt_num_imp_DisplayI8_fmt |)"
definition core_fmt_num_DebugI16_fmt :: "i16 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_DebugI16_fmt _ f = fmt_ok f"
definition core_fmt_DebugI16 :: "i16 core_fmt_Debug" where
  "core_fmt_DebugI16 = (| core_fmt_Debug_fmt = core_fmt_num_DebugI16_fmt |)"
definition core_fmt_num_imp_DisplayI16_fmt :: "i16 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_imp_DisplayI16_fmt _ f = fmt_ok f"
definition core_fmt_DisplayI16 :: "i16 core_fmt_Display" where
  "core_fmt_DisplayI16 = (| core_fmt_Display_fmt = core_fmt_num_imp_DisplayI16_fmt |)"
definition core_fmt_num_DebugI32_fmt :: "i32 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_DebugI32_fmt _ f = fmt_ok f"
definition core_fmt_DebugI32 :: "i32 core_fmt_Debug" where
  "core_fmt_DebugI32 = (| core_fmt_Debug_fmt = core_fmt_num_DebugI32_fmt |)"
definition core_fmt_num_imp_DisplayI32_fmt :: "i32 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_imp_DisplayI32_fmt _ f = fmt_ok f"
definition core_fmt_DisplayI32 :: "i32 core_fmt_Display" where
  "core_fmt_DisplayI32 = (| core_fmt_Display_fmt = core_fmt_num_imp_DisplayI32_fmt |)"
definition core_fmt_num_DebugI64_fmt :: "i64 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_DebugI64_fmt _ f = fmt_ok f"
definition core_fmt_DebugI64 :: "i64 core_fmt_Debug" where
  "core_fmt_DebugI64 = (| core_fmt_Debug_fmt = core_fmt_num_DebugI64_fmt |)"
definition core_fmt_num_imp_DisplayI64_fmt :: "i64 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_imp_DisplayI64_fmt _ f = fmt_ok f"
definition core_fmt_DisplayI64 :: "i64 core_fmt_Display" where
  "core_fmt_DisplayI64 = (| core_fmt_Display_fmt = core_fmt_num_imp_DisplayI64_fmt |)"
definition core_fmt_num_DebugI128_fmt :: "i128 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_DebugI128_fmt _ f = fmt_ok f"
definition core_fmt_DebugI128 :: "i128 core_fmt_Debug" where
  "core_fmt_DebugI128 = (| core_fmt_Debug_fmt = core_fmt_num_DebugI128_fmt |)"
definition core_fmt_num_imp_DisplayI128_fmt :: "i128 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_imp_DisplayI128_fmt _ f = fmt_ok f"
definition core_fmt_DisplayI128 :: "i128 core_fmt_Display" where
  "core_fmt_DisplayI128 = (| core_fmt_Display_fmt = core_fmt_num_imp_DisplayI128_fmt |)"
definition core_fmt_num_DebugIsize_fmt :: "isize \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_DebugIsize_fmt _ f = fmt_ok f"
definition core_fmt_DebugIsize :: "isize core_fmt_Debug" where
  "core_fmt_DebugIsize = (| core_fmt_Debug_fmt = core_fmt_num_DebugIsize_fmt |)"
definition core_fmt_num_imp_DisplayIsize_fmt :: "isize \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_imp_DisplayIsize_fmt _ f = fmt_ok f"
definition core_fmt_DisplayIsize :: "isize core_fmt_Display" where
  "core_fmt_DisplayIsize = (| core_fmt_Display_fmt = core_fmt_num_imp_DisplayIsize_fmt |)"
definition core_fmt_num_DebugU8_fmt :: "u8 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_DebugU8_fmt _ f = fmt_ok f"
definition core_fmt_DebugU8 :: "u8 core_fmt_Debug" where
  "core_fmt_DebugU8 = (| core_fmt_Debug_fmt = core_fmt_num_DebugU8_fmt |)"
definition core_fmt_num_imp_DisplayU8_fmt :: "u8 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_imp_DisplayU8_fmt _ f = fmt_ok f"
definition core_fmt_DisplayU8 :: "u8 core_fmt_Display" where
  "core_fmt_DisplayU8 = (| core_fmt_Display_fmt = core_fmt_num_imp_DisplayU8_fmt |)"
definition core_fmt_num_DebugU16_fmt :: "u16 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_DebugU16_fmt _ f = fmt_ok f"
definition core_fmt_DebugU16 :: "u16 core_fmt_Debug" where
  "core_fmt_DebugU16 = (| core_fmt_Debug_fmt = core_fmt_num_DebugU16_fmt |)"
definition core_fmt_num_imp_DisplayU16_fmt :: "u16 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_imp_DisplayU16_fmt _ f = fmt_ok f"
definition core_fmt_DisplayU16 :: "u16 core_fmt_Display" where
  "core_fmt_DisplayU16 = (| core_fmt_Display_fmt = core_fmt_num_imp_DisplayU16_fmt |)"
definition core_fmt_num_DebugU32_fmt :: "u32 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_DebugU32_fmt _ f = fmt_ok f"
definition core_fmt_DebugU32 :: "u32 core_fmt_Debug" where
  "core_fmt_DebugU32 = (| core_fmt_Debug_fmt = core_fmt_num_DebugU32_fmt |)"
definition core_fmt_num_imp_DisplayU32_fmt :: "u32 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_imp_DisplayU32_fmt _ f = fmt_ok f"
definition core_fmt_DisplayU32 :: "u32 core_fmt_Display" where
  "core_fmt_DisplayU32 = (| core_fmt_Display_fmt = core_fmt_num_imp_DisplayU32_fmt |)"
definition core_fmt_num_DebugU64_fmt :: "u64 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_DebugU64_fmt _ f = fmt_ok f"
definition core_fmt_DebugU64 :: "u64 core_fmt_Debug" where
  "core_fmt_DebugU64 = (| core_fmt_Debug_fmt = core_fmt_num_DebugU64_fmt |)"
definition core_fmt_num_imp_DisplayU64_fmt :: "u64 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_imp_DisplayU64_fmt _ f = fmt_ok f"
definition core_fmt_DisplayU64 :: "u64 core_fmt_Display" where
  "core_fmt_DisplayU64 = (| core_fmt_Display_fmt = core_fmt_num_imp_DisplayU64_fmt |)"
definition core_fmt_num_DebugU128_fmt :: "u128 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_DebugU128_fmt _ f = fmt_ok f"
definition core_fmt_DebugU128 :: "u128 core_fmt_Debug" where
  "core_fmt_DebugU128 = (| core_fmt_Debug_fmt = core_fmt_num_DebugU128_fmt |)"
definition core_fmt_num_imp_DisplayU128_fmt :: "u128 \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_imp_DisplayU128_fmt _ f = fmt_ok f"
definition core_fmt_DisplayU128 :: "u128 core_fmt_Display" where
  "core_fmt_DisplayU128 = (| core_fmt_Display_fmt = core_fmt_num_imp_DisplayU128_fmt |)"
definition core_fmt_num_DebugUsize_fmt :: "usize \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_DebugUsize_fmt _ f = fmt_ok f"
definition core_fmt_DebugUsize :: "usize core_fmt_Debug" where
  "core_fmt_DebugUsize = (| core_fmt_Debug_fmt = core_fmt_num_DebugUsize_fmt |)"
definition core_fmt_num_imp_DisplayUsize_fmt :: "usize \<Rightarrow> core_fmt_Formatter \<Rightarrow> fmt_result" where
  "core_fmt_num_imp_DisplayUsize_fmt _ f = fmt_ok f"
definition core_fmt_DisplayUsize :: "usize core_fmt_Display" where
  "core_fmt_DisplayUsize = (| core_fmt_Display_fmt = core_fmt_num_imp_DisplayUsize_fmt |)"

(* [Result::unwrap], [Result::expect], [Option::expect]: panic on the error
   case (the [Debug] dictionary used to print the error is ignored). *)
definition core_result_Result_unwrap :: "'e core_fmt_Debug \<Rightarrow> ('t, 'e) core_result_Result \<Rightarrow> 't result" where
  "core_result_Result_unwrap _ r = (case r of core_result_Result_Ok x \<Rightarrow> Ok x | core_result_Result_Err _ \<Rightarrow> Fail Failure)"
definition core_result_Result_expect :: "'e core_fmt_Debug \<Rightarrow> ('t, 'e) core_result_Result \<Rightarrow> str \<Rightarrow> 't result" where
  "core_result_Result_expect _ r _ = (case r of core_result_Result_Ok x \<Rightarrow> Ok x | core_result_Result_Err _ \<Rightarrow> Fail Failure)"
definition core_option_Option_expect :: "'t option \<Rightarrow> str \<Rightarrow> 't result" where
  "core_option_Option_expect x _ = (case x of Some v \<Rightarrow> Ok v | None \<Rightarrow> Fail Failure)"


(*** alloc::alloc::Global: the global allocator, an opaque unit-like type *)
type_synonym alloc_alloc_Global = unit

(* [Clone] / [Copy] for [bool] *)
definition core_clone_impls_CloneBool_clone :: "bool \<Rightarrow> bool" where
  "core_clone_impls_CloneBool_clone x = x"
definition core_clone_impls_CloneBool_clone_from :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "core_clone_impls_CloneBool_clone_from _ y = y"
definition core_clone_CloneBool :: "bool core_clone_Clone" where
  "core_clone_CloneBool = (| core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition core_marker_CopyBool :: "bool core_marker_Copy" where
  "core_marker_CopyBool = (| cloneInst = core_clone_CloneBool |)"

(* Builtin [Clone]/[Copy] instances used by Aeneas for the builtin types
   whose clone is the identity (unit, tuples, ...). *)
definition BuiltinClone :: "'a core_clone_Clone" where
  "BuiltinClone = (| core_clone_Clone_clone = (\<lambda>x. Ok x),
    core_clone_Clone_clone_from = (\<lambda>_ y. Ok y) |)"
definition BuiltinCopy :: "'a core_marker_Copy" where
  "BuiltinCopy = (| cloneInst = BuiltinClone |)"

(* Builtin [FnOnce]/[FnMut]/[Fn] instances for function values. *)
definition BuiltinFnOnce :: "('i \<Rightarrow> 'o result, 'i, 'o) core_ops_function_FnOnce" where
  "BuiltinFnOnce = (| core_ops_function_FnOnce_call_once = (\<lambda>f x. f x) |)"
definition BuiltinFnMut :: "('i \<Rightarrow> 'o result, 'i, 'o) core_ops_function_FnMut" where
  "BuiltinFnMut = (| fnOnceInst = BuiltinFnOnce,
    core_ops_function_FnMut_call_mut = (\<lambda>f x. (v <- f x; Ok (v, f))) |)"
definition BuiltinFn :: "('i \<Rightarrow> 'o result, 'i, 'o) core_ops_function_Fn" where
  "BuiltinFn = (| fnMutInst = BuiltinFnMut, core_ops_function_Fn_call = (\<lambda>f x. f x) |)"

(*** core::cmp (continued): Eq, and PartialEq / Clone of std types *)

(* Trait declaration: [core::cmp::Eq] *)
record 'self core_cmp_Eq =
  partialEqInst :: "('self, 'self) core_cmp_PartialEq"
  core_cmp_Eq_assert_fields_are_eq :: "'self \<Rightarrow> unit result"

definition core_cmp_Eq_assert_fields_are_eq_default_body :: "'self \<Rightarrow> unit result" where
  "core_cmp_Eq_assert_fields_are_eq_default_body _ = Ok ()"
definition core_cmp_Eq_assert_fields_are_eq_default :: "'self core_cmp_Eq \<Rightarrow> 'self \<Rightarrow> unit result" where
  "core_cmp_Eq_assert_fields_are_eq_default _ _ = Ok ()"

definition core_cmp_impls_PartialEqBool_eq :: "bool \<Rightarrow> bool \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqBool_eq x y = Ok (x = y)"
definition core_cmp_impls_PartialEqBool_ne :: "bool \<Rightarrow> bool \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqBool_ne x y = Ok (x \<noteq> y)"
definition core_cmp_PartialEqBool :: "(bool, bool) core_cmp_PartialEq" where
  "core_cmp_PartialEqBool = (| core_cmp_PartialEq_eq = core_cmp_impls_PartialEqBool_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqBool_ne |)"

definition core_cmp_impls_PartialEqUnit_eq :: "unit \<Rightarrow> unit \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqUnit_eq _ _ = Ok True"
definition core_cmp_impls_PartialEqUnit_ne :: "unit \<Rightarrow> unit \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqUnit_ne _ _ = Ok False"
definition core_cmp_PartialEqUnit :: "(unit, unit) core_cmp_PartialEq" where
  "core_cmp_PartialEqUnit = (| core_cmp_PartialEq_eq = core_cmp_impls_PartialEqUnit_eq,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqUnit_ne |)"

(* [impl PartialEq<&B> for &A]: compare the referenced values *)
definition core_cmp_impls_PartialEqShared_eq ::
  "('a, 'b) core_cmp_PartialEq \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqShared_eq inst x y = core_cmp_PartialEq_eq inst x y"
definition core_cmp_impls_PartialEqShared_ne ::
  "('a, 'b) core_cmp_PartialEq \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool result" where
  "core_cmp_impls_PartialEqShared_ne inst x y = core_cmp_PartialEq_ne inst x y"
definition core_cmp_PartialEqShared ::
  "('a, 'b) core_cmp_PartialEq \<Rightarrow> ('a, 'b) core_cmp_PartialEq" where
  "core_cmp_PartialEqShared inst = (|
    core_cmp_PartialEq_eq = core_cmp_impls_PartialEqShared_eq inst,
    core_cmp_PartialEq_ne = core_cmp_impls_PartialEqShared_ne inst |)"

(* [impl PartialEq for Box<T>]: boxes are transparent *)
definition alloc_boxed_PartialEqBox_eq ::
  "('t, 't) core_cmp_PartialEq \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> bool result" where
  "alloc_boxed_PartialEqBox_eq inst x y = core_cmp_PartialEq_eq inst x y"
definition alloc_boxed_PartialEqBox_ne ::
  "('t, 't) core_cmp_PartialEq \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> bool result" where
  "alloc_boxed_PartialEqBox_ne inst x y = core_cmp_PartialEq_ne inst x y"
definition core_cmp_PartialEqBox ::
  "('t, 't) core_cmp_PartialEq \<Rightarrow> ('t, 't) core_cmp_PartialEq" where
  "core_cmp_PartialEqBox inst = (|
    core_cmp_PartialEq_eq = alloc_boxed_PartialEqBox_eq inst,
    core_cmp_PartialEq_ne = alloc_boxed_PartialEqBox_ne inst |)"

(* [impl PartialEq<Vec<U>> for Vec<T>]: element-wise comparison *)
partial_function (result) list_all2_result ::
  "('t \<Rightarrow> 'u \<Rightarrow> bool result) \<Rightarrow> 't list \<Rightarrow> 'u list \<Rightarrow> bool result" where
  "list_all2_result eq xs ys =
    (case (xs, ys) of
       ([], []) \<Rightarrow> Ok True
     | (x # xs', y # ys') \<Rightarrow> (b <- eq x y; if b then list_all2_result eq xs' ys' else Ok False)
     | _ \<Rightarrow> Ok False)"

definition alloc_vec_partial_eq_PartialEqVec_eq ::
  "('t, 'u) core_cmp_PartialEq \<Rightarrow> 't alloc_vec_Vec \<Rightarrow> 'u alloc_vec_Vec \<Rightarrow> bool result" where
  "alloc_vec_partial_eq_PartialEqVec_eq inst xs ys =
    list_all2_result (core_cmp_PartialEq_eq inst) xs ys"
definition alloc_vec_partial_eq_PartialEqVec_ne ::
  "('t, 'u) core_cmp_PartialEq \<Rightarrow> 't alloc_vec_Vec \<Rightarrow> 'u alloc_vec_Vec \<Rightarrow> bool result" where
  "alloc_vec_partial_eq_PartialEqVec_ne inst xs ys =
    (b <- alloc_vec_partial_eq_PartialEqVec_eq inst xs ys; Ok (\<not> b))"
definition core_cmp_PartialEqVec ::
  "('t, 'u) core_cmp_PartialEq \<Rightarrow> ('t alloc_vec_Vec, 'u alloc_vec_Vec) core_cmp_PartialEq" where
  "core_cmp_PartialEqVec inst = (|
    core_cmp_PartialEq_eq = alloc_vec_partial_eq_PartialEqVec_eq inst,
    core_cmp_PartialEq_ne = alloc_vec_partial_eq_PartialEqVec_ne inst |)"

(* [impl Clone for Box<T>], [impl Clone for Vec<T>], [impl Clone for Global] *)
definition alloc_boxed_CloneBox_clone ::
  "'t core_clone_Clone \<Rightarrow> 't \<Rightarrow> 't result" where
  "alloc_boxed_CloneBox_clone inst x = core_clone_Clone_clone inst x"
definition core_clone_CloneBox ::
  "'t core_clone_Clone \<Rightarrow> 't core_clone_Clone" where
  "core_clone_CloneBox inst = (|
    core_clone_Clone_clone = alloc_boxed_CloneBox_clone inst,
    core_clone_Clone_clone_from =
      core_clone_Clone_clone_from_default_body (alloc_boxed_CloneBox_clone inst) |)"

partial_function (result) list_clone_result ::
  "('t \<Rightarrow> 't result) \<Rightarrow> 't list \<Rightarrow> 't list result" where
  "list_clone_result clone xs =
    (case xs of
       [] \<Rightarrow> Ok []
     | x # xs' \<Rightarrow> (y <- clone x; ys <- list_clone_result clone xs'; Ok (y # ys)))"

definition alloc_vec_CloneVec_clone ::
  "'t core_clone_Clone \<Rightarrow> 't alloc_vec_Vec \<Rightarrow> 't alloc_vec_Vec result" where
  "alloc_vec_CloneVec_clone inst v = list_clone_result (core_clone_Clone_clone inst) v"
definition core_clone_CloneVec ::
  "'t core_clone_Clone \<Rightarrow> ('t alloc_vec_Vec) core_clone_Clone" where
  "core_clone_CloneVec inst = (|
    core_clone_Clone_clone = alloc_vec_CloneVec_clone inst,
    core_clone_Clone_clone_from =
      core_clone_Clone_clone_from_default_body (alloc_vec_CloneVec_clone inst) |)"

definition alloc_alloc_CloneGlobal_clone :: "alloc_alloc_Global \<Rightarrow> alloc_alloc_Global result" where
  "alloc_alloc_CloneGlobal_clone x = Ok x"
definition core_clone_CloneGlobal :: "alloc_alloc_Global core_clone_Clone" where
  "core_clone_CloneGlobal = (|
    core_clone_Clone_clone = alloc_alloc_CloneGlobal_clone,
    core_clone_Clone_clone_from = core_clone_Clone_clone_from_default_body alloc_alloc_CloneGlobal_clone |)"


(*** core::iter *)

(* [core::iter::adapters::step_by::StepBy]: an iterator and a step (the real
   struct keeps [step - 1] and a [first_take] flag; this is the Lean model). *)
record 'i core_iter_adapters_step_by_StepBy =
  core_iter_adapters_step_by_StepBy_iter :: 'i
  core_iter_adapters_step_by_StepBy_step_by :: usize

(* Trait declaration: [core::iter::traits::iterator::Iterator].  Only [next]
   and [step_by] are modelled; the associated type [Item] is a type parameter. *)
record ('self, 'item) core_iter_traits_iterator_Iterator =
  core_iter_traits_iterator_Iterator_next :: "'self \<Rightarrow> ('item option \<times> 'self) result"
  core_iter_traits_iterator_Iterator_step_by ::
    "'self \<Rightarrow> usize \<Rightarrow> 'self core_iter_adapters_step_by_StepBy result"

(* Default implementation of [Iterator::step_by]: panics on a zero step. *)
definition core_iter_traits_iterator_Iterator_step_by_default_body ::
  "'self \<Rightarrow> usize \<Rightarrow> 'self core_iter_adapters_step_by_StepBy result" where
  "core_iter_traits_iterator_Iterator_step_by_default_body self n =
    (if n = 0 then Fail Failure
     else Ok (| core_iter_adapters_step_by_StepBy_iter = self,
                core_iter_adapters_step_by_StepBy_step_by = n |))"

definition core_iter_traits_iterator_Iterator_step_by_default ::
  "('self, 'item) core_iter_traits_iterator_Iterator \<Rightarrow> 'self \<Rightarrow> usize \<Rightarrow>
   'self core_iter_adapters_step_by_StepBy result" where
  "core_iter_traits_iterator_Iterator_step_by_default _ = core_iter_traits_iterator_Iterator_step_by_default_body"

(* Trait declaration: [core::iter::range::Step] *)
record 'self core_iter_range_Step =
  stepCloneInst :: "'self core_clone_Clone"
  stepPartialOrdInst :: "('self, 'self) core_cmp_PartialOrd"
  core_iter_range_Step_steps_between :: "'self \<Rightarrow> 'self \<Rightarrow> (usize \<times> usize option) result"
  core_iter_range_Step_forward_checked :: "'self \<Rightarrow> usize \<Rightarrow> 'self option result"
  core_iter_range_Step_backward_checked :: "'self \<Rightarrow> usize \<Rightarrow> 'self option result"
  core_iter_range_Step_forward_overflowing :: "'self \<Rightarrow> usize \<Rightarrow> ('self \<times> bool) result"
  core_iter_range_Step_backward_overflowing :: "'self \<Rightarrow> usize \<Rightarrow> ('self \<times> bool) result"

(* [Step] for the machine integers *)
definition scalar_steps_between :: "int \<Rightarrow> int \<Rightarrow> (usize \<times> usize option) result" where
  "scalar_steps_between a b =
    Ok (if a \<le> b then
          (if b - a \<le> usize_max then (b - a, Some (b - a)) else (usize_max, None))
        else (0, None))"
definition scalar_forward_checked :: "scalar_ty \<Rightarrow> int \<Rightarrow> usize \<Rightarrow> int option result" where
  "scalar_forward_checked ty a n = Ok (if scalar_in_bounds ty (a + n) then Some (a + n) else None)"
definition scalar_backward_checked :: "scalar_ty \<Rightarrow> int \<Rightarrow> usize \<Rightarrow> int option result" where
  "scalar_backward_checked ty a n = Ok (if scalar_in_bounds ty (a - n) then Some (a - n) else None)"
definition scalar_forward_overflowing :: "scalar_ty \<Rightarrow> int \<Rightarrow> usize \<Rightarrow> (int \<times> bool) result" where
  "scalar_forward_overflowing ty a n = Ok (scalar_wrap ty (a + n), \<not> scalar_in_bounds ty (a + n))"
definition scalar_backward_overflowing :: "scalar_ty \<Rightarrow> int \<Rightarrow> usize \<Rightarrow> (int \<times> bool) result" where
  "scalar_backward_overflowing ty a n = Ok (scalar_wrap ty (a - n), \<not> scalar_in_bounds ty (a - n))"
definition core_iter_range_StepI8_steps_between :: "i8 \<Rightarrow> i8 \<Rightarrow> (usize \<times> usize option) result" where
  "core_iter_range_StepI8_steps_between a b = scalar_steps_between a b"
definition core_iter_range_StepI8_forward_checked :: "i8 \<Rightarrow> usize \<Rightarrow> i8 option result" where
  "core_iter_range_StepI8_forward_checked a n = scalar_forward_checked I8 a n"
definition core_iter_range_StepI8_backward_checked :: "i8 \<Rightarrow> usize \<Rightarrow> i8 option result" where
  "core_iter_range_StepI8_backward_checked a n = scalar_backward_checked I8 a n"
definition core_iter_range_StepI8_forward_overflowing :: "i8 \<Rightarrow> usize \<Rightarrow> (i8 \<times> bool) result" where
  "core_iter_range_StepI8_forward_overflowing a n = scalar_forward_overflowing I8 a n"
definition core_iter_range_StepI8_backward_overflowing :: "i8 \<Rightarrow> usize \<Rightarrow> (i8 \<times> bool) result" where
  "core_iter_range_StepI8_backward_overflowing a n = scalar_backward_overflowing I8 a n"
definition core_iter_range_StepI8 :: "i8 core_iter_range_Step" where
  "core_iter_range_StepI8 = (|
    stepCloneInst = core_clone_CloneI8,
    stepPartialOrdInst = core_cmp_PartialOrdI8,
    core_iter_range_Step_steps_between = core_iter_range_StepI8_steps_between,
    core_iter_range_Step_forward_checked = core_iter_range_StepI8_forward_checked,
    core_iter_range_Step_backward_checked = core_iter_range_StepI8_backward_checked,
    core_iter_range_Step_forward_overflowing = core_iter_range_StepI8_forward_overflowing,
    core_iter_range_Step_backward_overflowing = core_iter_range_StepI8_backward_overflowing |)"
definition core_iter_range_StepI16_steps_between :: "i16 \<Rightarrow> i16 \<Rightarrow> (usize \<times> usize option) result" where
  "core_iter_range_StepI16_steps_between a b = scalar_steps_between a b"
definition core_iter_range_StepI16_forward_checked :: "i16 \<Rightarrow> usize \<Rightarrow> i16 option result" where
  "core_iter_range_StepI16_forward_checked a n = scalar_forward_checked I16 a n"
definition core_iter_range_StepI16_backward_checked :: "i16 \<Rightarrow> usize \<Rightarrow> i16 option result" where
  "core_iter_range_StepI16_backward_checked a n = scalar_backward_checked I16 a n"
definition core_iter_range_StepI16_forward_overflowing :: "i16 \<Rightarrow> usize \<Rightarrow> (i16 \<times> bool) result" where
  "core_iter_range_StepI16_forward_overflowing a n = scalar_forward_overflowing I16 a n"
definition core_iter_range_StepI16_backward_overflowing :: "i16 \<Rightarrow> usize \<Rightarrow> (i16 \<times> bool) result" where
  "core_iter_range_StepI16_backward_overflowing a n = scalar_backward_overflowing I16 a n"
definition core_iter_range_StepI16 :: "i16 core_iter_range_Step" where
  "core_iter_range_StepI16 = (|
    stepCloneInst = core_clone_CloneI16,
    stepPartialOrdInst = core_cmp_PartialOrdI16,
    core_iter_range_Step_steps_between = core_iter_range_StepI16_steps_between,
    core_iter_range_Step_forward_checked = core_iter_range_StepI16_forward_checked,
    core_iter_range_Step_backward_checked = core_iter_range_StepI16_backward_checked,
    core_iter_range_Step_forward_overflowing = core_iter_range_StepI16_forward_overflowing,
    core_iter_range_Step_backward_overflowing = core_iter_range_StepI16_backward_overflowing |)"
definition core_iter_range_StepI32_steps_between :: "i32 \<Rightarrow> i32 \<Rightarrow> (usize \<times> usize option) result" where
  "core_iter_range_StepI32_steps_between a b = scalar_steps_between a b"
definition core_iter_range_StepI32_forward_checked :: "i32 \<Rightarrow> usize \<Rightarrow> i32 option result" where
  "core_iter_range_StepI32_forward_checked a n = scalar_forward_checked I32 a n"
definition core_iter_range_StepI32_backward_checked :: "i32 \<Rightarrow> usize \<Rightarrow> i32 option result" where
  "core_iter_range_StepI32_backward_checked a n = scalar_backward_checked I32 a n"
definition core_iter_range_StepI32_forward_overflowing :: "i32 \<Rightarrow> usize \<Rightarrow> (i32 \<times> bool) result" where
  "core_iter_range_StepI32_forward_overflowing a n = scalar_forward_overflowing I32 a n"
definition core_iter_range_StepI32_backward_overflowing :: "i32 \<Rightarrow> usize \<Rightarrow> (i32 \<times> bool) result" where
  "core_iter_range_StepI32_backward_overflowing a n = scalar_backward_overflowing I32 a n"
definition core_iter_range_StepI32 :: "i32 core_iter_range_Step" where
  "core_iter_range_StepI32 = (|
    stepCloneInst = core_clone_CloneI32,
    stepPartialOrdInst = core_cmp_PartialOrdI32,
    core_iter_range_Step_steps_between = core_iter_range_StepI32_steps_between,
    core_iter_range_Step_forward_checked = core_iter_range_StepI32_forward_checked,
    core_iter_range_Step_backward_checked = core_iter_range_StepI32_backward_checked,
    core_iter_range_Step_forward_overflowing = core_iter_range_StepI32_forward_overflowing,
    core_iter_range_Step_backward_overflowing = core_iter_range_StepI32_backward_overflowing |)"
definition core_iter_range_StepI64_steps_between :: "i64 \<Rightarrow> i64 \<Rightarrow> (usize \<times> usize option) result" where
  "core_iter_range_StepI64_steps_between a b = scalar_steps_between a b"
definition core_iter_range_StepI64_forward_checked :: "i64 \<Rightarrow> usize \<Rightarrow> i64 option result" where
  "core_iter_range_StepI64_forward_checked a n = scalar_forward_checked I64 a n"
definition core_iter_range_StepI64_backward_checked :: "i64 \<Rightarrow> usize \<Rightarrow> i64 option result" where
  "core_iter_range_StepI64_backward_checked a n = scalar_backward_checked I64 a n"
definition core_iter_range_StepI64_forward_overflowing :: "i64 \<Rightarrow> usize \<Rightarrow> (i64 \<times> bool) result" where
  "core_iter_range_StepI64_forward_overflowing a n = scalar_forward_overflowing I64 a n"
definition core_iter_range_StepI64_backward_overflowing :: "i64 \<Rightarrow> usize \<Rightarrow> (i64 \<times> bool) result" where
  "core_iter_range_StepI64_backward_overflowing a n = scalar_backward_overflowing I64 a n"
definition core_iter_range_StepI64 :: "i64 core_iter_range_Step" where
  "core_iter_range_StepI64 = (|
    stepCloneInst = core_clone_CloneI64,
    stepPartialOrdInst = core_cmp_PartialOrdI64,
    core_iter_range_Step_steps_between = core_iter_range_StepI64_steps_between,
    core_iter_range_Step_forward_checked = core_iter_range_StepI64_forward_checked,
    core_iter_range_Step_backward_checked = core_iter_range_StepI64_backward_checked,
    core_iter_range_Step_forward_overflowing = core_iter_range_StepI64_forward_overflowing,
    core_iter_range_Step_backward_overflowing = core_iter_range_StepI64_backward_overflowing |)"
definition core_iter_range_StepI128_steps_between :: "i128 \<Rightarrow> i128 \<Rightarrow> (usize \<times> usize option) result" where
  "core_iter_range_StepI128_steps_between a b = scalar_steps_between a b"
definition core_iter_range_StepI128_forward_checked :: "i128 \<Rightarrow> usize \<Rightarrow> i128 option result" where
  "core_iter_range_StepI128_forward_checked a n = scalar_forward_checked I128 a n"
definition core_iter_range_StepI128_backward_checked :: "i128 \<Rightarrow> usize \<Rightarrow> i128 option result" where
  "core_iter_range_StepI128_backward_checked a n = scalar_backward_checked I128 a n"
definition core_iter_range_StepI128_forward_overflowing :: "i128 \<Rightarrow> usize \<Rightarrow> (i128 \<times> bool) result" where
  "core_iter_range_StepI128_forward_overflowing a n = scalar_forward_overflowing I128 a n"
definition core_iter_range_StepI128_backward_overflowing :: "i128 \<Rightarrow> usize \<Rightarrow> (i128 \<times> bool) result" where
  "core_iter_range_StepI128_backward_overflowing a n = scalar_backward_overflowing I128 a n"
definition core_iter_range_StepI128 :: "i128 core_iter_range_Step" where
  "core_iter_range_StepI128 = (|
    stepCloneInst = core_clone_CloneI128,
    stepPartialOrdInst = core_cmp_PartialOrdI128,
    core_iter_range_Step_steps_between = core_iter_range_StepI128_steps_between,
    core_iter_range_Step_forward_checked = core_iter_range_StepI128_forward_checked,
    core_iter_range_Step_backward_checked = core_iter_range_StepI128_backward_checked,
    core_iter_range_Step_forward_overflowing = core_iter_range_StepI128_forward_overflowing,
    core_iter_range_Step_backward_overflowing = core_iter_range_StepI128_backward_overflowing |)"
definition core_iter_range_StepIsize_steps_between :: "isize \<Rightarrow> isize \<Rightarrow> (usize \<times> usize option) result" where
  "core_iter_range_StepIsize_steps_between a b = scalar_steps_between a b"
definition core_iter_range_StepIsize_forward_checked :: "isize \<Rightarrow> usize \<Rightarrow> isize option result" where
  "core_iter_range_StepIsize_forward_checked a n = scalar_forward_checked Isize a n"
definition core_iter_range_StepIsize_backward_checked :: "isize \<Rightarrow> usize \<Rightarrow> isize option result" where
  "core_iter_range_StepIsize_backward_checked a n = scalar_backward_checked Isize a n"
definition core_iter_range_StepIsize_forward_overflowing :: "isize \<Rightarrow> usize \<Rightarrow> (isize \<times> bool) result" where
  "core_iter_range_StepIsize_forward_overflowing a n = scalar_forward_overflowing Isize a n"
definition core_iter_range_StepIsize_backward_overflowing :: "isize \<Rightarrow> usize \<Rightarrow> (isize \<times> bool) result" where
  "core_iter_range_StepIsize_backward_overflowing a n = scalar_backward_overflowing Isize a n"
definition core_iter_range_StepIsize :: "isize core_iter_range_Step" where
  "core_iter_range_StepIsize = (|
    stepCloneInst = core_clone_CloneIsize,
    stepPartialOrdInst = core_cmp_PartialOrdIsize,
    core_iter_range_Step_steps_between = core_iter_range_StepIsize_steps_between,
    core_iter_range_Step_forward_checked = core_iter_range_StepIsize_forward_checked,
    core_iter_range_Step_backward_checked = core_iter_range_StepIsize_backward_checked,
    core_iter_range_Step_forward_overflowing = core_iter_range_StepIsize_forward_overflowing,
    core_iter_range_Step_backward_overflowing = core_iter_range_StepIsize_backward_overflowing |)"
definition core_iter_range_StepU8_steps_between :: "u8 \<Rightarrow> u8 \<Rightarrow> (usize \<times> usize option) result" where
  "core_iter_range_StepU8_steps_between a b = scalar_steps_between a b"
definition core_iter_range_StepU8_forward_checked :: "u8 \<Rightarrow> usize \<Rightarrow> u8 option result" where
  "core_iter_range_StepU8_forward_checked a n = scalar_forward_checked U8 a n"
definition core_iter_range_StepU8_backward_checked :: "u8 \<Rightarrow> usize \<Rightarrow> u8 option result" where
  "core_iter_range_StepU8_backward_checked a n = scalar_backward_checked U8 a n"
definition core_iter_range_StepU8_forward_overflowing :: "u8 \<Rightarrow> usize \<Rightarrow> (u8 \<times> bool) result" where
  "core_iter_range_StepU8_forward_overflowing a n = scalar_forward_overflowing U8 a n"
definition core_iter_range_StepU8_backward_overflowing :: "u8 \<Rightarrow> usize \<Rightarrow> (u8 \<times> bool) result" where
  "core_iter_range_StepU8_backward_overflowing a n = scalar_backward_overflowing U8 a n"
definition core_iter_range_StepU8 :: "u8 core_iter_range_Step" where
  "core_iter_range_StepU8 = (|
    stepCloneInst = core_clone_CloneU8,
    stepPartialOrdInst = core_cmp_PartialOrdU8,
    core_iter_range_Step_steps_between = core_iter_range_StepU8_steps_between,
    core_iter_range_Step_forward_checked = core_iter_range_StepU8_forward_checked,
    core_iter_range_Step_backward_checked = core_iter_range_StepU8_backward_checked,
    core_iter_range_Step_forward_overflowing = core_iter_range_StepU8_forward_overflowing,
    core_iter_range_Step_backward_overflowing = core_iter_range_StepU8_backward_overflowing |)"
definition core_iter_range_StepU16_steps_between :: "u16 \<Rightarrow> u16 \<Rightarrow> (usize \<times> usize option) result" where
  "core_iter_range_StepU16_steps_between a b = scalar_steps_between a b"
definition core_iter_range_StepU16_forward_checked :: "u16 \<Rightarrow> usize \<Rightarrow> u16 option result" where
  "core_iter_range_StepU16_forward_checked a n = scalar_forward_checked U16 a n"
definition core_iter_range_StepU16_backward_checked :: "u16 \<Rightarrow> usize \<Rightarrow> u16 option result" where
  "core_iter_range_StepU16_backward_checked a n = scalar_backward_checked U16 a n"
definition core_iter_range_StepU16_forward_overflowing :: "u16 \<Rightarrow> usize \<Rightarrow> (u16 \<times> bool) result" where
  "core_iter_range_StepU16_forward_overflowing a n = scalar_forward_overflowing U16 a n"
definition core_iter_range_StepU16_backward_overflowing :: "u16 \<Rightarrow> usize \<Rightarrow> (u16 \<times> bool) result" where
  "core_iter_range_StepU16_backward_overflowing a n = scalar_backward_overflowing U16 a n"
definition core_iter_range_StepU16 :: "u16 core_iter_range_Step" where
  "core_iter_range_StepU16 = (|
    stepCloneInst = core_clone_CloneU16,
    stepPartialOrdInst = core_cmp_PartialOrdU16,
    core_iter_range_Step_steps_between = core_iter_range_StepU16_steps_between,
    core_iter_range_Step_forward_checked = core_iter_range_StepU16_forward_checked,
    core_iter_range_Step_backward_checked = core_iter_range_StepU16_backward_checked,
    core_iter_range_Step_forward_overflowing = core_iter_range_StepU16_forward_overflowing,
    core_iter_range_Step_backward_overflowing = core_iter_range_StepU16_backward_overflowing |)"
definition core_iter_range_StepU32_steps_between :: "u32 \<Rightarrow> u32 \<Rightarrow> (usize \<times> usize option) result" where
  "core_iter_range_StepU32_steps_between a b = scalar_steps_between a b"
definition core_iter_range_StepU32_forward_checked :: "u32 \<Rightarrow> usize \<Rightarrow> u32 option result" where
  "core_iter_range_StepU32_forward_checked a n = scalar_forward_checked U32 a n"
definition core_iter_range_StepU32_backward_checked :: "u32 \<Rightarrow> usize \<Rightarrow> u32 option result" where
  "core_iter_range_StepU32_backward_checked a n = scalar_backward_checked U32 a n"
definition core_iter_range_StepU32_forward_overflowing :: "u32 \<Rightarrow> usize \<Rightarrow> (u32 \<times> bool) result" where
  "core_iter_range_StepU32_forward_overflowing a n = scalar_forward_overflowing U32 a n"
definition core_iter_range_StepU32_backward_overflowing :: "u32 \<Rightarrow> usize \<Rightarrow> (u32 \<times> bool) result" where
  "core_iter_range_StepU32_backward_overflowing a n = scalar_backward_overflowing U32 a n"
definition core_iter_range_StepU32 :: "u32 core_iter_range_Step" where
  "core_iter_range_StepU32 = (|
    stepCloneInst = core_clone_CloneU32,
    stepPartialOrdInst = core_cmp_PartialOrdU32,
    core_iter_range_Step_steps_between = core_iter_range_StepU32_steps_between,
    core_iter_range_Step_forward_checked = core_iter_range_StepU32_forward_checked,
    core_iter_range_Step_backward_checked = core_iter_range_StepU32_backward_checked,
    core_iter_range_Step_forward_overflowing = core_iter_range_StepU32_forward_overflowing,
    core_iter_range_Step_backward_overflowing = core_iter_range_StepU32_backward_overflowing |)"
definition core_iter_range_StepU64_steps_between :: "u64 \<Rightarrow> u64 \<Rightarrow> (usize \<times> usize option) result" where
  "core_iter_range_StepU64_steps_between a b = scalar_steps_between a b"
definition core_iter_range_StepU64_forward_checked :: "u64 \<Rightarrow> usize \<Rightarrow> u64 option result" where
  "core_iter_range_StepU64_forward_checked a n = scalar_forward_checked U64 a n"
definition core_iter_range_StepU64_backward_checked :: "u64 \<Rightarrow> usize \<Rightarrow> u64 option result" where
  "core_iter_range_StepU64_backward_checked a n = scalar_backward_checked U64 a n"
definition core_iter_range_StepU64_forward_overflowing :: "u64 \<Rightarrow> usize \<Rightarrow> (u64 \<times> bool) result" where
  "core_iter_range_StepU64_forward_overflowing a n = scalar_forward_overflowing U64 a n"
definition core_iter_range_StepU64_backward_overflowing :: "u64 \<Rightarrow> usize \<Rightarrow> (u64 \<times> bool) result" where
  "core_iter_range_StepU64_backward_overflowing a n = scalar_backward_overflowing U64 a n"
definition core_iter_range_StepU64 :: "u64 core_iter_range_Step" where
  "core_iter_range_StepU64 = (|
    stepCloneInst = core_clone_CloneU64,
    stepPartialOrdInst = core_cmp_PartialOrdU64,
    core_iter_range_Step_steps_between = core_iter_range_StepU64_steps_between,
    core_iter_range_Step_forward_checked = core_iter_range_StepU64_forward_checked,
    core_iter_range_Step_backward_checked = core_iter_range_StepU64_backward_checked,
    core_iter_range_Step_forward_overflowing = core_iter_range_StepU64_forward_overflowing,
    core_iter_range_Step_backward_overflowing = core_iter_range_StepU64_backward_overflowing |)"
definition core_iter_range_StepU128_steps_between :: "u128 \<Rightarrow> u128 \<Rightarrow> (usize \<times> usize option) result" where
  "core_iter_range_StepU128_steps_between a b = scalar_steps_between a b"
definition core_iter_range_StepU128_forward_checked :: "u128 \<Rightarrow> usize \<Rightarrow> u128 option result" where
  "core_iter_range_StepU128_forward_checked a n = scalar_forward_checked U128 a n"
definition core_iter_range_StepU128_backward_checked :: "u128 \<Rightarrow> usize \<Rightarrow> u128 option result" where
  "core_iter_range_StepU128_backward_checked a n = scalar_backward_checked U128 a n"
definition core_iter_range_StepU128_forward_overflowing :: "u128 \<Rightarrow> usize \<Rightarrow> (u128 \<times> bool) result" where
  "core_iter_range_StepU128_forward_overflowing a n = scalar_forward_overflowing U128 a n"
definition core_iter_range_StepU128_backward_overflowing :: "u128 \<Rightarrow> usize \<Rightarrow> (u128 \<times> bool) result" where
  "core_iter_range_StepU128_backward_overflowing a n = scalar_backward_overflowing U128 a n"
definition core_iter_range_StepU128 :: "u128 core_iter_range_Step" where
  "core_iter_range_StepU128 = (|
    stepCloneInst = core_clone_CloneU128,
    stepPartialOrdInst = core_cmp_PartialOrdU128,
    core_iter_range_Step_steps_between = core_iter_range_StepU128_steps_between,
    core_iter_range_Step_forward_checked = core_iter_range_StepU128_forward_checked,
    core_iter_range_Step_backward_checked = core_iter_range_StepU128_backward_checked,
    core_iter_range_Step_forward_overflowing = core_iter_range_StepU128_forward_overflowing,
    core_iter_range_Step_backward_overflowing = core_iter_range_StepU128_backward_overflowing |)"
definition core_iter_range_StepUsize_steps_between :: "usize \<Rightarrow> usize \<Rightarrow> (usize \<times> usize option) result" where
  "core_iter_range_StepUsize_steps_between a b = scalar_steps_between a b"
definition core_iter_range_StepUsize_forward_checked :: "usize \<Rightarrow> usize \<Rightarrow> usize option result" where
  "core_iter_range_StepUsize_forward_checked a n = scalar_forward_checked Usize a n"
definition core_iter_range_StepUsize_backward_checked :: "usize \<Rightarrow> usize \<Rightarrow> usize option result" where
  "core_iter_range_StepUsize_backward_checked a n = scalar_backward_checked Usize a n"
definition core_iter_range_StepUsize_forward_overflowing :: "usize \<Rightarrow> usize \<Rightarrow> (usize \<times> bool) result" where
  "core_iter_range_StepUsize_forward_overflowing a n = scalar_forward_overflowing Usize a n"
definition core_iter_range_StepUsize_backward_overflowing :: "usize \<Rightarrow> usize \<Rightarrow> (usize \<times> bool) result" where
  "core_iter_range_StepUsize_backward_overflowing a n = scalar_backward_overflowing Usize a n"
definition core_iter_range_StepUsize :: "usize core_iter_range_Step" where
  "core_iter_range_StepUsize = (|
    stepCloneInst = core_clone_CloneUsize,
    stepPartialOrdInst = core_cmp_PartialOrdUsize,
    core_iter_range_Step_steps_between = core_iter_range_StepUsize_steps_between,
    core_iter_range_Step_forward_checked = core_iter_range_StepUsize_forward_checked,
    core_iter_range_Step_backward_checked = core_iter_range_StepUsize_backward_checked,
    core_iter_range_Step_forward_overflowing = core_iter_range_StepUsize_forward_overflowing,
    core_iter_range_Step_backward_overflowing = core_iter_range_StepUsize_backward_overflowing |)"

(* [impl Iterator for Range<A>] *)
definition core_iter_range_IteratorRange_next ::
  "'a core_iter_range_Step \<Rightarrow> 'a core_ops_range_Range \<Rightarrow> ('a option \<times> 'a core_ops_range_Range) result" where
  "core_iter_range_IteratorRange_next inst r =
    (lt <- core_cmp_PartialOrd_lt (stepPartialOrdInst inst) (core_ops_range_Range_start r) (core_ops_range_Range_end_' r);
     if lt then
       (s <- core_clone_Clone_clone (stepCloneInst inst) (core_ops_range_Range_start r);
        n <- core_iter_range_Step_forward_checked inst s 1;
        case n of
          None \<Rightarrow> Fail Failure
        | Some n \<Rightarrow> Ok (Some s, r (| core_ops_range_Range_start := n |)))
     else Ok (None, r))"

definition core_iter_range_IteratorRange ::
  "'a core_iter_range_Step \<Rightarrow> ('a core_ops_range_Range, 'a) core_iter_traits_iterator_Iterator" where
  "core_iter_range_IteratorRange inst = (|
    core_iter_traits_iterator_Iterator_next = core_iter_range_IteratorRange_next inst,
    core_iter_traits_iterator_Iterator_step_by = core_iter_traits_iterator_Iterator_step_by_default_body |)"

(* [impl Iterator for StepBy<I>]: skip [step - 1] elements after each one. *)
partial_function (result) step_by_skip ::
  "('i \<Rightarrow> ('item option \<times> 'i) result) \<Rightarrow> 'i \<Rightarrow> nat \<Rightarrow> 'i result" where
  "step_by_skip next it n =
    (if n = 0 then Ok it
     else ((opt, it') <- next it;
           case opt of None \<Rightarrow> Ok it' | Some _ \<Rightarrow> step_by_skip next it' (n - 1)))"

definition core_iter_adapters_step_by_IteratorStepBy_next ::
  "('i, 'item) core_iter_traits_iterator_Iterator \<Rightarrow> 'i core_iter_adapters_step_by_StepBy \<Rightarrow>
   ('item option \<times> 'i core_iter_adapters_step_by_StepBy) result" where
  "core_iter_adapters_step_by_IteratorStepBy_next inst self =
    ((opt, it) <- core_iter_traits_iterator_Iterator_next inst (core_iter_adapters_step_by_StepBy_iter self);
     case opt of
       None \<Rightarrow> Ok (None, self (| core_iter_adapters_step_by_StepBy_iter := it |))
     | Some x \<Rightarrow>
         (it' <- step_by_skip (core_iter_traits_iterator_Iterator_next inst) it
                   (nat (core_iter_adapters_step_by_StepBy_step_by self) - 1);
          Ok (Some x, self (| core_iter_adapters_step_by_StepBy_iter := it' |))))"

definition core_iter_adapters_step_by_IteratorStepBy ::
  "('i, 'item) core_iter_traits_iterator_Iterator \<Rightarrow>
   ('i core_iter_adapters_step_by_StepBy, 'item) core_iter_traits_iterator_Iterator" where
  "core_iter_adapters_step_by_IteratorStepBy inst = (|
    core_iter_traits_iterator_Iterator_next = core_iter_adapters_step_by_IteratorStepBy_next inst,
    core_iter_traits_iterator_Iterator_step_by = core_iter_traits_iterator_Iterator_step_by_default_body |)"

(* [impl Iterator for slice::Iter<T>] *)
definition core_slice_iter_IteratorSliceIter ::
  "('a core_slice_iter_Iter, 'a) core_iter_traits_iterator_Iterator" where
  "core_slice_iter_IteratorSliceIter = (|
    core_iter_traits_iterator_Iterator_next = core_slice_iter_IteratorSliceIter_next,
    core_iter_traits_iterator_Iterator_step_by = core_iter_traits_iterator_Iterator_step_by_default_body |)"

end
