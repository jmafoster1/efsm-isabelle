section\<open>Extended Finite State Machines\<close>
text\<open>
This section presents the theories associated with EFSMs. First we define a language of arithmetic
expressions for guards, outputs, and updates similar to that in IMP \cite{fixme}. We then go on to
define the guard logic such that nonsensical guards (such as testing to see if an integer is greater
than a string) can never evaluate to true. Next, the guard language is defined in terms of
arithmetic expressions and binary relations. In the interest of simplifying the conversion of guards
to constraints, we use a Nor logic, although we define syntax hacks for the expression of guards
using other logical operators. With the underlying types defined, we then define EFSMs and prove
that they are prefix-closed, that is to say that if a string of inputs is accepted by the machine
then all of its prefixes are also accepted.
\<close>
subsection \<open>Arithmetic Expressions\<close>
text\<open>
This theory defines a language of arithmetic expressions over literal values and variables. Here,
values are limited to integers and strings. Variables may be either inputs or registers. We also
limit ourselves to a simple arithmetic of plus and minus as a proof of concept.
\<close>

theory AExp
  imports Value VName FinFun.FinFun "HOL-Library.Option_ord"
begin

no_notation relcomp (infixr "O" 75) and comp  (infixl "o" 55)
declare One_nat_def [simp del]
unbundle finfun_syntax

type_synonym registers = "nat \<Rightarrow>f value option"
type_synonym inputs = "value list"
type_synonym outputs = "value option list"

text_raw\<open>\snip{aexp_otype}{1}{2}{%\<close>
datatype aexp_o = L "value" | V vname_o | Plus aexp_o aexp_o | Minus aexp_o aexp_o | Times aexp_o aexp_o
text_raw\<open>}%endsnip\<close>

fun is_lit :: "aexp_o \<Rightarrow> bool" where
  "is_lit (L _) = True" |
  "is_lit _ = False"

lemma aexp_o_induct_separate_V_cases: "(\<And>x. P (L x)) \<Longrightarrow>
    (\<And>x. P (V (I x))) \<Longrightarrow>
    (\<And>x. P (V (R x))) \<Longrightarrow>
    (\<And>x. P (V (O x))) \<Longrightarrow>
    (\<And>x1a x2a. P x1a \<Longrightarrow> P x2a \<Longrightarrow> P (Plus x1a x2a)) \<Longrightarrow>
    (\<And>x1a x2a. P x1a \<Longrightarrow> P x2a \<Longrightarrow> P (Minus x1a x2a)) \<Longrightarrow> (\<And>x1a x2a. P x1a \<Longrightarrow> P x2a \<Longrightarrow> P (Times x1a x2a)) \<Longrightarrow> P aexp_o"
  by (metis aexp_o.induct vname_o.exhaust)

fun aval_o :: "aexp_o \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> value option" where
  "aval_o (L x) _ _ _ = Some x" |
  "aval_o (V (I ix)) i r o = Some (i ! ix)" |
  "aval_o (V (R ix)) i r o = (r $ ix)" |
  "aval_o (V (O ix)) i r o = (o ! ix)" |
  "aval_o (Plus a\<^sub>1 a\<^sub>2) i r o = value_plus (aval_o a\<^sub>1 i r o)(aval_o a\<^sub>2 i r o)" |
  "aval_o (Minus a\<^sub>1 a\<^sub>2) i r o = value_minus (aval_o a\<^sub>1 i r o) (aval_o a\<^sub>2 i r o)" |
  "aval_o (Times a\<^sub>1 a\<^sub>2) i r o = value_times (aval_o a\<^sub>1 i r o) (aval_o a\<^sub>2 i r o)"

lemma aval_o_plus_symmetry: "aval_o (Plus x y) i r o = aval_o (Plus y x) i r o"
  by (simp add: value_plus_symmetry)

abbreviation null_state ("<>") where
  "null_state \<equiv> (K$ None)"

lemma default_empty: "infinite (UNIV :: 'a set) \<Longrightarrow> finfun_default (<>::'a \<Rightarrow>f 'b option) = None"
  by (simp add: finfun_default_def finfun_default_aux_def)

lemma finfun_to_list_empty: "infinite (UNIV :: 'a set) \<Longrightarrow> finfun_to_list (<>::'a::linorder \<Rightarrow>f 'b option) = []"
  by (simp add: finfun_to_list_const)

nonterminal maplets and maplet

(* TODO: get the <1 := L (Num x)> kind of syntax back *)
syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /:=/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[:=]/ _")
  ""         :: "maplet \<Rightarrow> maplets"             ("_")
  "_Maplets" :: "[maplet, maplets] \<Rightarrow> maplets" ("_,/ _")
  "_MapUpd"  :: "['a \<rightharpoonup> 'b, maplets] \<Rightarrow> 'a \<rightharpoonup> 'b" ("_/'(_')" [900, 0] 900)
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1[_])")
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1<_>)")

translations
  "_MapUpd m (_Maplets xy ms)"  \<rightleftharpoons> "_MapUpd (_MapUpd m xy) ms"
  "_MapUpd m (_maplet  x y)"    \<rightleftharpoons> "m(x $:= CONST Some y)"
  "_Map ms"                     \<rightleftharpoons> "_MapUpd (CONST empty) ms"
  "_Map (_Maplets ms1 ms2)"     \<leftharpoondown> "_MapUpd (_Map ms1) ms2"
  "_Maplets ms1 (_Maplets ms2 ms3)" \<leftharpoondown> "_Maplets (_Maplets ms1 ms2) ms3"

(*syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /:=/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[:=]/ _")
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1<_>)")*)

instantiation aexp_o :: plus begin
fun plus_aexp_o :: "aexp_o \<Rightarrow> aexp_o \<Rightarrow> aexp_o" where
  "plus_aexp_o (L (Num n1)) (L (Num n2)) = L (Num (n1+n2))" |
  "plus_aexp_o x y = Plus x y"

instance by standard
end

instantiation aexp_o :: minus begin
fun minus_aexp_o :: "aexp_o \<Rightarrow> aexp_o \<Rightarrow> aexp_o" where
  "minus_aexp_o (L (Num n1)) (L (Num n2)) = L (Num (n1-n2))" |
  "minus_aexp_o x y = Minus x y"

instance by standard
end

definition input2state :: "value list \<Rightarrow> registers" where
  "input2state n = fold (\<lambda>(k, v) f. f(k $:= Some v)) (enumerate 0 n) (K$ None)"

primrec input2state_prim :: "value list \<Rightarrow> nat \<Rightarrow> registers" where
  "input2state_prim [] _ = (K$ None)" |
  "input2state_prim (v#t) k = (input2state_prim t (k+1))(k $:= Some v)"

lemma input2state_append: "input2state (i @ [a]) = (input2state i)(length i $:= Some a)"
  apply (simp add: eq_finfun_All_ext finfun_All_def finfun_All_except_def)
  apply clarify
  by (simp add: input2state_def enumerate_eq_zip)

lemma fold_conv_foldr: "fold f xs = foldr f (rev xs)"
  by (simp add: foldr_conv_fold)

lemma input2state_out_of_bounds: "i \<ge> length ia \<Longrightarrow> input2state ia $ i = None"
proof(induct ia rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: input2state_def)
next
  case (snoc a as)
  then show ?case
    by (simp add: input2state_def enumerate_eq_zip)
qed

lemma input2state_within_bounds: "input2state i $ x = Some a \<Longrightarrow> x < length i"
  by (metis input2state_out_of_bounds not_le_imp_less option.distinct(1))

lemma input2state_empty: "input2state [] $ x1 = None"
  by (simp add: input2state_out_of_bounds)

lemma input2state_nth: "i < length ia \<Longrightarrow> input2state ia $ i = Some (ia ! i)"
proof(induct ia rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc a ia)
  then show ?case
    apply (simp add: input2state_def enumerate_eq_zip)
    by (simp add: finfun_upd_apply nth_append)
qed

lemma input2state_some: "i < length ia \<Longrightarrow> ia ! i = x \<Longrightarrow> input2state ia $ i = Some x"
  by (simp add: input2state_nth)

lemma input2state_take:
  "x1 < A \<Longrightarrow>
   A \<le> length i \<Longrightarrow>
   x = vname_o.I x1 \<Longrightarrow>
   input2state i $ x1 = input2state (take A i) $ x1"
proof(induct i)
  case Nil
  then show ?case
    by simp
next
  case (Cons a i)
  then show ?case
    by (simp add: input2state_nth)
qed

lemma input2state_not_None: "(input2state i $ x \<noteq> None) \<Longrightarrow> (x < length i)"
  using input2state_within_bounds by blast

lemma input2state_Some: "(\<exists>v. input2state i $ x = Some v) = (x < length i)"
  apply standard
  using input2state_within_bounds apply blast
  by (simp add: input2state_nth)

lemma input2state_cons:
  "x1 > 0 \<Longrightarrow>
   x1 < length ia \<Longrightarrow>
   input2state (a # ia) $ x1 = input2state ia $ (x1-1)"
  by (simp add: input2state_nth)

lemma input2state_cons_shift: "input2state i $ x1 = Some a \<Longrightarrow> input2state (b # i) $ (Suc x1) = Some a"
proof(induct i rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: input2state_def)
next
  case (snoc x xs)
  then show ?case
    using input2state_within_bounds[of xs x1 a]
    using input2state_cons[of "Suc x1" "xs @ [x]" b]
    apply simp
    apply (case_tac "x1 < length xs")
     apply simp
    by (metis finfun_upd_apply input2state_append input2state_nth length_Cons length_append_singleton lessI list.sel(3) nth_tl)
qed

lemma input2state_exists: "\<exists>i. input2state i $ x1 = Some a"
proof(induct x1)
  case 0
  then show ?case
    apply (rule_tac x="[a]" in exI)
    by (simp add: input2state_def)
next
  case (Suc x1)
  then show ?case
    apply clarify
    apply (rule_tac x="a#i" in exI)
    by (simp add: input2state_cons_shift)
qed

primrec repeat :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "repeat 0 _ = []" |
  "repeat (Suc m) a = a#(repeat m a)"

lemma length_repeat: "length (repeat n a) = n"
proof(induct n)
  case 0
  then show ?case
    by simp
next
  case (Suc a)
  then show ?case
    by simp
qed

lemma length_append_repeat: "length (i@(repeat a y)) \<ge> length i"
  by simp

lemma length_input2state_repeat: "input2state i $ x = Some a \<Longrightarrow> y < length (i @ repeat y a)"
  by (metis append.simps(1) append_eq_append_conv input2state_within_bounds length_append length_repeat list.size(3) neqE not_add_less2 zero_order(3))

lemma input2state_double_exists: "\<exists>i. input2state i $ x = Some a \<and> input2state i $ y = Some a"
  apply (insert input2state_exists[of x a])
  apply clarify
  apply (case_tac "x \<ge> y")
  apply (rule_tac x="list_update i y a" in exI)
  apply (metis (no_types, lifting) input2state_within_bounds input2state_nth input2state_out_of_bounds le_trans length_list_update not_le_imp_less nth_list_update_eq nth_list_update_neq)
  apply (rule_tac x="list_update (i@(repeat y a)) y a" in exI)
  apply (simp add: not_le)
  by (metis length_input2state_repeat input2state_nth input2state_out_of_bounds le_trans length_append_repeat length_list_update not_le_imp_less nth_append nth_list_update_eq nth_list_update_neq option.distinct(1))

lemma input2state_double_exists_2: "x \<noteq> y \<Longrightarrow> \<exists>i. input2state i $ x = Some a \<and> input2state i $ y = Some a'"
  apply (insert input2state_exists[of x a])
  apply clarify
  apply (case_tac "x \<ge> y")
  apply (rule_tac x="list_update i y a'" in exI)
  apply (metis (no_types, lifting) input2state_within_bounds input2state_nth input2state_out_of_bounds le_trans length_list_update not_le_imp_less nth_list_update_eq nth_list_update_neq)
  apply (rule_tac x="list_update (i@(repeat y a')) y a'" in exI)
  apply (simp add: not_le)
  apply standard
  apply (metis input2state_nth input2state_within_bounds le_trans length_append_repeat length_list_update linorder_not_le nth_append nth_list_update_neq order_refl)
  by (metis input2state_nth length_append length_input2state_repeat length_list_update length_repeat nth_list_update_eq)

lemma aval_o_plus_aexp_o: "aval_o (a+b) = aval_o (Plus a b)"
  apply(induct a b rule: plus_aexp_o.induct)
  by (simp_all add: value_plus_def)

lemma aval_o_minus_aexp_o: "aval_o (a-b) = aval_o (Minus a b)"
  apply(induct a b rule: minus_aexp_o.induct)
  by (simp_all add: value_minus_def)

fun aexp_o_constrains :: "aexp_o \<Rightarrow> aexp_o \<Rightarrow> bool" where
  "aexp_o_constrains (L l) a = (L l = a)" |
  "aexp_o_constrains (V v) v' = (V v = v')" |
  "aexp_o_constrains (Plus a1 a2) v = ((Plus a1 a2) = v \<or> (Plus a1 a2) = v \<or> (aexp_o_constrains a1 v \<or> aexp_o_constrains a2 v))" |
  "aexp_o_constrains (Minus a1 a2) v = ((Minus a1 a2) = v \<or> (aexp_o_constrains a1 v \<or> aexp_o_constrains a2 v))" |
  "aexp_o_constrains (Times a1 a2) v = ((Times a1 a2) = v \<or> (aexp_o_constrains a1 v \<or> aexp_o_constrains a2 v))"

fun aexp_o_same_structure :: "aexp_o \<Rightarrow> aexp_o \<Rightarrow> bool" where
  "aexp_o_same_structure (L v) (L v') = True" |
  "aexp_o_same_structure (V v) (V v') = True" |
  "aexp_o_same_structure (Plus a1 a2) (Plus a1' a2') = (aexp_o_same_structure a1 a1' \<and> aexp_o_same_structure a2 a2')" |
  "aexp_o_same_structure (Minus a1 a2) (Minus a1' a2') = (aexp_o_same_structure a1 a1' \<and> aexp_o_same_structure a2 a2')" |
  "aexp_o_same_structure _ _ = False"

fun enumerate_aexp_o_inputs :: "aexp_o \<Rightarrow> nat set" where
  "enumerate_aexp_o_inputs (L _) = {}" |
  "enumerate_aexp_o_inputs (V (I n)) = {n}" |
  "enumerate_aexp_o_inputs (V (R n)) = {}" |
  "enumerate_aexp_o_inputs (V (O n)) = {}" |
  "enumerate_aexp_o_inputs (Plus v va) = enumerate_aexp_o_inputs v \<union> enumerate_aexp_o_inputs va" |
  "enumerate_aexp_o_inputs (Minus v va) = enumerate_aexp_o_inputs v \<union> enumerate_aexp_o_inputs va" |
  "enumerate_aexp_o_inputs (Times v va) = enumerate_aexp_o_inputs v \<union> enumerate_aexp_o_inputs va"

lemma enumerate_aexp_o_inputs_list: "\<exists>l. enumerate_aexp_o_inputs a = set l"
proof(induct a)
  case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
      apply (metis List.set_insert empty_set enumerate_aexp_o_inputs.simps(2))
    by auto
next
  case (Plus a1 a2)
  then show ?case
    by (metis enumerate_aexp_o_inputs.simps(5) set_append)
next
  case (Minus a1 a2)
  then show ?case
    by (metis enumerate_aexp_o_inputs.simps(6) set_append)
next
  case (Times a1 a2)
  then show ?case
    by (metis enumerate_aexp_o_inputs.simps(7) set_append)
qed

fun enumerate_aexp_o_regs :: "aexp_o \<Rightarrow> nat set" where
  "enumerate_aexp_o_regs (L _) = {}" |
  "enumerate_aexp_o_regs (V (R n)) = {n}" |
  "enumerate_aexp_o_regs (V (I _)) = {}" |
  "enumerate_aexp_o_regs (V (O _)) = {}" |
  "enumerate_aexp_o_regs (Plus v va) = enumerate_aexp_o_regs v \<union> enumerate_aexp_o_regs va" |
  "enumerate_aexp_o_regs (Minus v va) = enumerate_aexp_o_regs v \<union> enumerate_aexp_o_regs va" |
  "enumerate_aexp_o_regs (Times v va) = enumerate_aexp_o_regs v \<union> enumerate_aexp_o_regs va"

lemma enumerate_aexp_o_regs_list: "\<exists>l. enumerate_aexp_o_regs a = set l"
proof(induct a)
  case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
      apply simp
     apply (metis List.set_insert empty_set enumerate_aexp_o_regs.simps(2))
    by simp
next
  case (Plus a1 a2)
  then show ?case
    by (metis enumerate_aexp_o_regs.simps(5) set_append)
next
  case (Minus a1 a2)
  then show ?case
    by (metis enumerate_aexp_o_regs.simps(6) set_append)
next
  case (Times a1 a2)
  then show ?case
    by (metis enumerate_aexp_o_regs.simps(7) set_append)
qed

fun enumerate_aexp_o_outputs :: "aexp_o \<Rightarrow> nat set" where
  "enumerate_aexp_o_outputs (L _) = {}" |
  "enumerate_aexp_o_outputs (V (I n)) = {}" |
  "enumerate_aexp_o_outputs (V (R n)) = {}" |
  "enumerate_aexp_o_outputs (V (O n)) = {n}" |
  "enumerate_aexp_o_outputs (Plus v va) = enumerate_aexp_o_outputs v \<union> enumerate_aexp_o_outputs va" |
  "enumerate_aexp_o_outputs (Minus v va) = enumerate_aexp_o_outputs v \<union> enumerate_aexp_o_outputs va" |
  "enumerate_aexp_o_outputs (Times v va) = enumerate_aexp_o_outputs v \<union> enumerate_aexp_o_outputs va"

lemma enumerate_aexp_o_outputs_list: "\<exists>l. enumerate_aexp_o_outputs a = set l"
proof(induct a)
  case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
      apply simp+
    by (metis List.set_insert empty_set)
next
  case (Plus a1 a2)
  then show ?case
    by (metis enumerate_aexp_o_outputs.simps(5) set_append)
next
  case (Minus a1 a2)
  then show ?case
    by (metis enumerate_aexp_o_outputs.simps(6) set_append)
next
  case (Times a1 a2)
  then show ?case
    by (metis enumerate_aexp_o_outputs.simps(7) set_append)
qed

lemma no_variables_aval_o:
  "enumerate_aexp_o_inputs a = {} \<Longrightarrow>
   enumerate_aexp_o_regs a = {} \<Longrightarrow>
   enumerate_aexp_o_outputs a = {} \<Longrightarrow>
   aval_o a i r o = aval_o a i' r' o'"
  by (induct a rule: aexp_o_induct_separate_V_cases, auto)

lemma enumerate_aexp_o_inputs_not_empty: "(enumerate_aexp_o_inputs a \<noteq> {}) = (\<exists>b c. enumerate_aexp_o_inputs a = set (b#c))"
  using enumerate_aexp_o_inputs_list by fastforce

lemma set_union_append: "set l \<union> set la = set (l@la)"
  by simp

definition max_input :: "aexp_o \<Rightarrow> nat option" where
  "max_input g = (let inputs = (enumerate_aexp_o_inputs g) in if inputs = {} then None else Some (Max inputs))"

definition max_reg :: "aexp_o \<Rightarrow> nat option" where
  "max_reg g = (let regs = (enumerate_aexp_o_regs g) in if regs = {} then None else Some (Max regs))"

lemma max_reg_V_I: "max_reg (V (I n)) = None"
  by (simp add: max_reg_def)

lemma max_reg_V_R: "max_reg (V (R n)) = Some n"
  by (simp add: max_reg_def)

lemmas max_reg_V = max_reg_V_I max_reg_V_R

lemma max_reg_Plus: "max_reg (Plus a1 a2) = max (max_reg a1) (max_reg a2)"
  apply (simp add: max_reg_def Let_def max_absorb2)
  by (metis List.finite_set Max.union enumerate_aexp_o_regs_list sup_None_2 sup_Some sup_max)

lemma max_reg_Minus: "max_reg (Minus a1 a2) = max (max_reg a1) (max_reg a2)"
  apply (simp add: max_reg_def Let_def max_absorb2)
  by (metis List.finite_set Max.union enumerate_aexp_o_regs_list sup_None_2 sup_Some sup_max)

lemma max_reg_Times: "max_reg (Times a1 a2) = max (max_reg a1) (max_reg a2)"
  apply (simp add: max_reg_def Let_def max_absorb2)
  by (metis List.finite_set Max.union enumerate_aexp_o_regs_list sup_None_2 sup_Some sup_max)

lemma enumerate_aexp_o_regs_empty_reg_unconstrained:
  "enumerate_aexp_o_regs a = {} \<Longrightarrow> \<forall>r. \<not> aexp_o_constrains a (V (R r))"
  by (induct a rule: aexp_o_induct_separate_V_cases, auto)

lemma enumerate_aexp_o_inputs_empty_input_unconstrained:
  "enumerate_aexp_o_inputs a = {} \<Longrightarrow> \<forall>r. \<not> aexp_o_constrains a (V (I r))"
  by (induct a rule: aexp_o_induct_separate_V_cases, auto)

lemma unconstrained_variable_swap_aval_o: 
  "\<forall>i. \<not> aexp_o_constrains a (V (I i)) \<Longrightarrow>
   \<forall>r. \<not> aexp_o_constrains a (V (R r)) \<Longrightarrow>
   aval_o a i r o = aval_o a i' r' o"
  by (induct a rule: aexp_o_induct_separate_V_cases, auto)

lemma max_input_I: "max_input (V (vname_o.I i)) = Some i"
  by (simp add: max_input_def)

lemma max_input_Plus: "max_input (Plus a1 a2) = max (max_input a1) (max_input a2)"
  apply (simp add: max_input_def Let_def max.commute max_absorb2)
  by (metis List.finite_set Max.union enumerate_aexp_o_inputs_list sup_Some sup_max)

lemma max_input_Minus: "max_input (Minus a1 a2) = max (max_input a1) (max_input a2)"
  apply (simp add: max_input_def Let_def max.commute max_absorb2)
  by (metis List.finite_set Max.union enumerate_aexp_o_inputs_list sup_Some sup_max)

lemma max_input_Times: "max_input (Times a1 a2) = max (max_input a1) (max_input a2)"
  apply (simp add: max_input_def Let_def max.commute max_absorb2)
  by (metis List.finite_set Max.union enumerate_aexp_o_inputs_list sup_Some sup_max)

fun enumerate_aexp_o_strings :: "aexp_o \<Rightarrow> String.literal set" where
  "enumerate_aexp_o_strings (L (Str s)) = {s}" |
  "enumerate_aexp_o_strings (L (Num s)) = {}" |
  "enumerate_aexp_o_strings (V _) = {}" |
  "enumerate_aexp_o_strings (Plus a1 a2) = enumerate_aexp_o_strings a1 \<union> enumerate_aexp_o_strings a2" |
  "enumerate_aexp_o_strings (Minus a1 a2) = enumerate_aexp_o_strings a1 \<union> enumerate_aexp_o_strings a2" |
  "enumerate_aexp_o_strings (Times a1 a2) = enumerate_aexp_o_strings a1 \<union> enumerate_aexp_o_strings a2"

fun enumerate_aexp_o_ints :: "aexp_o \<Rightarrow> int set" where
  "enumerate_aexp_o_ints (L (Str s)) = {}" |
  "enumerate_aexp_o_ints (L (Num s)) = {s}" |
  "enumerate_aexp_o_ints (V _) = {}" |
  "enumerate_aexp_o_ints (Plus a1 a2) = enumerate_aexp_o_ints a1 \<union> enumerate_aexp_o_ints a2" |
  "enumerate_aexp_o_ints (Minus a1 a2) = enumerate_aexp_o_ints a1 \<union> enumerate_aexp_o_ints a2" |
  "enumerate_aexp_o_ints (Times a1 a2) = enumerate_aexp_o_ints a1 \<union> enumerate_aexp_o_ints a2"

definition enumerate_vars_o :: "aexp_o \<Rightarrow> vname_o set" where
  "enumerate_vars_o a = (image I (enumerate_aexp_o_inputs a)) \<union> (image R (enumerate_aexp_o_regs a)) \<union> (image O (enumerate_aexp_o_inputs a))"

lemma enumerate_aexp_o_inputs_aexp_o_constrains: "(\<forall>r. \<not> aexp_o_constrains a (V (I r))) = (enumerate_aexp_o_inputs a = {})"
proof (induct a)
  case (L x)
  then show ?case by simp
next
  case (V x)
  then show ?case by (cases x, auto)
next
  case (Plus a1 a2)
  then show ?case by auto
next
  case (Minus a1 a2)
  then show ?case by auto
next
  case (Times a1 a2)
  then show ?case by auto
qed

lemma enumerate_aexp_o_regs_aexp_o_constrains: "(\<forall>r. \<not> aexp_o_constrains a (V (R r))) = (enumerate_aexp_o_regs a = {})"
proof (induct a)
  case (L x)
  then show ?case by simp
next
  case (V x)
  then show ?case by (cases x, auto)
next
  case (Plus a1 a2)
  then show ?case by auto
next
  case (Minus a1 a2)
  then show ?case by auto
next
  case (Times a1 a2)
  then show ?case by auto
qed

lemma enumerate_aexp_o_outputs_aexp_o_constrains: "(\<forall>r. \<not> aexp_o_constrains a (V (O r))) = (enumerate_aexp_o_outputs a = {})"
proof (induct a)
  case (L x)
  then show ?case by simp
next
  case (V x)
  then show ?case by (cases x, auto)
next
  case (Plus a1 a2)
  then show ?case by auto
next
  case (Minus a1 a2)
  then show ?case by auto
next
  case (Times a1 a2)
  then show ?case by auto
qed

lemma aval_o_take:
  "max_input A < Some a \<Longrightarrow>
   a \<le> length i \<Longrightarrow>
   max_input A \<le> Some (length i) \<Longrightarrow>
   aval_o A i r o = aval_o A (take a i) r o"
proof (induct A)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
      apply (simp add: max_input_I)
    by auto
next
  case (Plus A1 A2)
  then show ?case
    by (simp add: max_input_Plus)
next
  case (Minus A1 A2)
  then show ?case
    by (simp add: max_input_Minus)
next
  case (Times A1 A2)
  then show ?case
    by (simp add: max_input_Times)
qed

lemma max_reg_None_aval_o_swap: "max_reg A = None \<Longrightarrow>
       aval_o A i r o = aval_o A i r' o"
  apply (induct A)
      apply simp
     apply (metis aexp_o_constrains.simps(2) aval_o.simps(2) max_reg_V_R option.simps(3) unconstrained_variable_swap_aval_o)
    apply (metis (no_types) aval_o.simps(5) max.left_commute max_def_raw max_reg_Plus sup_None_2 sup_max)
   apply (metis (no_types) aval_o.simps(6) max.left_commute max_def_raw max_reg_Minus sup_None_2 sup_max)
  by (metis (no_types) aval_o.simps(7) max.left_commute max_def_raw max_reg_Times sup_None_2 sup_max)

typedef aexp = "{a :: aexp_o. \<forall>n. \<not> aexp_o_constrains a (V (O n))}"  morphisms aexp Abs_aexp
proof -
  obtain nns :: "aexp_o \<Rightarrow> nat list" where
    "\<forall>a. enumerate_aexp_o_outputs a = set (nns a)"
    by (meson enumerate_aexp_o_outputs_list)
  then show ?thesis
    using enumerate_aexp_o_outputs.simps(2) enumerate_aexp_o_outputs_aexp_o_constrains by force
qed

setup_lifting type_definition_aexp
lift_definition aval :: "aexp \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> value option" is "\<lambda>a i r. aval_o a i r []".
lift_definition enumerate_aexp_inputs :: "aexp \<Rightarrow> nat set" is "enumerate_aexp_o_inputs".
lift_definition enumerate_aexp_regs :: "aexp \<Rightarrow> nat set" is "enumerate_aexp_o_regs".
lift_definition enumerate_aexp_strings :: "aexp \<Rightarrow> String.literal set" is "enumerate_aexp_o_strings".
lift_definition enumerate_aexp_ints :: "aexp \<Rightarrow> int set" is "enumerate_aexp_o_ints".
lift_definition enumerate_vars :: "aexp \<Rightarrow> vname_o set" is "enumerate_vars_o".
lift_definition aexp_constrains :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" is aexp_o_constrains.

lemma enumerate_aexp_regs_list: "\<exists>l. enumerate_aexp_regs a = set l"
  by (simp add: enumerate_aexp_o_regs_list enumerate_aexp_regs.rep_eq)

end
