subsection \<open>Guard Expressions\<close>
text\<open>
This theory defines the guard language of EFSMs which can be translated directly to and from
contexts. This is similar to boolean expressions from IMP \cite{fixme}. Boolean values true and
false respectively represent the guards which are always and never satisfied. Guards may test
for (in)equivalence of two arithmetic expressions or be connected using nor logic into compound
expressions. Additionally, a guard may also test to see if a particular variable is null. This is
useful if an EFSM transition is intended only to initialise a register.  We also define syntax hacks
for the relations less than, less than or equal to, greater than or equal to, and not equal to as
well as the expression of logical conjunction, disjunction, and negation in terms of nor logic.
\<close>

theory GExp
imports AExp Trilean
begin

definition I :: "nat \<Rightarrow> vname_o" where
  "I n = vname_o.I (n-1)"
declare I_def [simp]
hide_const I

text_raw\<open>\snip{gexp_otype}{1}{2}{%\<close>
datatype gexp_o = Bc bool | Eq aexp_o aexp_o | Gt aexp_o aexp_o | In vname_o "value list" |  Nor gexp_o gexp_o
text_raw\<open>}%endsnip\<close>

fun gval_o :: "gexp_o \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> trilean" where
  "gval_o (Bc True) _ _ _ = true" |
  "gval_o (Bc False) _ _ _ = false" |
  "gval_o (Gt a\<^sub>1 a\<^sub>2) i r o = value_gt (aval_o a\<^sub>1 i r o) (aval_o a\<^sub>2 i r o)" |
  "gval_o (Eq a\<^sub>1 a\<^sub>2) i r o = value_eq (aval_o a\<^sub>1 i r o) (aval_o a\<^sub>2 i r o)" |
  "gval_o (In (I x) l) i r o = (if i ! x \<in> set l then true else false)" |
  "gval_o (In (R x) l) i r o = (if r $ x \<in> set (map Some l) then true else false)" |
  "gval_o (In (O x) l) i r o = (if o ! x \<in> set (map Some l) then true else false)" |
  "gval_o (Nor a\<^sub>1 a\<^sub>2) i r o = \<not>\<^sub>? ((gval_o a\<^sub>1 i r o) \<or>\<^sub>? (gval_o a\<^sub>2 i r o))"

definition gNot :: "gexp_o \<Rightarrow> gexp_o"  where
  "gNot g \<equiv> Nor g g"

definition gOr :: "gexp_o \<Rightarrow> gexp_o \<Rightarrow> gexp_o" (*infix "\<or>" 60*) where
  "gOr v va \<equiv> Nor (Nor v va) (Nor v va)"

definition gAnd :: "gexp_o \<Rightarrow> gexp_o \<Rightarrow> gexp_o" (*infix "\<and>" 60*) where
  "gAnd v va \<equiv> Nor (Nor v v) (Nor va va)"

definition gImplies :: "gexp_o \<Rightarrow> gexp_o \<Rightarrow> gexp_o" where
  "gImplies p q \<equiv> gOr (gNot p) q"

definition Lt :: "aexp_o \<Rightarrow> aexp_o \<Rightarrow> gexp_o" (*infix "<" 60*) where
  "Lt a b \<equiv> Gt b a"

definition Le :: "aexp_o \<Rightarrow> aexp_o \<Rightarrow> gexp_o" (*infix "\<le>" 60*) where
  "Le v va \<equiv> gNot (Gt v va)"

definition Ge :: "aexp_o \<Rightarrow> aexp_o \<Rightarrow> gexp_o" (*infix "\<ge>" 60*) where
  "Ge v va \<equiv> gNot (Lt v va)"

definition Ne :: "aexp_o \<Rightarrow> aexp_o \<Rightarrow> gexp_o" (*infix "\<noteq>" 60*) where
  "Ne v va \<equiv> gNot (Eq v va)"

lemmas connectives = gAnd_def gOr_def gNot_def Lt_def Le_def Ge_def Ne_def

lemma gval_o_gOr: "gval_o (gOr x y) i r o = (gval_o x i r o) \<or>\<^sub>? (gval_o y i r o)"
  by (simp add: maybe_double_negation maybe_or_idempotent gOr_def)

lemma gval_o_gNot: "gval_o (gNot x) i r o = \<not>\<^sub>? (gval_o x i r o)"
  by (simp add: maybe_or_idempotent gNot_def)

lemma gval_o_gAnd: "gval_o (gAnd g1 g2) i r o = (gval_o g1 i r o) \<and>\<^sub>? (gval_o g2 i r o)"
  by (simp add: de_morgans_1 maybe_double_negation maybe_or_idempotent gAnd_def)

lemma gAnd_commute: "gval_o (gAnd a b) i r o = gval_o (gAnd b a) i r o"
  using gval_o_gAnd times_trilean_commutative by auto

lemma gOr_commute: "gval_o (gOr a b) i r o = gval_o (gOr b a) i r o"
  by (simp add: plus_trilean_commutative gOr_def)

lemma gval_o_gAnd_True: "(gval_o (gAnd g1 g2) i r o = true) = ((gval_o g1 i r o = true) \<and> gval_o g2 i r o = true)"
  using gval_o_gAnd maybe_and_not_true by fastforce

lemma nor_equiv: "gval_o (gNot (gOr a b)) i r o = gval_o (Nor a b) i r o"
  by (simp add: gval_o_gNot gval_o_gOr)

definition satisfiable :: "gexp_o \<Rightarrow> bool" where
  "satisfiable g \<equiv> (\<exists>i r o. gval_o g i r o = true)"

definition "satisfiable_list l = satisfiable (fold gAnd l (Bc True))"

lemma unsatisfiable_false: "\<not> satisfiable (Bc False)"
  by (simp add: satisfiable_def)

lemma satisfiable_true: "satisfiable (Bc True)"
  by (simp add: satisfiable_def)

definition valid :: "gexp_o \<Rightarrow> bool" where
  "valid g \<equiv> (\<forall>i r o. gval_o g i r o = true)"

lemma valid_true: "valid (Bc True)"
  by (simp add: valid_def)

definition gexp_o_implies :: "gexp_o \<Rightarrow> gexp_o \<Rightarrow> bool" where
  "gexp_o_implies g1 g2 = (\<forall>i r o. gval_o g1 i r o = true \<longrightarrow> gval_o g2 i r o = true)"

fun gexp_o_constrains :: "gexp_o \<Rightarrow> aexp_o \<Rightarrow> bool" where
  "gexp_o_constrains (Bc _) _ = False" |
  "gexp_o_constrains (Eq a1 a2) a = (aexp_o_constrains a1 a \<or> aexp_o_constrains a2 a)" |
  "gexp_o_constrains (Gt a1 a2) a = (aexp_o_constrains a1 a \<or> aexp_o_constrains a2 a)" |
  "gexp_o_constrains (Nor g1 g2) a = (gexp_o_constrains g1 a \<or> gexp_o_constrains g2 a)" |
  "gexp_o_constrains (In v l) a = aexp_o_constrains (aexp_o.V v) a"

fun contains_bool :: "gexp_o \<Rightarrow> bool" where
  "contains_bool (Bc _) = True" |
  "contains_bool (Nor g1 g2) = (contains_bool g1 \<or> contains_bool g2)" |
  "contains_bool _ = False"

fun gexp_o_same_structure :: "gexp_o \<Rightarrow> gexp_o \<Rightarrow> bool" where
  "gexp_o_same_structure (Bc b) (Bc b') = (b = b')" |
  "gexp_o_same_structure (Eq a1 a2) (Eq a1' a2') = (aexp_o_same_structure a1 a1' \<and> aexp_o_same_structure a2 a2')" |
  "gexp_o_same_structure (Gt a1 a2) (Gt a1' a2') = (aexp_o_same_structure a1 a1' \<and> aexp_o_same_structure a2 a2')" |
  "gexp_o_same_structure (Nor g1 g2) (Nor g1' g2') = (gexp_o_same_structure g1 g1' \<and> gexp_o_same_structure g2 g2')" |
  "gexp_o_same_structure (In v l) (In v' l') = (v = v' \<and> l = l')" |
  "gexp_o_same_structure _ _ = False"

lemma gval_o_foldr_true: "(gval_o (foldr gAnd G (Bc True)) i r o = true) = (\<forall>g \<in> set G. gval_o g i r o = true)"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def gval_o_gAnd maybe_and_true)
    by simp
qed

fun enumerate_gexp_o_inputs :: "gexp_o \<Rightarrow> nat set" where
  "enumerate_gexp_o_inputs (Bc _) = {}" |
  "enumerate_gexp_o_inputs (Eq v va) = enumerate_aexp_o_inputs v \<union> enumerate_aexp_o_inputs va" |
  "enumerate_gexp_o_inputs (Gt v va) = enumerate_aexp_o_inputs v \<union> enumerate_aexp_o_inputs va" |
  "enumerate_gexp_o_inputs (In v va) = enumerate_aexp_o_inputs (aexp_o.V v)" |
  "enumerate_gexp_o_inputs (Nor v va) = enumerate_gexp_o_inputs v \<union> enumerate_gexp_o_inputs va"

lemma enumerate_gexp_o_inputs_list: "\<exists>l. enumerate_gexp_o_inputs g = set l"
proof(induct g)
  case (Bc x)
  then show ?case
    by simp
next
  case (Eq x1a x2)
  then show ?case
    by (metis enumerate_aexp_o_inputs_list enumerate_gexp_o_inputs.simps(2) set_append)
next
  case (Gt x1a x2)
  then show ?case
    by (metis enumerate_aexp_o_inputs_list enumerate_gexp_o_inputs.simps(3) set_append)
next
  case (In x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_o_inputs_list)
next
  case (Nor g1 g2)
  then show ?case
    by (metis enumerate_gexp_o_inputs.simps(5) set_append)
qed

definition max_input :: "gexp_o \<Rightarrow> nat option" where
  "max_input g = (let inputs = (enumerate_gexp_o_inputs g) in if inputs = {} then None else Some (Max inputs))"

definition max_input_list :: "gexp_o list \<Rightarrow> nat option" where
  "max_input_list g = fold max (map (\<lambda>g. max_input g) g) None"

lemma max_input_list_cons: "max_input_list (a # G) = max (max_input a) (max_input_list G)"
  apply (simp add: max_input_list_def)
  apply (cases "max_input a")
   apply (simp add: max_def_raw)
  by (metis (no_types, lifting) List.finite_set Max.insert Max.set_eq_fold fold_simps(1) list.set(2) max.assoc set_empty)

fun enumerate_gexp_o_regs :: "gexp_o \<Rightarrow> nat set" where
  "enumerate_gexp_o_regs (Bc _) = {}" |
  "enumerate_gexp_o_regs (Eq v va) = enumerate_aexp_o_regs v \<union> enumerate_aexp_o_regs va" |
  "enumerate_gexp_o_regs (Gt v va) = enumerate_aexp_o_regs v \<union> enumerate_aexp_o_regs va" |
  "enumerate_gexp_o_regs (In v va) = enumerate_aexp_o_regs (aexp_o.V v)" |
  "enumerate_gexp_o_regs (Nor v va) = enumerate_gexp_o_regs v \<union> enumerate_gexp_o_regs va"

lemma enumerate_gexp_o_regs_list: "\<exists>l. enumerate_gexp_o_regs g = set l"
proof(induct g)
case (Bc x)
  then show ?case
  by simp
next
  case (Eq x1a x2)
  then show ?case
    by (metis enumerate_aexp_o_regs_list enumerate_gexp_o_regs.simps(2) set_append)
next
  case (Gt x1a x2)
  then show ?case
    by (metis enumerate_aexp_o_regs_list enumerate_gexp_o_regs.simps(3) set_append)
next
  case (In x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_o_regs_list)
next
  case (Nor g1 g2)
  then show ?case
    by (metis enumerate_gexp_o_regs.simps(5) set_append)
qed

fun enumerate_gexp_o_outputs :: "gexp_o \<Rightarrow> nat set" where
  "enumerate_gexp_o_outputs (Bc _) = {}" |
  "enumerate_gexp_o_outputs (Eq v va) = enumerate_aexp_o_outputs v \<union> enumerate_aexp_o_outputs va" |
  "enumerate_gexp_o_outputs (Gt v va) = enumerate_aexp_o_outputs v \<union> enumerate_aexp_o_outputs va" |
  "enumerate_gexp_o_outputs (In v va) = enumerate_aexp_o_outputs (aexp_o.V v)" |
  "enumerate_gexp_o_outputs (Nor v va) = enumerate_gexp_o_outputs v \<union> enumerate_gexp_o_outputs va"

lemma enumerate_gexp_o_outputs_list: "\<exists>l. enumerate_gexp_o_outputs g = set l"
proof(induct g)
case (Bc x)
  then show ?case
  by simp
next
  case (Eq x1a x2)
  then show ?case
    by (metis enumerate_aexp_o_outputs_list enumerate_gexp_o_outputs.simps(2) set_union_append)
next
  case (Gt x1a x2)
  then show ?case
    by (metis enumerate_aexp_o_outputs_list enumerate_gexp_o_outputs.simps(3) set_union)
next
  case (In x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_o_outputs_list)
next
  case (Nor g1 g2)
  then show ?case
    by (metis enumerate_gexp_o_outputs.simps(5) set_append)
qed

lemma no_variables_list_gval_o:
  "enumerate_gexp_o_inputs g = {} \<Longrightarrow>
   enumerate_gexp_o_regs g = {} \<Longrightarrow>
   enumerate_gexp_o_outputs g = {} \<Longrightarrow>
   gval_o g i r o = gval_o g i' r' o'"
  apply (induct g)
      apply (metis (full_types) gval_o.simps(1) gval_o.simps(2))
     apply (metis Un_empty enumerate_gexp_o_inputs.simps(2) enumerate_gexp_o_outputs.simps(2) enumerate_gexp_o_regs.simps(2) gval_o.simps(4) no_variables_aval_o)
    apply (metis Un_empty enumerate_gexp_o_inputs.simps(3) enumerate_gexp_o_outputs.simps(3) enumerate_gexp_o_regs.simps(3) gval_o.simps(3) no_variables_aval_o)
   apply (case_tac x1a)
  by auto

lemma no_variables_list_valid_or_unsat:
  "enumerate_gexp_o_inputs g = {} \<Longrightarrow>
   enumerate_gexp_o_regs g = {} \<Longrightarrow>
   enumerate_gexp_o_outputs g = {} \<Longrightarrow>
   valid g \<or> \<not> satisfiable g"
  apply (induct g)
      apply (metis (full_types) unsatisfiable_false valid_true)
     apply (metis no_variables_list_gval_o satisfiable_def valid_def)
    apply (metis no_variables_list_gval_o satisfiable_def valid_def)
   apply (metis no_variables_list_gval_o satisfiable_def valid_def)
  by (metis no_variables_list_gval_o satisfiable_def valid_def)

definition max_reg :: "gexp_o \<Rightarrow> nat option" where
  "max_reg g = (let regs = (enumerate_gexp_o_regs g) in if regs = {} then None else Some (Max regs))"

lemma max_reg_gNot: "max_reg (gNot x) = max_reg x"
  by (simp add: max_reg_def gNot_def)

lemma max_reg_Eq: "max_reg (Eq a b) = max (AExp.max_reg a) (AExp.max_reg b)"
  apply (simp add: max_reg_def AExp.max_reg_def Let_def max_absorb2)
  by (metis List.finite_set Max.union enumerate_aexp_o_regs_list less_eq_option_Some_None max_def sup_Some sup_max)

lemma max_reg_Gt: "max_reg (Gt a b) = max (AExp.max_reg a) (AExp.max_reg b)"
  apply (simp add: max_reg_def AExp.max_reg_def Let_def max_absorb2)
  by (metis List.finite_set Max.union enumerate_aexp_o_regs_list less_eq_option_Some_None max_def sup_Some sup_max)

lemma max_reg_Nor: "max_reg (Nor a b) = max (max_reg a) (max_reg b)"
  apply (simp add: max_reg_def AExp.max_reg_def Let_def max_absorb2)
  by (metis List.finite_set Max.union enumerate_gexp_o_regs_list less_eq_option_Some_None max_def sup_Some sup_max)

lemma enumerate_gexp_o_regs_empty_reg_unconstrained: "enumerate_gexp_o_regs g = {} \<Longrightarrow> \<forall>r. \<not> gexp_o_constrains g (aexp_o.V (R r))"
proof(induct g)
case (Bc x)
  then show ?case
    by simp
next
  case (Eq x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_o_regs_empty_reg_unconstrained)
next
  case (Gt x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_o_regs_empty_reg_unconstrained)
next
  case (In v l)
  then show ?case
    by auto
next
  case (Nor g1 g2)
  then show ?case
    by simp
qed

lemma gexp_o_constrains_inputs: "(\<forall>r. \<not> gexp_o_constrains g (aexp_o.V (I r))) = (enumerate_gexp_o_inputs g = {})"
  apply (induct g)
  using enumerate_aexp_o_inputs_aexp_o_constrains by fastforce+

lemma gexp_o_constrains_outputs: "(\<forall>r. \<not> gexp_o_constrains g (aexp_o.V (O r))) = (enumerate_gexp_o_outputs g = {})"
  apply (induct g)
  using enumerate_aexp_o_outputs_aexp_o_constrains by fastforce+

lemma gexp_o_constrains_regs: "(\<forall>r. \<not> gexp_o_constrains g (aexp_o.V (R r))) = (enumerate_gexp_o_regs g = {})"
  apply (induct g)
  using enumerate_aexp_o_regs_aexp_o_constrains by fastforce+

lemma unconstrained_variable_swap_gval_o:
   "\<forall>r. \<not> gexp_o_constrains g (aexp_o.V (I r)) \<Longrightarrow>
    \<forall>r. \<not> gexp_o_constrains g (aexp_o.V (R r)) \<Longrightarrow>
    \<forall>r. \<not> gexp_o_constrains g (aexp_o.V (O r)) \<Longrightarrow>
    gval_o g i r o = gval_o g i' r' o'"
  by (simp only: gexp_o_constrains_inputs gexp_o_constrains_outputs gexp_o_constrains_regs no_variables_list_gval_o)

lemma gval_o_In_cons: "gval_o (In v (a # as)) i r o = (gval_o (Eq (aexp_o.V v) (L a)) i r o \<or>\<^sub>? gval_o (In v as) i r o)"
  by (cases v, auto)

lemma possible_to_be_in: "s \<noteq> [] \<Longrightarrow> satisfiable (In v s)"
  apply (simp add: satisfiable_def neq_Nil_conv)
  apply clarify
  apply (simp add: gval_o_In_cons)
  apply (cases v)
    apply (simp, metis Ex_list_of_length less_Suc_eq nth_list_update_eq)
   apply (simp, meson finfun_upd_apply)
  by (simp, metis Ex_list_of_length less_Suc_eq nth_list_update_eq)

definition max_reg_list :: "gexp_o list \<Rightarrow> nat option" where
  "max_reg_list g = (fold max (map (\<lambda>g. max_reg g) g) None)"

lemma max_reg_list_cons: "max_reg_list (a # G) = max (max_reg a) (max_reg_list G)"
  apply (simp add: max_reg_list_def)
  by (metis (no_types, lifting) List.finite_set Max.insert Max.set_eq_fold fold.simps(1) id_apply list.simps(15) max.assoc set_empty)

lemma max_reg_list_append_singleton: "max_reg_list (as@[bs]) = max (max_reg_list as) (max_reg_list [bs])"
  apply (simp add: max_reg_list_def)
  by (metis max.commute sup_None_2 sup_max)

lemma max_reg_list_append: "max_reg_list (as@bs) = max (max_reg_list as) (max_reg_list bs)"
proof(induct bs rule: rev_induct)
  case Nil
  then show ?case
    by (metis append_Nil2 fold_simps(1) list.simps(8) max_reg_list_def sup_None_2 sup_max)
next
  case (snoc x xs)
  then show ?case
    by (metis append_assoc max.assoc max_reg_list_append_singleton)
qed

definition apply_guards_o :: "gexp_o list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> bool" where
  "apply_guards_o G i r o = (\<forall>g \<in> set (map (\<lambda>g. gval_o g i r o) G). g = true)"

lemma apply_guards_o_singleton: "(apply_guards_o [g] i r o) = (gval_o g i r o = true)"
  by (simp add: apply_guards_o_def)

lemma apply_guards_o_empty [simp]: "apply_guards_o [] i r o"
  by (simp add: apply_guards_o_def)

lemma apply_guards_o_cons: "apply_guards_o (a # G) i r o = (gval_o a i r o = true \<and> apply_guards_o G i r o)"
  by (simp add: apply_guards_o_def)

lemma apply_guards_o_double_cons: "apply_guards_o (y # x # G) i r o = (gval_o (gAnd y x) i r o = true \<and> apply_guards_o G i r o)"
  using apply_guards_o_cons gval_o_gAnd_True by auto

lemma apply_guards_o_append: "apply_guards_o (a@a') i r o = (apply_guards_o a i r o \<and> apply_guards_o a' i r o)"
  using apply_guards_o_def by auto

lemma apply_guards_o_foldr: "apply_guards_o G i r o = (gval_o (foldr gAnd G (Bc True)) i r o = true)"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_o_def)
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def)
    using apply_guards_o_cons gval_o_gAnd_True by auto
qed

lemma rev_apply_guards_o: "apply_guards_o (rev G) i r o = apply_guards_o G i r o"
  by (simp add: apply_guards_o_def)

lemma apply_guards_o_fold: "apply_guards_o G i r o = (gval_o (fold gAnd G (Bc True)) i r o = true)"
  using rev_apply_guards_o[symmetric]
  by (simp add: foldr_conv_fold apply_guards_o_foldr)

lemma fold_apply_guards_o: "(gval_o (fold gAnd G (Bc True)) i r o = true) = apply_guards_o G i r o"
  by (simp add: apply_guards_o_fold)

lemma foldr_apply_guards_o: "(gval_o (foldr gAnd G (Bc True)) i r o = true) = apply_guards_o G i r o"
  by (simp add: apply_guards_o_foldr)

lemma apply_guards_o_subset: "set g' \<subseteq> set g \<Longrightarrow> apply_guards_o g i r o \<longrightarrow> apply_guards_o g' i r o"
proof(induct g)
  case Nil
  then show ?case
    by simp
next
  case (Cons a g)
  then show ?case
    using apply_guards_o_def by auto
qed

lemma apply_guards_o_subset_append: "set G \<subseteq> set G' \<Longrightarrow> apply_guards_o (G @ G') i r o = apply_guards_o (G') i r o"
  using apply_guards_o_append apply_guards_o_subset by blast

lemma apply_guards_o_rearrange: "x \<in> set G \<Longrightarrow> apply_guards_o G i r o = apply_guards_o (x#G) i r o"
  using apply_guards_o_def by auto

lemma max_input_Bc: "max_input (Bc x) = None"
  by (simp add: max_input_def)

lemma max_input_Eq: "max_input (Eq a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def max_input_def Let_def max_absorb2)
  by (metis List.finite_set Max.union bot_option_def enumerate_aexp_o_inputs_not_empty max_bot2 sup_Some sup_max)

lemma max_input_Gt: "max_input (Gt a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def max_input_def Let_def max_absorb2)
  by (metis List.finite_set Max.union bot_option_def enumerate_aexp_o_inputs_not_empty max_bot2 sup_Some sup_max)

lemma gexp_o_max_input_Nor: "max_input (Nor g1 g2) = max (max_input g1) (max_input g2)"
  apply (simp add: AExp.max_input_def max_input_def Let_def max_absorb2)
  by (metis List.finite_set Max.union enumerate_gexp_o_inputs_list less_eq_option_Some_None max_def sup_Some sup_max)

lemma max_input_In: "max_input (In v l) = AExp.max_input (aexp_o.V v)"
  by (simp add: AExp.max_input_def GExp.max_input_def)

lemma rev_singleton: "rev [a] = [a]"
  by simp

lemma singleton_append: "[a]@l = a#l"
  by simp

lemma gval_o_foldr_gOr_invalid: "(gval_o (fold gOr l g) i r o = invalid) = (\<exists>g' \<in> (set (g#l)). gval_o g' i r o = invalid)"
proof(induct l rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  then show ?case
    apply (simp only: fold_conv_foldr foldr.simps append.simps rev_append rev_singleton comp_def gval_o_gOr)
    using maybe_or_invalid by auto
qed

lemma gval_o_foldr_gOr_true: "(gval_o (fold gOr l g) i r o = true) = ((\<exists>g' \<in> (set (g#l)). gval_o g' i r o = true) \<and> (\<forall>g' \<in> (set (g#l)). gval_o g' i r o \<noteq> invalid))"
proof(induct l rule: rev_induct)
  case Nil
  then show ?case
    by auto
next
  case (snoc x xs)
  then show ?case
    apply (simp only: fold_conv_foldr foldr.simps append.simps rev_append rev_singleton comp_def gval_o_gOr)
    apply (simp add: maybe_or_true)
    by (metis (no_types, lifting) fold_conv_foldr gval_o_foldr_gOr_invalid list.set_intros(1) list.set_intros(2) set_ConsD)
qed

lemma gval_o_foldr_gOr_false: "(gval_o (fold gOr l g) i r o = false) = (\<forall>g' \<in> (set (g#l)). gval_o g' i r o = false)"
proof(induct l rule: rev_induct)
  case Nil
  then show ?case
    by auto
next
  case (snoc x xs)
  then show ?case
    apply (simp only: fold_conv_foldr foldr.simps append.simps rev_append rev_singleton comp_def gval_o_gOr)
    apply (simp add: maybe_or_false)
    by auto
qed

lemma gval_o_fold_gOr_rev: "gval_o (fold gOr (rev l) g) i r o = gval_o (fold gOr l g) i r o"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    apply (simp del: fold.simps)
    apply (case_tac "gval_o (fold gOr (a # l) g) i r o")
    apply (simp del: gval_o.simps fold.simps)
      apply (simp only: gval_o_foldr_gOr_true)
    using gval_o_foldr_gOr_invalid gval_o_foldr_gOr_true apply auto[1]
    apply (simp del: gval_o.simps fold.simps)
     apply (simp only: gval_o_foldr_gOr_false)
    using gval_o_foldr_gOr_false apply auto[1]
    apply (simp del: gval_o.simps fold.simps)
    apply (simp only: gval_o_foldr_gOr_invalid)
    using gval_o_foldr_gOr_invalid by auto
qed

lemma gval_o_fold_gOr_foldr: "gval_o (fold gOr l g) i r o = gval_o (foldr gOr l g) i r o"
  by (simp add: foldr_conv_fold gval_o_fold_gOr_rev)

lemma gval_o_fold_gOr: "gval_o (fold gOr (a # l) g) i r o = (gval_o a i r o \<or>\<^sub>? gval_o (fold gOr l g) i r o)"
  by (simp only: gval_o_fold_gOr_foldr foldr.simps comp_def gval_o_gOr)

lemma gval_o_In_empty [simp]: "gval_o (In v []) i r o = false"
  by (cases v, auto)

lemma gval_o_In_fold: "gval_o (In v l) i r o = gval_o (fold gOr (map (\<lambda>x. Eq (aexp_o.V v) (L x)) l) (Bc False)) i r o"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    by (simp only: gval_o_In_cons list.map gval_o_fold_gOr)
qed

fun fold_In :: "vname_o \<Rightarrow> value list \<Rightarrow> gexp_o" where
  "fold_In _ [] = Bc False" |
  "fold_In v [l] = Eq (aexp_o.V v) (L l)" |
  "fold_In v (l#t) = fold gOr (map (\<lambda>x. Eq (aexp_o.V v) (L x)) t) (Eq (aexp_o.V v) (L l))"

lemma fold_maybe_or_invalid_base: "fold (\<or>\<^sub>?) l invalid = invalid"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    by (metis fold_simps(2) maybe_or_valid)
qed

lemma fold_maybe_or_true_base_never_false: "fold (\<or>\<^sub>?) l true \<noteq> false"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    by (metis fold_maybe_or_invalid_base fold_simps(2) maybe_not.cases maybe_or_valid plus_trilean.simps(4) plus_trilean.simps(6))
qed

lemma fold_true_fold_false_not_invalid: "fold (\<or>\<^sub>?) l true = true \<Longrightarrow> fold (\<or>\<^sub>?) (rev l) false \<noteq> invalid"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    apply simp
    by (metis fold_maybe_or_invalid_base maybe_or_invalid maybe_or_true)
qed

lemma fold_true_invalid_fold_rev_false_invalid:  "fold (\<or>\<^sub>?) l true = invalid \<Longrightarrow> fold (\<or>\<^sub>?) (rev l) false = invalid"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    apply simp
    by (metis maybe_or_true maybe_or_valid)
qed

lemma fold_maybe_or_rev: "fold (\<or>\<^sub>?) l b = fold (\<or>\<^sub>?) (rev l) b"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
  proof(induction a b rule: plus_trilean.induct)
    case (1 uu)
    then show ?case
      by (simp add: fold_maybe_or_invalid_base)
  next
    case "2_1"
    then show ?case
      by (simp add: fold_maybe_or_invalid_base)
  next
    case "2_2"
    then show ?case
      by (simp add: fold_maybe_or_invalid_base)
  next
    case "3_1"
    then show ?case
      apply simp
      by (metis add.assoc fold_maybe_or_true_base_never_false maybe_not.cases maybe_or_idempotent maybe_or_true)
  next
    case "3_2"
    then show ?case
      apply simp
      apply (case_tac "fold (\<or>\<^sub>?) l true")
        apply (simp add: eq_commute[of true])
        apply (case_tac "fold (\<or>\<^sub>?) (rev l) false")
          apply simp
         apply simp
        apply (simp add: fold_true_fold_false_not_invalid)
       apply (simp add: fold_maybe_or_true_base_never_false)
      by (simp add: fold_true_invalid_fold_rev_false_invalid)
  next
    case 4
    then show ?case
      by (simp add: maybe_or_zero)
  next
    case 5
    then show ?case
      by (simp add: maybe_or_zero)
  qed
qed

lemma fold_maybe_or_cons: "fold (\<or>\<^sub>?) (a#l) b = a \<or>\<^sub>? (fold (\<or>\<^sub>?) l b)"
  apply (simp only: fold_maybe_or_rev[of "(a # l)"])
  apply (simp only: fold_conv_foldr rev_rev_ident foldr.simps comp_def)
  by (simp only: foldr_conv_fold rev_rev_ident fold_maybe_or_rev[symmetric])

lemma gval_o_fold_gOr_map: "gval_o (fold gOr l (Bc False)) i r o = fold (\<or>\<^sub>?) (map (\<lambda>g. gval_o g i r o) l) (false)"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    using fold_maybe_or_cons gval_o_fold_gOr by auto
qed

lemma gval_o_unfold_first: "gval_o (fold gOr (map (\<lambda>x. Eq (aexp_o.V v) (L x)) ls) (Eq (aexp_o.V v) (L l))) i r o =
       gval_o (fold gOr (map (\<lambda>x. Eq (aexp_o.V v) (L x)) (l#ls)) (Bc False)) i r o"
proof(induct ls)
  case Nil
  then show ?case
    by (simp add: gOr_def)
next
  case (Cons a ls)
  then show ?case
    using gval_o_fold_gOr by auto
qed

lemma gval_o_fold_in: "gval_o (In v l) i r o = gval_o (fold_In v l) i r o"
proof(induct l rule: fold_In.induct)
  case (1 uu)
  then show ?case
    by simp
next
  case (2 v l)
  then show ?case
    by (simp add: gval_o_In_cons)
next
  case (3 v l va vb)
  then show ?case
    apply (simp only: gval_o_In_cons fold_In.simps gval_o_unfold_first)
    by (metis (no_types, lifting) gval_o_In_fold gval_o_fold_gOr list.simps(9))
qed

lemma gval_o_fold_gAnd_append_singleton:
  "gval_o (fold gAnd (a @ [G]) (Bc True)) i r o = gval_o (fold gAnd a (Bc True)) i r o \<and>\<^sub>? gval_o G i r o"
  apply (simp add: fold_conv_foldr del: foldr.simps)
  by (simp only: foldr.simps comp_def gval_o_gAnd times_trilean_commutative)

lemma gval_o_fold_rev_true:
  "gval_o (fold gAnd (rev G) (Bc True)) i r o = true \<Longrightarrow>
   gval_o (fold gAnd G (Bc True)) i r o = true"
  by (simp add: fold_conv_foldr gval_o_foldr_true)

lemma gval_o_fold_not_invalid_all_valid_contra:
  "\<exists>g \<in> set G. gval_o g i r o = invalid \<Longrightarrow>
   gval_o (fold gAnd G (Bc True)) i r o = invalid"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc a G)
  then show ?case
    apply (simp only: gval_o_fold_gAnd_append_singleton)
    apply simp
    using maybe_and_valid by blast
qed

lemma gval_o_fold_not_invalid_all_valid:
  "gval_o (fold gAnd G (Bc True)) i r o \<noteq> invalid \<Longrightarrow>
   \<forall>g \<in> set G. gval_o g i r o \<noteq> invalid"
  using gval_o_fold_not_invalid_all_valid_contra by blast

lemma all_gval_o_not_false:
  "(\<forall>g \<in> set G. gval_o g i r o \<noteq> false) = (\<forall>g \<in> set G. gval_o g i r o = true) \<or> (\<exists>g \<in> set G. gval_o g i r o = invalid)"
  using trilean.exhaust by auto

lemma must_have_one_false_contra:
  "\<forall>g \<in> set G. gval_o g i r o \<noteq> false \<Longrightarrow>
   gval_o (fold gAnd G (Bc True)) i r o \<noteq> false"
  using all_gval_o_not_false[of G i r o]
  apply simp
  apply (case_tac "(\<forall>g\<in>set G. gval_o g i r o = true)")
   apply (metis (no_types, lifting) fold_apply_guards_o foldr_apply_guards_o gval_o_foldr_true trilean.distinct(1))
  by (simp add: gval_o_fold_not_invalid_all_valid_contra)

lemma must_have_one_false:
  "gval_o (fold gAnd G (Bc True)) i r o = false \<Longrightarrow>
   \<exists>g \<in> set G. gval_o g i r o = false"
  using must_have_one_false_contra by blast

lemma all_valid_fold: "\<forall>g \<in> set G. gval_o g i r o \<noteq> invalid \<Longrightarrow> gval_o (fold gAnd G (Bc True)) i r o \<noteq> invalid"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc a G)
  then show ?case
    apply (simp add: fold_conv_foldr del: foldr.simps)
    apply (simp only: foldr.simps comp_def gval_o_gAnd)
    by (simp add: maybe_and_invalid)
qed

lemma one_false_all_valid_false: "\<exists>g\<in>set G. gval_o g i r o = false \<Longrightarrow> \<forall>g\<in>set G. gval_o g i r o \<noteq> invalid \<Longrightarrow> gval_o (fold gAnd G (Bc True)) i r o = false"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  then show ?case
    apply (simp add: fold_conv_foldr del: foldr.simps)
    apply (simp only: foldr.simps comp_def gval_o_gAnd)
    apply (case_tac "gval_o x i r o = false")
     apply simp
     apply (case_tac "gval_o (foldr gAnd (rev xs) (Bc True)) i r o")
       apply simp
      apply simp
     apply simp
    using all_valid_fold
     apply (simp add: fold_conv_foldr)
    apply simp
    by (metis maybe_not.cases times_trilean.simps(5))
qed

lemma gval_o_fold_rev_false: "gval_o (fold gAnd (rev G) (Bc True)) i r o = false \<Longrightarrow> gval_o (fold gAnd G (Bc True)) i r o = false"
  using must_have_one_false[of "rev G" i r o]
        gval_o_fold_not_invalid_all_valid[of "rev G" i r o]
  by (simp add: one_false_all_valid_false)

lemma fold_invalid_means_one_invalid: "gval_o (fold gAnd G (Bc True)) i r o = invalid \<Longrightarrow> \<exists>g \<in> set G. gval_o g i r o = invalid"
  using all_valid_fold by blast

lemma gval_o_fold_rev_invalid: "gval_o (fold gAnd (rev G) (Bc True)) i r o = invalid \<Longrightarrow> gval_o (fold gAnd G (Bc True)) i r o = invalid"
  using fold_invalid_means_one_invalid[of "rev G" i r o]
  by (simp add: gval_o_fold_not_invalid_all_valid_contra)

lemma gval_o_fold_rev_equiv_fold: "gval_o (fold gAnd (rev G) (Bc True)) i r o =  gval_o (fold gAnd G (Bc True)) i r o"
  apply (cases "gval_o (fold gAnd (rev G) (Bc True)) i r o")
    apply (simp add: gval_o_fold_rev_true)
   apply (simp add: gval_o_fold_rev_false)
  by (simp add: gval_o_fold_rev_invalid)

lemma gval_o_fold_equiv_fold_rev: "gval_o (fold gAnd G (Bc True)) i r o = gval_o (fold gAnd (rev G) (Bc True)) i r o"
  by (simp add: gval_o_fold_rev_equiv_fold)

lemma gval_o_fold_equiv_gval_o_foldr: "gval_o (fold gAnd G (Bc True)) i r o = gval_o (foldr gAnd G (Bc True)) i r o"
proof -
  have "gval_o (fold gAnd G (Bc True)) i r o = gval_o (fold gAnd (rev G) (Bc True)) i r o"
    using gval_o_fold_equiv_fold_rev by force
  then show ?thesis
  by (simp add: foldr_conv_fold)
qed

lemma gval_o_foldr_equiv_gval_o_fold: "gval_o (foldr gAnd G (Bc True)) i r o = gval_o (fold gAnd G (Bc True)) i r o"
  by (simp add: gval_o_fold_equiv_gval_o_foldr)

lemma gval_o_fold_cons: "gval_o (fold gAnd (g # gs) (Bc True)) i r o = gval_o g i r o \<and>\<^sub>? gval_o (fold gAnd gs (Bc True)) i r o"
  apply (simp only: apply_guards_o_fold gval_o_fold_equiv_gval_o_foldr)
  by (simp only: foldr.simps comp_def gval_o_gAnd)

lemma gval_o_take:
  "max_input G < Some a \<Longrightarrow>
   a \<le> length i \<Longrightarrow>
   max_input G \<le> Some (length i) \<Longrightarrow>
   gval_o G i r o = gval_o G (take a i) r o"
  apply (induct G)
      apply (simp add: no_variables_list_gval_o)
  using aval_o_take max_input_Eq apply auto[1]
  using aval_o_take max_input_Gt apply auto[1]
   apply (case_tac x1a)
  using max_input_I max_input_In apply auto[1]
    apply simp
   apply simp
  by (simp add: gexp_o_max_input_Nor)

lemma gval_o_fold_take:
  "max_input_list G < Some a \<Longrightarrow>
   a \<le> length i \<Longrightarrow>
   max_input_list G \<le> Some (length i) \<Longrightarrow>
   gval_o (fold gAnd G (Bc True)) i r o = gval_o (fold gAnd G (Bc True)) (take a i) r o"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons g gs)
  then show ?case
    apply (simp only: gval_o_fold_cons)
    apply (simp add: max_input_list_cons)
    using gval_o_take by auto
qed

lemma max_is_None: "(max x y = None) = (x = None \<and> y = None)"
  by (metis less_eq_option_None_code less_eq_option_None_is_None max_def)

lemma max_reg_None_gval_o_swap: "max_reg G = None \<Longrightarrow>
       gval_o G i r o = gval_o G i r' o"
  apply (induct G)
      apply (simp add: no_variables_list_gval_o)
     apply (metis gval_o.simps(4) max_is_None max_reg_Eq max_reg_None_aval_o_swap)
    apply (metis gval_o.simps(3) max_is_None max_reg_Gt max_reg_None_aval_o_swap)
   apply (case_tac x1a)
     apply simp
    apply (simp add: GExp.max_reg_def)
   apply simp
  by (simp add: max_is_None max_reg_Nor)

lemma gval_o_fold_swap_regs:
  "max_reg_list G = None \<Longrightarrow>
   gval_o (fold gAnd G (Bc True)) i r o = gval_o (fold gAnd G (Bc True)) i r' o"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (simp only: gval_o_fold_equiv_gval_o_foldr foldr.simps comp_def gval_o_gAnd)
    by (metis max_is_None max_reg_None_gval_o_swap max_reg_list_cons)
qed

unbundle finfun_syntax

primrec padding :: "nat \<Rightarrow> 'a list" where
  "padding 0 = []" |
  "padding (Suc m) = (Eps (\<lambda>x. True))#(padding m)"

definition take_or_pad :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "take_or_pad a n = (if length a \<ge> n then take n a else a@(padding (n-length a)))"

lemma length_padding: "length (padding n) = n"
proof(induct n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by simp
qed

lemma length_take_or_pad: "length (take_or_pad a n) = n"
proof(induct n)
  case 0
  then show ?case
    by (simp add: take_or_pad_def)
next
  case (Suc n)
  then show ?case
    apply (simp add: take_or_pad_def)
    apply standard
     apply auto[1]
    by (simp add: length_padding)
qed

fun enumerate_gexp_o_strings :: "gexp_o \<Rightarrow> String.literal set" where
  "enumerate_gexp_o_strings (Bc _) = {}" |
  "enumerate_gexp_o_strings (Eq a1 a2) = enumerate_aexp_o_strings a1 \<union> enumerate_aexp_o_strings a2" |
  "enumerate_gexp_o_strings (Gt a1 a2) = enumerate_aexp_o_strings a1 \<union> enumerate_aexp_o_strings a2" |
  "enumerate_gexp_o_strings (In v l) = enumerate_aexp_o_strings (aexp_o.V v) \<union> (fold (\<union>) (map (\<lambda>x. enumerate_aexp_o_strings (L x)) l) {})" |
  "enumerate_gexp_o_strings (Nor g1 g2) = enumerate_gexp_o_strings g1 \<union> enumerate_gexp_o_strings g2"

fun enumerate_gexp_o_ints :: "gexp_o \<Rightarrow> int set" where
  "enumerate_gexp_o_ints (Bc _) = {}" |
  "enumerate_gexp_o_ints (Eq a1 a2) = enumerate_aexp_o_ints a1 \<union> enumerate_aexp_o_ints a2" |
  "enumerate_gexp_o_ints (Gt a1 a2) = enumerate_aexp_o_ints a1 \<union> enumerate_aexp_o_ints a2" |
  "enumerate_gexp_o_ints (In v l) = enumerate_aexp_o_ints (aexp_o.V v) \<union> (fold (\<union>) (map (\<lambda>x. enumerate_aexp_o_ints (L x)) l) {})" |
  "enumerate_gexp_o_ints (Nor g1 g2) = enumerate_gexp_o_ints g1 \<union> enumerate_gexp_o_ints g2"

definition restricted_once :: "vname_o \<Rightarrow> gexp_o list \<Rightarrow> bool" where
  "restricted_once v G = (length (filter (\<lambda>g. gexp_o_constrains g (aexp_o.V v)) G) = 1)"

definition not_restricted :: "vname_o \<Rightarrow> gexp_o list \<Rightarrow> bool" where
  "not_restricted v G = (length (filter (\<lambda>g. gexp_o_constrains g (aexp_o.V v)) G) = 0)"

lemma restricted_once_cons: "restricted_once v (g#gs) = ((gexp_o_constrains g (aexp_o.V v) \<and> not_restricted v gs) \<or> ((\<not> gexp_o_constrains g (aexp_o.V v)) \<and> restricted_once v gs))"
  by (simp add: restricted_once_def not_restricted_def)

lemma not_restricted_cons: "not_restricted v (g#gs) = ((\<not> gexp_o_constrains g (aexp_o.V v)) \<and> not_restricted v gs)"
  by (simp add: not_restricted_def)

definition enumerate_vars :: "gexp_o \<Rightarrow> vname_o list" where
  "enumerate_vars g = sorted_list_of_set ((image R (enumerate_gexp_o_regs g)) \<union> (image I (enumerate_gexp_o_inputs g)))"

typedef gexp = "{g :: gexp_o. \<forall>n. \<not> gexp_o_constrains g (aexp_o.V (O n))}"  morphisms gexp Abs_gexp
  using gexp_o_constrains.simps(1) by fastforce

setup_lifting type_definition_gexp
lift_definition gval :: "gexp \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> trilean" is "gval_o".
lift_definition enumerate_gexp_inputs :: "gexp \<Rightarrow> nat set" is "enumerate_gexp_o_inputs".
lift_definition enumerate_gexp_regs :: "gexp \<Rightarrow> nat set" is "enumerate_gexp_o_regs".
lift_definition enumerate_gexp_strings :: "gexp \<Rightarrow> String.literal set" is "enumerate_gexp_o_strings".
lift_definition enumerate_gexp_ints :: "gexp \<Rightarrow> int set" is "enumerate_gexp_o_ints".
lift_definition apply_guards :: "gexp list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> bool" is "\<lambda>a i r. apply_guards_o a i r []".

lemma enumerate_gexp_regs_list: "\<exists>l. enumerate_gexp_regs g = set l"
  by (simp add: enumerate_gexp_o_regs_list enumerate_gexp_regs.rep_eq)

lemma apply_guards_append: "apply_guards (a@a') i r = (apply_guards a i r \<and> apply_guards a' i r)"
  by (simp add: apply_guards_def apply_guards_o_append)


end
