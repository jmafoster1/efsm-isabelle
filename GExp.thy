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

definition I :: "nat \<Rightarrow> vname" where
  "I n = vname.I (n-1)"
declare I_def [simp]
hide_const I

text_raw\<open>\snip{gexptype}{1}{2}{%\<close>
datatype 'a gexp = Bc bool | Eq "'a aexp" "'a aexp" | Gt "'a aexp" "'a aexp" | In 'a "value list" |  Nor "'a gexp" "'a gexp"
text_raw\<open>}%endsnip\<close>

fun gval :: "'a gexp \<Rightarrow> 'a datastate \<Rightarrow> trilean" where
  "gval (Bc True) _ = true" |
  "gval (Bc False) _ = false" |
  "gval (Gt a\<^sub>1 a\<^sub>2) s = value_gt (aval a\<^sub>1 s) (aval a\<^sub>2 s)" |
  "gval (Eq a\<^sub>1 a\<^sub>2) s = value_eq (aval a\<^sub>1 s) (aval a\<^sub>2 s)" |
  "gval (In v l) s = (if s v \<in> set (map Some l) then true else false)" |
  "gval (Nor a\<^sub>1 a\<^sub>2) s = \<not>\<^sub>? ((gval a\<^sub>1 s) \<or>\<^sub>? (gval a\<^sub>2 s))"

definition gNot :: "'a gexp \<Rightarrow> 'a gexp"  where
  "gNot g \<equiv> Nor g g"

definition gOr :: "'a gexp \<Rightarrow> 'a gexp \<Rightarrow> 'a gexp" (*infix "\<or>" 60*) where
  "gOr v va \<equiv> Nor (Nor v va) (Nor v va)"

definition gAnd :: "'a gexp \<Rightarrow> 'a gexp \<Rightarrow> 'a gexp" (*infix "\<and>" 60*) where
  "gAnd v va \<equiv> Nor (Nor v v) (Nor va va)"

definition gImplies :: "'a gexp \<Rightarrow> 'a gexp \<Rightarrow> 'a gexp" where
  "gImplies p q \<equiv> gOr (gNot p) q"

definition Lt :: "'a aexp \<Rightarrow> 'a aexp \<Rightarrow> 'a gexp" (*infix "<" 60*) where
  "Lt a b \<equiv> Gt b a"

lemma gval_Lt [simp]:  "gval (Lt a\<^sub>1 a\<^sub>2) s = value_gt (aval a\<^sub>2 s) (aval a\<^sub>1 s)"
  by (simp add: Lt_def)

definition Le :: "'a aexp \<Rightarrow> 'a aexp \<Rightarrow> 'a gexp" (*infix "\<le>" 60*) where
  "Le v va \<equiv> gNot (Gt v va)"

lemma gval_Le [simp]:  "gval (Le a\<^sub>1 a\<^sub>2) s = \<not>\<^sub>? (value_gt (aval a\<^sub>1 s) (aval a\<^sub>2 s))"
  by (simp add: Le_def value_gt_def gNot_def maybe_or_idempotent)

definition Ge :: "'a aexp \<Rightarrow> 'a aexp \<Rightarrow> 'a gexp" (*infix "\<ge>" 60*) where
  "Ge v va \<equiv> gNot (Lt v va)"

lemma gval_Ge [simp]:  "gval (Ge a\<^sub>1 a\<^sub>2) s = \<not>\<^sub>? (value_gt (aval a\<^sub>2 s) (aval a\<^sub>1 s))"
  by (simp add: Ge_def value_gt_def gNot_def maybe_or_idempotent)

definition Ne :: "'a aexp \<Rightarrow> 'a aexp \<Rightarrow> 'a gexp" (*infix "\<noteq>" 60*) where
  "Ne v va \<equiv> gNot (Eq v va)"

lemma gval_Ne [simp]:  "gval (Ne a\<^sub>1 a\<^sub>2) s = \<not>\<^sub>? (value_eq (aval a\<^sub>2 s) (aval a\<^sub>1 s))"
  by (simp add: Ne_def value_gt_def gNot_def maybe_or_idempotent)

lemmas connectives = gAnd_def gOr_def gNot_def Lt_def Le_def Ge_def Ne_def

lemma gval_gOr: "gval (gOr x y) r = (gval x r) \<or>\<^sub>? (gval y r)"
  by (simp add: maybe_double_negation maybe_or_idempotent gOr_def)

lemma gval_gNot: "gval (gNot x) s = \<not>\<^sub>? (gval x s)"
  by (simp add: maybe_or_idempotent gNot_def)

lemma gval_gAnd: "gval (gAnd g1 g2) s = (gval g1 s) \<and>\<^sub>? (gval g2 s)"
  by (simp add: de_morgans_1 maybe_double_negation maybe_or_idempotent gAnd_def)

lemma gAnd_commute: "gval (gAnd a b) s = gval (gAnd b a) s"
  by (simp add: gval_gAnd times_trilean_commutative)

lemma gOr_commute: "gval (gOr a b) s = gval (gOr b a) s"
  by (simp add: plus_trilean_commutative gOr_def)

lemma gval_gAnd_True: "(gval (gAnd g1 g2) s = true) = ((gval g1 s = true) \<and> gval g2 s = true)"
  by (simp add: gval_gAnd maybe_and_true)

lemma nor_equiv: "gval (gNot (gOr a b)) s = gval (Nor a b) s"
  by (simp add: gval_gNot gval_gOr)

definition satisfiable :: "vname gexp \<Rightarrow> bool" where
  "satisfiable g \<equiv> (\<exists>i r. gval g (join_ir i r) = true)"

definition "satisfiable_list l = satisfiable (fold gAnd l (Bc True))"

lemma unsatisfiable_false: "\<not> satisfiable (Bc False)"
  by (simp add: satisfiable_def)

lemma satisfiable_true: "satisfiable (Bc True)"
  by (simp add: satisfiable_def)

definition valid :: "vname gexp \<Rightarrow> bool" where
  "valid g \<equiv> (\<forall>s. gval g s = true)"

lemma valid_true: "valid (Bc True)"
  by (simp add: valid_def)

fun gexp_constrains :: "'a gexp \<Rightarrow> 'a aexp \<Rightarrow> bool" where
  "gexp_constrains (Bc _) _ = False" |
  "gexp_constrains (Eq a1 a2) a = (aexp_constrains a1 a \<or> aexp_constrains a2 a)" |
  "gexp_constrains (Gt a1 a2) a = (aexp_constrains a1 a \<or> aexp_constrains a2 a)" |
  "gexp_constrains (Nor g1 g2) a = (gexp_constrains g1 a \<or> gexp_constrains g2 a)" |
  "gexp_constrains (In v l) a = aexp_constrains (V v) a"

fun contains_bool :: "'a gexp \<Rightarrow> bool" where
  "contains_bool (Bc _) = True" |
  "contains_bool (Nor g1 g2) = (contains_bool g1 \<or> contains_bool g2)" |
  "contains_bool _ = False"

fun gexp_same_structure :: "'a gexp \<Rightarrow> 'a gexp \<Rightarrow> bool" where
  "gexp_same_structure (Bc b) (Bc b') = (b = b')" |
  "gexp_same_structure (Eq a1 a2) (Eq a1' a2') = (aexp_same_structure a1 a1' \<and> aexp_same_structure a2 a2')" |
  "gexp_same_structure (Gt a1 a2) (Gt a1' a2') = (aexp_same_structure a1 a1' \<and> aexp_same_structure a2 a2')" |
  "gexp_same_structure (Nor g1 g2) (Nor g1' g2') = (gexp_same_structure g1 g1' \<and> gexp_same_structure g2 g2')" |
  "gexp_same_structure (In v l) (In v' l') = (v = v' \<and> l = l')" |
  "gexp_same_structure _ _ = False"

lemma gval_foldr_true: "(gval (foldr gAnd G (Bc True)) s = true) = (\<forall>g \<in> set G. gval g s = true)"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def gval_gAnd maybe_and_true)
    by simp
qed

fun enumerate_gexp_inputs :: "vname gexp \<Rightarrow> nat set" where
  "enumerate_gexp_inputs (Bc _) = {}" |
  "enumerate_gexp_inputs (Eq v va) = enumerate_aexp_inputs v \<union> enumerate_aexp_inputs va" |
  "enumerate_gexp_inputs (Gt v va) = enumerate_aexp_inputs v \<union> enumerate_aexp_inputs va" |
  "enumerate_gexp_inputs (In v va) = enumerate_aexp_inputs (V v)" |
  "enumerate_gexp_inputs (Nor v va) = enumerate_gexp_inputs v \<union> enumerate_gexp_inputs va"

lemma enumerate_gexp_inputs_list: "\<exists>l. enumerate_gexp_inputs g = set l"
proof(induct g)
  case (Bc x)
  then show ?case
    by simp
next
  case (Eq x1a x2)
  then show ?case
    by (metis enumerate_aexp_inputs_list enumerate_gexp_inputs.simps(2) set_append)
next
  case (Gt x1a x2)
  then show ?case
    by (metis enumerate_aexp_inputs_list enumerate_gexp_inputs.simps(3) set_append)
next
  case (In x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_inputs_list)
next
  case (Nor g1 g2)
  then show ?case
    by (metis enumerate_gexp_inputs.simps(5) set_append)
qed

definition max_input :: "vname gexp \<Rightarrow> nat option" where
  "max_input g = (let inputs = (enumerate_gexp_inputs g) in if inputs = {} then None else Some (Max inputs))"

definition max_input_list :: "vname gexp list \<Rightarrow> nat option" where
  "max_input_list g = fold max (map (\<lambda>g. max_input g) g) None"

lemma max_input_list_cons: "max_input_list (a # G) = max (max_input a) (max_input_list G)"
  apply (simp add: max_input_list_def)
  apply (cases "max_input a")
   apply (simp add: max_def_raw)
  by (metis (no_types, lifting) List.finite_set Max.insert Max.set_eq_fold fold_simps(1) list.set(2) max.assoc set_empty)

fun enumerate_gexp_regs :: "vname gexp \<Rightarrow> nat set" where
  "enumerate_gexp_regs (Bc _) = {}" |
  "enumerate_gexp_regs (Eq v va) = enumerate_aexp_regs v \<union> enumerate_aexp_regs va" |
  "enumerate_gexp_regs (Gt v va) = enumerate_aexp_regs v \<union> enumerate_aexp_regs va" |
  "enumerate_gexp_regs (In v va) = enumerate_aexp_regs (V v)" |
  "enumerate_gexp_regs (Nor v va) = enumerate_gexp_regs v \<union> enumerate_gexp_regs va"

lemma enumerate_gexp_regs_list: "\<exists>l. enumerate_gexp_regs g = set l"
proof(induct g)
case (Bc x)
  then show ?case
  by simp
next
  case (Eq x1a x2)
  then show ?case
    by (metis enumerate_aexp_regs_list enumerate_gexp_regs.simps(2) set_append)
next
  case (Gt x1a x2)
  then show ?case
    by (metis enumerate_aexp_regs_list enumerate_gexp_regs.simps(3) set_append)
next
  case (In x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_regs_list)
next
  case (Nor g1 g2)
  then show ?case
    by (metis enumerate_gexp_regs.simps(5) set_append)
qed

lemma no_variables_list_gval:
  "enumerate_gexp_inputs g = {} \<Longrightarrow>
   enumerate_gexp_regs g = {} \<Longrightarrow>
   gval g s = gval g s'"
proof(induct g)
case (Bc x)
  then show ?case
    by (metis (full_types) gval.simps(1) gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    by (metis append_is_Nil_conv enumerate_aexp_inputs_list enumerate_aexp_regs_list enumerate_gexp_inputs.simps(2) enumerate_gexp_regs.simps(2) gval.simps(4) no_variables_aval set_empty set_union_append)
next
  case (Gt x1a x2)
  then show ?case
    by (metis append_is_Nil_conv enumerate_aexp_inputs_list enumerate_aexp_regs_list enumerate_gexp_inputs.simps(3) enumerate_gexp_regs.simps(3) gval.simps(3) no_variables_aval set_empty set_union_append)
next
  case (In x1a x2)
  then show ?case
    by (simp, metis aval.simps(2) no_variables_aval)
next
  case (Nor g1 g2)
  then show ?case
    by simp
qed

lemma no_variables_list_valid_or_unsat:
  "enumerate_gexp_inputs g = {} \<Longrightarrow>
   enumerate_gexp_regs g = {} \<Longrightarrow>
   valid g \<or> \<not> satisfiable g"
proof(induct g)
  case (Bc x)
  then show ?case
    by (metis (full_types) unsatisfiable_false valid_true)
next
  case (Eq x1a x2)
  then show ?case
    by (metis no_variables_list_gval satisfiable_def valid_def)
next
  case (Gt x1a x2)
  then show ?case
    by (metis no_variables_list_gval satisfiable_def valid_def)
next
  case (Nor g1 g2)
  then show ?case
    by (metis no_variables_list_gval satisfiable_def valid_def)
next
  case (In g1 g2)
  then show ?case
    by (metis no_variables_list_gval satisfiable_def valid_def)
qed

definition max_reg :: "vname gexp \<Rightarrow> nat option" where
  "max_reg g = (let regs = (enumerate_gexp_regs g) in if regs = {} then None else Some (Max regs))"

lemma max_reg_gNot: "max_reg (gNot x) = max_reg x"
  by (simp add: max_reg_def gNot_def)

lemma max_reg_Eq: "max_reg (Eq a b) = max (AExp.max_reg a) (AExp.max_reg b)"
  apply (simp add: max_reg_def AExp.max_reg_def Let_def max_absorb2)
  by (metis List.finite_set Max.union enumerate_aexp_regs_list less_eq_option_Some_None max_def sup_Some sup_max)

lemma max_reg_Gt: "max_reg (Gt a b) = max (AExp.max_reg a) (AExp.max_reg b)"
  apply (simp add: max_reg_def AExp.max_reg_def Let_def max_absorb2)
  by (metis List.finite_set Max.union enumerate_aexp_regs_list less_eq_option_Some_None max_def sup_Some sup_max)

lemma max_reg_Nor: "max_reg (Nor a b) = max (max_reg a) (max_reg b)"
  apply (simp add: max_reg_def AExp.max_reg_def Let_def max_absorb2)
  by (metis List.finite_set Max.union enumerate_gexp_regs_list less_eq_option_Some_None max_def sup_Some sup_max)

lemma no_reg_gval_swap_regs: "max_reg g = None \<Longrightarrow> gval g (join_ir i r) = gval g (join_ir i r')"
proof(induct g)
case (Bc x)
  then show ?case
    by (metis (full_types) gval.simps(1) gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    by (metis gval.simps(4) max.idem max.left_commute max_reg_Eq no_reg_aval_swap_regs sup_None_2 sup_max)
next
  case (Gt x1a x2)
  then show ?case
    by (metis gval.simps(3) max.idem max.left_commute max_reg_Gt no_reg_aval_swap_regs sup_None_2 sup_max)
next
  case (Nor g1 g2)
  then show ?case
    by (metis (no_types, lifting) gval.simps(6) max.idem max.left_commute max_reg_Nor sup_None_2 sup_max)
next
  case (In v l)
  then show ?case
    by (metis AExp.max_reg_def GExp.max_reg_def aval.simps(2) enumerate_gexp_regs.simps(4) gval.simps(5) no_reg_aval_swap_regs)
qed

lemma enumerate_gexp_regs_empty_reg_unconstrained: "enumerate_gexp_regs g = {} \<Longrightarrow> \<forall>r. \<not> gexp_constrains g (V (R r))"
proof(induct g)
case (Bc x)
  then show ?case
    by simp
next
  case (Eq x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_regs_empty_reg_unconstrained)
next
  case (Gt x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_regs_empty_reg_unconstrained)
next
  case (In v l)
  then show ?case
    by auto
next
  case (Nor g1 g2)
  then show ?case
    by simp
qed

lemma unconstrained_variable_swap_gval:
   "\<forall>r. \<not> gexp_constrains g (V (vname.I r)) \<Longrightarrow>
    \<forall>r. \<not> gexp_constrains g (V (R r)) \<Longrightarrow>
    gval g s = gval g s'"
proof(induct g)
case (Bc x)
  then show ?case
    by (simp add: no_variables_list_gval)
next
  case (Eq x1a x2)
  then show ?case
    by (metis gexp_constrains.simps(2) gval.simps(4) unconstrained_variable_swap_aval)
next
  case (Gt x1a x2)
  then show ?case
    by (metis gexp_constrains.simps(3) gval.simps(3) unconstrained_variable_swap_aval)
next
  case (In v l)
  then show ?case
    by (cases v, auto)
next
  case (Nor g1 g2)
  then show ?case
    by simp
qed

lemma gval_In_cons: "gval (In v (a # as)) s = (gval (Eq (V v) (L a)) s \<or>\<^sub>? gval (In v as) s)"
  by (cases "s v", auto)

lemma possible_to_be_in: "s \<noteq> [] \<Longrightarrow> satisfiable (In v s)"
proof-
  assume "s \<noteq> []"
  have aux: "\<exists>v' i r. join_ir i r v = Some v' \<and> v' \<in> set s \<Longrightarrow>
             \<exists>i r. (case join_ir i r v of None \<Rightarrow> false | Some v \<Rightarrow> if v \<in> set s then true else false) = true"
    by (metis (mono_tags, lifting) option.simps(5))
  show ?thesis
    apply (simp add: satisfiable_def gval_In_cons)
    apply (cases s)
     apply (simp add: \<open>s \<noteq> []\<close>)
    using join_ir_double_exists by fastforce
qed

definition max_reg_list :: "vname gexp list \<Rightarrow> nat option" where
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

definition apply_guards :: "vname gexp list \<Rightarrow> vname datastate \<Rightarrow> bool" where
  "apply_guards G s = (\<forall>g \<in> set (map (\<lambda>g. gval g s) G). g = true)"

lemma apply_guards_singleton[simp]: "(apply_guards [g] s) = (gval g s = true)"
  by (simp add: apply_guards_def)

lemma apply_guards_empty [simp]: "apply_guards [] s"
  by (simp add: apply_guards_def)

lemma apply_guards_cons: "apply_guards (a # G) c = (gval a c = true \<and> apply_guards G c)"
  by (simp add: apply_guards_def)

lemma apply_guards_double_cons: "apply_guards (y # x # G) s = (gval (gAnd y x) s = true \<and> apply_guards G s)"
  by (simp add: apply_guards_cons gval_gAnd_True)

lemma apply_guards_append: "apply_guards (a@a') s = (apply_guards a s \<and> apply_guards a' s)"
  using apply_guards_def by auto

lemma apply_guards_foldr: "apply_guards G s = (gval (foldr gAnd G (Bc True)) s = true)"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_def)
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def)
    by (simp add: apply_guards_cons gval_gAnd_True)
qed

lemma rev_apply_guards: "apply_guards (rev G) s = apply_guards G s"
  by (simp add: apply_guards_def)

lemma apply_guards_fold: "apply_guards G s = (gval (fold gAnd G (Bc True)) s = true)"
  using rev_apply_guards[symmetric]
  by (simp add: foldr_conv_fold apply_guards_foldr)

lemma fold_apply_guards: "(gval (fold gAnd G (Bc True)) s = true) = apply_guards G s"
  by (simp add: apply_guards_fold)

lemma foldr_apply_guards: "(gval (foldr gAnd G (Bc True)) s = true) = apply_guards G s"
  by (simp add: apply_guards_foldr)

lemma apply_guards_subset: "set g' \<subseteq> set g \<Longrightarrow> apply_guards g c \<longrightarrow> apply_guards g' c"
proof(induct g)
  case Nil
  then show ?case
    by simp
next
  case (Cons a g)
  then show ?case
    using apply_guards_def by auto
qed

lemma apply_guards_subset_append: "set G \<subseteq> set G' \<Longrightarrow> apply_guards (G @ G') s = apply_guards (G') s"
  using apply_guards_append apply_guards_subset by blast

lemma apply_guards_rearrange: "x \<in> set G \<Longrightarrow> apply_guards G s = apply_guards (x#G) s"
  using apply_guards_def by auto

lemma no_reg_apply_guards_swap_regs:
  "max_reg_list G = None \<Longrightarrow>
   apply_guards G (join_ir i r) = apply_guards G (join_ir i r')"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    by (metis apply_guards_cons less_eq_option_None max_def max_reg_list_cons no_reg_gval_swap_regs sup_None_2 sup_max)
qed

lemma max_input_Bc: "max_input (Bc x) = None"
  by (simp add: max_input_def)

lemma max_input_Eq: "max_input (Eq a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def max_input_def Let_def max_absorb2)
  by (metis List.finite_set Max.union bot_option_def enumerate_aexp_inputs_not_empty max_bot2 sup_Some sup_max)

lemma max_input_Gt: "max_input (Gt a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def max_input_def Let_def max_absorb2)
  by (metis List.finite_set Max.union bot_option_def enumerate_aexp_inputs_not_empty max_bot2 sup_Some sup_max)

lemma gexp_max_input_Nor: "max_input (Nor g1 g2) = max (max_input g1) (max_input g2)"
  apply (simp add: AExp.max_input_def max_input_def Let_def max_absorb2)
  by (metis List.finite_set Max.union enumerate_gexp_inputs_list less_eq_option_Some_None max_def sup_Some sup_max)

lemma gexp_max_input_In: "max_input (In v l) = AExp.max_input (V v)"
  by (simp add: AExp.max_input_def GExp.max_input_def)

lemma rev_singleton: "rev [a] = [a]"
  by simp

lemma singleton_append: "[a]@l = a#l"
  by simp

lemma gval_foldr_gOr_invalid: "(gval (fold gOr l g) s = invalid) = (\<exists>g' \<in> (set (g#l)). gval g' s = invalid)"
proof(induct l rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  then show ?case
    apply (simp only: fold_conv_foldr foldr.simps append.simps rev_append rev_singleton comp_def gval_gOr)
    using maybe_or_invalid by auto
qed

lemma gval_foldr_gOr_true: "(gval (fold gOr l g) s = true) = ((\<exists>g' \<in> (set (g#l)). gval g' s = true) \<and> (\<forall>g' \<in> (set (g#l)). gval g' s \<noteq> invalid))"
proof(induct l rule: rev_induct)
  case Nil
  then show ?case
    by auto
next
  case (snoc x xs)
  then show ?case
    apply (simp only: fold_conv_foldr foldr.simps append.simps rev_append rev_singleton comp_def gval_gOr)
    apply (simp add: maybe_or_true)
    by (metis (no_types, lifting) fold_conv_foldr gval_foldr_gOr_invalid list.set_intros(1) list.set_intros(2) set_ConsD)
qed

lemma gval_foldr_gOr_false: "(gval (fold gOr l g) s = false) = (\<forall>g' \<in> (set (g#l)). gval g' s = false)"
proof(induct l rule: rev_induct)
  case Nil
  then show ?case
    by auto
next
  case (snoc x xs)
  then show ?case
    apply (simp only: fold_conv_foldr foldr.simps append.simps rev_append rev_singleton comp_def gval_gOr)
    apply (simp add: maybe_or_false)
    by auto
qed

lemma gval_fold_gOr_rev: "gval (fold gOr (rev l) g) s = gval (fold gOr l g) s"
  apply (cases "gval (fold gOr l g) s")
    apply (simp, simp add: gval_foldr_gOr_true)
   apply (simp, simp add: gval_foldr_gOr_false)
  by (simp, simp add: gval_foldr_gOr_invalid)

lemma gval_fold_gOr_foldr: "gval (fold gOr l g) s = gval (foldr gOr l g) s"
  by (simp add: foldr_conv_fold gval_fold_gOr_rev)

lemma gval_fold_gOr: "gval (fold gOr (a # l) g) s = (gval a s \<or>\<^sub>? gval (fold gOr l g) s)"
  by (simp only: gval_fold_gOr_foldr foldr.simps comp_def gval_gOr)

lemma gval_In_fold: "gval (In v l) s = gval (fold gOr (map (\<lambda>x. Eq (V v) (L x)) l) (Bc False)) s"
proof(induct l)
  case Nil
  then show ?case
    apply (cases "s v")
    by auto
next
  case (Cons a l)
  then show ?case
    by (simp only: gval_In_cons list.map gval_fold_gOr)
qed

fun fold_In :: "'a \<Rightarrow> value list \<Rightarrow> 'a gexp" where
  "fold_In _ [] = Bc False" |
  "fold_In v [l] = Eq (V v) (L l)" |
  "fold_In v (l#t) = fold gOr (map (\<lambda>x. Eq (V v) (L x)) t) (Eq (V v) (L l))"

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

lemma gval_fold_gOr_map: "gval (fold gOr l (Bc False)) s = fold (\<or>\<^sub>?) (map (\<lambda>g. gval g s) l) (false)"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    by (metis fold_maybe_or_cons gval_fold_gOr list.simps(9))
qed

lemma gval_unfold_first: "gval (fold gOr (map (\<lambda>x. Eq (V v) (L x)) ls) (Eq (V v) (L l))) s =
       gval (fold gOr (map (\<lambda>x. Eq (V v) (L x)) (l#ls)) (Bc False)) s"
proof(induct ls)
  case Nil
  then show ?case
    by (simp add: gOr_def)
next
  case (Cons a ls)
  then show ?case
  proof -
    have "gval (fold gOr (map (\<lambda>va. Eq (V v) (L va)) ls) (gOr (Eq (V v) (L l)) (Bc False))) s = gval (fold gOr (map (\<lambda>va. Eq (V v) (L va)) (l # ls)) (Bc False)) s"
      by simp
    then have "gval (fold gOr (map (\<lambda>va. Eq (V v) (L va)) (a # ls)) (Eq (V v) (L l))) s = gval (fold gOr (Eq (V v) (L a) # map (\<lambda>va. Eq (V v) (L va)) ls) (gOr (Eq (V v) (L l)) (Bc False))) s"
      by (metis (no_types) Cons.hyps gval_fold_gOr list.simps(9))
    then show ?thesis
      by force
  qed
qed

lemma fold_Eq_true: "\<forall>v. fold (\<or>\<^sub>?) (map (\<lambda>x. if v = x then true else false) vs) true = true"
  by(induct vs, auto)

lemma gval_fold_In_hd: "s v = Some a \<Longrightarrow> gval (fold_In v (a # l)) s = true"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons v vs)
  then show ?case
    apply (simp only: fold_In.simps gval_unfold_first gval_fold_gOr_map)
    by (simp add: comp_def fold_Eq_true)
qed

lemma x_in_set_fold_eq: "x \<in> set ll \<Longrightarrow> fold (\<or>\<^sub>?) (map (\<lambda>xa. if x = xa then true else false) ll) false = true"
proof(induct ll)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ll)
  then show ?case
    apply simp
    apply standard
     apply (simp add: fold_Eq_true)
    by auto
qed

lemma gval_fold_In_true_if: "s v \<in> Some ` set l \<Longrightarrow> gval (fold_In v l) s = true"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons l ll)
  then show ?case
  proof(induct ll)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a ll)
    then show ?case
      apply (simp only: fold_In.simps gval_unfold_first gval_fold_gOr_map)
      apply (simp add: comp_def fold_Eq_true)
      using x_in_set_fold_eq by fastforce
    qed
  qed

lemma x_not_in_set_fold_eq: "s v \<notin> Some ` set ll \<Longrightarrow> false = fold (\<or>\<^sub>?) (map (\<lambda>x. if s v = Some x then true else false) ll) false"
  by(induct ll, auto)

lemma gval_fold_In_false_if: "s v \<notin> Some ` set l \<longrightarrow> false = gval (fold_In v l) s"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons l ll)
  then show ?case
  proof(induct ll)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a ll)
    then show ?case
      apply (simp only: fold_In.simps gval_unfold_first gval_fold_gOr_map)
      apply (simp add: comp_def fold_Eq_true)
      apply clarify
      using x_not_in_set_fold_eq by force
  qed
qed


lemma gval_fold_in: "gval (In v l) s = gval (fold_In v l) s"
  apply simp
  apply standard
   apply (simp add: gval_fold_In_true_if)
  by (metis gval_fold_In_false_if)

lemma gval_take:
  "max_input g < Some a \<Longrightarrow>
   gval g (join_ir i r) = gval g (join_ir (take a i) r)"
proof(induct g)
case (Bc x)
  then show ?case
    by (metis (full_types) gval.simps(1) gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    by (metis aval_take gval.simps(4) max_input_Eq max_less_iff_conj)
next
  case (Gt x1a x2)
  then show ?case
    by (metis aval_take gval.simps(3) max_input_Gt max_less_iff_conj)
next
  case (Nor g1 g2)
  then show ?case
    by (simp add: maybe_not_eq gexp_max_input_Nor)
next
  case (In v l)
  then show ?case
    apply (simp add: gexp_max_input_In)
    using aval_take by fastforce
qed

lemma gval_no_reg_swap_regs:
  "max_input g < Some a \<Longrightarrow>
   max_reg g = None \<Longrightarrow>
   gval g (join_ir i ra) = gval g (join_ir (take a i) r)"
proof(induct g)
case (Bc x)
  then show ?case
    by (metis (full_types) gval.simps(1) gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    by (metis gval_take no_reg_gval_swap_regs)
next
  case (Gt x1a x2)
  then show ?case
    by (metis gval_take no_reg_gval_swap_regs)
next
  case (Nor g1 g2)
  then show ?case
    by (metis gval_take no_reg_gval_swap_regs)
next
  case (In v l)
  then show ?case
    apply (simp add: gexp_max_input_In)
    by (metis AExp.max_reg_def GExp.max_reg_def aval.simps(2) aval_no_reg_swap_regs enumerate_gexp_regs.simps(4))
qed

lemma gval_fold_gAnd_append_singleton:
  "gval (fold gAnd (a @ [G]) (Bc True)) s = gval (fold gAnd a (Bc True)) s \<and>\<^sub>? gval G s"
  apply (simp add: fold_conv_foldr del: foldr.simps)
  by (simp only: foldr.simps comp_def gval_gAnd times_trilean_commutative)

lemma gval_fold_rev_true:
  "gval (fold gAnd (rev G) (Bc True)) s = true \<Longrightarrow>
   gval (fold gAnd G (Bc True)) s = true"
  by (simp add: fold_conv_foldr gval_foldr_true)

lemma gval_fold_not_invalid_all_valid_contra:
  "\<exists>g \<in> set G. gval g s = invalid \<Longrightarrow>
   gval (fold gAnd G (Bc True)) s = invalid"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc a G)
  then show ?case
    apply (simp only: gval_fold_gAnd_append_singleton)
    apply simp
    using maybe_and_valid by blast
qed

lemma gval_fold_not_invalid_all_valid:
  "gval (fold gAnd G (Bc True)) s \<noteq> invalid \<Longrightarrow>
   \<forall>g \<in> set G. gval g s \<noteq> invalid"
  using gval_fold_not_invalid_all_valid_contra by blast

lemma all_gval_not_false:
  "(\<forall>g \<in> set G. gval g s \<noteq> false) = (\<forall>g \<in> set G. gval g s = true) \<or> (\<exists>g \<in> set G. gval g s = invalid)"
  using trilean.exhaust by auto

lemma must_have_one_false_contra:
  "\<forall>g \<in> set G. gval g s \<noteq> false \<Longrightarrow>
   gval (fold gAnd G (Bc True)) s \<noteq> false"
  using all_gval_not_false[of G s]
  apply simp
  apply (case_tac "(\<forall>g\<in>set G. gval g s = true)")
  apply (metis (full_types) foldr_conv_fold gval_fold_rev_true gval_foldr_true not_true)
  by (simp add: gval_fold_not_invalid_all_valid_contra)

lemma must_have_one_false:
  "gval (fold gAnd G (Bc True)) s = false \<Longrightarrow>
   \<exists>g \<in> set G. gval g s = false"
  using must_have_one_false_contra by blast

lemma all_valid_fold: "\<forall>g \<in> set G. gval g s \<noteq> invalid \<Longrightarrow> gval (fold gAnd G (Bc True)) s \<noteq> invalid"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc a G)
  then show ?case
    apply (simp add: fold_conv_foldr del: foldr.simps)
    apply (simp only: foldr.simps comp_def gval_gAnd)
    by (simp add: maybe_and_invalid)
qed

lemma one_false_all_valid_false: "\<exists>g\<in>set G. gval g s = false \<Longrightarrow> \<forall>g\<in>set G. gval g s \<noteq> invalid \<Longrightarrow> gval (fold gAnd G (Bc True)) s = false"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  then show ?case
    apply (simp add: fold_conv_foldr del: foldr.simps)
    apply (simp only: foldr.simps comp_def gval_gAnd)
    apply (case_tac "gval x s = false")
     apply simp
     apply (case_tac "gval (foldr gAnd (rev xs) (Bc True)) s")
       apply simp
      apply simp
     apply simp
    using all_valid_fold
     apply (simp add: fold_conv_foldr)
     apply auto[1]
    by (simp add: maybe_and_false)
qed

lemma gval_fold_rev_false: "gval (fold gAnd (rev G) (Bc True)) s = false \<Longrightarrow> gval (fold gAnd G (Bc True)) s = false"
  using must_have_one_false[of "rev G" s]
        gval_fold_not_invalid_all_valid[of "rev G" s]
  by (simp add: one_false_all_valid_false)

lemma fold_invalid_means_one_invalid: "gval (fold gAnd G (Bc True)) s = invalid \<Longrightarrow> \<exists>g \<in> set G. gval g s = invalid"
  using all_valid_fold by blast

lemma gval_fold_rev_invalid: "gval (fold gAnd (rev G) (Bc True)) s = invalid \<Longrightarrow> gval (fold gAnd G (Bc True)) s = invalid"
  using fold_invalid_means_one_invalid[of "rev G" s]
  by (simp add: gval_fold_not_invalid_all_valid_contra)

lemma gval_fold_rev_equiv_fold: "gval (fold gAnd (rev G) (Bc True)) s =  gval (fold gAnd G (Bc True)) s"
  apply (cases "gval (fold gAnd (rev G) (Bc True)) s")
    apply (simp add: gval_fold_rev_true)
   apply (simp add: gval_fold_rev_false)
  by (simp add: gval_fold_rev_invalid)

lemma gval_fold_equiv_fold_rev: "gval (fold gAnd G (Bc True)) s = gval (fold gAnd (rev G) (Bc True)) s"
  by (simp add: gval_fold_rev_equiv_fold)

lemma gval_fold_equiv_gval_foldr: "gval (fold gAnd G (Bc True)) s = gval (foldr gAnd G (Bc True)) s"
proof -
  have "gval (fold gAnd G (Bc True)) s = gval (fold gAnd (rev G) (Bc True)) s"
    using gval_fold_equiv_fold_rev by force
  then show ?thesis
  by (simp add: foldr_conv_fold)
qed

lemma gval_foldr_equiv_gval_fold: "gval (foldr gAnd G (Bc True)) s = gval (fold gAnd G (Bc True)) s"
  by (simp add: gval_fold_equiv_gval_foldr)

lemma gval_fold_cons: "gval (fold gAnd (g # gs) (Bc True)) s = gval g s \<and>\<^sub>? gval (fold gAnd gs (Bc True)) s"
  apply (simp only: apply_guards_fold gval_fold_equiv_gval_foldr)
  by (simp only: foldr.simps comp_def gval_gAnd)

lemma gval_fold_take:
  "max_input_list G < Some a \<Longrightarrow>
   a \<le> length i \<Longrightarrow>
   max_input_list G \<le> Some (length i) \<Longrightarrow>
   gval (fold gAnd G (Bc True)) (join_ir i r) = gval (fold gAnd G (Bc True)) (join_ir (take a i) r)"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons g gs)
  then show ?case
    apply (simp only: gval_fold_cons)
    apply (simp add: max_input_list_cons)
    using gval_take[of g a i r]
    by simp
qed

lemma gval_fold_swap_regs:
  "max_reg_list G = None \<Longrightarrow>
   gval (fold gAnd G (Bc True)) (join_ir i r) = gval (fold gAnd G (Bc True)) (join_ir i r')"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (simp only: gval_fold_equiv_gval_foldr foldr.simps comp_def gval_gAnd)
    by (metis (no_types, lifting) less_eq_option_None max_def max_reg_list_cons no_reg_gval_swap_regs sup_None_2 sup_max)
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

fun enumerate_gexp_strings :: "'a gexp \<Rightarrow> String.literal set" where
  "enumerate_gexp_strings (Bc _) = {}" |
  "enumerate_gexp_strings (Eq a1 a2) = enumerate_aexp_strings a1 \<union> enumerate_aexp_strings a2" |
  "enumerate_gexp_strings (Gt a1 a2) = enumerate_aexp_strings a1 \<union> enumerate_aexp_strings a2" |
  "enumerate_gexp_strings (In v l) = fold (\<lambda>x acc. case x of Num n \<Rightarrow> acc | Str s \<Rightarrow> insert s acc) l {}" |
  "enumerate_gexp_strings (Nor g1 g2) = enumerate_gexp_strings g1 \<union> enumerate_gexp_strings g2"

fun enumerate_gexp_ints :: "'a gexp \<Rightarrow> int set" where
  "enumerate_gexp_ints (Bc _) = {}" |
  "enumerate_gexp_ints (Eq a1 a2) = enumerate_aexp_ints a1 \<union> enumerate_aexp_ints a2" |
  "enumerate_gexp_ints (Gt a1 a2) = enumerate_aexp_ints a1 \<union> enumerate_aexp_ints a2" |
  "enumerate_gexp_ints (In v l) = fold (\<lambda>x acc. case x of Str s \<Rightarrow> acc | Num n \<Rightarrow> insert n acc) l {}" |
  "enumerate_gexp_ints (Nor g1 g2) = enumerate_gexp_ints g1 \<union> enumerate_gexp_ints g2"

definition restricted_once :: "'a \<Rightarrow> 'a gexp list \<Rightarrow> bool" where
  "restricted_once v G = (length (filter (\<lambda>g. gexp_constrains g (V v)) G) = 1)"

definition not_restricted :: "'a \<Rightarrow> 'a gexp list \<Rightarrow> bool" where
  "not_restricted v G = (length (filter (\<lambda>g. gexp_constrains g (V v)) G) = 0)"

lemma restricted_once_cons: "restricted_once v (g#gs) = ((gexp_constrains g (V v) \<and> not_restricted v gs) \<or> ((\<not> gexp_constrains g (V v)) \<and> restricted_once v gs))"
  by (simp add: restricted_once_def not_restricted_def)

lemma not_restricted_cons: "not_restricted v (g#gs) = ((\<not> gexp_constrains g (V v)) \<and> not_restricted v gs)"
  by (simp add: not_restricted_def)

definition enumerate_vars :: "vname gexp \<Rightarrow> vname list" where
  "enumerate_vars g = sorted_list_of_set ((image R (enumerate_gexp_regs g)) \<union> (image I (enumerate_gexp_inputs g)))"
end
