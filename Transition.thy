theory Transition
imports GExp
begin
section\<open>Transitions\<close>
text\<open>Here we define the transitions which make up EFSMs. As per \cite{foster2018}, each transitions
has a label and an arity and optionally, guards, outputs, and Updates. To implement this, we use
the record type such that each component of the transition can be accessed.\<close>

type_synonym label = String.literal
type_synonym arity = nat
type_synonym guard = "vname gexp"
type_synonym inputs = "value list"
type_synonym outputs = "value option list"
type_synonym output_function = "vname aexp"
type_synonym update_functions = "(nat \<times> vname aexp) list"
type_synonym update_function = "nat \<times> vname aexp"

text_raw\<open>\snip{transitiontype}{1}{2}{%\<close>
record transition =
  Label :: String.literal
  Arity :: nat
  Guards :: "guard list"
  Outputs :: "output_function list"
  Updates :: "update_functions"
text_raw\<open>}%endsnip\<close>

definition same_structure :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "same_structure t1 t2 = (
    Label t1 = Label t2 \<and>
    Arity t1 = Arity t2 \<and>
    length (Outputs t1) = length (Outputs t2)
  )"

definition finfun_as_list :: "('a::linorder \<Rightarrow>f 'b) \<Rightarrow> ('a \<times> 'b) list" where
  "finfun_as_list f = map (\<lambda>x. (x, f $ x)) (finfun_to_list f)"

definition enumerate_inputs :: "transition \<Rightarrow> nat set" where
  "enumerate_inputs t = (\<Union> (set (map enumerate_gexp_inputs (Guards t)))) \<union>
                        (\<Union> (set (map enumerate_aexp_inputs (Outputs t)))) \<union>
                        (\<Union> (set (map (\<lambda>(_, u). enumerate_aexp_inputs u) (Updates t))))"

definition max_input :: "transition \<Rightarrow> nat option" where
  "max_input t = (if enumerate_inputs t = {} then None else Some (Max (enumerate_inputs t)))"

definition total_max_input :: "transition \<Rightarrow> nat" where
  "total_max_input t = (case max_input t of None \<Rightarrow> 0 | Some a \<Rightarrow> a)"

definition enumerate_regs :: "transition \<Rightarrow> nat set" where
  "enumerate_regs t = (\<Union> (set (map GExp.enumerate_regs (Guards t)))) \<union>
                      (\<Union> (set (map AExp.enumerate_regs (Outputs t)))) \<union>
                      (\<Union> (set (map (\<lambda>(_, u). AExp.enumerate_regs u) (Updates t)))) \<union>
                      (\<Union> (set (map (\<lambda>(r, _). AExp.enumerate_regs (V (R r))) (Updates t))))"

definition max_reg :: "transition \<Rightarrow> nat option" where
  "max_reg t = (if enumerate_regs t = {} then None else Some (Max (enumerate_regs t)))"

definition total_max_reg :: "transition \<Rightarrow> nat" where
  "total_max_reg t = (case max_reg t of None \<Rightarrow> 0 | Some a \<Rightarrow> a)"

definition enumerate_ints :: "transition \<Rightarrow> int set" where
  "enumerate_ints t = (\<Union> (set (map enumerate_gexp_ints (Guards t)))) \<union>
                      (\<Union> (set (map enumerate_aexp_ints (Outputs t)))) \<union>
                      (\<Union> (set (map (\<lambda>(_, u). enumerate_aexp_ints u) (Updates t)))) \<union>
                      (\<Union> (set (map (\<lambda>(r, _). enumerate_aexp_ints (V (R r))) (Updates t))))"

definition valid_transition :: "transition \<Rightarrow> bool" where
  "valid_transition t = (case max_input t of None \<Rightarrow> Arity t = 0 | Some x \<Rightarrow> x < Arity t)"

definition can_take :: "nat \<Rightarrow> vname gexp list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> bool" where
  "can_take a g i r = (length i = a \<and> apply_guards g (join_ir i r))"

lemma can_take_empty [simp]: "length i = a \<Longrightarrow> can_take a [] i c"
  by (simp add: can_take_def)

lemma can_take_subset_append:
  assumes "set (Guards t) \<subseteq> set (Guards t')"
  shows "can_take a (Guards t @ Guards t') i c = can_take a (Guards t') i c"
  using assms
  by (simp add: apply_guards_subset_append can_take_def)

definition "can_take_transition t i r = can_take (Arity t) (Guards t) i r"

lemma can_take_transition_empty_guard: "Guards t = [] \<Longrightarrow> \<exists>i. can_take_transition t i c"
  by (simp add: can_take_transition_def can_take_def Ex_list_of_length)

lemma valid_list_can_take: "\<forall>g \<in> set (Guards t). valid g \<Longrightarrow> \<exists>i. can_take_transition t i c"
  by (simp add: can_take_transition_def can_take_def apply_guards_def valid_def Ex_list_of_length)

lemma cant_take_if:
  "\<exists>g \<in> set (Guards t). gval g (join_ir i r) \<noteq> true \<Longrightarrow> \<not> can_take_transition t i r"
  using apply_guards_cons apply_guards_rearrange can_take_def can_take_transition_def by blast

inductive eq_upto_rename :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "Label t1 = Label t2 \<Longrightarrow>
   Arity t1 = Arity t2 \<Longrightarrow>
   bij f \<Longrightarrow>
   image (\<lambda>g1. GExp.rename_regs g1 f) (set g1) = set g2 \<Longrightarrow>
   map (\<lambda>p. AExp.rename_regs p f) o1 = o2 \<Longrightarrow>
   map_of (map (\<lambda>(r, u). (f r, AExp.rename_regs u f)) (Updates t1)) = map_of (Updates t2) \<Longrightarrow>
  eq_upto_rename t1 t2"

end
