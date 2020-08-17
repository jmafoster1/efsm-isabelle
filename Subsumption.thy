section \<open>Contexts and Subsumption\<close>
text\<open>This theory uses contexts to extend the idea of transition subsumption from \cite{lorenzoli2008} to
EFSM transitions with register update functions. The \emph{subsumption in context} relation is the
main contribution of \cite{foster2018}.\<close>

theory Subsumption
  imports
    EFSM GExp
begin

definition posterior_separate :: "nat \<Rightarrow> vname gexp list \<Rightarrow> update_function list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> registers option" where
  "posterior_separate a g u i r = (if can_take a g i r then Some (apply_updates u (join_ir i r) r) else None)"

definition posterior :: "transition \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> registers option" where
  "posterior t i r = posterior_separate (Arity t) (Guards t) (Updates t) i r"

definition subsumes :: "transition \<Rightarrow> registers \<Rightarrow> transition \<Rightarrow> bool" where
  "subsumes t2 r t1 = (Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and>
                       (\<forall>i. can_take_transition t1 i r \<longrightarrow> can_take_transition t2 i r) \<and>
                       (\<forall>i. can_take_transition t1 i r \<longrightarrow>
                            evaluate_outputs t1 i r = evaluate_outputs t2 i r) \<and>
                       (\<forall>p1 p2 i. posterior_separate (Arity t1) (Guards t1) (Updates t2) i r = Some p2 \<longrightarrow>
                                  posterior_separate (Arity t1) (Guards t1) (Updates t1) i r = Some p1 \<longrightarrow>
                                  (\<forall>P r'. (p1 $ r' = None) \<or> (P (p2 $ r') \<longrightarrow> P (p1 $ r'))))
                      )"

lemma transition_subsumes_self: "subsumes t c t"
  by (simp add: subsumes_def)

lemma subsumption:
  "(Label t1 = Label t2 \<and> Arity t1 = Arity t2) \<Longrightarrow>
   (\<forall>i. can_take_transition t1 i r \<longrightarrow> can_take_transition t2 i r) \<Longrightarrow>
   (\<forall>i. can_take_transition t1 i r \<longrightarrow>
        evaluate_outputs t1 i r = evaluate_outputs t2 i r) \<Longrightarrow>

   (\<forall>p1 p2 i. posterior_separate (Arity t1) (Guards t1) (Updates t2) i r = Some p2 \<longrightarrow>
              posterior_separate (Arity t1) (Guards t1) (Updates t1) i r = Some p1 \<longrightarrow>
              (\<forall>P r'. (p1 $ r' = None) \<or> (P (p2 $ r') \<longrightarrow> P (p1 $ r')))) \<Longrightarrow>
   subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma bad_guards:
  "\<exists>i. can_take_transition t1 i r \<and> \<not> can_take_transition t2 i r \<Longrightarrow>
   \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma inconsistent_updates:
  "\<exists>p2 p1. (\<exists>i. posterior_separate (Arity t1) (Guards t1) (Updates t2) i r = Some p2 \<and>
                posterior_separate (Arity t1) (Guards t1) (Updates t1) i r = Some p1) \<and>
           (\<exists>r' P. P (p2 $ r') \<and> (\<exists>y. p1 $ r' = Some y) \<and> \<not> P (p1 $ r')) \<Longrightarrow>

    \<not> subsumes t2 r t1"
  by (metis (no_types, hide_lams) option.simps(3) subsumes_def)

lemma bad_outputs:
  "\<exists>i. can_take_transition t1 i r \<and> evaluate_outputs t1 i r \<noteq> evaluate_outputs t2 i r \<Longrightarrow>
   \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma no_choice_no_subsumption: "Label t = Label t' \<Longrightarrow>
   Arity t = Arity t' \<Longrightarrow>
   \<not> choice t t' \<Longrightarrow>
   \<exists>i. can_take_transition t' i c \<Longrightarrow>
  \<not> subsumes t c t'"
  by (meson bad_guards can_take_def can_take_transition_def choice_def)

lemma subsumption_def_alt: "subsumes t1 c t2 = (Label t2 = Label t1 \<and>
    Arity t2 = Arity t1 \<and>
    (\<forall>i. can_take_transition t2 i c \<longrightarrow> can_take_transition t1 i c) \<and>
    (\<forall>i. can_take_transition t2 i c \<longrightarrow> evaluate_outputs t2 i c = evaluate_outputs t1 i c) \<and>
    (\<forall>i. can_take_transition t2 i c \<longrightarrow>
         (\<forall>r' P.
             P (evaluate_updates t1 i c $ r') \<longrightarrow>
             evaluate_updates t2 i c $ r' = None \<or> P (evaluate_updates t2 i c $ r'))))"
  apply (simp add: subsumes_def posterior_separate_def can_take_transition_def[symmetric])
  by blast

lemma subsumes_update_equality:
  "subsumes t1 c t2 \<Longrightarrow> (\<forall>i. can_take_transition t2 i c \<longrightarrow>
         (\<forall>r'.
             ((evaluate_updates t1 i c $ r') = (evaluate_updates t2 i c $ r')) \<or>
             evaluate_updates t2 i c $ r' = None))"
  apply (simp add: subsumption_def_alt)
  apply clarify
  apply (erule_tac x=i in allE)+
  apply simp
  apply (erule_tac x=r' in allE)
  by auto

text_raw\<open>\snip{subsumptionPreorder}{1}{2}{%\<close>
lemma subsumes_reflexive: "subsumes t c t"
  by (simp add: subsumes_def)

lemma subsumption_transitive:
  assumes p1: "subsumes t1 c t2"
      and p2: "subsumes t2 c t3"
  shows "subsumes t1 c t3"
  using p1 p2
  apply (simp add: subsumes_def)
  by (metis subsumes_update_equality p1 p2 can_take_transition_def option.distinct(1) option.sel posterior_separate_def)
text_raw\<open>}%endsnip\<close>

subsection\<open>Direct Subsumption\<close>
text\<open>When merging EFSM transitions, one must \emph{account for} the behaviour of the other. The
\emph{subsumption in context} relation formalises the intuition that, in certain contexts, a
transition $t_2$ reproduces the behaviour of, and updates the data state in a manner consistent
with, another transition $t_1$, meaning that $t_2$ can be used in place of $t_1$ with no observable
difference in behaviour.

The subsumption in context relation requires us to supply a context in which to test subsumption,
but there is a problem when we try to apply this to inference: Which context should we use? The
\emph{direct subsumption} relation works at EFSM level to determine when and whether one transition
is able to account for the behaviour of another such that we can use one in place of another without
adversely effecting observable behaviour.\<close>

definition directly_subsumes :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "directly_subsumes e1 e2 s1 s2 t1 t2 \<equiv> (\<exists>c. subsumes t1 c t2) \<and>
                                         (\<forall>c1 c2. (obtainable s1 c1 e1 \<and> obtainable s2 c2 e2) \<longrightarrow> subsumes t1 c2 t2)"

lemma directly_subsumes_self: "directly_subsumes e1 e2 s s' t t"
  apply (simp add: directly_subsumes_def)
  by (simp add: transition_subsumes_self)

lemma subsumes_in_all_contexts_directly_subsumes:
  "(\<And>c. subsumes t2 c t1) \<Longrightarrow> directly_subsumes e1 e2 s s' t2 t1"
  by (simp add: directly_subsumes_def)

lemma gets_us_to_and_not_subsumes:
  "(\<exists>c1. obtainable s c1 e1) \<and> (\<exists>c2. obtainable s' c2 e2 \<and> \<not> subsumes t1 c2 t2) \<Longrightarrow>
   \<not> directly_subsumes e1 e2 s s' t1 t2"
  by (simp add: directly_subsumes_def)

lemma cant_directly_subsume:
  "(\<And>c. \<not> subsumes t c t') \<Longrightarrow> \<not> directly_subsumes m m' s s' t t'"
  by (simp add: directly_subsumes_def)

end
