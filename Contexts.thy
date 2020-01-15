subsection \<open>Contexts\<close>
text\<open>
This theory defines contexts as a way of relating possible constraints on register values to
observable output. We then use contexts to extend the idea of transition subsumption to EFSM
transitions with register update functions.
\<close>

theory Contexts
  imports
    EFSM GExp
begin

definition can_take :: "nat \<Rightarrow> gexp list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> bool" where
  "can_take a g i r = (length i = a \<and> apply_guards g i r)"

lemma can_take_empty [simp]: "length i = a \<Longrightarrow> can_take a [] i c"
  by (simp add: can_take_def apply_guards_def)

lemma can_take_subset_append: "set (Guard t) \<subseteq> set (Guard t') \<Longrightarrow> can_take a (Guard t @ Guard t') i c = can_take a (Guard t') i c"
  by (simp add: apply_guards_subset_append can_take_def)

definition "can_take_transition t i r = can_take (Arity t) (Guard t) i r"

lemma can_take_transition_empty_guard: "Guard t = [] \<Longrightarrow> \<exists>i. can_take_transition t i c"
  by (simp add: can_take_transition_def can_take_def Ex_list_of_length apply_guards_def)

lemma valid_list_can_take: "\<forall>g \<in> set (Guard t). valid g \<Longrightarrow> \<exists>i. can_take_transition t i c"
  by (simp add: can_take_transition_def can_take_def apply_guards_def valid_def valid_o_def apply_guards_o_def Ex_list_of_length)

lemma cant_take_if: "\<exists>g \<in> set (Guard t). gval g i r \<noteq> true \<Longrightarrow> \<not> can_take_transition t i r"
  by (simp add: can_take_transition_def can_take_def not_true_not_apply_guards)

lemma subset_map: "set g \<subseteq> set g' \<Longrightarrow> set (map f g) \<subseteq> set (map f g')"
  by auto

lemma medial_subset:
  "length i = Arity t \<Longrightarrow>
   Arity t = Arity t' \<Longrightarrow>
   set (Guard t') \<subseteq> set (Guard t) \<Longrightarrow>
   can_take_transition t i r \<Longrightarrow>
   can_take_transition t' i r"
  apply (simp add: can_take_transition_def can_take_def apply_guards_def)
  by (metis subset_map apply_guards_o_subset)

definition posterior_separate :: "nat \<Rightarrow> gexp list \<Rightarrow> update_function list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> registers option" where
  "posterior_separate a g u i r = (if can_take a g i r then Some (apply_updates u i r r) else None)"

definition posterior :: "transition \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> registers option" where
  "posterior t i r = posterior_separate (Arity t) (Guard t) (Updates t) i r"

definition subsumes :: "transition \<Rightarrow> registers \<Rightarrow> transition \<Rightarrow> bool" where
  "subsumes t2 r t1 = (Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and>
                       (\<forall>i. can_take_transition t1 i r \<longrightarrow> can_take_transition t2 i r) \<and>
                       (\<forall>i. can_take_transition t1 i r \<longrightarrow>
                            apply_outputs (Outputs t1) i r = apply_outputs (Outputs t2) i r) \<and>
                       (\<forall>p1 p2 i. posterior_separate (Arity t1) (Guard t1) (Updates t2) i r = Some p2 \<longrightarrow>
                                  posterior_separate (Arity t1) (Guard t1) (Updates t1) i r = Some p1 \<longrightarrow>
                                  (\<forall>P r'. (p1 $ r' = None) \<or> (P (p2 $ r') \<longrightarrow> P (p1 $ r'))))
                      )"

lemma subsumption: 
  "(Label t1 = Label t2 \<and> Arity t1 = Arity t2) \<Longrightarrow>
   (\<forall>i. can_take_transition t1 i r \<longrightarrow> can_take_transition t2 i r) \<Longrightarrow>
   (\<forall>i. can_take_transition t1 i r \<longrightarrow>
        apply_outputs (Outputs t1) i r = apply_outputs (Outputs t2) i r) \<Longrightarrow>
   (\<forall>p1 p2 i. posterior_separate (Arity t1) (Guard t1) (Updates t2) i r = Some p2 \<longrightarrow>
              posterior_separate (Arity t1) (Guard t1) (Updates t1) i r = Some p1 \<longrightarrow>
              (\<forall>P r'. (p1 $ r' = None) \<or> (P (p2 $ r') \<longrightarrow> P (p1 $ r')))) \<Longrightarrow>
   subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma bad_guards:
  "\<exists>i. can_take_transition t1 i r \<and> \<not> can_take_transition t2 i r \<Longrightarrow>
   \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma inconsistent_updates:
  "\<exists>p2 p1. (\<exists>i. posterior_separate (Arity t1) (Guard t1) (Updates t2) i r = Some p2 \<and>
                posterior_separate (Arity t1) (Guard t1) (Updates t1) i r = Some p1) \<and>
           (\<exists>r' P. P (p2 $ r') \<and> (\<exists>y. p1 $ r' = Some y) \<and> \<not> P (p1 $ r')) \<Longrightarrow>
    \<not> subsumes t2 r t1"
  by (metis (no_types, hide_lams) option.simps(3) subsumes_def)

lemma bad_outputs: "\<exists>i. can_take_transition t1 i r \<and> apply_outputs (Outputs t1) i r \<noteq> apply_outputs (Outputs t2) i r \<Longrightarrow>
 \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma transition_subsumes_self: "subsumes t c t"
  by (simp add: subsumes_def)

definition posterior_sequence :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> registers option" where
  "posterior_sequence e s r t = (case accepting_sequence e s r t [] of
    None \<Rightarrow> None |
    Some seq \<Rightarrow>
      if seq = [] then
        Some r
      else let
        (_, _, _, r') = last seq in Some r'
  )"

abbreviation anterior_context :: "transition_matrix \<Rightarrow> trace \<Rightarrow> registers option" where
  "anterior_context e t \<equiv> posterior_sequence e 0 <> t"

lemma anterior_context_empty: "anterior_context e [] = Some <>"
  by (simp add: posterior_sequence_def)

lemma posterior_sequence_implies_accepting_sequence: "posterior_sequence e s d t = Some ca \<Longrightarrow> accepting_sequence e s d t [] \<noteq> None"
  apply (simp add: posterior_sequence_def)
  by (cases "accepting_sequence e s d t []", auto)

lemma accepting_sequence_accepts: "accepting_sequence e s d t [] = Some y \<Longrightarrow> accepts e s d t"
proof(induct t arbitrary: d)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply (simp add: Let_def)
    apply (case_tac "ffilter (\<lambda>(s', T). accepts e s' (apply_updates (Updates T) (snd a) d d) t)
         (possible_steps e s d (fst a) (snd a)) = {||}")
     apply simp
    apply simp
    apply (case_tac "SOME x.
             x |\<in>| possible_steps e s d (fst a) (snd a) \<and>
             (case x of (s', T) \<Rightarrow> accepts e s' (apply_updates (Updates T) (snd a) d d) t)")
    apply (simp add: Let_def)
    apply (case_tac a)
    apply simp
    apply (rule accepts.step)
    by fastforce
qed

lemma posterior_sequence_accepts: "posterior_sequence e s d t = Some ca \<longrightarrow> accepts e s d t"
  using posterior_sequence_implies_accepting_sequence[of e s d t ca]
  apply simp
  apply clarify
  apply simp
  using accepting_sequence_accepts
  by auto

lemma anterior_context_accepts: "\<exists>c. anterior_context e p = Some c \<Longrightarrow> accepts_trace e p"
  using posterior_sequence_accepts by blast

lemma posterior_sequence_gives_accept: "posterior_sequence e s d t \<noteq> None \<Longrightarrow> accepts e s d t"
  using option.discI posterior_sequence_accepts by auto

lemma accepting_sequence_posterior_sequence_not_none:
  "accepting_sequence e s d t [] \<noteq> None \<Longrightarrow>
   posterior_sequence e s d t \<noteq> None"
  apply (simp add: posterior_sequence_def)
  apply (case_tac "accepting_sequence e s d t []")
   apply simp
  apply simp
  apply (case_tac "last a")
  by simp

lemma posterior_sequence_none_accepting_sequence_none: "(posterior_sequence e s d t = None) = (accepting_sequence e s d t [] = None)"
  apply standard
  using accepting_sequence_posterior_sequence_not_none apply blast
  by (simp add: posterior_sequence_def)

lemma rejects_gives_no_accepting_sequence: "\<forall>s d. \<not>accepts e s d t \<longrightarrow> accepting_sequence e s d t [] = None"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply (cases a)
    apply (simp only: trace_reject_2)
    apply (simp add: Let_def)
    apply (case_tac "SOME x.
                x |\<in>| possible_steps e s d aa b \<and>
                (case x of (s', T) \<Rightarrow> accepts e s' (apply_updates (Updates T) b d d) t)")
    apply simp
    by fastforce
qed

lemma rejects_gives_no_posterior_sequence: "\<not>accepts e s d t \<Longrightarrow> posterior_sequence e s d t = None"
  by (simp add: posterior_sequence_def rejects_gives_no_accepting_sequence)

lemma no_accepting_sequence_rejected: "\<forall>d s seq. accepting_sequence e s d t seq = None \<longrightarrow> \<not> accepts e s d t"
proof(induct t)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply (rule accepts.cases)
      apply simp
     apply simp
    apply clarify
    apply (simp add: Let_def)
    apply (case_tac "ffilter (\<lambda>(s', T). accepts e s' (apply_updates (Updates T) i da da) t) (possible_steps e sa da l i) = {||}")
     apply auto[1]
    apply simp
    apply (case_tac "SOME x. x |\<in>| possible_steps e sa da l i \<and> (case x of (s', T) \<Rightarrow> accepts e s' (apply_updates (Updates T) i da da) t)")
    apply (simp add: Let_def)
    by (metis (no_types, lifting) case_prodD case_prodI someI_ex)
qed

lemma no_posterior_sequence_reject: "posterior_sequence e s d t = None \<Longrightarrow> \<not>accepts e s d t"
  apply (simp add: posterior_sequence_none_accepting_sequence_none)
  using no_accepting_sequence_rejected
  by blast

lemma accepts_gives_context: "\<forall>s d. accepts e s d t \<longrightarrow> (\<exists>c. posterior_sequence e s d t = Some c)"
  using no_posterior_sequence_reject by blast

lemma accepts_trace_gives_context: "accepts_trace e p \<Longrightarrow> (\<exists>c. anterior_context e p = Some c)"
  using accepts_gives_context by auto

lemma accepts_trace_anterior_not_none: "accepts_trace e p \<Longrightarrow> anterior_context e p \<noteq> None"
  using accepts_trace_gives_context by blast

lemma no_choice_no_subsumption:
  "Label t = Label t' \<Longrightarrow>
   Arity t = Arity t' \<Longrightarrow>
   \<not> choice t t' \<Longrightarrow>
   \<exists>i. can_take_transition t' i c \<Longrightarrow>
  \<not> subsumes t c t'"
  by (meson bad_guards can_take_def can_take_transition_def choice_def)
end