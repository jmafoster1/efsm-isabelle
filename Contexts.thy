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

lemma medial_subset:   "length i = Arity t \<Longrightarrow>
   Arity t = Arity t' \<Longrightarrow>
   set (Guards t') \<subseteq> set (Guards t) \<Longrightarrow>
   can_take_transition t i r \<Longrightarrow>
   can_take_transition t' i r"
  by (simp add: can_take_transition_def can_take_def apply_guards_subset)

definition posterior_separate :: "nat \<Rightarrow> vname gexp list \<Rightarrow> update_function list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> registers option" where
  "posterior_separate a g u i r = (if can_take a g i r then Some (apply_updates u (join_ir i r) r) else None)"

definition posterior :: "transition \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> registers option" where
  "posterior t i r = posterior_separate (Arity t) (Guards t) (Updates t) i r"

definition subsumes :: "transition \<Rightarrow> registers \<Rightarrow> transition \<Rightarrow> bool" where
  "subsumes t2 r t1 = (Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and>
                       (\<forall>i. can_take_transition t1 i r \<longrightarrow> can_take_transition t2 i r) \<and>
                       (\<forall>i. can_take_transition t1 i r \<longrightarrow>
                            apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                       (\<forall>p1 p2 i. posterior_separate (Arity t1) (Guards t1) (Updates t2) i r = Some p2 \<longrightarrow>
                                  posterior_separate (Arity t1) (Guards t1) (Updates t1) i r = Some p1 \<longrightarrow>
                                  (\<forall>P r'. (p1 $ r' = None) \<or> (P (p2 $ r') \<longrightarrow> P (p1 $ r'))))
                      )"

lemma subsumption: 
  "(Label t1 = Label t2 \<and> Arity t1 = Arity t2) \<Longrightarrow>
   (\<forall>i. can_take_transition t1 i r \<longrightarrow> can_take_transition t2 i r) \<Longrightarrow>
   (\<forall>i. can_take_transition t1 i r \<longrightarrow>
        apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<Longrightarrow>
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
  "\<exists>i. can_take_transition t1 i r \<and> apply_outputs (Outputs t1) (join_ir i r) \<noteq> apply_outputs (Outputs t2) (join_ir i r) \<Longrightarrow>
 \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma transition_subsumes_self: "subsumes t c t"
  by (simp add: subsumes_def)

primrec accepting_sequence :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) list \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) list option" where
  "accepting_sequence _ _ r [] obs = Some (rev obs)" |
  "accepting_sequence e s r (a#t) obs = (let
    poss = possible_steps e s r (fst a) (snd a);
    accepting = ffilter (\<lambda>(s', T). accepts e s' (apply_updates (Updates T) (join_ir (snd a) r) r) t) poss in
    case random_member accepting of
    None \<Rightarrow> None |
    Some (s', T) \<Rightarrow> let
      r' = (apply_updates (Updates T) (join_ir (snd a) r) r) in
      accepting_sequence e s' r' t ((T, s', (apply_outputs (Outputs T) (join_ir (snd a) r)), r')#obs)
  )"

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

lemma posterior_sequence_implies_accepting_sequence:
  "posterior_sequence e s d t = Some ca \<Longrightarrow> accepting_sequence e s d t [] \<noteq> None"
  apply (simp add: posterior_sequence_def)
  by (cases "accepting_sequence e s d t []", auto)

lemma accepting_sequence_accepts:
  "accepting_sequence e s r t [] = Some y \<Longrightarrow> accepts e s r t"
proof(induct t arbitrary: r)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a ts)
  then show ?case
    apply (cases a)
      apply simp
      apply (case_tac "random_member
              (ffilter (\<lambda>(s', T). accepts e s' (apply_updates (Updates T) (join_ir b r) r) ts) (possible_steps e s r aa b))")
     apply simp
    using accepts.step random_member_Some by fastforce
qed

lemma posterior_sequence_accepts:
  "posterior_sequence e s d t = Some ca \<longrightarrow> accepts e s d t"
  using posterior_sequence_implies_accepting_sequence[of e s d t ca]
  apply simp
  apply clarify
  apply simp
  using accepting_sequence_accepts
  by auto

lemma anterior_context_accepts:
  "\<exists>c. anterior_context e p = Some c \<Longrightarrow> accepts_trace e p"
  using posterior_sequence_accepts by blast

lemma posterior_sequence_gives_accept:
  "posterior_sequence e s d t \<noteq> None \<Longrightarrow> accepts e s d t"
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

lemma posterior_sequence_none_accepting_sequence_none:
  "(posterior_sequence e s d t = None) = (accepting_sequence e s d t [] = None)"
  apply standard
  using accepting_sequence_posterior_sequence_not_none apply blast
  by (simp add: posterior_sequence_def)

lemma rejects_gives_no_accepting_sequence:
  "rejects e s r t \<Longrightarrow> accepting_sequence e s r t [] = None"
proof(induct t arbitrary: s r)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply (cases a)
    apply simp
    apply (case_tac "random_member
              (ffilter (\<lambda>(s', T). accepts e s' (apply_updates (Updates T) (join_ir b r) r) t) (possible_steps e s r aa b))")
     apply simp
    using accepts.step random_member_Some by fastforce
qed

lemma rejects_gives_no_posterior_sequence:
  "rejects e s d t \<Longrightarrow> posterior_sequence e s d t = None"
  using posterior_sequence_gives_accept by blast

lemma no_accepting_sequence_rejected:
  "accepting_sequence e s d t seq = None \<longrightarrow> rejects e s d t"
proof(induct t arbitrary: s d seq)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply (cases a)
    apply simp
    apply (case_tac "random_member
              (ffilter (\<lambda>(s', T). accepts e s' (apply_updates (Updates T) (join_ir b d) d) t) (possible_steps e s d aa b))")
     apply simp
     apply clarify
     apply (rule accepts.cases)
       apply simp
      apply simp
     apply auto[1]
    apply simp
    apply (case_tac aaa)
    apply clarify
    apply (rule accepts.cases)
      apply simp
     apply simp
    apply clarify
    apply simp
    by (metis (mono_tags, lifting) case_prodD ffmember_filter random_member_Some)
qed

lemma no_posterior_sequence_reject:
  "posterior_sequence e s d t = None \<Longrightarrow> \<not>accepts e s d t"
  apply (simp add: posterior_sequence_none_accepting_sequence_none)
  using no_accepting_sequence_rejected
  by blast

lemma accepts_gives_context:
  "\<forall>s d. accepts e s d t \<longrightarrow> (\<exists>c. posterior_sequence e s d t = Some c)"
  using no_posterior_sequence_reject by blast

lemma accepts_trace_gives_context:
  "accepts_trace e p \<Longrightarrow> (\<exists>c. anterior_context e p = Some c)"
  using accepts_gives_context by auto

lemma accepts_trace_anterior_not_none:
  "accepts_trace e p \<Longrightarrow> anterior_context e p \<noteq> None"
  using accepts_trace_gives_context by blast

lemma no_choice_no_subsumption:   "Label t = Label t' \<Longrightarrow>
   Arity t = Arity t' \<Longrightarrow>
   \<not> choice t t' \<Longrightarrow>
   \<exists>i. can_take_transition t' i c \<Longrightarrow>
  \<not> subsumes t c t'"
  by (meson bad_guards can_take_def can_take_transition_def choice_def)

lemma subsumption_def_alt: "subsumes t1 c t2 = (Label t2 = Label t1 \<and>
    Arity t2 = Arity t1 \<and>
    (\<forall>i. can_take_transition t2 i c \<longrightarrow> can_take_transition t1 i c) \<and>
    (\<forall>i. can_take_transition t2 i c \<longrightarrow> apply_outputs (Outputs t2) (join_ir i c) = apply_outputs (Outputs t1) (join_ir i c)) \<and>
    (\<forall>i. can_take_transition t2 i c \<longrightarrow>
         (\<forall>r' P.
             P (apply_updates (Updates t1) (join_ir i c) c $ r') \<longrightarrow>
             apply_updates (Updates t2) (join_ir i c) c $ r' = None \<or> P (apply_updates (Updates t2) (join_ir i c) c $ r'))))"
  apply (simp add: subsumes_def posterior_separate_def can_take_transition_def[symmetric])
  by blast

lemma subsumes_update_equality:
  "subsumes t1 c t2 \<Longrightarrow> (\<forall>i. can_take_transition t2 i c \<longrightarrow>
         (\<forall>r'.
             ((apply_updates (Updates t1) (join_ir i c) c $ r') = (apply_updates (Updates t2) (join_ir i c) c $ r')) \<or>
             apply_updates (Updates t2) (join_ir i c) c $ r' = None))"
  apply (simp add: subsumption_def_alt)
  apply clarify
  apply (erule_tac x=i in allE)+
  apply simp
  apply (erule_tac x=r' in allE)
  by auto

lemma subsumption_def_alt2: "subsumes t1 c t2 = (Label t2 = Label t1 \<and>
    Arity t2 = Arity t1 \<and>
    (\<forall>i. can_take_transition t2 i c \<longrightarrow> can_take_transition t1 i c) \<and>
    (\<forall>i. can_take_transition t2 i c \<longrightarrow> apply_outputs (Outputs t2) (join_ir i c) = apply_outputs (Outputs t1) (join_ir i c)) \<and>
    (\<forall>i. can_take_transition t2 i c \<longrightarrow>
         (\<forall>r'. ((apply_updates (Updates t1) (join_ir i c) c $ r') = (apply_updates (Updates t2) (join_ir i c) c $ r')) \<or>
             apply_updates (Updates t2) (join_ir i c) c $ r' = None)))"
  apply (simp add: subsumes_def)
  apply standard
   apply (simp add: subsumes_update_equality subsumption)
  by (metis can_take_transition_def option.sel posterior_separate_def)

lemma subsumes_trans:
    assumes p1: "subsumes t1 c t2" and p2: "subsumes t2 c t3"
  shows "subsumes t1 c t3"
  using p1 p2
  apply (simp add: subsumes_def)
  by (metis subsumes_update_equality p1 p2 can_take_transition_def option.distinct(1) option.sel posterior_separate_def)

end


