subsection \<open>Extended Finite State Machines\<close>
text\<open>
This theory defines extended finite state machines. Each EFSM takes a type variable which represents
$S$. This is a slight devaition from the definition presented in \cite{foster2018} as this
type variable may be of an infinite type such as integers, however the intended use is for custom
finite types. See the examples for details.
\<close>

theory EFSM
  imports "HOL-Library.FSet" Transition FSet_Utils
begin

declare One_nat_def [simp del]

type_synonym cfstate = nat
type_synonym inputs = "value list"
type_synonym outputs = "value option list"

type_synonym event = "(label \<times> inputs)"
type_synonym trace = "event list"
type_synonym observation = "outputs list"
type_synonym transition_matrix = "((cfstate \<times> cfstate) \<times> transition) fset"

no_notation relcomp (infixr "O" 75) and comp (infixl "o" 55)

(* An execution represents a run of the software and has the form [(label, inputs, outputs)]*)
type_synonym execution = "(label \<times> value list \<times> value list) list"
type_synonym log = "execution list"

definition Str :: "string \<Rightarrow> value" where
  "Str s \<equiv> value.Str (String.implode s)"

lemma str_not_num:
  "Str s \<noteq> Num x1"
  by (simp add: Str_def)

definition S :: "transition_matrix \<Rightarrow> nat fset" where
  "S m = (fimage (\<lambda>((s, s'), t). s) m) |\<union>| fimage (\<lambda>((s, s'), t). s') m"

lemma S_ffUnion:
  "S e = ffUnion (fimage (\<lambda>((s, s'), _). {|s, s'|}) e)"
  unfolding S_def
  by(induct e, auto)

definition apply_outputs :: "'a aexp list \<Rightarrow> 'a datastate \<Rightarrow> value option list" where
  "apply_outputs p s = map (\<lambda>p. aval p s) p"

lemma apply_outputs_nth:
  "i < length p \<Longrightarrow> apply_outputs p s ! i = aval (p ! i) s"
  by (simp add: apply_outputs_def)

lemmas apply_outputs = datastate apply_outputs_def

lemma apply_outputs_empty [simp]:
  "apply_outputs [] s = []"
  by (simp add: apply_outputs_def)

lemma apply_outputs_preserves_length:
  "length (apply_outputs p s) = length p"
  by (simp add: apply_outputs_def)

lemma apply_outputs_literal:
  assumes "P ! r = L v"
      and "r < length P"
    shows "apply_outputs P s ! r = Some v"
  by (simp add: assms apply_outputs_nth)

lemma apply_outputs_register:
  assumes "r < length P"
  shows "apply_outputs (list_update P r (V (R p))) (join_ir i c) ! r = c $ p"
  by (metis apply_outputs_nth assms aval.simps(2) join_ir_R length_list_update nth_list_update_eq)

lemma apply_outputs_unupdated:
  assumes "ia \<noteq> r"
      and "ia < length P"
    shows "apply_outputs P j ! ia = apply_outputs (list_update P r v)j ! ia"
  by (metis apply_outputs_nth assms(1) assms(2) length_list_update nth_list_update_neq)

definition choice :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice t t' = (\<exists> i r. apply_guards (Guard t) (join_ir i r) \<and> apply_guards (Guard t') (join_ir i r))"

definition choice_alt :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice_alt t t' = (\<exists> i r. apply_guards (Guard t@Guard t') (join_ir i r))"

lemma choice_alt:
  "choice t t' = choice_alt t t'"
  by (simp add: choice_def choice_alt_def apply_guards_append)

lemma choice_symmetry:
  "choice x y = choice y x"
  using choice_def by auto

primrec apply_updates :: "update_function list \<Rightarrow> vname datastate \<Rightarrow> registers \<Rightarrow> registers" where
  "apply_updates [] _ new = new" |
  "apply_updates (h#t) old new = (apply_updates t old new)(fst h $:= aval (snd h) old)"

lemma apply_updates_foldr:
  "apply_updates u old new = foldr (\<lambda>h r. r(fst h $:= aval (snd h) old)) u new"
  by (induct u, auto)

lemma r_not_updated_stays_the_same:
  assumes "r \<notin> fst ` set U"
  shows "apply_updates U c d $ r = d $ r"
  using assms
  by (induct U, auto)

definition possible_steps :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (cfstate \<times> transition) fset" where
  "possible_steps e s r l i = fimage (\<lambda>((origin, dest), t). (dest, t)) (ffilter (\<lambda>((origin, dest), t). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guard t) (join_ir i r)) e)"

lemma possible_steps_alt_aux:
  "possible_steps e s r l i = {|(d, t)|} \<Longrightarrow>
       ffilter (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (join_ir i r)) e = {|((s, d), t)|}"
proof(induct e)
  case empty
  then show ?case
    by (simp add: fempty_not_finsert possible_steps_def)
next
  case (insert x e)
  then show ?case
    apply (case_tac x, case_tac a)
    apply (simp add: possible_steps_def)
    apply (simp add: ffilter_finsert)
    apply (case_tac "aa = s \<and> Label b = l \<and> length i = Arity b \<and> apply_guards (Guard b) (join_ir i r)")
    by auto
qed

lemma possible_steps_alt:
  "(possible_steps e s r l i = {|(d, t)|}) = (ffilter
     (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (join_ir i r))
     e = {|((s, d), t)|})"
  apply standard
   apply (simp add: possible_steps_alt_aux)
  by (simp add: possible_steps_def)

lemma possible_steps_singleton:
  "(possible_steps e s r l i = {|(d, t)|}) =
    ({((origin, dest), t) \<in> fset e. origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (join_ir i r)} = {((s, d), t)})"
  apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def)
  by fast

lemma possible_steps_apply_guards:
  "possible_steps e s r l i = {|(s', t)|} \<Longrightarrow> apply_guards (Guard t) (join_ir i r)"
  apply (simp add: possible_steps_singleton)
  by auto

lemma possible_steps_empty:
  "(possible_steps e s r l i = {||}) = (\<forall>((origin, dest), t) \<in> fset e. origin \<noteq> s \<or> Label t \<noteq> l \<or> \<not> can_take_transition t i r)"
  apply (simp add: can_take_transition_def can_take_def)
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def)
  by auto

lemma singleton_dest:
  "fis_singleton (possible_steps e s r aa b) \<Longrightarrow>
       fthe_elem (possible_steps e s r aa b) = (baa, aba) \<Longrightarrow>
       ((s, baa), aba) |\<in>| e"
  apply (simp add: fis_singleton_def fthe_elem_def singleton_equiv)
  apply (simp add: possible_steps_def fmember_def)
  by auto

inductive accepts :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "accepts e s d []" |
  step: "(s', t) |\<in>| possible_steps e s r l i \<Longrightarrow>
         accepts e s' (apply_updates (Updates t) (join_ir i r) r) ts \<Longrightarrow>
         accepts e s r ((l, i)#ts)"

abbreviation "rejects e s d t \<equiv> \<not> accepts e s d t"

abbreviation accepts_trace :: "transition_matrix \<Rightarrow> trace \<Rightarrow> bool" where
  "accepts_trace e t \<equiv> accepts e 0 <> t"

lemma no_possible_steps_rejects:
  "possible_steps e s d l i = {||} \<Longrightarrow> rejects e s d ((l, i)#t)"
  using accepts.cases by blast

lemma accepts_step_equiv:
  "accepts e s d ((l, i)#t) = (\<exists>(s', T) |\<in>| possible_steps e s d l i. accepts e s' (apply_updates (Updates T) (join_ir i d) d) t)"
  apply standard
   apply (rule accepts.cases, simp)
    apply simp
   apply auto[1]
  using accepts.step by blast

fun accepts_prim :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  "accepts_prim e s d [] = True" |
  "accepts_prim e s d ((l, i)#t) = (
    let poss_steps = possible_steps e s d l i in
    (\<exists>(s', T) |\<in>| poss_steps. accepts_prim e s' (apply_updates (Updates T) (join_ir i d) d) t)
  )"

lemma accepts_prim:
  "accepts e s r t = accepts_prim e s r t"
proof(induct t arbitrary: r s)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons h t)
  then show ?case
    apply (cases h)
    apply simp
    apply standard
     apply (rule accepts.cases, simp)
      apply simp
     apply auto[1]
    using accepts.step by blast
qed

lemma accepts_single_possible_step:
  assumes "possible_steps e s d l i = {|(s', t)|}"
      and "accepts e s' (apply_updates (Updates t) (join_ir i d) d) trace"
    shows "accepts e s d ((l, i)#trace)"
  apply (rule accepts.step[of s' t])
  using assms by auto

lemma accepts_single_possible_step_atomic:
  assumes "possible_steps e s d (fst h) (snd h) = {|(s', t)|}"
      and "accepts e s' (apply_updates (Updates t) (join_ir (snd h) d) d) trace"
    shows "accepts e s d (h#trace)"
  by (metis accepts_single_possible_step assms(1) assms(2) prod.collapse)

lemma accepts_must_be_possible_step:
  "accepts e s r (h # t) \<Longrightarrow> \<exists>aa ba. (aa, ba) |\<in>| possible_steps e s r (fst h) (snd h)"
  using accepts_step_equiv by fastforce

inductive input_simulation :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "input_simulation e1 s1 r1 e2 s2 r2 []" |
  step: "\<forall>(s1', t1) |\<in>| possible_steps e1 s1 r1 l i.
           \<exists>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i.
            input_simulation e1 s1' (apply_updates (Updates t1) (join_ir i r1) r1) e2 s2' (apply_updates (Updates t2) (join_ir i r2) r2) es \<Longrightarrow>
         input_simulation e1 s1 r1 e2 s2 r2 ((l, i)#es)"

lemma input_simulation_induct:
"(\<And>l i t. input_simulation e1 s1 r1 e2 s2 r2 t \<Longrightarrow> input_simulation e1 s1 r1 e2 s2 r2 ((l, i) # t)) \<Longrightarrow>
input_simulation e1 s1 r1 e2 s2 r2 t"
  using input_simulation.base by (induct t, auto)

lemma input_simulation_acceptance:
"input_simulation e1 s1 r1 e2 s2 r2 t \<Longrightarrow> accepts e1 s1 r1 t \<Longrightarrow> accepts e2 s2 r2 t"
proof(induct t arbitrary: s1 r1 s2 r2)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply (cases a, clarify)
    apply simp
    apply (rule input_simulation.cases)
       apply simp
      apply simp
    apply (simp add: no_possible_steps_rejects)
    apply clarify
    apply simp
    apply (simp add: accepts_step_equiv[of e1])
    apply clarify
    apply (erule_tac x="(aa, b)" in fBallE)
     apply simp
     apply clarify
    subgoal for l i s1' t1 s2' t2
      apply (rule accepts.step[of s2' t2])
      by auto
    by simp
qed

definition input_simulates :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "input_simulates e1 e2 \<equiv> \<forall>t. input_simulation e1 0 <> e2 0 <> t"

lemma input_simulates_induct:
"(\<And>l i t. input_simulation e1 0 <> e2 0 <> t \<Longrightarrow> input_simulation e1 0 <> e2 0 <> ((l, i) # t)) \<Longrightarrow>
input_simulates e1 e2"
  using input_simulates_def input_simulation_induct by blast

lemma input_simulates_accepts_trace:
  "input_simulates e1 e2 \<Longrightarrow> accepts_trace e1 t \<Longrightarrow> accepts_trace e2 t"
  apply (simp add: input_simulates_def)
  using input_simulation_acceptance by blast

definition random_member :: "'a fset \<Rightarrow> 'a option" where
  "random_member f = (if f = {||} then None else Some (Eps (\<lambda>x. x |\<in>| f)))"

lemma random_member_singleton [simp]:
  "random_member {|a|} = Some a"
  by (simp add: random_member_def)

definition step :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) option" where
  "step e s r l i = (case random_member (possible_steps e s r l i) of
      None \<Rightarrow> None |
      Some (s', t) \<Rightarrow>  Some (t, s', apply_outputs (Outputs t) (join_ir i r), apply_updates (Updates t) (join_ir i r) r)
  )"

lemma step_some:
  "possibilities = (possible_steps e s r l i) \<Longrightarrow>
   random_member possibilities = Some (s', t) \<Longrightarrow>
   apply_outputs (Outputs t) (join_ir i r) = p \<Longrightarrow>
   apply_updates (Updates t) (join_ir i r) r = r' \<Longrightarrow>
   step e s r l i = Some (t, s', p, r')"
  by (simp add: step_def)

lemma no_possible_steps_1:
  "possible_steps e s r l i = {||} \<Longrightarrow> step e s r l i = None"
  by (simp add: step_def random_member_def)

primrec observe_all :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (transition \<times> nat \<times> outputs \<times> registers) list" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r (h#t)  =
    (case (step e s r (fst h) (snd h)) of
      (Some (transition, s', outputs, updated)) \<Rightarrow> (((transition, s', outputs, updated)#(observe_all e s' updated t))) |
      _ \<Rightarrow> []
    )"

definition state :: "(transition \<times> nat \<times> outputs \<times> vname datastate) \<Rightarrow> nat" where
  "state x \<equiv> fst (snd x)"

definition observe_trace :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where
  "observe_trace e s r t \<equiv> map (\<lambda>(t,x,y,z). y) (observe_all e s r t)"

lemma observe_trace_empty [simp]:
  "observe_trace e s r [] = []"
  by (simp add: observe_trace_def)

lemma observe_trace_step:

  "step e s r (fst h) (snd h) = Some (t, s', p, r') \<Longrightarrow>
   observe_trace e s' r' es = obs \<Longrightarrow>
   observe_trace e s r (h#es) = p#obs"
  by (simp add: observe_trace_def)

lemma observe_trace_possible_step:
  "possible_steps e s r (fst h) (snd h) = {|(s', t)|} \<Longrightarrow>
   apply_outputs (Outputs t) (join_ir (snd h) r) = p \<Longrightarrow>
   apply_updates (Updates t) (join_ir (snd h) r) r = r' \<Longrightarrow>
   observe_trace e s' r' es = obs \<Longrightarrow>
   observe_trace e s r (h#es) = p#obs"
  apply (rule observe_trace_step)
   apply (simp add: step_def random_member_def)
  by simp

lemma observe_trace_no_possible_step:
  "possible_steps e s r (fst h) (snd h) = {||} \<Longrightarrow>
   observe_trace e s r (h#es) = []"
  by (simp add: observe_trace_def step_def random_member_def)

definition observably_equivalent :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> trace \<Rightarrow> bool" where
  "observably_equivalent e1 e2 t = ((observe_trace e1 0 <> t) = (observe_trace e2 0 <> t))"

lemma observe_trace_no_possible_steps:
  "possible_steps e1 s1 r1 (fst h) (snd h) = {||} \<Longrightarrow>
   possible_steps e2 s2 r2 (fst h) (snd h) = {||} \<Longrightarrow>
   (observe_trace e1 s1 r1 (h#t)) = (observe_trace e2 s2 r2 (h#t))"
  by (simp add: observe_trace_def step_def random_member_def)

lemma observe_trace_one_possible_step:
  "possible_steps e1 s1 r (fst h) (snd h) = {|(s1', t1)|} \<Longrightarrow>
   possible_steps e2 s2 r (fst h) (snd h) = {|(s2', t2)|} \<Longrightarrow>
   apply_outputs (Outputs t1) (join_ir (snd h) r) = apply_outputs (Outputs t2) (join_ir (snd h) r) \<Longrightarrow>
   apply_updates (Updates t1) (join_ir (snd h) r) r = r' \<Longrightarrow>
   apply_updates (Updates t2) (join_ir (snd h) r) r = r' \<Longrightarrow>
   (observe_trace e1 s1' r' t) = (observe_trace e2 s2' r' t) \<Longrightarrow>
   (observe_trace e1 s1 r (h#t)) = (observe_trace e2 s2 r (h#t))"
  by (simp add: observe_trace_def step_def)

lemma observably_equivalent_no_possible_step:

  "possible_steps e1 s1 r1 (fst h) (snd h) = {||} \<Longrightarrow>
   possible_steps e2 s2 r2 (fst h) (snd h) = {||} \<Longrightarrow>
   observe_trace e1 s1 r1 (h#t) = observe_trace e2 s2 r2 (h#t)"
  by (simp add: observe_trace_no_possible_step)

lemma observably_equivalent_reflexive:
  "observably_equivalent e1 e1 t"
  by (simp add: observably_equivalent_def)

lemma observably_equivalent_symmetric:
  "observably_equivalent e1 e2 t = observably_equivalent e2 e1 t"
  using observably_equivalent_def by auto

lemma observably_equivalent_transitive:
  "observably_equivalent e1 e2 t \<Longrightarrow>
   observably_equivalent e2 e3 t \<Longrightarrow>
   observably_equivalent e1 e3 t"
  by (simp add: observably_equivalent_def)

lemma observe_trace_preserves_length:
  "length (observe_all e s r t) = length (observe_trace e s r t)"
  by (simp add: observe_trace_def)

lemma length_observation_leq_length_trace:
  "\<And>s r. length (observe_all e s r t) \<le> length t"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    apply (case_tac "step e s r (fst a) (snd a)")
    by auto
qed

lemma accepts_possible_steps_not_empty:
  "accepts e s d (h#t) \<Longrightarrow> possible_steps e s d (fst h) (snd h) \<noteq> {||}"
  apply (rule accepts.cases)
  by auto

lemma accepts_must_be_step:
  "accepts e s d (h#ts) \<Longrightarrow> \<exists>t s' p d'. step e s d (fst h) (snd h) = Some (t, s', p, d')"
  apply (cases h)
  apply (simp add: accepts_step_equiv step_def)
  apply clarify
  apply (case_tac "(possible_steps e s d a b)")
   apply (simp add: random_member_def)
  apply (simp add: random_member_def)
  apply (case_tac "SOME xa. xa = x \<or> xa |\<in>| S'")
  by simp

lemma accepts_cons_step:
  "accepts e s r (h # t) \<Longrightarrow> step e s r (fst h) (snd h) \<noteq>  None"
  by (simp add: accepts_must_be_step)

lemma no_step_none:
  "step e s r aa ba = None \<Longrightarrow> rejects e s r ((aa, ba) # p)"
  using accepts_cons_step by fastforce

lemma step_none_rejects:
  "step e s d (fst h) (snd h) = None \<Longrightarrow> rejects e s d (h#t)"
  using no_step_none surjective_pairing by fastforce

lemma possible_steps_not_empty_iff:
  "step e s d a b \<noteq> None \<Longrightarrow>
   \<exists>aa ba. (aa, ba) |\<in>| possible_steps e s d a b"
  apply (simp add: step_def)
  apply (case_tac "possible_steps e s d a b")
   apply (simp add: random_member_def)
  by auto

lemma trace_reject:
  "(rejects e s d ((a, b)#t)) = (possible_steps e s d a b = {||} \<or> (\<forall>(s', T) |\<in>| possible_steps e s d a b. rejects e s' (apply_updates (Updates T) (join_ir b d) d) t))"
  using accepts_prim by fastforce

lemma trace_reject_no_possible_steps_atomic:
  "possible_steps e s d (fst a) (snd a) = {||} \<Longrightarrow> rejects e s d (a#t)"
  using accepts_possible_steps_not_empty by auto

lemma trace_reject_later:
  "\<forall>(s', T) |\<in>| possible_steps e s d a b. rejects e s' (apply_updates (Updates T) (join_ir b d) d) t \<Longrightarrow> rejects e s d ((a, b)#t)"
  using trace_reject by auto

lemma rejects_prefix_all_s_d:
  "rejects e s d t \<longrightarrow> rejects e s d (t @ t')"
proof(induct t arbitrary: s d)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply (cases a)
    apply (simp add: trace_reject)
    by blast
qed

lemma rejects_prefix:
  "rejects e s d t \<Longrightarrow> rejects e s d (t @ t')"
  by (simp add: rejects_prefix_all_s_d)

lemma prefix_closure:
  "accepts e s d (t@t') \<Longrightarrow> accepts e s d t"
  using rejects_prefix_all_s_d by blast

lemma accepts_head:
  "accepts e s d (h#t) \<Longrightarrow> accepts e s d [h]"
  by (metis accepts.simps accepts_must_be_possible_step prod.exhaust_sel)

inductive gets_us_to :: "cfstate \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "s = target \<Longrightarrow> gets_us_to target _ s _ []" |
  step_some: "\<exists>(s', T) |\<in>| possible_steps e s d (fst h) (snd h). gets_us_to target e s' (apply_updates (Updates T) (join_ir i r) r) t \<Longrightarrow> gets_us_to target e s r (h#t)" |
  step_none: "step e s r (fst h) (snd h) = None \<Longrightarrow> s = target \<Longrightarrow> gets_us_to target e s r (h#t)"

definition "trace_gets_us_to s e = gets_us_to s e 0 <>"

lemma no_further_steps:
  "s \<noteq> s' \<Longrightarrow> \<not> gets_us_to s e s' r []"
  apply safe
  apply (rule gets_us_to.cases)
  by auto

primrec accepting_sequence :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) list \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) list option" where
  "accepting_sequence _ _ r [] obs = Some (rev obs)" |
  "accepting_sequence e s r (a#t) obs = (let
    poss = possible_steps e s r (fst a) (snd a);
    accepting = ffilter (\<lambda>(s', T). accepts e s' (apply_updates (Updates T) (join_ir (snd a) r) r) t) poss  in
    if accepting = {||} then
      None
    else let
      (s', T) = Eps (\<lambda>x. x |\<in>| accepting);
      r' = (apply_updates (Updates T) (join_ir (snd a) r) r) in
      accepting_sequence e s' r' t ((T, s', (apply_outputs (Outputs T) (join_ir (snd a) r)), r')#obs)
  )"

lemma observe_trace_empty_iff:
  "(observe_trace e s r t = []) = (observe_all e s r t = [])"
  by (simp add: observe_trace_def)

definition enumerate_strings :: "transition_matrix \<Rightarrow> String.literal set" where
  "enumerate_strings e = \<Union> (image (\<lambda>(_, t). Transition.enumerate_strings t) (fset e))"

definition enumerate_ints :: "transition_matrix \<Rightarrow> int set" where
  "enumerate_ints e = \<Union> (image (\<lambda>(_, t). Transition.enumerate_ints t) (fset e))"

definition max_reg :: "transition_matrix \<Rightarrow> nat option" where
  "max_reg e = (let maxes = (fimage (\<lambda>(_, t). Transition.max_reg t) e) in if maxes = {||} then None else fMax maxes)"

definition max_output :: "transition_matrix \<Rightarrow> nat" where
  "max_output e = fMax (fimage (\<lambda>(_, t). length (Outputs t)) e)"

definition all_regs :: "transition_matrix \<Rightarrow> nat set" where
  "all_regs e = \<Union> (image (\<lambda>(_, t). enumerate_registers t) (fset e))"

definition max_input :: "transition_matrix \<Rightarrow> nat option" where
  "max_input e = fMax (fimage (\<lambda>(_, t). Transition.max_input t) e)"

fun maxS :: "transition_matrix \<Rightarrow> nat" where
  "maxS t = (if t = {||} then 0 else fMax ((fimage (\<lambda>((origin, dest), t). origin) t) |\<union>| (fimage (\<lambda>((origin, dest), t). dest) t)))"

definition max_int :: "transition_matrix \<Rightarrow> int" where
  "max_int e = Max (insert 0 (enumerate_ints e))"

lemma finite_all_regs:
  "finite (all_regs e)"
  apply (simp add: all_regs_def enumerate_registers_def)
  apply clarify
  apply standard
   apply (rule finite_UnI)+
     apply (metis List.finite_set enumerate_gexp_regs_list finite_UN_I)
    apply (metis List.finite_set outputs_regs_list set_map)
   apply (metis List.finite_set enumerate_aexp_regs_list finite_UN_I split_beta)
  by auto

definition isomorphic :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "isomorphic e1 e2 = ((\<forall>((s1, s2), t) |\<in>| e1. \<exists>f. ((f s1, f s2), t) |\<in>| e2) \<and>
                       (\<forall>((s1, s2), t) |\<in>| e2. \<exists>f. ((f s1, f s2), t) |\<in>| e1))"


end
