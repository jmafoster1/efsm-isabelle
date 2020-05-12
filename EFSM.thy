subsection \<open>Extended Finite State Machines\<close>
text\<open>
This theory defines extended finite state machines as presented in \cite{foster2018}. States are
indexed by natural numbers, however, since transition matrices are implemented by finite sets, the
number of reachable states in $S$ is necessarily finite. For ease of implementation, we implicitly
make the initial state zero for all EFSMs. This allows EFSMs to be represented purely by their
transition matrix which, in this implementation, is a finite set of tuples of the form
$((s_1, s_2), t)$ in which $s_1$ is the origin state, $s_2$ is the destination state, and t is a
transition.
\<close>

theory EFSM
  imports "HOL-Library.FSet" Transition FSet_Utils
begin

declare One_nat_def [simp del]

type_synonym cfstate = nat
type_synonym inputs = "value list"
type_synonym outputs = "value option list"

type_synonym action = "(label \<times> inputs)"
type_synonym execution = "action list"
type_synonym observation = "outputs list"
type_synonym transition_matrix = "((cfstate \<times> cfstate) \<times> transition) fset"

no_notation relcomp (infixr "O" 75) and comp (infixl "o" 55)

(* An execution represents a run of the software and has the form [(label, inputs, outputs)]*)
type_synonym event = "(label \<times> inputs \<times> value list)"
type_synonym trace = "event list"
type_synonym log = "trace list"

definition Str :: "string \<Rightarrow> value" where
  "Str s \<equiv> value.Str (String.implode s)"

lemma str_not_num: "Str s \<noteq> Num x1"
  by (simp add: Str_def)

definition S :: "transition_matrix \<Rightarrow> nat fset" where
  "S m = (fimage (\<lambda>((s, s'), t). s) m) |\<union>| fimage (\<lambda>((s, s'), t). s') m"

lemma S_ffUnion: "S e = ffUnion (fimage (\<lambda>((s, s'), _). {|s, s'|}) e)"
  unfolding S_def
  by(induct e, auto)

definition choice :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice t t' = (\<exists> i r. apply_guards (Guards t) (join_ir i r) \<and> apply_guards (Guards t') (join_ir i r))"

definition choice_alt :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice_alt t t' = (\<exists> i r. apply_guards (Guards t@Guards t') (join_ir i r))"

lemma choice_alt: "choice t t' = choice_alt t t'"
  by (simp add: choice_def choice_alt_def apply_guards_append)

lemma choice_symmetry: "choice x y = choice y x"
  using choice_def by auto

definition possible_steps :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (cfstate \<times> transition) fset" where
  "possible_steps e s r l i = fimage (\<lambda>((origin, dest), t). (dest, t)) (ffilter (\<lambda>((origin, dest), t). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guards t) (join_ir i r)) e)"

lemma fmember_possible_steps: "(s', t) |\<in>| possible_steps e s r l i = (((s, s'), t) \<in> {((origin, dest), t) \<in> fset e. origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r)})"
  apply (simp add: possible_steps_def ffilter_def fimage_def fmember_def Abs_fset_inverse)
  by force

lemma possible_steps_alt_aux:
  "possible_steps e s r l i = {|(d, t)|} \<Longrightarrow>
       ffilter (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r)) e = {|((s, d), t)|}"
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
    apply (case_tac "aa = s \<and> Label b = l \<and> length i = Arity b \<and> apply_guards (Guards b) (join_ir i r)")
    by auto
qed

lemma possible_steps_alt: "(possible_steps e s r l i = {|(d, t)|}) = (ffilter
     (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r))
     e = {|((s, d), t)|})"
  apply standard
   apply (simp add: possible_steps_alt_aux)
  by (simp add: possible_steps_def)

lemma possible_steps_singleton: "(possible_steps e s r l i = {|(d, t)|}) =
    ({((origin, dest), t) \<in> fset e. origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r)} = {((s, d), t)})"
  apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def)
  by fast

lemma possible_steps_apply_guards:
  "possible_steps e s r l i = {|(s', t)|} \<Longrightarrow>
   apply_guards (Guards t) (join_ir i r)"
  apply (simp add: possible_steps_singleton)
  by auto

lemma possible_steps_empty:
  "(possible_steps e s r l i = {||}) = (\<forall>((origin, dest), t) \<in> fset e. origin \<noteq> s \<or> Label t \<noteq> l \<or> \<not> can_take_transition t i r)"
  apply (simp add: can_take_transition_def can_take_def)
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def)
  by auto

lemma singleton_dest:
  assumes "fis_singleton (possible_steps e s r aa b)"
      and "fthe_elem (possible_steps e s r aa b) = (baa, aba)"
    shows "((s, baa), aba) |\<in>| e"
  using assms
  apply (simp add: fis_singleton_fthe_elem)
  using possible_steps_alt_aux by force

inductive recognises :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base: "recognises e s d []" |
  step: "(s', t) |\<in>| possible_steps e s r l i \<Longrightarrow>
         recognises e s' (apply_updates (Updates t) (join_ir i r) r) ts \<Longrightarrow>
         recognises e s r ((l, i)#ts)"

abbreviation "rejects e s d t \<equiv> \<not> recognises e s d t"

abbreviation recognises_trace :: "transition_matrix \<Rightarrow> execution \<Rightarrow> bool" where
  "recognises_trace e t \<equiv> recognises e 0 <> t"

lemma no_possible_steps_rejects:
  "possible_steps e s d l i = {||} \<Longrightarrow> rejects e s d ((l, i)#t)"
  using recognises.cases by blast

lemma recognises_step_equiv: "recognises e s d ((l, i)#t) =
   (\<exists>(s', T) |\<in>| possible_steps e s d l i. recognises e s' (apply_updates (Updates T) (join_ir i d) d) t)"
  apply standard
   apply (rule recognises.cases, simp)
    apply simp
   apply auto[1]
  using recognises.step by blast

fun recognises_prim :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  "recognises_prim e s d [] = True" |
  "recognises_prim e s d ((l, i)#t) = (
    let poss_steps = possible_steps e s d l i in
    (\<exists>(s', T) |\<in>| poss_steps. recognises_prim e s' (apply_updates (Updates T) (join_ir i d) d) t)
  )"

lemma recognises_prim [code]: "recognises e s r t = recognises_prim e s r t"
proof(induct t arbitrary: r s)
  case Nil
  then show ?case
    by (simp add: recognises.base)
next
  case (Cons h t)
  then show ?case
    apply (cases h)
    apply simp
    apply standard
     apply (rule recognises.cases, simp)
      apply simp
     apply auto[1]
    using recognises.step by blast
qed

lemma recognises_single_possible_step:
  assumes "possible_steps e s d l i = {|(s', t)|}"
      and "recognises e s' (apply_updates (Updates t) (join_ir i d) d) trace"
    shows "recognises e s d ((l, i)#trace)"
  apply (rule recognises.step[of s' t])
  using assms by auto

lemma recognises_single_possible_step_atomic:
  assumes "possible_steps e s d (fst h) (snd h) = {|(s', t)|}"
      and "recognises e s' (apply_updates (Updates t) (join_ir (snd h) d) d) trace"
    shows "recognises e s d (h#trace)"
  by (metis recognises_single_possible_step assms(1) assms(2) prod.collapse)

lemma recognises_must_be_possible_step:
  "recognises e s r (h # t) \<Longrightarrow>
   \<exists>aa ba. (aa, ba) |\<in>| possible_steps e s r (fst h) (snd h)"
  using recognises_step_equiv by fastforce

inductive accepts_trace :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "accepts_trace e s d []" |
  step: "\<exists>(s', T) |\<in>| possible_steps e s d l i.
         evaluate_outputs T i d = map Some p \<and>
         accepts_trace e s' (apply_updates (Updates T) (join_ir i d) d) t \<Longrightarrow>
         accepts_trace e s d ((l, i, p)#t)"

abbreviation "rejects_trace e s d t \<equiv> \<not> accepts_trace e s d t"

lemma accepts_trace_step:
  "accepts_trace e s d ((l, i, p)#t) = (\<exists>(s', T) |\<in>| possible_steps e s d l i.
         evaluate_outputs T i d = map Some p \<and>
         accepts_trace e s' (apply_updates (Updates T) (join_ir i d) d) t)"
  apply standard
   defer
   apply (simp add: accepts_trace.step)
  apply (rule accepts_trace.cases)
  by auto

lemma rejects_trace_step:
"rejects_trace e s d ((l, i, p)#t) = (
  (\<forall>(s', T) |\<in>| possible_steps e s d l i.  evaluate_outputs T i d \<noteq> map Some p \<or> rejects_trace e s' (apply_updates (Updates T) (join_ir i d) d) t)
)"
  apply (simp add: accepts_trace_step)
  by auto

fun accepts_trace_prim :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  "accepts_trace_prim _ _ _ [] = True" |
  "accepts_trace_prim e s d ((l, i, p)#t) = (
    let poss_steps = possible_steps e s d l i in
    if fis_singleton poss_steps then
      let (s', T) = fthe_elem poss_steps in
      if evaluate_outputs T i d = map Some p then
        accepts_trace_prim e s' (apply_updates (Updates T) (join_ir i d) d) t
      else False
    else
      (\<exists>(s', T) |\<in>| poss_steps.
         apply_outputs (Outputs T) (join_ir i d) = (map Some p) \<and>
         accepts_trace_prim e s' (apply_updates (Updates T) (join_ir i d) d) t))"

lemma accepts_trace_prim [code]: "accepts_trace e s d l = accepts_trace_prim e s d l"
proof(induct l arbitrary: s d)
  case Nil
  then show ?case
    by (simp add: accepts_trace.base)
next
  case (Cons a l)
  then show ?case
    apply (cases a)
    apply (simp add: accepts_trace_step Let_def fis_singleton_alt)
    by auto
qed

definition accepts_log :: "trace set \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "accepts_log T e = (\<forall>t \<in> T. accepts_trace e 0 <> t)"

inductive execution_equivalence :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base: "execution_equivalence e1 s1 r1 e2 s2 r2 []" |
  step: "\<forall>(s1', t1) |\<in>| possible_steps e1 s1 r1 l i.
           \<exists>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i.
            execution_equivalence e1 s1' (apply_updates (Updates t1) (join_ir i r1) r1) e2 s2' (apply_updates (Updates t2) (join_ir i r2) r2) es \<Longrightarrow>

         execution_equivalence e1 s1 r1 e2 s2 r2 ((l, i)#es)"

lemma execution_equivalence_induct:
  "(\<And>l i t. execution_equivalence e1 s1 r1 e2 s2 r2 t \<Longrightarrow>
   execution_equivalence e1 s1 r1 e2 s2 r2 ((l, i) # t)) \<Longrightarrow>

execution_equivalence e1 s1 r1 e2 s2 r2 t"
  using execution_equivalence.base by (induct t, auto)

lemma execution_equivalence_acceptance:
  "execution_equivalence e1 s1 r1 e2 s2 r2 t \<Longrightarrow>
   recognises e1 s1 r1 t \<Longrightarrow>
   recognises e2 s2 r2 t"
proof(induct t arbitrary: s1 r1 s2 r2)
  case Nil
  then show ?case
    by (simp add: recognises.base)
next
  case (Cons a t)
  then show ?case
    apply (cases a, clarify)
    apply simp
    apply (rule execution_equivalence.cases)
       apply simp
      apply simp
    apply (simp add: no_possible_steps_rejects)
    apply clarify
    apply simp
    apply (simp add: recognises_step_equiv[of e1])
    apply clarify
    apply (erule_tac x="(aa, b)" in fBallE)
     apply simp
     apply clarify
    subgoal for l i s1' t1 s2' t2
      apply (rule recognises.step[of s2' t2])
      by auto
    by simp
qed

definition execution_equivalent :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "execution_equivalent e1 e2 \<equiv> \<forall>t. execution_equivalence e1 0 <> e2 0 <> t"

lemma execution_equivalent_induct:
  "(\<And>l i t. execution_equivalence e1 0 <> e2 0 <> t \<Longrightarrow>
   execution_equivalence e1 0 <> e2 0 <> ((l, i) # t)) \<Longrightarrow>

execution_equivalent e1 e2"
  using execution_equivalent_def execution_equivalence_induct by blast

lemma execution_equivalent_recognises_trace:
  "execution_equivalent e1 e2 \<Longrightarrow>
   recognises_trace e1 t \<Longrightarrow>
   recognises_trace e2 t"
  apply (simp add: execution_equivalent_def)
  using execution_equivalence_acceptance by blast

definition random_member :: "'a fset \<Rightarrow> 'a option" where
  "random_member f = (if f = {||} then None else Some (Eps (\<lambda>x. x |\<in>| f)))"

lemma random_member_nonempty: "s \<noteq> {||} = (random_member s \<noteq> None)"
  by (simp add: random_member_def)

lemma random_member_singleton [simp]: "random_member {|a|} = Some a"
  by (simp add: random_member_def)

lemma random_member_is_member:
  "random_member ss = Some s \<Longrightarrow> s |\<in>| ss"
  apply (simp add: random_member_def)
  by (metis equalsffemptyI option.distinct(1) option.inject verit_sko_ex_indirect)

lemma random_member_None[simp]: "random_member ss = None = (ss = {||})"
  by (simp add: random_member_def)

lemma random_member_empty[simp]: "random_member {||} = None"
  by simp

definition step :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) option" where
  "step e s r l i = (case random_member (possible_steps e s r l i) of
      None \<Rightarrow> None |
      Some (s', t) \<Rightarrow>  Some (t, s', apply_outputs (Outputs t) (join_ir i r), apply_updates (Updates t) (join_ir i r) r)
  )"

lemma step_member: "step e s r l i = Some (t, s', p, r') \<Longrightarrow> (s', t) |\<in>| possible_steps e s r l i"
  apply (simp add: step_def)
  apply (case_tac "random_member (possible_steps e s r l i)")
   apply simp
  by (case_tac a, simp add: random_member_is_member)

lemma step_outputs: "step e s r l i = Some (t, s', p, r') \<Longrightarrow> evaluate_outputs t i r = p"
  apply (simp add: step_def)
  apply (case_tac "random_member (possible_steps e s r l i)")
  by auto

lemma step_some: "possibilities = (possible_steps e s r l i) \<Longrightarrow>
   random_member possibilities = Some (s', t) \<Longrightarrow>
   apply_outputs (Outputs t) (join_ir i r) = p \<Longrightarrow>
   apply_updates (Updates t) (join_ir i r) r = r' \<Longrightarrow>
   step e s r l i = Some (t, s', p, r')"
  by (simp add: step_def)

lemma step_None: "step e s r l i = None = (possible_steps e s r l i = {||})"
  by (simp add: step_def prod.case_eq_if random_member_def)

lemma step_Some: "step e s r l i = Some (t, s', p, r') =
  (
    random_member (possible_steps e s r l i) = Some (s', t) \<and>
    apply_outputs (Outputs t) (join_ir i r) = p \<and>
    apply_updates (Updates t) (join_ir i r) r = r'
  )"
  apply (simp add: step_def)
  apply (case_tac "random_member (possible_steps e s r l i)")
   apply simp
  by (case_tac a, auto)

lemma no_possible_steps_1:
  "possible_steps e s r l i = {||} \<Longrightarrow> step e s r l i = None"
  by (simp add: step_def random_member_def)

primrec observe_all :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> (transition \<times> nat \<times> outputs \<times> registers) list" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r (h#t)  =
    (case (step e s r (fst h) (snd h)) of
      (Some (transition, s', outputs, updated)) \<Rightarrow> (((transition, s', outputs, updated)#(observe_all e s' updated t))) |
      _ \<Rightarrow> []
    )"

fun execute :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> trace" where
  "execute _ _ _ [] = []" |
  "execute e s r ((l, i)#as)  = (
    let
      viable = possible_steps e s r l i;
      output_viable = ffilter (\<lambda>(_, t). \<forall>p \<in> set (evaluate_outputs t i r). p \<noteq> None) viable
    in
    if viable = {||} then
      []
    else
      let (s', t) = Eps (\<lambda>x. x |\<in>| viable) in
      (l, i, map (\<lambda>p. case p of Some o \<Rightarrow> o) (evaluate_outputs t i r))#(execute e s' (evaluate_updates t i r) as)
    )"

fun observe_execution :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> outputs list" where
  "observe_execution _ _ _ [] = []" |
  "observe_execution e s r ((l, i)#as)  = (
    let viable = possible_steps e s r l i in
    if viable = {||} then
      []
    else
      let (s', t) = Eps (\<lambda>x. x |\<in>| viable) in
      (evaluate_outputs t i r)#(observe_execution e s' (evaluate_updates t i r) as)
    )"

lemma observe_execution_step_def: "observe_execution e s r ((l, i)#as)  = (
    case step e s r l i of
      None \<Rightarrow> []|
      Some (t, s', p, r') \<Rightarrow> p#(observe_execution e s' r' as)
    )"
  apply (simp add: step_def)
  apply (case_tac "possible_steps e s r l i")
   apply simp
  apply (simp add: random_member_def)
  apply (case_tac "SOME xa. xa = x \<or> xa |\<in>| S'")
  by simp

lemma observe_execution_step:
  "step e s r (fst h) (snd h) = Some (t, s', p, r') \<Longrightarrow>
   observe_execution e s' r' es = obs \<Longrightarrow>
   observe_execution e s r (h#es) = p#obs"
  apply (cases h, simp add: step_def)
  apply (case_tac "possible_steps e s r a b = {||}")
   apply simp
  apply (case_tac "SOME x. x |\<in>| possible_steps e s r a b")
  apply (simp add: random_member_def)
  by auto

lemma observe_execution_possible_step:
  "possible_steps e s r (fst h) (snd h) = {|(s', t)|} \<Longrightarrow>
   apply_outputs (Outputs t) (join_ir (snd h) r) = p \<Longrightarrow>
   apply_updates (Updates t) (join_ir (snd h) r) r = r' \<Longrightarrow>
   observe_execution e s' r' es = obs \<Longrightarrow>
   observe_execution e s r (h#es) = p#obs"
  by (simp add: observe_execution_step step_some)

lemma observe_execution_no_possible_step:
  "possible_steps e s r (fst h) (snd h) = {||} \<Longrightarrow>
   observe_execution e s r (h#es) = []"
  by (cases h, simp)

lemma observe_execution_no_possible_steps:
  "possible_steps e1 s1 r1 (fst h) (snd h) = {||} \<Longrightarrow>
   possible_steps e2 s2 r2 (fst h) (snd h) = {||} \<Longrightarrow>
   (observe_execution e1 s1 r1 (h#t)) = (observe_execution e2 s2 r2 (h#t))"
  by (simp add: observe_execution_no_possible_step)

lemma observe_execution_one_possible_step:
  "possible_steps e1 s1 r (fst h) (snd h) = {|(s1', t1)|} \<Longrightarrow>
   possible_steps e2 s2 r (fst h) (snd h) = {|(s2', t2)|} \<Longrightarrow>
   apply_outputs (Outputs t1) (join_ir (snd h) r) = apply_outputs (Outputs t2) (join_ir (snd h) r) \<Longrightarrow>

   apply_updates (Updates t1) (join_ir (snd h) r) r = r' \<Longrightarrow>
   apply_updates (Updates t2) (join_ir (snd h) r) r = r' \<Longrightarrow>
   (observe_execution e1 s1' r' t) = (observe_execution e2 s2' r' t) \<Longrightarrow>
   (observe_execution e1 s1 r (h#t)) = (observe_execution e2 s2 r (h#t))"
  by (simp add: observe_execution_possible_step)

lemma observe_execution_preserves_length:
  "length (observe_all e s r as) = length (observe_execution e s r as)"
proof(induct as arbitrary: s r)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case
    apply (cases a, simp add: step_def)
    apply (case_tac "possible_steps e s r aa b = {||}")
     apply simp
    apply (simp add: random_member_def)
    apply (case_tac "SOME x. x |\<in>| possible_steps e s r aa b")
    by simp
qed

lemma length_observation_leq_length_trace:
  "\<And>s r. length (observe_all e s r t) \<le> length t"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    by (case_tac "step e s r (fst a) (snd a)", auto)
qed

lemma recognises_possible_steps_not_empty:
  "recognises e s d (h#t) \<Longrightarrow> possible_steps e s d (fst h) (snd h) \<noteq> {||}"
  apply (rule recognises.cases)
  by auto

lemma recognises_must_be_step:
  "recognises e s d (h#ts) \<Longrightarrow>
   \<exists>t s' p d'. step e s d (fst h) (snd h) = Some (t, s', p, d')"
  apply (cases h)
  apply (simp add: recognises_step_equiv step_def)
  apply clarify
  apply (case_tac "(possible_steps e s d a b)")
   apply (simp add: random_member_def)
  apply (simp add: random_member_def)
  apply (case_tac "SOME xa. xa = x \<or> xa |\<in>| S'")
  by simp

lemma recognises_cons_step:
  "recognises e s r (h # t) \<Longrightarrow> step e s r (fst h) (snd h) \<noteq>  None"
  by (simp add: recognises_must_be_step)

lemma no_step_none:
  "step e s r aa ba = None \<Longrightarrow> rejects e s r ((aa, ba) # p)"
  using recognises_cons_step by fastforce

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
  using recognises_prim by fastforce

lemma trace_reject_no_possible_steps_atomic:
  "possible_steps e s d (fst a) (snd a) = {||} \<Longrightarrow> rejects e s d (a#t)"
  using recognises_possible_steps_not_empty by auto

lemma trace_reject_later:
  "\<forall>(s', T) |\<in>| possible_steps e s d a b. rejects e s' (apply_updates (Updates T) (join_ir b d) d) t \<Longrightarrow>
   rejects e s d ((a, b)#t)"
  using trace_reject by auto

lemma prefix_closure: "recognises e s d (t@t') \<Longrightarrow> recognises e s d t"
proof(induct t arbitrary: s d)
  case Nil
  then show ?case
    by (simp add: recognises.base)
next
  case (Cons a t)
  then show ?case
    apply (cases a, clarsimp)
    apply (rule recognises.cases)
      apply simp
     apply simp
    by (rule recognises.step, auto)
qed

lemma rejects_prefix: "rejects e s d t \<Longrightarrow> rejects e s d (t @ t')"
  using prefix_closure by blast

lemma recognises_head: "recognises e s d (h#t) \<Longrightarrow> recognises e s d [h]"
  by (metis recognises.simps recognises_must_be_possible_step prod.exhaust_sel)

inductive gets_us_to :: "cfstate \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base: "s = target \<Longrightarrow> gets_us_to target _ s _ []" |
  step_some: "\<exists>(s', T) |\<in>| possible_steps e s d (fst h) (snd h). gets_us_to target e s' (apply_updates (Updates T) (join_ir i r) r) t \<Longrightarrow>
   gets_us_to target e s r (h#t)" |
  step_none: "step e s r (fst h) (snd h) = None \<Longrightarrow>
   s = target \<Longrightarrow>
   gets_us_to target e s r (h#t)"

definition "trace_gets_us_to s e = gets_us_to s e 0 <>"

lemma no_further_steps:
  "s \<noteq> s' \<Longrightarrow> \<not> gets_us_to s e s' r []"
  apply safe
  apply (rule gets_us_to.cases)
  by auto

lemma observe_execution_empty_iff:
  "(observe_execution e s r t = []) = (observe_all e s r t = [])"
  by (metis length_greater_0_conv observe_execution_preserves_length)

definition max_reg :: "transition_matrix \<Rightarrow> nat option" where
  "max_reg e = (let maxes = (fimage (\<lambda>(_, t). Transition.max_reg t) e) in if maxes = {||} then None else fMax maxes)"

definition enumerate_ints :: "transition_matrix \<Rightarrow> int set" where
  "enumerate_ints e = \<Union> (image (\<lambda>(_, t). Transition.enumerate_ints t) (fset e))"

definition max_int :: "transition_matrix \<Rightarrow> int" where
  "max_int e = Max (insert 0 (enumerate_ints e))"

definition max_output :: "transition_matrix \<Rightarrow> nat" where
  "max_output e = fMax (fimage (\<lambda>(_, t). length (Outputs t)) e)"

definition all_regs :: "transition_matrix \<Rightarrow> nat set" where
  "all_regs e = \<Union> (image (\<lambda>(_, t). enumerate_regs t) (fset e))"

definition max_input :: "transition_matrix \<Rightarrow> nat option" where
  "max_input e = fMax (fimage (\<lambda>(_, t). Transition.max_input t) e)"

fun maxS :: "transition_matrix \<Rightarrow> nat" where
  "maxS t = (if t = {||} then 0 else fMax ((fimage (\<lambda>((origin, dest), t). origin) t) |\<union>| (fimage (\<lambda>((origin, dest), t). dest) t)))"

lemma finite_all_regs: "finite (all_regs e)"
  apply (simp add: all_regs_def enumerate_regs_def)
  apply clarify
  apply standard
   apply (rule finite_UnI)+
  using GExp.finite_enumerate_regs apply blast
  using AExp.finite_enumerate_regs apply blast
   apply (simp add: AExp.finite_enumerate_regs prod.case_eq_if)
  by auto

definition isomorphic :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "isomorphic e1 e2 = (\<exists>f. bij f \<and> (\<forall>((s1, s2), t) |\<in>| e1. ((f s1, f s2), t) |\<in>| e2))"

definition rename_regs :: "(nat \<Rightarrow> nat) \<Rightarrow> transition_matrix \<Rightarrow> transition_matrix" where
  "rename_regs f e = fimage (\<lambda>(tf, t). (tf, Transition.rename_regs f t)) e"

definition eq_upto_rename_strong :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "eq_upto_rename_strong e1 e2 = (\<exists>f. bij f \<and> rename_regs f e1 = e2)"

inductive trace_equivalence :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base: "trace_equivalence e1 s1 r1 e2 s2 r2 []" |
  step: "\<forall>(s1', t1) |\<in>| possible_steps e1 s1 r1 l i.
           \<exists>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i.
            apply_outputs (Outputs t1) (join_ir i r1) = apply_outputs (Outputs t2) (join_ir i r2) \<and>
            trace_equivalence e1 s1' (apply_updates (Updates t1) (join_ir i r1) r1) e2 s2' (apply_updates (Updates t2) (join_ir i r2) r2) es \<Longrightarrow>
         trace_equivalence e1 s1 r1 e2 s2 r2 ((l, i)#es)"

lemma trace_equivalence_step: "trace_equivalence e1 s1 r1 e2 s2 r2 ((l, i)#es) = (
  \<forall>(s1', t1) |\<in>| possible_steps e1 s1 r1 l i.
           \<exists>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i.
            apply_outputs (Outputs t1) (join_ir i r1) = apply_outputs (Outputs t2) (join_ir i r2) \<and>
            trace_equivalence e1 s1' (apply_updates (Updates t1) (join_ir i r1) r1) e2 s2' (apply_updates (Updates t2) (join_ir i r2) r2) es)"
  apply standard
   apply (rule trace_equivalence.cases)
     apply simp
    apply simp
   apply simp
  by (simp add: trace_equivalence.step)

definition trace_equivalent :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "trace_equivalent e1 e2 \<equiv> \<forall>t. trace_equivalence e1 0 <> e2 0 <> t"

lemma observe_execution_first_outputs_equiv:
  "observe_execution e1 s1 r1 ((l, i) # ts) = observe_execution e2 s2 r2 ((l, i) # ts) \<Longrightarrow>
   step e1 s1 r1 l i = Some (t, s', p, r') \<Longrightarrow>
   \<exists>(s2', t2)|\<in>|possible_steps e2 s2 r2 l i. evaluate_outputs t2 i r2 = p"
  apply (simp only: observe_execution_step_def)
  apply (case_tac "step e2 s2 r2 l i")
   apply simp
  apply simp
  apply (case_tac a)
  apply clarsimp
  by (meson step_member case_prodI rev_fBexI step_outputs)

inductive trace_simulation :: "(cfstate \<Rightarrow> cfstate) \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "s2 = f s1 \<Longrightarrow> trace_simulation f e1 s1 r1 e2 s2 r2 []" |
  step: "s2 = f s1 \<Longrightarrow>
              \<forall>(s1', t1) |\<in>| possible_steps e1 s1 r1 l i. evaluate_outputs t1 i r1 = map Some o \<longrightarrow>
              (\<exists>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i. evaluate_outputs t2 i r2 = map Some o \<and>
              trace_simulation f e1 s1' (evaluate_updates t1 i r1) e2 s2' (evaluate_updates t2 i r2) es) \<Longrightarrow>
              trace_simulation f e1 s1 r1 e2 s2 r2 ((l, i, o)#es)"

lemma step_none: "s2 = f s1 \<Longrightarrow> \<nexists>(s1', t1) |\<in>| possible_steps e1 s1 r1 l i. evaluate_outputs t1 i r1 = map Some o \<Longrightarrow>
trace_simulation f e1 s1 r1 e2 s2 r2 ((l, i, o)#es)"
  by (rule trace_simulation.step, auto)

definition "simulates e1 e2 = (\<exists>f. \<forall>t. trace_simulation f e1 0 <> e2 0 <> t)"

definition T :: "transition_matrix \<Rightarrow> trace set" where
  "T e = {t. accepts_trace e 0 <> t}"

definition "observably_equivalent e1 e2 = (T e1 = T e2)"

lemma pair_list_induct [case_names Nil Cons]:
  "f [] \<Longrightarrow> (\<And>l i as. f as \<Longrightarrow> f ((l, i) # as)) \<Longrightarrow> f l"
  by (induct l, auto)

lemma triple_list_induct [case_names Nil Cons]:
  "f [] \<Longrightarrow> (\<And>l i o as. f as \<Longrightarrow> f ((l, i, o) # as)) \<Longrightarrow> f l"
  by (induct l, auto)

lemma accepts_trace_exists_possible_step:
  "accepts_trace e1 s1 r1 ((aa, b, c) # t) \<Longrightarrow>
       \<exists>(s1', t1)|\<in>|possible_steps e1 s1 r1 aa b.
          evaluate_outputs t1 b r1 = map Some c"
  using accepts_trace_step by auto

lemma "rejects_trace e2 s2 r2 t \<Longrightarrow>
 accepts_trace e1 s1 r1 t \<Longrightarrow>
\<not>trace_simulation f e1 s1 r1 e2 s2 r2 t"
proof(induct t arbitrary: s1 r1 s2 r2)
  case Nil
  then show ?case
    using accepts_trace.base by blast
next
  case (Cons a t)
  then show ?case
    apply (cases a)
    apply (simp add: rejects_trace_step)
    apply (simp add: accepts_trace_step)
    apply clarify
    apply (rule trace_simulation.cases)
      apply simp
     apply simp
    by blast
qed

lemma accepts_trace_simulation:
"accepts_trace e1 s1 r1 t \<Longrightarrow> trace_simulation f e1 s1 r1 e2 s2 r2 t \<Longrightarrow> accepts_trace e2 s2 r2 t"
proof(induct t arbitrary: s1 r1 s2 r2)
  case Nil
  then show ?case
    by (simp add: accepts_trace.base)
next
  case (Cons h t)
  then show ?case
    apply (cases h, clarsimp)                     
    apply (simp add: accepts_trace_step)
    apply (rule trace_simulation.cases)
      apply simp
     apply simp
    by blast
qed

lemma simulates_trace_subset: "simulates e1 e2 \<Longrightarrow> T e1 \<subseteq> T e2"
  apply (simp add: simulates_def T_def)
  using accepts_trace_simulation by blast

lemma simulation_implies_observably_equivalent:
"simulates e1 e2 \<Longrightarrow> simulates e2 e1 \<Longrightarrow> observably_equivalent e1 e2"
  using simulates_trace_subset observably_equivalent_def by auto

lemma observably_equivalent_reflexive: "observably_equivalent e1 e1"
  by (simp add: observably_equivalent_def)

lemma observably_equivalent_symmetric:
  "observably_equivalent e1 e2 = observably_equivalent e2 e1"
  using observably_equivalent_def by auto

lemma observably_equivalent_transitive:
  "observably_equivalent e1 e2 \<Longrightarrow>
   observably_equivalent e2 e3 \<Longrightarrow>
   observably_equivalent e1 e3"
  by (simp add: observably_equivalent_def)

lemma observably_equivalent:
  "\<forall>t. accepts_trace e1 0 <> t = accepts_trace e2 0 <> t \<Longrightarrow> observably_equivalent e1 e2"
  by (simp add: T_def observably_equivalent_def)

inductive exec_diff :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base: "(s1', t1) |\<in>| possible_steps e1 s1 r1 l i \<Longrightarrow>
         \<nexists>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i. evaluate_outputs t1 i r1 = evaluate_outputs t2 i r2 \<Longrightarrow>
         exec_diff e1 s1 r1 e2 s2 r2 ((l, i)#t)" |
  step: "(s1', t1) |\<in>| possible_steps e1 s1 r1 l i \<Longrightarrow>
         (s2', t2) |\<in>| possible_steps e2 s2 r2 l i \<Longrightarrow>
         exec_diff e1 s1' (evaluate_updates t1 i r1) e2 s2' (evaluate_updates t2 i r2) t \<Longrightarrow>
         exec_diff e1 s1 r1 e2 s2 r2 ((l, i)#t)"

lemma accepts_trace_step_2: "(s2', t2) |\<in>| possible_steps e2 s2 r2 l i \<Longrightarrow>
       accepts_trace e2 s2' (evaluate_updates t2 i r2) t \<Longrightarrow>
       evaluate_outputs t2 i r2 = map Some p \<Longrightarrow>
       accepts_trace e2 s2 r2 ((l, i, p)#t)"
  by (rule accepts_trace.step, auto)

end
