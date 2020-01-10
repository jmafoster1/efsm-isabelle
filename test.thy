theory test
imports Contexts
begin

definition "t1 = \<lparr>Label = STR ''t'', Arity = 1, Guard = [], Outputs = [], Updates = [(1, L (Num 5))]\<rparr>"
definition "t2 = \<lparr>Label = STR ''t'', Arity = 1, Guard = [], Outputs = [], Updates = [(1, V (I 0))]\<rparr>"

lemma "\<not> subsumes t1 c t2"
  apply (rule inconsistent_updates2)
  apply (simp add: t1_def t2_def posterior_def posterior_separate_def)
  apply (rule_tac x="c(1 := Num 5)" in exI)
  apply (rule_tac x="c(1 := Num 2)" in exI)
  apply simp
  apply standard
   apply (rule_tac x="[Num 2]" in exI)
   apply (simp add: join_ir_def input2state_def)
  apply (rule_tac x=1 in exI)
  apply (rule_tac x="\<lambda>x. x = Some (Num 5)" in exI)
  by simp

lemma "\<not> subsumes t2 c t1"
  apply (rule inconsistent_updates2)
  apply (simp add: t1_def t2_def posterior_def posterior_separate_def)
  apply (rule_tac x="c(1 := Num 2)" in exI)
  apply (rule_tac x="c(1 := Num 5)" in exI)
  apply simp
  apply standard
   apply (rule_tac x="[Num 2]" in exI)
   apply (simp add: join_ir_def input2state_def)
  apply (rule_tac x=1 in exI)
  apply (rule_tac x="\<lambda>x. x = Some (Num 2)" in exI)
  by simp

lemma "subsumes (t2\<lparr>Guard:=[Eq (V (I 0)) (L (Num 5))]\<rparr>) c (t1\<lparr>Guard:=[Eq (V (I 0)) (L (Num 5))]\<rparr>)"
  apply (simp add: subsumes_def t1_def t2_def can_take_transition_def posterior_def posterior_separate_def can_take_def apply_guards_def join_ir_def input2state_def)
  by auto

lemma "subsumes (t1\<lparr>Guard:=[Eq (V (I 0)) (L (Num 5))]\<rparr>) c (t2\<lparr>Guard:=[Eq (V (I 0)) (L (Num 5))]\<rparr>)"
  apply (simp add: subsumes_def t1_def t2_def can_take_transition_def posterior_def posterior_separate_def can_take_def apply_guards_def join_ir_def input2state_def)
  by auto

hide_const t1
hide_const t2

definition subsumes_alt :: "transition \<Rightarrow> registers \<Rightarrow> transition \<Rightarrow> bool" where
  "subsumes_alt t2 r t1 = (Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and>
                       (\<forall>i. can_take_transition t1 i r \<longrightarrow> can_take_transition t2 i r) \<and>
                       (\<forall>i. can_take_transition t1 i r \<longrightarrow>
                            apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                       (\<forall>p1 p2 i. posterior_separate (Arity t1) (Guard t1) (Updates t2) i r = Some p2 \<and>
                                  posterior_separate (Arity t1) (Guard t1) (Updates t1) i r = Some p1 \<longrightarrow>
                                  (\<forall>P r'. (p1 $ r' = None) \<or> (P (p2 $ r') \<longrightarrow> P (p1 $ r'))))
                      )"

lemma subsumes_alt: "subsumes t1 c t2 = subsumes_alt t1 c t2"
  apply (simp add: subsumes_def subsumes_alt_def)
  apply safe
    apply (erule_tac x=p1 in allE)
    apply (erule_tac x=p2 in allE)
    apply (case_tac "(\<forall>P. P (p2 $ r') \<longrightarrow> p1 $ r' = None \<or> P (p1 $ r'))")
     apply auto[1]
    apply (metis (full_types) apply_guards_append can_take_def can_take_transition_def posterior_separate_def)
   apply (erule_tac x=p1 in allE)
   apply (erule_tac x=p2 in allE)
   apply (metis option.distinct(1) posterior_separate_def)
  apply (erule_tac x=p1 in allE)
  apply (erule_tac x=p2 in allE)
  apply (case_tac "(\<forall>P. P (p2 $ r) \<longrightarrow> p1 $ r = None \<or> P (p1 $ r))")
   apply auto[1]
  by (metis option.distinct(1) posterior_def posterior_separate_def)

end