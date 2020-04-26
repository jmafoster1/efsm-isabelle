subsection\<open>An Observationally Equivalent Model\<close>
text\<open>This theory defines a second formalisation of the drinks machine example which produces
identical output to the first model. This property is called \emph{observational equivalence} and is
discussed in more detail in \cite{foster2018}.\<close>
theory Drinks_Machine_2
  imports Drinks_Machine
begin

definition vend_nothing :: "transition" where
"vend_nothing \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guards = [],
        Outputs =  [],
        Updates = [(1, V (R 1)), (2, V (R 2))]
      \<rparr>"

lemmas transitions = Drinks_Machine.transitions vend_nothing_def

definition drinks2 :: transition_matrix where
"drinks2 = {|
              ((0,1), select),
              ((1,1), vend_nothing),
              ((1,2), coin),
              ((2,2), coin),
              ((2,2), vend_fail),
              ((2,3), vend)
         |}"

lemma possible_steps_0: "length i = 1 \<Longrightarrow> possible_steps drinks2 0 r ((STR ''select'')) i = {|(1, select)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma possible_steps_1: "length i = 1 \<Longrightarrow> possible_steps drinks2 1 r ((STR ''coin'')) i = {|(2, coin)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma possible_steps_2_coin: "length i = 1 \<Longrightarrow> possible_steps drinks2 2 r ((STR ''coin'')) i = {|(2, coin)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma possible_steps_2_vend: "r $ 2 = Some (Num n) \<Longrightarrow> n \<ge> 100 \<Longrightarrow> possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(3, vend)|}"
  apply (simp add: possible_steps_singleton drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma accepts_first_select: "accepts drinks 0 r ((aa, b) # as) \<Longrightarrow> aa = STR ''select'' \<and> length b = 1"
  using accepts_must_be_possible_step[of drinks 0 r "(aa, b)" as]
  apply simp
  apply clarify
  by (metis first_step_select accepts_possible_steps_not_empty drinks_0_rejects fst_conv snd_conv)

lemma drinks2_vend_insufficient: "possible_steps drinks2 1 r ((STR ''vend'')) [] = {|(1, vend_nothing)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma drinks2_vend_insufficient2: "r $ 2 = Some (Num x1) \<Longrightarrow> x1 < 100 \<Longrightarrow> possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(2, vend_fail)|}"
  apply (simp add: possible_steps_singleton drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma drinks2_vend_sufficient: "r $ 2 = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(3, vend)|}"
  apply (simp add: possible_steps_singleton drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma accepts_1_2: "accepts drinks 1 r t \<longrightarrow> accepts drinks2 2 r t"
proof(induct t arbitrary: r)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a as)
  then show ?case
    apply (cases a)
    apply (simp add: accepts_step_equiv)
    apply (case_tac "a=(STR ''vend'', [])")
     apply (case_tac "\<exists>n. r$2 = Some (Num n)")
      apply clarify
      apply (case_tac "n < 100")
       apply (simp add: drinks_vend_insufficient drinks2_vend_insufficient2)
      apply (simp add: drinks_vend_sufficient drinks2_vend_sufficient)
      apply (metis accepts_prim accepts_prim.elims(3) drinks_rejects_future)
    using drinks_vend_invalid apply blast
    apply (case_tac "\<exists>i. a=(STR ''coin'', [i])")
     apply clarify
     apply (simp add: possible_steps_1_coin possible_steps_2_coin)
    by (metis accepts.simps drinks_1_rejects_trace fBexE old.prod.exhaust)
qed

lemma drinks_reject_0_2: "\<nexists>i. a = (STR ''select'', [i]) \<Longrightarrow> possible_steps drinks 0 r (fst a) (snd a) = {||}"
  apply (rule drinks_0_rejects)
  by (cases a, case_tac "snd a", auto)

(*Here's the lemma for which
proof(induction t rule: input_simulation_induct arbitrary: r)
breaks
*)

lemma input_simulation_1_2: "input_simulation drinks 1 r drinks2 2 r t"
proof(induction t arbitrary: r)
  case Nil
  then show ?case
    by (simp add: input_simulation.base)
next
  case (Cons a t)
  then show ?case
    apply (cases a, clarify)
    apply simp
    subgoal for l i
      apply (rule input_simulation.step)
      apply (case_tac "l = STR ''coin'' \<and> length i = 1")
       apply (simp add: possible_steps_1_coin possible_steps_2_coin coin_def)
      apply (case_tac "a=(STR ''vend'', [])")
       apply (case_tac "r$2")
      using drinks_vend_invalid apply simp
       apply (case_tac aa)
        apply (case_tac "x1 < 100")
         apply (clarify, simp add: drinks_vend_insufficient drinks2_vend_insufficient2)
        apply (clarify, simp add: drinks_vend_sufficient drinks2_vend_sufficient)
        apply (induct t)
         apply (simp add: input_simulation.base)
        apply (case_tac aa, clarify)
        apply (rule input_simulation.step)
        apply (simp add: drinks_end)
      using drinks_vend_invalid apply simp
      using drinks_1_rejects by auto
    done
qed

lemma input_simulation_1_1: "input_simulation drinks 1 <2 $:= Some (Num 0), 1 $:= i> drinks2 1 <2 $:= Some (Num 0), 1 $:= i> t"
proof(induction rule: input_simulation_induct)
  case (1 l i t)
  then show ?case
    apply (case_tac "l = STR ''coin'' \<and> length i = 1")
     apply (rule input_simulation.step)
     apply (simp add: possible_steps_1_coin possible_steps_1 input_simulation_1_2)
    apply (case_tac "l = STR ''vend'' \<and> i = []")
     apply (rule input_simulation.step)
     apply (simp add: drinks_vend_insufficient drinks2_vend_insufficient transitions finfun_update_twist apply_updates_def)
     apply (rule input_simulation.step)
    using drinks_1_rejects by auto
qed

lemma input_simulation: "input_simulates drinks drinks2"
proof(induction rule: input_simulates_induct)
  case (1 l i t)
  then show ?case
    apply (case_tac "l = STR ''select'' \<and> length i = 1")
     apply simp
     apply (rule input_simulation.step)
     apply (simp add: possible_steps_0 Drinks_Machine.possible_steps_0 select_def apply_updates_def)
    using input_simulation_1_1
    apply (simp add: finfun_update_twist)
     apply (rule input_simulation.step)
    using drinks_0_rejects by auto
qed

lemma acceptance: "accepts_trace drinks t \<Longrightarrow> accepts_trace drinks2 t"
  using input_simulation input_simulates_accepts_trace
  by simp

lemma purchase_coke: "observe_trace drinks2 0 <> [((STR ''select''), [Str ''coke'']), ((STR ''coin''), [Num 50]), ((STR ''coin''), [Num 50]), ((STR ''vend''), [])] =
                       [[], [Some (Num 50)], [Some (Num 100)], [Some (Str ''coke'')]]"
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_0)
     apply (simp add: select_def join_ir_def input2state_def accepts_from_1 acceptance)
    apply (simp add: select_def)
  apply (rule observe_trace_possible_step)
      apply (simp add: possible_steps_1)
     apply (simp add: coin_def value_plus_def join_ir_def input2state_def)
  using accepts_1_2 accepts_from_1a
    apply (simp add: coin_def value_plus_def join_ir_def input2state_def apply_outputs_def apply_updates_def)
   apply (simp add: coin_def value_plus_def join_ir_def input2state_def)
  apply (rule observe_trace_possible_step)
      apply (simp add: possible_steps_2_coin)
     apply (simp add: coin_def value_plus_def join_ir_def input2state_def accepts_from_2 accepts_1_2)
    apply (simp add: coin_def value_plus_def join_ir_def input2state_def apply_outputs_def apply_updates_def)
   apply (simp add: coin_def value_plus_def join_ir_def input2state_def)
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_2_vend apply_updates_def value_plus_def input2state_def)
    apply (simp add: apply_outputs_def vend_def apply_updates_def input2state_def)
   apply (simp add: vend_def apply_updates_def)
  by simp

lemma drinks2_0_invalid: "\<not> (aa = (STR ''select'') \<and> length (b) = 1) \<Longrightarrow>
    (possible_steps drinks2 0 <> aa b) = {||}"
  apply (simp add: drinks2_def possible_steps_def transitions)
  by force

lemma drinks2_vend_r2_none: "r $ 2 = None \<Longrightarrow> possible_steps drinks2 2 r ((STR ''vend'')) [] = {||}"
  apply (simp add: possible_steps_empty drinks2_def can_take_transition_def can_take_def transitions)
  by (simp add: value_gt_def)

lemma drinks2_end: "possible_steps drinks2 3 r a b = {||}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma drinks2_vend_r2_String: "r $ 2 = Some (value.Str x2) \<Longrightarrow>
                possible_steps drinks2 2 r ((STR ''vend'')) [] = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions can_take_transition_def can_take_def value_gt_def)

lemma drinks2_2_invalid: "fst a = (STR ''coin'') \<longrightarrow> length (snd a) \<noteq> 1 \<Longrightarrow>
          a \<noteq> ((STR ''vend''), []) \<Longrightarrow>
          possible_steps drinks2 2 r (fst a) (snd a) = {||}"
  apply (simp add: possible_steps_empty drinks2_def transitions can_take_transition_def can_take_def)
  by (metis prod.collapse)

lemma drinks2_1_invalid: "\<not>(a = (STR ''coin'') \<and> length b = 1) \<Longrightarrow>
      \<not>(a = (STR ''vend'') \<and> b = []) \<Longrightarrow>
    possible_steps drinks2 1 r a b = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions can_take_transition_def can_take_def value_gt_def)

lemma drinks2_vend_invalid: "\<nexists>n. r $ 2 = Some (Num n) \<Longrightarrow> possible_steps drinks2 2 r (STR ''vend'') [] = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions can_take_transition_def can_take_def value_gt_def MaybeBoolInt_not_num_1)

lemma equiv_1_2: "observe_trace drinks 1 r t = observe_trace drinks2 2 r t"
proof(induct t arbitrary: r)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply (case_tac "fst a = STR ''coin'' \<and> length (snd a) = 1")
     defer
     apply (case_tac "a = (STR ''vend'', [])")
      defer
      apply (rule observe_trace_no_possible_steps)
       apply (simp add: drinks_1_rejects)
      apply (simp add: drinks2_2_invalid)
     apply (rule observe_trace_one_possible_step)
          apply (simp add: possible_steps_1_coin)
         apply (simp add: possible_steps_2_coin)
        apply simp+
    apply (case_tac "\<exists>n. r $ 2 = Some (Num n)")
     defer
     apply (rule observe_trace_no_possible_steps)
      apply (simp add: drinks_vend_invalid)
     apply (simp add: drinks2_vend_invalid)
    apply clarify
    apply (case_tac "n < 100")
     apply (rule observe_trace_one_possible_step)
          apply (simp add: Drinks_Machine.drinks_vend_insufficient)
         apply (simp add: drinks2_vend_insufficient2)
        apply simp+
    apply (rule observe_trace_one_possible_step)
         apply (simp add: Drinks_Machine.drinks_vend_sufficient)
        apply (simp add: drinks2_vend_sufficient)
       apply simp+
    apply (induct t)
     apply simp
    apply (rule observe_trace_no_possible_steps)
     apply (simp add: drinks_end)
    by (simp add: drinks2_end)
qed

lemma equiv_1_1: "observe_trace drinks 1 <2 $:= Some (Num 0), 1 $:= i> t = observe_trace drinks2 1 <2 $:= Some (Num 0), 1 $:= i> t"
proof(induct t)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply (case_tac "fst a = STR ''coin'' \<and> length (snd a) = 1")
     defer
     apply (case_tac "a = (STR ''vend'', [])")
      defer
      apply (rule observe_trace_no_possible_steps)
       apply (simp add: drinks_1_rejects)
      apply (metis drinks2_1_invalid prod.collapse)
     apply (rule observe_trace_one_possible_step)
          apply (simp add: possible_steps_1_coin)
         apply (simp add: possible_steps_1)
        apply simp+
     apply (simp add: equiv_1_2)
    apply (rule observe_trace_one_possible_step)
         apply (simp add: drinks_vend_insufficient)
        apply (simp add: drinks2_vend_insufficient)
       apply (simp add: vend_fail_def vend_nothing_def)+
    by (simp add: datastate(1) finfun_update_twist apply_updates_def)
qed

(* Corresponds to Example 3 in Foster et. al. *)
lemma observational_equivalence: "observably_equivalent drinks drinks2 t"
proof (induct t)
  case Nil
  then show ?case
    by (simp add: observably_equivalent_def)
  next
  case (Cons a t)
  then show ?case
    apply (simp add: observably_equivalent_def)
    apply (case_tac "fst a = STR ''select'' \<and> length (snd a) = 1")
     apply (rule observe_trace_one_possible_step)
          apply (simp add: Drinks_Machine.possible_steps_0)
         apply (simp add: possible_steps_0)
       apply simp+
     apply (simp add: select_def join_ir_def input2state_nth apply_updates_def)
     apply (metis equiv_1_1 empty_None finfun_update_twist numeral_eq_one_iff semiring_norm(85))
     apply (rule observe_trace_no_possible_steps)
    using drinks_0_rejects apply blast
    using drinks2_0_invalid by auto
qed

end
