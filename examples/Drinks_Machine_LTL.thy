theory Drinks_Machine_LTL
imports "Drinks_Machine" "EFSM.EFSM_LTL"
begin

lemma LTL_r2_not_always_gt_100:
  "not (alw (check_exp (Gt (V (Rg 2)) (L (Num 100))))) (watch drinks i)"
  apply (simp add: not_alw_iff watch_def)
  apply (rule ev.base)
  by (simp add: check_exp_def value_gt_def)

lemma possible_steps_select_wrong_arity: "a = STR ''select'' \<Longrightarrow>
       length b \<noteq> 1 \<Longrightarrow>
       possible_steps drinks 0 <> a b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: select_def)

lemma possible_steps_0_not_select: "a \<noteq> STR ''select'' \<Longrightarrow>
       possible_steps drinks 0 <> a b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: select_def)

lemma statename_smap: "alw (nxt (state_eq (Some 2)) impl (state_eq (Some 1))) s =
       alw (nxt (\<lambda>x. shd x = (Some 2)) impl (\<lambda>x. shd x = (Some 1))) (smap statename s)"
  by (simp add: state_eq_def alw_iff_sdrop)

lemma drinks_no_possible_steps_1:
  assumes not_coin: "\<not> (a = STR ''coin'' \<and> length b = 1)"
      and not_vend: "\<not> (a = STR ''vend'' \<and> b = [])"
shows "possible_steps drinks 1 r a b = {||}"
  using drinks_1_rejects not_coin not_vend by auto

lemma apply_updates_vend: "apply_updates (Updates vend) (join_ir [] r) r = r"
  by (simp add: vend_def apply_updates_def)

lemma drinks_step_2_none: "ltl_step drinks (Some 2) r e = (None, [], r)"
  by (simp add: drinks_end ltl_step_none)

lemma one_before_two_2:
  "alw (\<lambda>x. statename (shd (stl x)) = Some 2 \<longrightarrow> statename (shd x) = Some 1) (make_full_observation drinks (Some 2) r [r $ 1] x2a)"
proof(coinduction)
  case alw
  then show ?case
    apply simp
    apply standard
    apply (simp add: drinks_end ltl_step_none)
    apply (rule disjI2)
    apply (simp add: drinks_step_2_none)
    by (metis (mono_tags, lifting) alw_mono nxt.simps once_none_nxt_always_none option.simps(3) state_eq_def)
qed

lemma one_before_two_aux:
  assumes "\<exists> p r i. j = nxt (make_full_observation drinks (Some 1) r p) i"
  shows "alw (\<lambda>x. nxt (state_eq (Some 2)) x \<longrightarrow> state_eq (Some 1) x) j"
  using assms apply(coinduct)
  apply (simp add: state_eq_def)
  apply clarify
  apply standard
   apply simp
  subgoal for x p r i
    apply (cases i, simp)
    subgoal for x1 x2
    apply (cases x2, simp)
      subgoal for x1a x2a
        apply (cases x1a, simp)
        apply (case_tac "possible_steps drinks 1 r a b = {||}")
         apply simp
        apply (rule disjI2)
        apply (metis (mono_tags, lifting) alw_iff_sdrop once_none_always_none option.distinct(1) sdrop_simps(2) state_eq_def)
        apply simp
        apply (case_tac "SOME x. x |\<in>| possible_steps drinks 1 r a b")
        apply simp
        subgoal for a b s' t
          apply (case_tac "a = STR ''coin'' \<and> length b = 1")
           apply (simp add: possible_steps_1_coin)
           apply (metis stream.sel(2))
          apply (case_tac "a = STR ''vend'' \<and> b = []")
           defer
           apply (simp add: drinks_no_possible_steps_1)
          apply (cases "r $ 2")
           apply (simp add: drinks_vend_invalid)
          subgoal for v
            apply (cases v)
             defer
           apply (simp add: drinks_vend_invalid)
            subgoal for n
              apply (case_tac "n < 100")
               apply (simp add: drinks_vend_insufficient)
               apply (metis stream.sel(2))
              apply (rule disjI2)
              apply (simp add: drinks_vend_sufficient apply_updates_vend)
              apply clarify
              by (simp add: vend_def apply_outputs_def one_before_two_2)
            done
          done
        done
      done
    done
  done

(* Here is the lemma with quantified variables that I am trying to prove *)
lemma "alw (\<lambda>x. nxt (state_eq (Some 2)) x \<longrightarrow> state_eq (Some 1) x)
            (nxt (make_full_observation drinks (Some 1) r p) i)"
  using one_before_two_aux by blast

lemma LTL_nxt_2_means_vend:
  "alw (nxt (state_eq (Some 2)) impl (state_eq (Some 1))) (watch drinks i)"
  apply (simp only: statename_smap watch_def)
  apply simp
proof(coinduction)
  case alw
  then show ?case
    apply simp
    apply (case_tac "shd i")
    apply (case_tac "a \<noteq> STR ''select''")
     apply (simp add: possible_steps_0_not_select)
     apply (rule disjI2, rule alw_mono[of "\<lambda>x. shd (stl x) = None"])
      apply (simp add: smap_statename_None Linear_Temporal_Logic_on_Streams.alw_sconst)
     apply simp
    apply (case_tac "length b \<noteq> 1")
     apply (simp add: possible_steps_select_wrong_arity)
     apply (rule disjI2, rule alw_mono[of "\<lambda>x. shd (stl x) = None"])
      apply (simp add: smap_statename_None Linear_Temporal_Logic_on_Streams.alw_sconst)
     apply simp
    apply (simp add: possible_steps_0 select_def)
    apply (rule disjI2)
    apply (simp add: alw_smap state_eq_def[symmetric])
    apply (simp only: nxt.simps[symmetric])
    using one_before_two_aux by blast
qed

lemma possible_steps_0_invalid:
  "\<not> (l = STR ''select'' \<and> length i = 1) \<Longrightarrow>
   possible_steps drinks 0 <> l i = {||}"
  using possible_steps_0_not_select possible_steps_select_wrong_arity by fastforce

lemma costsMoney_aux:
  assumes "\<exists>p r i. j = (nxt (make_full_observation drinks (Some 1) r p) i)"
  shows "alw (\<lambda>xs. nxt (state_eq (Some 2)) xs \<longrightarrow> check_exp (Ge (V (Rg 2)) (L (Num 100))) xs) j"
  using assms apply(coinduct)
  apply (simp add: state_eq_def)
  apply clarify
  apply (case_tac i)
  apply clarify
  apply simp
  apply (case_tac x2)
  apply clarify
  apply simp
  apply (case_tac "a = STR ''vend'' \<and> b = []")
   apply simp
   apply (case_tac "r $ 2")
    apply (simp add: drinks_vend_invalid)
    apply (rule disjI2)
    apply (rule alw_mono[of "nxt (state_eq None)"])
     apply (simp add: once_none_nxt_always_none)
    apply (simp add: state_eq_def)
   apply (case_tac aa)
    defer
    apply (simp add: drinks_vend_invalid)
    apply (rule disjI2)
    apply (rule alw_mono[of "nxt (state_eq None)"])
     apply (simp add: once_none_nxt_always_none)
    apply (simp add: state_eq_def)
   apply (case_tac "a = STR ''coin'' \<and> length b = 1")
    prefer 2
    apply (simp add: drinks_no_possible_steps_1)
    apply (rule disjI2)
    apply (rule alw_mono[of "nxt (state_eq None)"])
     apply (simp add: once_none_nxt_always_none)
    apply (simp add: state_eq_def)
   apply (simp add: possible_steps_1_coin)
   apply (rule disjI1)
   apply (metis stream.sel(2))
  apply clarify
  apply simp
  apply (case_tac "x1 < 100")
   apply (simp add: drinks_vend_insufficient)
   apply (metis stream.sel(2))
  apply (simp add: drinks_vend_sufficient apply_updates_vend)
  apply standard
   apply (simp add: check_exp_def connectives value_gt_def)
  apply (rule disjI2)
  apply (rule alw_mono[of "nxt (state_eq None)"])
   apply (coinduction, simp)
   apply (simp add: state_eq_def drinks_step_2_none once_none_nxt_always_none)
  by (simp add: state_eq_def)

(* costsMoney: THEOREM drinks |- G(X(cfstate=State_2) => gval(value_ge(r_2, Some(NUM(100))))); *)
lemma LTL_costsMoney:
  "(alw (nxt (state_eq (Some 2)) impl (check_exp (Ge (V (Rg 2)) (L (Num 100)))))) (watch drinks i)"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: watch_def state_eq_def)
    apply (cases "shd i")
    subgoal for l ip
      apply (case_tac "l = STR ''select'' \<and> length ip = 1")
       defer
       apply (simp add: possible_steps_0_invalid)
       apply (rule disjI2)
       apply (rule alw_mono[of "nxt (state_eq None)"])
        apply (simp add: once_none_nxt_always_none)
       apply (simp add: state_eq_def)
      apply (simp add: possible_steps_0 select_def)
      apply (rule disjI2)
      apply (simp add: state_eq_def[symmetric])
      apply (simp only: nxt.simps[symmetric])
      using costsMoney_aux by blast
    done
qed

lemma LTL_costsMoney_aux:
  "(alw (not (check_exp (Ge (V (Rg 2)) (L (Num 100)))) impl (not (nxt (state_eq (Some 2)))))) (watch drinks i)"
  by (metis (no_types, lifting) LTL_costsMoney alw_mono)

lemma implode_select: "String.implode ''select'' = STR ''select''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_coin: "String.implode ''coin'' = STR ''coin''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_vend: "String.implode ''vend'' = STR ''vend''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemmas implode_labels = implode_select implode_coin implode_vend(* neverReachS2: THEOREM drinks |- label=select AND I(1) = STR(String_coke) AND
                                X(label=coin AND I(1) = NUM(100)) AND
                                X(X(label=vendAND I=InputSequence !empty)) => X(X(X(cfstate=State_2)));;*)
lemma LTL_neverReachS2:"(((((action_eq (''select'', [Str ''coke''])))
                    aand
                    (nxt ((action_eq (''coin'', [Num 100])))))
                    aand
                    (nxt (nxt((label_eq ''vend'' aand (input_eq []))))))
                    impl
                    (nxt (nxt (nxt (state_eq (Some 2))))))
                    (watch drinks i)"
  apply (simp add: watch_def action_eq implode_labels)
  apply (cases i)
  apply clarify
  apply simp
  apply (simp add: possible_steps_0 select_def)
  apply (case_tac "shd x2", clarify)
  apply (simp add: possible_steps_1_coin coin_def value_plus_def finfun_update_twist apply_updates_def)
  apply (case_tac "shd (stl x2)", clarify)
  by (simp add: drinks_vend_sufficient state_eq_def)

lemma ltl_step_not_select:
  "\<nexists>i. e = (STR ''select'', [i]) \<Longrightarrow>
   ltl_step drinks (Some 0) r e = (None, [], r)"
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def select_def)
  by (cases e, case_tac b, auto)

lemma ltl_step_select:
  "ltl_step drinks (Some 0) <> (STR ''select'', [i]) = (Some 1, [], <1 $:= Some i, 2 $:= Some (Num 0)>)"
  apply (rule  ltl_step_some[of _ _ _ _ _ _ select])
    apply (simp add: possible_steps_0)
   apply (simp add: select_def)
  by (simp add: select_def finfun_update_twist apply_updates_def)

lemma ltl_step_not_coin_or_vend:
  "\<nexists>i. e = (STR ''coin'', [i]) \<Longrightarrow>
    e \<noteq> (STR ''vend'', []) \<Longrightarrow>
    ltl_step drinks (Some 1) r e = (None, [], r)"
  apply (rule ltl_step_none)
  apply (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def transitions)
  by (case_tac e, case_tac b, auto)

lemma ltl_step_coin:
  "\<exists>p r'. ltl_step drinks (Some 1) r (STR ''coin'', [i]) = (Some 1, p, r')"
  by (simp add: possible_steps_1_coin)

lemma alw_tl:
  "alw \<phi> (make_full_observation e (Some 0) <> [] xs) \<Longrightarrow>
    alw \<phi>
     (make_full_observation e (fst (ltl_step e (Some 0) <> (shd xs))) (snd (snd (ltl_step e (Some 0) <> (shd xs))))
       (fst (snd (ltl_step e (Some 0) <> (shd xs)))) (stl xs))"
  by auto

lemma stop_at_none:
  "alw (\<lambda>xs. output (shd (stl xs)) = [Some (EFSM.Str drink)] \<longrightarrow> check_exp (Ge (V (Rg 2)) (L (Num 100))) xs)
            (make_full_observation drinks None r p t)"
  apply (rule alw_mono[of "nxt (output_eq [])"])
   apply (simp add: no_output_none_nxt)
  by (simp add: output_eq_def)

text\<open>The approach here is to split \texttt{ltl\_step} down to its various cases such that we can
analyse them all separately rather than having to do cases on label and inputs in LTL proofs. Here,
the \texttt{vend\_fail}, \texttt{coin}, and \texttt{invalid} cases don't need guards because they
either don't change the state, or don't have a guard we care about. We need the antecedent of the
vend case since vend has a guard which affects the truth value of \texttt{drinks\_cost\_money}.\<close>

lemma ltl_steps_1:
  assumes vend_fail: "P (Some 1, [], r)"
  assumes coin: "P (Some 1, [value_plus (r$2) (Some (i!0))], r(2 $:= value_plus (r$2) (Some (i!0))))"
  assumes invalid: "P (None, [], r)"
  assumes vend: "possible_steps drinks 1 r l i = {|(2, vend)|} \<longrightarrow> P (Some 2, [r$1], r)"
  shows "P (ltl_step drinks (Some 1) r (l, i))"
proof-
  show ?thesis
    apply (case_tac "l = STR ''coin'' \<and> length i = 1")
     apply (simp add: possible_steps_1_coin coin_def apply_outputs_def finfun_update_twist apply_updates_def coin)
    apply (case_tac "l = STR ''vend'' \<and> i = []")
     apply (case_tac "r $ 2")
      apply (simp add: drinks_vend_invalid invalid)
     apply (case_tac a)
      apply (case_tac "x1 < 100")
       apply (simp add: drinks_vend_insufficient vend_fail_def apply_updates_def)
       apply (metis finfun_upd_triv vend_fail)
      apply (simp add: drinks_vend_sufficient vend_def apply_outputs_def apply_updates_def)
      apply (metis finfun_upd_triv not_le possible_steps_2_vend vend)
     apply (simp add: drinks_vend_r2_String invalid)
    by (simp add: drinks_no_possible_steps_1 invalid)

qed

lemma drink_costs_money_aux:
  assumes "\<exists>p r t. j = make_full_observation drinks (Some 1) r p t"
  shows "alw (\<lambda>xs. output (shd (stl xs)) = [Some (EFSM.Str drink)] \<longrightarrow> check_exp (Ge (V (Rg 2)) (L (Num 100))) xs) j"
  using assms apply coinduct
  apply clarify
  apply simp
  apply (case_tac "shd t")
  apply (simp del: ltl_step.simps)
  apply (rule ltl_steps_1)
     apply auto[1]
  using value_plus_never_string Str_def apply force
   apply simp
   apply (metis (mono_tags, lifting) alw_mono list.distinct(1) no_output_none_nxt nxt.simps output_eq_def)
  apply simp
  apply standard
  apply standard
   apply (simp add: check_exp_def vend_ge_100)
  apply (rule disjI2, coinduction)
  by (simp add: drinks_step_2_none stop_at_none)

lemma LTL_drinks_cost_money:
  "alw (nxt (output_eq [Some (Str drink)]) impl (check_exp (Ge (V (Rg 2)) (L (Num 100))))) (watch drinks t)"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: watch_def output_eq_def)
    apply (case_tac "\<nexists>i. shd t = (STR ''select'', [i])")
     apply (simp add: ltl_step_not_select stop_at_none)
    apply simp
    apply (erule exE)
    apply (simp only: ltl_step_select, simp)
    apply (rule disjI2)
    using drink_costs_money_aux by blast
qed

lemma output_vend_aux:
  assumes "\<exists>p r t. j = make_full_observation drinks (Some 1) r p t"
  shows "alw (\<lambda>xs. label_eq ''vend'' xs \<and> output (shd (stl xs)) = [Some d] \<longrightarrow> check_exp (Ge (V (Rg 2)) (L (Num 100))) xs) j"
proof-
  have steps_1_invalid:
      "\<And>a b r. \<nexists>i. (a, b) = (STR ''coin'', [i]) \<Longrightarrow>
       \<nexists>i. (a, b) = (STR ''vend'', []) \<Longrightarrow>
       possible_steps drinks 1 r a b = {||}"
    subgoal for a b r
      apply (simp add: possible_steps_empty drinks_def transitions can_take_transition_def can_take_def)
      by (induct b, auto)
    done
  show ?thesis
  using assms apply coinduct
  apply clarsimp
  apply (case_tac "\<exists>i. shd t = (STR ''coin'', [i])")
   apply clarsimp
   apply (simp add: possible_steps_1_coin label_eq_def implode_vend)
   apply auto[1]
  apply (case_tac "\<exists>i. shd t = (STR ''vend'', [])")
   apply (case_tac "\<exists>n. r$2 = Some (Num n)")
    apply clarify
    apply (case_tac "n < 100")
     apply (simp add: drinks_vend_insufficient vend_fail_def output_eq_def)
     apply auto[1]
    apply (simp add: drinks_vend_sufficient output_eq_def check_exp_def value_gt_def)
    apply (rule disjI2, rule alw_mono[of "nxt (output_eq [])"])
     apply coinduction
     apply (simp add: alwD drinks_step_2_none no_output_none_if_empty no_output_none_nxt)
    apply (simp add: output_eq_def)
   apply (simp add: drinks_vend_invalid output_eq_def)
   apply (rule disjI2, rule alw_mono[of "nxt (output_eq [])"])
    apply (simp add: no_output_none_nxt)
   apply (simp add: output_eq_def)
  apply (case_tac "shd t")
  apply (simp add: steps_1_invalid output_eq_def)
  apply (rule disjI2, rule alw_mono[of "nxt (output_eq [])"])
   apply (simp add: no_output_none_nxt)
  by (simp add: output_eq_def)
qed

lemma LTL_output_vend:
  "alw (((label_eq ''vend'') aand (nxt (output_eq [Some d]))) impl (check_exp (Ge (V (Rg 2)) (L (Num 100)))))
  (watch drinks t)"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: watch_def output_eq_def)
    apply (case_tac "\<nexists>i. shd t = (STR ''select'', [i])")
     apply (simp add: ltl_step_not_select)
     apply (rule disjI2)
     apply (rule alw_mono[of "nxt (output_eq [])"])
      apply (simp add: no_output_none_nxt)
     apply (simp add: output_eq_def)
    apply simp
    apply (erule exE)
    apply (simp only: ltl_step_select, simp)
    using output_vend_aux by blast
qed


end
