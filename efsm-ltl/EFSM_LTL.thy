theory EFSM_LTL
imports "../EFSM" "HOL-Library.Linear_Temporal_Logic_on_Streams"
begin

text_raw\<open>\snip{statedef}{1}{2}{%\<close>
record state =
  statename :: "nat option"
  datastate :: registers
  action :: action
  "output" :: outputs
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{whitebox}{1}{2}{%\<close>
type_synonym whitebox_trace = "state stream"
text_raw\<open>}%endsnip\<close>

type_synonym property = "whitebox_trace \<Rightarrow> bool"

abbreviation label :: "state \<Rightarrow> String.literal" where
  "label s \<equiv> fst (action s)"

abbreviation inputs :: "state \<Rightarrow> value list" where
  "inputs s \<equiv> snd (action s)"

text_raw\<open>\snip{ltlStep}{1}{2}{%\<close>
fun ltl_step :: "transition_matrix \<Rightarrow> cfstate option \<Rightarrow> registers \<Rightarrow> action \<Rightarrow> (nat option \<times> outputs \<times> registers)" where
  "ltl_step _ None r _ = (None, [], r)" |
  "ltl_step e (Some s) r (l, i) = (let possibilities = possible_steps e s r l i in
                   if possibilities = {||} then (None, [], r)
                   else
                     let (s', t) = Eps (\<lambda>x. x |\<in>| possibilities) in
                     (Some s', (evaluate_outputs t i r), (evaluate_updates t i r))
                  )"
text_raw\<open>}%endsnip\<close>

lemma ltl_step_alt:
  "ltl_step e (Some s) r t = (let possibilities = possible_steps e s r (fst t) (snd t) in
                   if possibilities = {||} then (None, [], r)
                   else
                     let (s', t') = Eps (\<lambda>x. x |\<in>| possibilities) in
                     (Some s', (apply_outputs (Outputs t') (join_ir (snd t) r)), (apply_updates (Updates t') (join_ir (snd t) r) r))
                  )"
  apply (case_tac t)
  by (simp add: Let_def)

lemma ltl_step_none:
  "possible_steps e s r (fst ie) (snd ie) = {||} \<Longrightarrow>
   ltl_step e (Some s) r ie = (None, [], r)"
  by (simp add: ltl_step_alt)

lemma ltl_step_some: assumes "possible_steps e s r l i = {|(s', t)|}"
      and "evaluate_outputs t i r = p"
      and "evaluate_updates t i r = r'"
    shows "ltl_step e (Some s) r (l, i) = (Some s', p, r')"
  by (simp add: assms)

lemma ltl_step_cases: assumes invalid: "P (None, [], r)"
  assumes valid: "\<forall>(s', t) |\<in>| (possible_steps e s r l i). P (Some s', (evaluate_outputs t i r), (evaluate_updates t i r))"
  shows "P (ltl_step e (Some s) r (l, i))"
  apply simp
  apply (case_tac "possible_steps e s r l i")
   apply (simp add: invalid)
  apply simp
  apply (case_tac "SOME xa. xa = x \<or> xa |\<in>| S'")
  apply simp
  apply (insert assms(2))
  apply (simp add: fBall_def Ball_def fmember_def)
  by (metis (mono_tags, lifting) fst_conv prod.case_eq_if snd_conv someI_ex)

text_raw\<open>\snip{makeFullObservation}{1}{2}{%\<close>
primcorec make_full_observation :: "transition_matrix \<Rightarrow> cfstate option \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> action stream \<Rightarrow> whitebox_trace" where
  "make_full_observation e s d p i = (
    let (s', o', d') = ltl_step e s d (shd i) in
    \<lparr>statename = s, datastate = d, action=(shd i), output = p\<rparr>##(make_full_observation e s' d' o' (stl i))
  )"
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{watch}{1}{2}{%\<close>
definition watch :: "transition_matrix \<Rightarrow> action stream \<Rightarrow> whitebox_trace" where
  "watch e i \<equiv> (make_full_observation e (Some 0) <> [] i)"
text_raw\<open>}%endsnip\<close>

definition state_eq :: "nat option \<Rightarrow> whitebox_trace \<Rightarrow> bool" where
  "state_eq v s \<equiv> statename (shd s) = v"

lemma state_eq_holds: "state_eq s = holds (\<lambda>x. statename x = s)"
  apply (rule ext)
  by (simp add: state_eq_def holds_def)

lemma state_eq_None_not_Some:
  "state_eq None s \<Longrightarrow> \<not> state_eq (Some n) s"
  by (simp add: state_eq_def)

definition label_eq :: "string \<Rightarrow> whitebox_trace \<Rightarrow> bool" where
  "label_eq v s \<equiv> fst (action (shd s)) = (String.implode v)"

lemma watch_label: "label_eq l (watch e t) = (fst (shd t) = String.implode l)"
  by (simp add: label_eq_def watch_def)

definition input_eq :: "value list \<Rightarrow> whitebox_trace \<Rightarrow> bool" where
  "input_eq v s \<equiv> inputs (shd s) = v"

definition action_eq :: "(string \<times> inputs) \<Rightarrow> whitebox_trace \<Rightarrow> bool" where
  "action_eq e = label_eq (fst e) aand input_eq (snd e)"

lemmas action_eq = action_eq_def label_eq_def input_eq_def

definition output_eq :: "value option list \<Rightarrow> whitebox_trace \<Rightarrow> bool" where
  "output_eq v s \<equiv> output (shd s) = v"

lemma shd_state_is_none: "(state_eq None) (make_full_observation e None r p t)"
  by (simp add: state_eq_def)

lemma unfold_observe_none:
  "make_full_observation e None d p t = (\<lparr>statename = None, datastate = d, action=(shd t), output = p\<rparr>##(make_full_observation e None d [] (stl t)))"
  by (simp add: stream.expand)

lemma once_none_always_none:
  "alw (state_eq None) (make_full_observation e None r p t)"
proof -
  obtain ssa :: "((String.literal \<times> value list) stream \<Rightarrow> whitebox_trace) \<Rightarrow> (String.literal \<times> value list) stream" where
      "\<forall>f p s. f (stl (ssa f)) \<noteq> stl (f (ssa f)) \<or> alw p (f s) = alw (\<lambda>s. p (f s)) s"
    by (metis (no_types) alw_inv)
  then have "alw (state_eq None) (make_full_observation e None r [] (stl t))"
    by (metis (no_types) all_imp_alw shd_state_is_none stream.sel(2) unfold_observe_none)
  then show ?thesis
    by (metis (no_types) alw.simps shd_state_is_none stream.sel(2) unfold_observe_none)
qed

lemma once_none_nxt_always_none:
  "alw (nxt (state_eq None)) (make_full_observation e None r p t)"
proof(coinduction)
  case alw
  then show ?case
    apply simp
    by (metis alw_iff_sdrop nxt.simps once_none_always_none sdrop_simps(2) shd_state_is_none)
qed

lemma no_output_none:
  "nxt (alw (output_eq [])) (make_full_observation e None r p t)"
proof -
  obtain ss :: "((String.literal \<times> value list) stream \<Rightarrow> whitebox_trace) \<Rightarrow> (String.literal \<times> value list) stream" where
    "\<forall>f p s. f (stl (ss f)) \<noteq> stl (f (ss f)) \<or> alw p (f s) = alw (\<lambda>s. p (f s)) s"
    by (metis (no_types) alw_inv)
  then show ?thesis
    by (simp add: output_eq_def all_imp_alw)
qed

lemma no_output_none_nxt:
  "alw (nxt (output_eq [])) (make_full_observation e None r p t)"
  by (metis alw_inv alw_mono no_output_none nxt.simps)

lemma no_output_none_if_empty:
  "alw (output_eq []) (make_full_observation e None r [] t)"
  by (metis alw_nxt make_full_observation.sel(1) no_output_none output_eq_def state.select_convs(4))

lemma no_updates_none:
  "alw (\<lambda>x. datastate (shd x) = r) (make_full_observation e None r p t)"
proof -
  have "alw (\<lambda>x. datastate (shd x) = r) (make_full_observation e None r [] (stl t))"
    proof -
      obtain ss :: "((String.literal \<times> value list) stream \<Rightarrow> whitebox_trace) \<Rightarrow> (String.literal \<times> value list) stream" where
        "\<forall>f p s. f (stl (ss f)) \<noteq> stl (f (ss f)) \<or> alw p (f s) = alw (\<lambda>s. p (f s)) s"
        by (metis (no_types) alw_inv)
      then show ?thesis
        by (simp add: output_eq_def all_imp_alw)
    qed
    then show ?thesis
    proof(coinduction)
      case alw
      then show ?case
        by simp
    qed
  qed

lemma action_components:
  "(label_eq l aand input_eq i) s = (action (shd s) = (String.implode l, i))"
  apply (simp add: label_eq_def input_eq_def)
  by (metis fst_conv prod.collapse snd_conv)

lemma alw_not_some:
  "alw (\<lambda>xs. statename (shd xs) \<noteq> Some s) (make_full_observation e None r p t)"
  by (metis (mono_tags, lifting) alw_mono once_none_always_none option.distinct(1) state_eq_def)

lemma state_none:
  "((state_eq None) impl nxt (state_eq None)) (make_full_observation e s r p t)"
  by (simp add: state_eq_def)

lemma state_none_2:
  "(state_eq None) (make_full_observation e s r p t) \<Longrightarrow>
   (state_eq None) (make_full_observation e s r p (stl t))"
  by (simp add: state_eq_def)

lemma decompose_pair: "e \<noteq> (l, i) = (\<not> (fst e =l \<and> snd e = i))"
  by (metis fst_conv prod.collapse sndI)

text_raw\<open>\snip{ltlVName}{1}{2}{%\<close>
datatype ltl_vname = Ip nat | Op nat | Rg nat
text_raw\<open>}%endsnip\<close>

type_synonym ltl_gexp = "ltl_vname gexp"

definition join_iro :: "value list \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> ltl_vname datastate" where
  "join_iro i r p = (\<lambda>x. case x of
    Rg n \<Rightarrow> r $ n |
    Ip n \<Rightarrow> Some (i ! n) |
    Op n \<Rightarrow> p ! n
  )"

lemma join_iro_R [simp]: "join_iro i r p (Rg n) = r $ n"
  by (simp add: join_iro_def)

definition check_exp :: "ltl_gexp \<Rightarrow> whitebox_trace \<Rightarrow> bool" where
  "check_exp g s = (gval g (join_iro (snd (action (shd s))) (datastate (shd s)) (output (shd s))) = trilean.true)"

lemma alw_ev: "alw f = not (ev (\<lambda>s. \<not>f s))"
  by simp

lemma stream_eq_scons:
  "shd x = h \<Longrightarrow>
   stl x = t \<Longrightarrow>
   x = h##t"
  by auto

lemma alw_state_eq_smap:
  "alw (state_eq s) ss = alw (\<lambda>ss. shd ss = s) (smap statename ss)"
  apply standard
   apply (simp add: alw_iff_sdrop state_eq_def)
  by (simp add: alw_mono alw_smap state_eq_def)

lemma alw_holds: "alw (holds P) (h##t) = (P h \<and> alw (holds P) t)"
  apply standard
   apply auto[1]
  by (metis alw.simps holds_Stream stream.sel(2))

lemma alw_holds2: "alw (holds P) ss = (P (shd ss) \<and> alw (holds P) (stl ss))"
  by (meson alw.simps holds.elims(2) holds.elims(3))

lemma snth_sconst: "(\<forall>i. s !! i = h) = (s = sconst h)"
  by (metis funpow_code_def id_funpow sdrop_simps(1) sdrop_siterate siterate.simps(1) smap_alt smap_sconst snth.simps(1) stream.map_id)

lemma alw_sconst: "(alw (\<lambda>xs. shd xs = h) t) = (t = sconst h)"
  by (simp add: snth_sconst[symmetric] alw_iff_sdrop)

lemma smap_statename_None:
  "smap statename (make_full_observation e None r p i) = sconst None"
  by (meson EFSM_LTL.alw_sconst alw_state_eq_smap once_none_always_none)

(* Out of interest, Nitpick finds a spurious counterexample to this *)
lemma sdrop_if_suntil:
  "(p suntil q) \<omega> \<Longrightarrow>
   \<exists>j. q (sdrop j \<omega>) \<and> (\<forall>k < j. p (sdrop k \<omega>))"
proof(induction rule: suntil.induct)
  case (base \<omega>)
then show ?case
  by force
next
  case (step \<omega>)
  then show ?case
    apply clarify
    apply (rule_tac x="j+1" in exI)
    apply simp
    using ev_at_imp_snth less_Suc_eq_0_disj by auto
qed

lemma suntil_implies_until:
  "(\<phi> suntil \<psi>) \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega>"
  by (simp add: UNTIL.base UNTIL.step suntil_induct_strong)

lemma alw_implies_until:
  "alw \<phi> \<omega> \<Longrightarrow> (\<phi> until \<psi>) \<omega>"
  by (metis until_false until_mono)

lemma until_ev_suntil:
  "ev \<psi> \<omega> \<Longrightarrow>
   (\<phi> until \<psi>) \<omega> \<Longrightarrow>
   (\<phi> suntil \<psi>) \<omega>"
proof(induction rule: ev.induct)
  case (base xs)
  then show ?case
    by (simp add: suntil.base)
next
  case (step xs)
  then show ?case
    by (metis UNTIL.cases suntil.base suntil.step)
qed

lemma suntil_as_until:
  "(\<phi> suntil \<psi>) \<omega> = ((\<phi> until \<psi>) \<omega> \<and> ev \<psi> \<omega>)"
  using ev_suntil suntil_implies_until until_ev_suntil by blast

lemma not_relesased_yet:
  "(\<phi> until \<psi>) \<omega> \<Longrightarrow>
   \<not> \<psi> \<omega> \<Longrightarrow>
   \<phi> \<omega>"
  using UNTIL.cases by auto

lemma until_must_release:
  "ev (not \<phi>) \<omega> \<Longrightarrow>
   (\<phi> until \<psi>) \<omega> \<Longrightarrow>
   ev \<psi> \<omega>"
proof(induction rule: ev.induct)
  case (base xs)
  then show ?case
    using not_relesased_yet by blast
next
  case (step xs)
  then show ?case
    using UNTIL.cases by blast
qed

lemma until_as_suntil:
  "(\<phi> until \<psi>) \<omega> = ((\<phi> suntil \<psi>) or (alw \<phi>)) \<omega>"
  using alw_implies_until not_alw_iff suntil_implies_until until_ev_suntil until_must_release by blast

lemma not_suntil:
  "(\<not> (p suntil q) \<omega>) = (\<not> (p until q) \<omega> \<or> alw (not q) \<omega>)"
  by (simp add: suntil_as_until alw_iff_sdrop ev_iff_sdrop)

lemma "(p until q) \<omega> = (q \<omega> \<or> (p \<omega> \<and> (p until q) (stl \<omega>)))"
  using UNTIL.simps by auto

lemma stl_as_sdrop: "stl s = sdrop 1 s"
  by simp

lemma less_suc:
  "(\<forall>k<Suc j. p (sdrop k \<omega>)) = ((\<forall>k< j. p (sdrop k \<omega>)) \<and> p (sdrop j \<omega>))"
  using less_Suc_eq by auto

lemma sdrop_until:
  "q (sdrop j \<omega>) \<Longrightarrow>
   \<forall>k<j. p (sdrop k \<omega>) \<Longrightarrow>
   (p until q) \<omega>"
proof(induct j arbitrary: \<omega>)
  case 0
  then show ?case
    by (simp add: UNTIL.base)
next
  case (Suc j)
  then show ?case
    by (metis Suc_mono UNTIL.simps sdrop.simps(1) sdrop.simps(2) zero_less_Suc)
qed

lemma sdrop_suntil:
  "q (sdrop j \<omega>) \<Longrightarrow>
   (\<forall>k < j. p (sdrop k \<omega>)) \<Longrightarrow>
   (p suntil q) \<omega>"
  apply (simp add: suntil_as_until conj_commute)
  apply standard
   apply (simp add: nxt_ev nxt_sdrop)
  by (simp add: sdrop_until)

lemma sdrop_iff_suntil:
  "(p suntil q) \<omega> = (\<exists>j. q (sdrop j \<omega>) \<and> (\<forall>k < j. p (sdrop k \<omega>)))"
  using sdrop_if_suntil sdrop_suntil by blast

end
