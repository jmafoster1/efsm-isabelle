theory FSet_Utils
  imports "HOL-Library.FSet"
begin

syntax (ASCII)
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3ALL (_/:_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3EX (_/:_)./ _)" [0, 0, 10] 10)
  "_fBex1"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3EX! (_/:_)./ _)" [0, 0, 10] 10)

syntax (input)
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3! (_/:_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3? (_/:_)./ _)" [0, 0, 10] 10)
  "_fBex1"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3?! (_/:_)./ _)" [0, 0, 10] 10)

syntax
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>(_/|\<in>|_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>(_/|\<in>|_)./ _)" [0, 0, 10] 10)
  "_fBnex"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<nexists>(_/|\<in>|_)./ _)" [0, 0, 10] 10)
  "_fBex1"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>!(_/|\<in>|_)./ _)" [0, 0, 10] 10)

translations
  "\<forall>x|\<in>|A. P" \<rightleftharpoons> "CONST fBall A (\<lambda>x. P)"
  "\<exists>x|\<in>|A. P" \<rightleftharpoons> "CONST fBex  A (\<lambda>x. P)"
  "\<nexists>x|\<in>|A. P" \<rightleftharpoons> "CONST fBall A (\<lambda>x. \<not>P)"
  "\<exists>!x|\<in>|A. P" \<rightharpoonup> "\<exists>!x. x |\<in>| A \<and> P"

context includes fset.lifting begin
  lift_definition fprod  :: "'a fset \<Rightarrow> 'b fset \<Rightarrow> ('a \<times> 'b) fset " (infixr "|\<times>|" 80) is "\<lambda>a b. fset a \<times> fset b"
    by simp
  
  lift_definition fis_singleton :: "'a fset \<Rightarrow> bool" is "\<lambda>A. is_singleton (fset A)".
end

lemma fis_singleton_alt: "fis_singleton f = (\<exists>e. f = {|e|})"
  by (metis fis_singleton.rep_eq fset_inverse fset_simps(1) fset_simps(2) is_singleton_def)

definition "fSum \<equiv> fsum (\<lambda>x. x)"

lemma fprod_member: "x |\<in>| xs \<Longrightarrow> y |\<in>| ys \<Longrightarrow> (x, y) |\<in>| xs |\<times>| ys"
  by (simp add: fmember_def fprod_def Abs_fset_inverse)

lemma fprod_empty_l: "{||} |\<times>| a = {||}"
  using bot_fset_def fprod.abs_eq by force

lemma fprod_empty_r: "a |\<times>| {||} = {||}"
  by (simp add: fprod_def bot_fset_def Abs_fset_inverse)

lemmas fprod_empty = fprod_empty_l fprod_empty_r

lemma fprod_finsert: "(finsert a as) |\<times>| (finsert b bs) = finsert (a, b) (fimage (\<lambda>b. (a, b)) bs |\<union>| fimage (\<lambda>a. (a, b)) as |\<union>| (as |\<times>| bs))"
  apply (simp add: finsert_def fprod_def Abs_fset_inverse)
  apply (rule arg_cong[of "(insert (a, b) (fset as \<times> insert b (fset bs) \<union> insert a (fset as) \<times> fset bs))"
                    "(insert (a, b) (Pair a ` fset bs \<union> (\<lambda>a. (a, b)) ` fset as \<union> fset as \<times> fset bs))"
                    Abs_fset])
  by auto

lemma fis_singleton_code [code]: "fis_singleton s = (size s = 1)"
  apply (simp add: fis_singleton_def is_singleton_def)
  by (simp add: card_Suc_eq)

lemma fprod_subseteq: "x |\<subseteq>| x' \<and> y |\<subseteq>| y' \<Longrightarrow> x |\<times>| y |\<subseteq>| x' |\<times>| y'"
  apply (simp add: fprod_def less_eq_fset_def Abs_fset_inverse)
  by auto

lemma fimage_fprod: "(a, b) |\<in>| A |\<times>| B \<Longrightarrow> f a b |\<in>| (\<lambda>(x, y). f x y) |`| (A |\<times>| B)"
  by force

lemma fprod_singletons: "{|a|} |\<times>| {|b|} = {|(a, b)|}"
  apply (simp add: fprod_def)
  by (metis fset_inverse fset_simps(1) fset_simps(2))

lemma fprod_equiv: "(fset (f |\<times>| f') = s) = (((fset f) \<times> (fset f')) = s)"
  by (simp add: fprod_def Abs_fset_inverse)

lemma fset_both_sides: "(Abs_fset s = f) = (fset (Abs_fset s) = fset f)"
  by (simp add: fset_inject)

lemma Abs_ffilter: "(ffilter f s = s') = (Set.filter f (fset s) = (fset s'))"
  by (simp add: ffilter_def fset_both_sides Abs_fset_inverse)

lemma Abs_fimage: "(fimage f s = s') = (Set.image f (fset s) = (fset s'))"
  by (simp add: fimage_def fset_both_sides Abs_fset_inverse)

lemma ffilter_empty [simp]: "ffilter f {||} = {||}"
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  by auto

lemma ffilter_finsert: "ffilter f (finsert a s) = (if f a then finsert a (ffilter f s) else (ffilter f s))"
  apply simp
  apply standard
   apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
   apply auto[1]
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  by auto

lemma singleton_singleton [simp]: "fis_singleton {|a|}"
  by (simp add: fis_singleton_def)

lemma not_singleton_empty [simp]: "\<not> fis_singleton {||}"
  apply (simp add: fis_singleton_def)
  by (simp add: is_singleton_altdef)

lemma fset_equiv: "(f1 = f2) = (fset f1 = fset f2)"
  by (simp add: fset_inject)

lemma finsert_equiv: "(finsert e f = f') = (insert e (fset f) = (fset f'))"
  by (simp add: finsert_def fset_both_sides Abs_fset_inverse)

lemma filter_elements: "x |\<in>| Abs_fset (Set.filter f (fset s)) = (x \<in> (Set.filter f (fset s)))"
  by (metis ffilter.rep_eq fset_inverse notin_fset)

lemma singleton_equiv: "is_singleton s \<Longrightarrow> (the_elem s = i) = (s = {i})"
  by (meson is_singleton_the_elem the_elem_eq)

lemma sorted_list_of_empty [simp]: "sorted_list_of_fset {||} = []"
  by (simp add: sorted_list_of_fset_def)

lemma fmember_implies_member: "e |\<in>| f \<Longrightarrow> e \<in> fset f"
  by (simp add: fmember_def)

lemma fold_union_ffUnion: "fold (|\<union>|) l {||} = ffUnion (fset_of_list l)"
proof(induct l rule: rev_induct)
case Nil
  then show ?case by simp
next
  case (snoc a l)
  then show ?case
    by simp
qed

lemma filter_filter: "ffilter P (ffilter Q xs) = ffilter (\<lambda>x. Q x \<and> P x) xs"
  by auto

lemma fsubset_strict: "x2 |\<subset>| x1 \<Longrightarrow> \<exists>e. e |\<in>| x1 \<and> e |\<notin>| x2"
  by auto

lemma fsubset: "x2 |\<subset>| x1 \<Longrightarrow> \<nexists>e. e |\<in>| x2 \<and> e |\<notin>| x1"
  by auto

lemma size_fsubset_elem: 
  "\<exists>e. e |\<in>| x1 \<and> e |\<notin>| x2 \<Longrightarrow>
   \<nexists>e. e |\<in>| x2 \<and> e |\<notin>| x1 \<Longrightarrow>
   size x2 < size x1"
  apply (simp add: fmember_def)
  by (metis card_seteq finite_fset linorder_not_le subsetI)

lemma size_fsubset: "x2 |\<subset>| x1 \<Longrightarrow> size x2 < size x1"
  using fsubset fsubset_strict size_fsubset_elem
  by metis

definition fremove :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  where [code_abbrev]: "fremove x A = A - {|x|}"

lemma arg_cong_ffilter: "\<forall>e |\<in>| f. p e = p' e \<Longrightarrow> ffilter p f = ffilter p' f"
  by auto

lemma ffilter_singleton: "f e \<Longrightarrow> ffilter f {|e|} = {|e|}"
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  by auto

lemma ffilter_true: "ffilter (\<lambda>x. True) f = f"
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  by auto

lemma ffilter_true_pair: "ffilter (\<lambda>(x, y). True) f = f"
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  by auto

lemma ffilter_out_all: "\<forall>e |\<in>| f. \<not>P e \<Longrightarrow> ffilter P f = {||}"
  apply (simp add: ffilter_def fBall_def fset_both_sides Abs_fset_inverse)
  by auto

lemma fset_eq_alt: "(x = y) = (x |\<subseteq>| y \<and> size x = size y)"
  by (metis exists_least_iff le_less size_fsubset)

definition these :: "'a option fset \<Rightarrow> 'a fset"
  where "these A = the |`| (ffilter (\<lambda>x. x \<noteq> None) A)"

definition fimages :: "('a \<Rightarrow> 'b fset) \<Rightarrow> 'a fset \<Rightarrow> 'b fset" where
  "fimages f xs = ffUnion (fimage f xs)"

lemma ffold_empty [simp]: "ffold f b {||} = b"
  by (simp add: ffold_def)

lemma exists_fset_of_list: "\<exists>l. f = fset_of_list l"
  using exists_fset_of_list by fastforce

lemma sorted_list_of_fset_sort: "sorted_list_of_fset (fset_of_list l) = sort (remdups l)"
  by (simp add: fset_of_list.rep_eq sorted_list_of_fset.rep_eq sorted_list_of_set_sort_remdups)

lemma fMin_Min: "fMin (fset_of_list l) = Min (set l)"
  by (simp add: fMin.F.rep_eq fset_of_list.rep_eq)

lemma sorted_hd_Min: "sorted l \<Longrightarrow> l \<noteq> [] \<Longrightarrow> hd l = Min (set l)"
  by (metis List.finite_set Min_eqI eq_iff hd_Cons_tl insertE list.set_sel(1) list.simps(15) sorted.simps(2))

lemma hd_sort_Min: "l \<noteq> [] \<Longrightarrow> hd (sort l) = Min (set l)"
  by (metis sorted_hd_Min set_empty set_sort sorted_sort)

lemma hd_sort_remdups: "hd (sort (remdups l)) = hd (sort l)"
  by (metis hd_sort_Min remdups_eq_nil_iff set_remdups)

lemma hd_sorted_list_of_fset: "s \<noteq> {||} \<Longrightarrow> hd (sorted_list_of_fset s) = (fMin s)"
  apply (insert exists_fset_of_list[of s])
  apply (erule exE)
  apply simp
  apply (simp add: sorted_list_of_fset_sort fMin_Min hd_sort_remdups)
  by (metis fset_of_list_simps(1) hd_sort_Min)

lemma fminus_filter_singleton: "fset_of_list l |-| {|x|} = fset_of_list (filter (\<lambda>e. e \<noteq> x) l)"
  by auto

end