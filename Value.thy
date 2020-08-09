section\<open>Values\<close>

text\<open>Our EFSM implementation can currently handle integers and strings. Here we define a sum type
which combines these. We also define an arithmetic in terms of values such that EFSMs do not need
to be strongly typed.\<close>

theory Value
imports Trilean
begin

class aexp_value =
  fixes plus  :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" (infixl "+\<^sub>?" 65)
    and minus :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" (infixl "-\<^sub>?" 65)
    and times :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" (infixl "*\<^sub>?" 65)
    and gt :: "'a option \<Rightarrow> 'a option \<Rightarrow> trilean" (infix ">\<^sub>?" 65)
    and is_num :: "'a \<Rightarrow> bool" ("isNum _" [40] 40)
    and get_num :: "'a \<Rightarrow> int" ("getNum _" [40] 40)
  assumes plus_aexp_commute: "x +\<^sub>? y = y +\<^sub>? x"
begin
  definition value_eq :: "'a option \<Rightarrow> 'a option \<Rightarrow> trilean"(infix "=\<^sub>?" 65)  where
    "value_eq a b \<equiv> (if a = b then true else false)"
  declare value_eq_def [simp]
end


text_raw\<open>\snip{valuetype}{1}{2}{%\<close>
datatype "value" = Num int | Str String.literal
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{maybeIntArith}{1}{2}{%\<close>
fun MaybeArithInt :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> value option \<Rightarrow> value option \<Rightarrow> value option" where
  "MaybeArithInt f (Some (Num x)) (Some (Num y)) = Some (Num (f x y))" |
  "MaybeArithInt _ _ _ = None"
text_raw\<open>}%endsnip\<close>

lemma MaybeArithInt_not_None:
  "MaybeArithInt f a b \<noteq> None = (\<exists>n n'. a = Some (Num n) \<and> b = Some (Num n'))"
  using MaybeArithInt.elims MaybeArithInt.simps(1) by blast

lemma MaybeArithInt_Some:
  "MaybeArithInt f a b = Some (Num x) = (\<exists>n n'. a = Some (Num n) \<and> b = Some (Num n') \<and> f n n' = x)"
  using MaybeArithInt.elims MaybeArithInt.simps(1) by blast

lemma MaybeArithInt_None:
  "(MaybeArithInt f a1 a2 = None) = (\<nexists>n n'. a1 = Some (Num n) \<and> a2 = Some (Num n'))"
  using MaybeArithInt_not_None by blast

lemma MaybeArithInt_Not_Num:
  "(\<forall>n. MaybeArithInt f a1 a2 \<noteq> Some (Num n)) = (MaybeArithInt f a1 a2 = None)"
  by (metis MaybeArithInt.elims option.distinct(1))

lemma MaybeArithInt_never_string: "MaybeArithInt f a b \<noteq> Some (Str x)"
  using MaybeArithInt.elims by blast

fun MaybeBoolInt :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> value option \<Rightarrow> value option \<Rightarrow> trilean" where
  "MaybeBoolInt f (Some (Num a)) (Some (Num b)) = (if f a b then true else false)" |
  "MaybeBoolInt _ _ _ = invalid"

lemma MaybeBoolInt_not_num_1:
  "\<forall>n. r \<noteq> Some (Num n) \<Longrightarrow> MaybeBoolInt f n r = invalid"
  using MaybeBoolInt.elims by blast

instantiation "value" :: aexp_value begin
  definition "plus_value = MaybeArithInt (+)"
  definition "minus_value = MaybeArithInt (-)"
  definition "times_value = MaybeArithInt (*)"
  definition gt_value :: "value option \<Rightarrow> value option \<Rightarrow> trilean"  where
    "gt_value a b \<equiv> MaybeBoolInt (>) a b"
  fun is_num_value :: "value \<Rightarrow> bool" where
    "is_num_value (Num _) = True" |
    "is_num_value (Str _) = False"
  definition get_num_value :: "value \<Rightarrow> int" where
    "get_num_value v = (case v of (Num n) \<Rightarrow> n)"
instance
  apply standard
  subgoal for x y
    by (induct x y rule: MaybeArithInt.induct, simp_all add: plus_value_def)
  done
end

lemma plus_value_never_string: "a +\<^sub>? b \<noteq> Some (Str x)"
  by (simp add: plus_value_def MaybeArithInt_never_string)

lemma minus_value_never_string: "a -\<^sub>? b \<noteq> Some (Str x)"
  by (simp add: MaybeArithInt_never_string minus_value_def)

lemma times_value_never_string: "a *\<^sub>? b \<noteq> Some (Str x)"
  by (simp add: MaybeArithInt_never_string times_value_def)

end
