theory Value
imports Trilean
begin

section\<open>Values\<close>

text\<open>Our EFSM implementation can currently handle integers and strings. Here we define a sum type
which combines these. We also define an arithmetic in terms of values such that EFSMs do not need
to be strongly typed.\<close>

text_raw\<open>\snip{valuetype}{1}{2}{%\<close>
datatype "value" = Num int | Str String.literal
text_raw\<open>}%endsnip\<close>

fun is_Num :: "value \<Rightarrow> bool" where
  "is_Num (Num _) = True" |
  "is_Num (Str _) = False"

fun MaybeArithInt :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> value option \<Rightarrow> value option \<Rightarrow> value option" where
  "MaybeArithInt f (Some (Num x)) (Some (Num y)) = Some (Num (f x y))" |
  "MaybeArithInt _ _ _ = None"

lemma MaybeArithInt_not_None: "MaybeArithInt f a b \<noteq> None = (\<exists>n n'. a = Some (Num n) \<and> b = Some (Num n'))"
  using MaybeArithInt.elims MaybeArithInt.simps(1) by blast

lemma MaybeArithInt_Some: "MaybeArithInt f a b = Some (Num x) = (\<exists>n n'. a = Some (Num n) \<and> b = Some (Num n') \<and> f n n' = x)"
  using MaybeArithInt.elims MaybeArithInt.simps(1) by blast

lemma MaybeArithInt_None: "(MaybeArithInt f a1 a2 = None) = (\<nexists>n n'. a1 = Some (Num n) \<and> a2 = Some (Num n'))"
  using MaybeArithInt_not_None by blast

lemma MaybeArithInt_Not_Num: "(\<forall>n. MaybeArithInt f a1 a2 \<noteq> Some (Num n)) = (MaybeArithInt f a1 a2 = None)"
  by (metis MaybeArithInt.elims option.distinct(1))

lemma MaybeArithInt_never_string: "MaybeArithInt f a b \<noteq> Some (Str x)"
  using MaybeArithInt.elims by blast

definition "value_plus = MaybeArithInt (+)"

lemma value_plus_never_string: "value_plus a b \<noteq> Some (Str x)"
  by (simp add: value_plus_def MaybeArithInt_never_string)

lemma value_plus_symmetry: "value_plus x y = value_plus y x"
  apply (induct x y rule: MaybeArithInt.induct)
  by (simp_all add: value_plus_def)

definition "value_minus = MaybeArithInt (-)"

lemma value_minus_never_string: "value_minus a b \<noteq> Some (Str x)"
  by (simp add: MaybeArithInt_never_string value_minus_def)

definition "value_times = MaybeArithInt (*)"

lemma value_times_never_string: "value_times a b \<noteq> Some (Str x)"
  by (simp add: MaybeArithInt_never_string value_times_def)

fun MaybeBoolInt :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> value option \<Rightarrow> value option \<Rightarrow> trilean" where
  "MaybeBoolInt f (Some (Num a)) (Some (Num b)) = (if f a b then true else false)" |
  "MaybeBoolInt _ _ _ = invalid"

lemma MaybeBoolInt_not_num_1: "\<forall>n. r \<noteq> Some (Num n) \<Longrightarrow> MaybeBoolInt f n r = invalid"
  using MaybeBoolInt.elims by blast

definition value_gt :: "value option \<Rightarrow> value option \<Rightarrow> trilean"  where
  "value_gt a b \<equiv> MaybeBoolInt (>) a b"

definition value_eq :: "value option \<Rightarrow> value option \<Rightarrow> trilean"  where
  "value_eq a b \<equiv> (if a = b then true else false)"
declare value_eq_def [simp]

end
