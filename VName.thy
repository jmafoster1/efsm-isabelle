theory VName
imports Main
begin

section\<open>Variables\<close>
text\<open>Variables can either be inputs or registers. Here we define the vname datatype which allows
us to write expressions in terms of variables and case match during evaluation. We also make the
vname datatype a member of linorder such that we can establish a linear order on arithmetic
expressions and subsequently transitions.\<close>

text_raw\<open>\snip{vnametype}{1}{2}{%\<close>
datatype vname = I nat | R nat
text_raw\<open>}%endsnip\<close>

instantiation vname :: linorder begin
fun less_eq_vname :: "vname \<Rightarrow> vname \<Rightarrow> bool" where
  "less_eq_vname (I n1) (R n2) = True" |
  "less_eq_vname (R n1) (I n2) = False" |
  "less_eq_vname (I n1) (I n2) = less_eq n1 n2" |
  "less_eq_vname (R n1) (R n2) = less_eq n1 n2"

fun less_vname :: "vname \<Rightarrow> vname \<Rightarrow> bool" where
  "less_vname (I n1) (R n2) = True" |
  "less_vname (R n1) (I n2) = False" |
  "less_vname (I n1) (I n2) = less n1 n2" |
  "less_vname (R n1) (R n2) = less n1 n2"

instance
  apply standard
  subgoal for x y
    by(induct x y rule: less_vname.induct, auto)
  using less_eq_vname.elims(3) apply fastforce
  subgoal for x y z
    apply(induct x y rule: less_vname.induct)
       apply (metis less_eq_vname.elims(2) less_eq_vname.simps(1) vname.simps(4))
      apply simp
    using less_eq_vname.elims(3) order_trans apply fastforce
    by (metis le_trans less_eq_vname.elims(2) less_eq_vname.simps(4) vname.simps(4))
  subgoal for x y
    by(induct x y rule: less_vname.induct, auto)
  by (metis less_eq_vname.elims(3) less_eq_vname.simps(3) less_eq_vname.simps(4) linear)
end

end
