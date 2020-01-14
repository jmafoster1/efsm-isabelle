theory VName
imports Main
begin

no_notation relcomp (infixr "O" 75)

text_raw\<open>\snip{vname_otype}{1}{2}{%\<close>
datatype vname_o = I nat | R nat | O nat
text_raw\<open>}%endsnip\<close>

instantiation vname_o :: linorder begin
fun less_vname_o :: "vname_o \<Rightarrow> vname_o \<Rightarrow> bool" where
  "less_vname_o (I n1) (I n2) = less n1 n2" |
  "less_vname_o (I n1) (R n2) = True" |
  "less_vname_o (I n1) (O n2) = True" |

  "less_vname_o (R n1) (I n2) = False" |
  "less_vname_o (R n1) (R n2) = less n1 n2" |
  "less_vname_o (R n1) (O n2) = True" |

  "less_vname_o (O n1) (I n2) = False" |
  "less_vname_o (O n1) (R n2) = False" |
  "less_vname_o (O n1) (O n2) = less n1 n2"

fun less_eq_vname_o :: "vname_o \<Rightarrow> vname_o \<Rightarrow> bool" where
  "less_eq_vname_o v1 v2 = (v1 < v2 \<or> v1 = v2)"

instance proof
  fix x y z:: vname_o
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (induct x y rule: less_vname_o.induct, auto)
  show "x \<le> x"
    by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  proof(induct x y arbitrary: z rule: less_vname_o.induct)
    case (1 n1 n2)
    then show ?case
      by (cases z, auto)
  next
    case (2 n1 n2)
    then show ?case 
      by (cases z, auto)
  next
    case (3 n1 n2)
    then show ?case 
      by (cases z, auto)
  next
    case (4 n1 n2)
    then show ?case 
      by (cases z, auto)
  next
    case (5 n1 n2)
    then show ?case 
      by (cases z, auto)
  next
    case (6 n1 n2)
    then show ?case 
      by (cases z, auto)
  next
    case (7 n1 n2)
    then show ?case 
      by (cases z, auto)
  next
    case (8 n1 n2)
    then show ?case 
      by (cases z, auto)
  next
    case (9 n1 n2)
    then show ?case 
      by (cases z, auto)
  qed
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (induct x y rule: less_vname_o.induct, auto)
  show "x \<le> y \<or> y \<le> x"
    by (induct x y rule: less_vname_o.induct, auto)
qed
end

typedef vname = "{v :: vname_o. \<forall>n. v \<noteq> (O n)}"  morphisms vname Abs_vname
  by auto

end