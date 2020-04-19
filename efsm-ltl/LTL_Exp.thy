theory LTL_Exp
imports Main "../EFSM" FinFun.FinFun
begin

no_notation relcomp (infixr "O" 75) and comp (infixl "o" 55)

datatype ltl_vname = Ip nat | Op nat | Rg nat

type_synonym ltl_gexp = "ltl_vname gexp"

definition join_iro :: "value list \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> ltl_vname datastate" where
  "join_iro i r o = (\<lambda>x. case x of
    Rg n \<Rightarrow> r $ n |
    Ip n \<Rightarrow> Some (i ! n) |
    Op n \<Rightarrow> o ! n
  )"

lemma join_iro_R [simp]:
"join_iro i r o (Rg n) = r $ n"
  by (simp add: join_iro_def)

end