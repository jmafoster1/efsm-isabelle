theory 
GExp_Lexorder
imports 
  "GExp"
  "AExp_Lexorder"
  "HOL-Library.List_Lexorder"
begin

instantiation gexp :: (linorder) linorder begin
fun less_gexp :: "'a gexp \<Rightarrow> 'a gexp \<Rightarrow> bool"  where
  "less_gexp (Bc b1) (Bc b2) = (b1 < b2)" |
  "less_gexp (Bc b1) _ = True" |

  "less_gexp (Eq e1 e2) (Bc b2) = False" |
  "less_gexp (Eq e1 e2) (Eq e1' e2') = ((e1 < e1') \<or> ((e1 = e1') \<and> (e2 < e2')))" |
  "less_gexp (Eq e1 e2) _ = True" |

  "less_gexp (Gt e1 e2) (Bc b2) = False" |
  "less_gexp (Gt e1 e2) (Eq e1' e2') = False" |
  "less_gexp (Gt e1 e2) (Gt e1' e2') = ((e1 < e1') \<or> ((e1 = e1') \<and> (e2 < e2')))" |
  "less_gexp (Gt e1 e2) _ = True" |

  "less_gexp (In vb vc) (Nor v va) = True" |
  "less_gexp (In vb vc) (In v va) = (vb < v \<or> (vb = v \<and> vc < va))" |
  "less_gexp (In vb vc) _ = False" |

  "less_gexp (Nor g1 g2) (Nor g1' g2') = ((less_gexp g1 g1') \<or> ((g1 = g1') \<and> (less_gexp g2 g2')))" |
  "less_gexp (Nor g1 g2) _ = False"

definition less_eq_gexp :: "'a gexp \<Rightarrow> 'a gexp \<Rightarrow> bool"
  where "less_eq_gexp e1 e2 \<equiv> (e1 < e2) \<or> (e1 = e2)"

lemma gexp_antisym: "(x::'a gexp) < y = (\<not>(y < x) \<and> (x \<noteq> y))"
    apply (induction x y rule: less_gexp.induct)
                        apply auto[1]
                        apply simp+
    using aexp_antisym apply blast
                        apply simp+
    using aexp_antisym apply blast
    by auto

lemma gexp_trans: "(x::'a gexp) < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
proof (induction x y arbitrary: z rule: less_gexp.induct)
case (1 b1 b2)
  then show ?case
    by (cases z, auto)
next
  case ("2_1" b1 v va)
  then show ?case
    by (cases z, auto)
next
  case ("2_2" b1 v va)
  then show ?case 
    by (cases z, auto)
next
  case ("2_3" b1 v va)
  then show ?case 
    by (cases z, auto)
next
  case ("2_4" b1 v va)
  then show ?case 
    by (cases z, auto)
next
  case (3 e1 e2 b2)
  then show ?case 
    by (cases z, auto)
next
  case (4 e1 e2 e1' e2')
  then show ?case 
    by (cases z, auto)
next
  case ("5_1" e1 e2 v va)
  then show ?case 
    by (cases z, auto)
next
  case ("5_2" e1 e2 v va)
  then show ?case 
    by (cases z, auto)
next
  case ("5_3" e1 e2 v va)
  then show ?case  
    by (cases z, auto)
next
  case (6 e1 e2 b2)
  then show ?case  
    by (cases z, auto)
next
  case (7 e1 e2 e1' e2')
  then show ?case  
    by (cases z, auto)
next
  case (8 e1 e2 e1' e2')
  then show ?case  
    by (cases z, auto)
next
  case ("9_1" e1 e2 v va)
  then show ?case  
    by (cases z, auto)
next
  case ("9_2" e1 e2 v va)
  then show ?case  
    by (cases z, auto)
next
  case (10 vb vc v va)
  then show ?case  
    by (cases z, auto)
next
  case (11 vb vc v va)
  then show ?case  
    by (cases z, auto)
next
  case ("12_1" vb vc v)
  then show ?case  
    by (cases z, auto)
next
  case ("12_2" vb vc v va)
  then show ?case  
    by (cases z, auto)
next
  case ("12_3" vb vc v va)
  then show ?case  
    by (cases z, auto)
next
  case (13 g1 g2 g1' g2')
  then show ?case
    by (cases z, auto)
next
  case ("14_1" g1 g2 v)
  then show ?case  
    by (cases z, auto)
next
  case ("14_2" g1 g2 v va)
  then show ?case
    by simp
next
  case ("14_3" g1 g2 v va)
  then show ?case
    by simp
next
  case ("14_4" g1 g2 v va)
  then show ?case
    by simp
qed

instance proof
  fix x y z :: "'a gexp"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (metis gexp_antisym less_eq_gexp_def)
  show "(x \<le> x)"
    by (simp add: less_eq_gexp_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (metis less_eq_gexp_def gexp_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_gexp_def using gexp_antisym by blast
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_gexp_def using gexp_antisym by blast
qed
end

end
