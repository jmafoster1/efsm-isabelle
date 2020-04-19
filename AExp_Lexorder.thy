theory AExp_Lexorder
imports AExp Value_Lexorder
begin

instantiation aexp :: (linorder) linorder begin
fun less_aexp :: "'a aexp \<Rightarrow> 'a aexp \<Rightarrow> bool"  where
  "less_aexp (L l1) (L l2) = (l1 < l2)" |
  "less_aexp (L l1) (V v2) = True" |
  "less_aexp (L l1) (Plus e1 e2) = True" |
  "less_aexp (L l1) (Minus e1 e2) = True" |
  "less_aexp (L l1) (Times e1 e2) = True" |

  "less_aexp (V v1) (L l1) = False" |
  "less_aexp (V v1) (V v2) = (v1 < v2)" |
  "less_aexp (V v1) (Plus e1 e2) = True" |
  "less_aexp (V v1) (Minus e1 e2) = True" |
  "less_aexp (V v1) (Times e1 e2) = True" |

  "less_aexp (Plus e1 e2) (L l2) = False" |
  "less_aexp (Plus e1 e2) (V v2) = False" |
  "less_aexp (Plus e1 e2) (Plus e1' e2') = ((less_aexp e1 e1') \<or> ((e1 = e1') \<and> (less_aexp e2 e2')))" |
  "less_aexp (Plus e1 e2) (Minus e1' e2') = True" |
  "less_aexp (Plus e1 e2) (Times e1' e2') = True" |

  "less_aexp (Minus e1 e2) (L l2) = False" |
  "less_aexp (Minus e1 e2) (V v2) = False" |
  "less_aexp (Minus e1 e2) (Plus e1' e2') = False" |
  "less_aexp (Minus e1 e2) (Minus e1' e2') = ((less_aexp e1 e1') \<or> ((e1 = e1') \<and> (less_aexp e2 e2')))" |
  "less_aexp (Minus e1 e2) (Times e1' e2') = True" |

  "less_aexp (Times e1 e2) (L l2) = False" |
  "less_aexp (Times e1 e2) (V v2) = False" |
  "less_aexp (Times e1 e2) (Plus e1' e2') = False" |
  "less_aexp (Times e1 e2) (Minus e1' e2') = False" |
  "less_aexp (Times e1 e2) (Times e1' e2') = ((less_aexp e1 e1') \<or> ((e1 = e1') \<and> (less_aexp e2 e2')))"

definition less_eq_aexp :: "'a aexp \<Rightarrow> 'a aexp \<Rightarrow> bool"
  where "less_eq_aexp e1 e2 \<equiv> (e1 < e2) \<or> (e1 = e2)"

lemma aexp_antisym: "(x::'a aexp) < y = (\<not>(y < x) \<and> (x \<noteq> y))"
  by (induction x y rule: less_aexp.induct) auto

lemma aexp_trans: "(x::'a aexp) < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  proof (induction x y arbitrary: z rule: less_aexp.induct)
    case (1 l1 l2)
    then show ?case by (cases z, auto)
  next
    case (2 l1 v2)
    then show ?case by (cases z, auto)
  next
    case (3 l1 e1 e2)
    then show ?case by (cases z, auto)
  next
    case (4 l1 e1 e2)
    then show ?case by (cases z, auto)
  next
    case (5 l1 e1 e2)
    then show ?case by (cases z, auto)
  next
    case (6 v1 l1)
    then show ?case by (cases z, auto)
  next
    case (7 v1 v2)
    then show ?case by (cases z, auto)
  next
    case (8 v1 e1 e2)
    then show ?case by (cases z, auto)
  next
    case (9 v1 e1 e2)
    then show ?case by (cases z, auto)
  next
    case (10 v1 e1 e2)
    then show ?case by (cases z, auto)
  next
    case (11 e1 e2 l2)
    then show ?case by (cases z, auto)
  next
    case (12 e1 e2 v2)
    then show ?case by (cases z, auto)
  next
    case (13 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
    case (14 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
    case (15 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
    case (16 e1 e2 l2)
    then show ?case by (cases z, auto)
  next
    case (17 e1 e2 v2)
    then show ?case by (cases z, auto)
  next
    case (18 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
    case (19 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
    case (20 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
    case (21 e1 e2 l2)
    then show ?case by (cases z, auto)
  next
    case (22 e1 e2 v2)
    then show ?case by (cases z, auto)
  next
    case (23 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
    case (24 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
    case (25 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  qed

instance proof
    fix x y z :: "'a aexp"
    show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
      by (metis aexp_antisym less_eq_aexp_def)
    show "(x \<le> x)"
      by (simp add: less_eq_aexp_def)
    show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      using aexp_trans by (metis less_eq_aexp_def)
    show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
      unfolding less_eq_aexp_def using aexp_antisym by blast
    show "x \<le> y \<or> y \<le> x"
      unfolding less_eq_aexp_def using aexp_antisym by blast
  qed
end

end