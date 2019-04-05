theory Week5
  imports Main
begin 

thm allI
thm exI
lemma none_not_implies_every: "\<not>(\<exists> x. \<not> F x) \<longrightarrow> (\<forall> x. F x)" 
proof (rule impI)
  assume "\<not>(\<exists> x. \<not> F x)"
  show "(\<forall> x. F x)"
  proof (rule allI)
    fix x
    show "F x"
    proof (rule ccontr)
      assume "\<not>(F x)"
      then have "\<exists> x. \<not> (F x)" by (rule exI)
      with `\<not>(\<exists> x. \<not> F x)` show False by (rule notE)
    qed
  qed
qed

thm allE
lemma not_all_implies_some_not:"\<not>(\<forall> y. F y) \<longrightarrow> (\<exists> x. \<not> F x)" 
proof (rule impI)
  assume "\<not> (\<forall> y. F y)"
  show "(\<exists> x. \<not> F x)"
  proof (rule ccontr)
    assume "\<not>(\<exists> x. \<not> F x)"
    with none_not_implies_every have "(\<forall> y. F y)" by (rule mp)
    with `\<not> (\<forall> y. F y)` show False by (rule notE)
  qed
qed

(* Proof by cases *)
lemma "(\<exists> x. F x) \<longrightarrow> (\<forall> y. F y)" oops

lemma"\<exists> x.(\<exists> y. F y) \<longrightarrow> F x" oops


lemma "(\<forall> x. R x y) \<longrightarrow> (\<forall> x. R y x \<longrightarrow>x = z) \<longrightarrow> y = z"  
proof(rule impI)
  assume "\<forall> x. R x y"
  then have "R y y" by (rule allE)
  show "(\<forall> x. R y x \<longrightarrow>x = z) \<longrightarrow> y = z"
  proof(rule impI)
    assume "\<forall> x. R y x \<longrightarrow> x = z"
    then have "R y y \<longrightarrow> y = z" by (rule allE)
    thus "y = z" using `R y y` by (rule mp)
  qed
qed

 

end