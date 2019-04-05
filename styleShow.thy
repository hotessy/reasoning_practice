theory styleShow
  imports Main
begin
(* Cantor's Theorem *)
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)" 
proof
assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by(simp add: surj_def) 
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)" 
proof
assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def) 
  from this show "False" by blast
qed


lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)" 
proof
assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def) 
  thus "False" by blast
qed


(*Exercise 5.1*)
lemma
  assumes T: "\<forall>x y .T x y \<or> T y x"
and A:"\<forall> x y .A x y \<and> A y x \<longrightarrow> x = y"
and TA: "\<forall> x y . T x y \<longrightarrow> A x y"
and "A x y"
shows "T x y"
  using A T TA assms(4) by blast
 


(*
lemma
  fixes f :: "'a \<Rightarrow> 'a set" 
  assumes s: "surj f" 
  shows "False"
*)

end