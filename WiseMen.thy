theory WiseMen
  imports Epistemic_S5
begin 

(* Wise Men Puzzle *)

type_synonym \<alpha> = "i \<Rightarrow> i \<Rightarrow> bool" (* denoting people *)
consts a::\<alpha> b::\<alpha> c::\<alpha> (* Three people *)
consts fool::\<alpha> (* All people *)
consts white::"\<alpha>\<Rightarrow>\<sigma>"

context
  assumes
A0a: "a \<noteq> b \<and> b \<noteq> c \<and> c \<noteq> a" and (* no two people are the same*)
A0b: "fool \<noteq> a \<and> fool \<noteq> b \<and> fool \<noteq> c" and (* no person is the fool *)
A1: "valid( \<^bold>\<box>fool (white a \<^bold>\<or> white b \<^bold>\<or> white c))" and (*fool knows it's one of a, b or c*)

(*if white is on X then Y and Z both know*)
A2_ab: "valid ( \<^bold>\<box>fool (white a \<^bold>\<rightarrow> \<^bold>\<box>b (white a)))" and
A2_ac: "valid ( \<^bold>\<box>fool (white a \<^bold>\<rightarrow> \<^bold>\<box>c (white a)))" and
A2_bc: "valid ( \<^bold>\<box>fool (white b \<^bold>\<rightarrow> \<^bold>\<box>c (white b)))" and
A2_ba: "valid ( \<^bold>\<box>fool (white b \<^bold>\<rightarrow> \<^bold>\<box>a (white b)))" and
A2_ca: "valid ( \<^bold>\<box>fool (white c \<^bold>\<rightarrow> \<^bold>\<box>a (white c)))" and
A2_cb: "valid ( \<^bold>\<box>fool (white c \<^bold>\<rightarrow> \<^bold>\<box>b (white c)))" and

(* if black is on X then Y and Z both know *)
A3_ab: "valid ( \<^bold>\<box>fool (\<^bold>\<not>(white a) \<^bold>\<rightarrow> \<^bold>\<box>b \<^bold>\<not>(white a)))" and
A3_ac: "valid ( \<^bold>\<box>fool (\<^bold>\<not>(white a) \<^bold>\<rightarrow> \<^bold>\<box>c \<^bold>\<not>(white a)))" and
A3_bc: "valid ( \<^bold>\<box>fool (\<^bold>\<not>(white b) \<^bold>\<rightarrow> \<^bold>\<box>c \<^bold>\<not>(white b)))" and
A3_ba: "valid ( \<^bold>\<box>fool (\<^bold>\<not>(white b) \<^bold>\<rightarrow> \<^bold>\<box>a \<^bold>\<not>(white b)))" and
A3_ca: "valid ( \<^bold>\<box>fool (\<^bold>\<not>(white c) \<^bold>\<rightarrow> \<^bold>\<box>a \<^bold>\<not>(white c)))" and
A3_cb: "valid ( \<^bold>\<box>fool (\<^bold>\<not>(white c) \<^bold>\<rightarrow> \<^bold>\<box>b \<^bold>\<not>(white c)))" and

(* Fool knows  X does't know about it's white spot*)
A4_a: "valid (\<^bold>\<box>fool \<^bold>\<not>(\<^bold>\<box>a (white a)))" and
A4_b: "valid (\<^bold>\<box>fool \<^bold>\<not>(\<^bold>\<box>b (white b)))" and

(* If fool knows somethings, then it's true *)
A5: "valid ((\<^bold>\<box>fool \<phi>) \<^bold>\<rightarrow> \<phi>)" 


begin

theorem 

(* Proving C knows it has white spot*)
C : "valid (\<^bold>\<box>c (white c))" 
  sledgehammer
  by (metis A1 A3_ab A3_ca A3_cb A4_a A4_b A5)



end