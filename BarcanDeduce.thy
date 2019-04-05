theory BarcanDeduce
  imports Main QML_S5

begin

lemma BF:  "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<box>(\<phi>(x))) \<^bold>\<rightarrow>  \<^bold>\<box>(\<^bold>\<forall>x. \<phi>(x))\<rfloor>"
  by simp


lemma CBF:  "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x. \<phi>(x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x. \<^bold>\<box>(\<phi>(x)))\<rfloor>"
   by simp

consts x::'a  y::'a
lemma NE: "valid((mforall(x mbox(mexists(y (y \<^bold>\<leftrightarrow> x))))))" 
  nitpick 
  oops


consts big::"'a \<Rightarrow> \<sigma>"
consts smaller::"'a \<Rightarrow> 'a \<Rightarrow> \<sigma>"

lemma "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>x. big x \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists> y. smaller y x))\<rfloor>"
  nitpick
  oops



end