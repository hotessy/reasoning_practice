theory IMP
  imports Main
begin 

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n " |
"aval (V v) s = s v" |
"aval (Plus a b) s = aval a s + aval b s"


value "aval (Plus (N 3) (V y)) ((\<lambda>x. 0) (x:= 7))"


lemma
"[ \<forall>x y. T x y \<or> T y x;
\<forall> x y . A x y \<and> A y x −\<rightarrow> x = y ; \<forall>x y. T x y −\<rightarrow> A x y ]
\<Longrightarrow> \<forall>x y. A x y −\<rightarrow> T x y" by blast

(*
definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"
*)

print_statement append_eq_conv_conj

end