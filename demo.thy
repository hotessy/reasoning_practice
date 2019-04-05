theory demo
  imports Main
begin

fun remove:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
"remove x [] = []" |
"remove x (y#ys) = (if x=y then (remove x ys) else y#(remove x ys))"

value "remove (2::int) [1, 2, 3]"


lemma "\<not>(List.member (remove element list) element)"
  apply (induct list)
  apply auto
  qed

lemma count_remove:  "(length l) = (length (remove e l)) + (count_list l e)"
  apply (induct l)
  by auto


lemma "(length (remove e l)) = (length l) \<longrightarrow> \<not> (List.member l e)"
  apply (induct l)
   apply (simp add: member_rec(2))
   apply auto
  apply (metis count_remove impossible_Cons le_add_same_cancel1 length_Cons zero_le)
  apply (metis Suc_n_not_le_n count_remove le_add_same_cancel1 zero_le)
  by (simp add: member_rec(1))

end

