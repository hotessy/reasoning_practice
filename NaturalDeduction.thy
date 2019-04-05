theory NaturalDeduction
  imports Main

begin

(*Introduction Rules*)
print_statement  conjI
lemma conj_rule: "P \<Longrightarrow> Q \<Longrightarrow> P \<and> (Q \<and> P)" 
  apply (rule conjI) 
   apply assumption 
  apply (rule conjI) 
   apply assumption
  apply assumption
  done


(*Elimination Rules*)
print_statement disjE
print_statement disjI1
print_statement disjI2
lemma disj_swap: "(P \<or> Q) \<Longrightarrow> (Q \<or> P)" 
  apply (erule disjE) (* `erule` versus `rule` versus `drule`  *)
   apply (rule disjI2) (*disjI1 versus disjI2*)
   apply assumption 
  apply (rule disjI1) 
  apply assumption
  done

(*Destruction Rules*)
print_statement conjunct1
print_statement conjunct2
lemma conj_swap: "P \<and> Q \<Longrightarrow> Q \<and> P" 
  apply (rule conjI)
   apply (drule conjunct2)
   apply assumption
  apply (drule conjunct1) 
  apply assumption
  done

print_statement conjE
lemma conj_swap2: "P \<and> Q \<Longrightarrow> Q \<and> P"  (*using conjE*) 
  apply (rule conjI)
   apply(erule conjE)
   apply assumption
  apply(erule conjE)
  apply assumption
  done


(*Implication*)
print_statement impI
print_statement HOL.uncurry
lemma imp_uncurry: "P \<longrightarrow> (Q \<longrightarrow> R) \<Longrightarrow> P \<and> Q \<longrightarrow> R" 
  apply (rule impI)
  apply (erule conjE)
  apply (drule mp)
   apply assumption
  apply (drule mp)
   apply assumption
  apply assumption
  done

(*Negation*)
thm notI
print_statement notE
print_statement classical

thm contrapos_pp
thm contrapos_pn
thm contrapos_np
thm contrapos_nn


lemma "\<not>(P\<longrightarrow> Q)\<Longrightarrow> \<not>(R\<longrightarrow> Q) \<Longrightarrow> R"
  apply (erule_tac Q = "R\<longrightarrow>Q" in contrapos_np)  (*erule_tac selscts the first assm*)
  apply (intro impI)
  by (erule notE)


lemma "(P \<or> Q) \<and> R \<Longrightarrow> P \<or> (Q \<and> R)" 
  apply (rule disjCI)
  apply (elim conjE disjE)
   apply assumption
  by (erule contrapos_np, rule conjI)



end

