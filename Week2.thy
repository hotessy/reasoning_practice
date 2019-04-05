theory Week2

imports Main Week1

begin 

print_statement notE
(*2 Negation Elimination v1*)

lemma negative_paradox: "\<not> A\<longrightarrow> A\<longrightarrow> B" 
proof (rule impI)
  assume "\<not>A"
  show "A\<longrightarrow> B"
  proof
    assume A
    with `\<not> A` show B by (rule notE) 
(*
from `\<not> A` have B using `A` by (rule notE)
thus B.*)
(*then show B using `\<not> A` by blast: not working*)
  qed
qed


(*2 Negation Elimination v1*)

lemma "A\<longrightarrow> \<not>A\<longrightarrow> B" 
proof (rule impI)
  assume A
  show "\<not>A\<longrightarrow> B"
  proof
    assume "\<not>A"
    then show B using `A` by (rule notE) 
(*with `A` show B by (rule notI: not working*)
  qed
qed

lemma modus_tollens: "(A\<longrightarrow> B) \<longrightarrow>(\<not> B\<longrightarrow> \<not> A)"
proof(rule impI)
  assume "A\<longrightarrow> B"
  show "\<not>B\<longrightarrow> \<not>A"
  proof (rule impI)
    assume "\<not>B"
    show "\<not>A"
    proof (rule notI)
      assume A
      with `A \<longrightarrow> B` have B by (rule mp)
      with `\<not>B` show False by (rule notE) (*HOW*)
    qed
  qed
qed



lemma "\<not>(A\<longrightarrow> B)\<longrightarrow> \<not>B" 
proof (rule impI)
  assume "\<not>(A\<longrightarrow> B)"
  show "\<not>B"
  proof (rule notI)
    assume B
    have "A\<longrightarrow> B"
    proof (rule impI)
      assume A
      from `B` show B.
          qed
          with `\<not>(A\<longrightarrow> B )` show False by (rule notE ) (*HOW*)

  qed
qed

thm ccontr
lemma contradiction: "(\<not> A\<longrightarrow> False)\<longrightarrow> A" 
proof (rule impI)
  assume "(\<not> A\<longrightarrow> False)"
  show A
  proof (rule ccontr)
    assume "\<not>A"
    with `\<not> A \<longrightarrow> False` show False by (rule mp ) 
  qed
qed

print_statement notE
lemma double_negation_elimination: "\<not>\<not>A \<longrightarrow> A" 
proof(rule impI)
  assume "\<not>\<not>A"
  show A
  proof(rule ccontr)
    assume "\<not>A"
    with `\<not>\<not>A` show False by (rule notE) 
  qed
qed


   
(*Exercises*)
print_statement contrapos_pn
lemma "A \<Longrightarrow> \<not>\<not>A" 
proof 
  assume A
  show "\<not>A \<Longrightarrow> False"
  proof(rule ccontr)
    assume "\<not>A"
    with `A` show False by blast
    qed
  qed

(*difference in proofs*)
lemma "A \<longrightarrow> \<not>\<not>A" 
proof (rule impI)
  assume A
  show "\<not>\<not>A"
  proof (rule notI)
    assume "\<not>A"
    with `A` show False by blast
  qed
qed


lemma contraposition:  "(A\<longrightarrow> \<not>B)\<longrightarrow> (B\<longrightarrow> \<not>A)" 
proof (rule impI)
  assume "(A\<longrightarrow> \<not>B)"
  show "(B\<longrightarrow> \<not>A)"
  proof (rule impI)
    assume B
    show "\<not>A"
    proof
      assume A
      from `A\<longrightarrow> \<not>B` have "\<not>B" using `A` by (rule mp)
      then show False using `B` by (rule notE)
    qed
  qed
qed

thm ccontr
lemma "(\<not>B \<longrightarrow> \<not>A)\<longrightarrow>(A\<longrightarrow> B)" 
proof (rule impI)
  assume "(\<not>B \<longrightarrow> \<not>A)"
  show "A\<longrightarrow> B"
  proof (rule impI)
    assume A 
    show B
    proof (rule ccontr)
      assume "\<not>B"
      with `\<not>B \<longrightarrow> \<not>A` have "\<not>A" by (rule mp)
(* from `\<not>B \<longrightarrow> \<not>A` have "\<not>A" using `\<not>B` by (rule mp )*)
      thus False using `A` by (rule notE)
    qed
  qed
qed




lemma "A \<longrightarrow> \<not> (A \<longrightarrow> \<not> A)" 
proof (rule impI)
  assume A
  show "\<not>(A \<longrightarrow> \<not> A)"
  proof (rule notI)
    assume "(A \<longrightarrow> \<not> A)"
    from `A \<longrightarrow> \<not>A` have "\<not>A" using `A` by (rule mp)
    thus False using `A` by (rule notE)
  qed
qed



lemma god_exists: "\<not>(A\<longrightarrow> B) \<longrightarrow> A"  (*similar to "\<not>(A\<longrightarrow> B)\<longrightarrow> \<not>B" *)
proof (rule impI)
  assume "\<not>(A\<longrightarrow> B)"
  show A
  proof (rule ccontr)
    assume "\<not>A"
    have "A \<longrightarrow> B"
    proof (rule impI)
      assume A
      with `\<not> A` show B by (rule notE) 
    qed 
    with `\<not> (A \<longrightarrow> B )` show False by (rule notE ) 
        qed
      qed








end