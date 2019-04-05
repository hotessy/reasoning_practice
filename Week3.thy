theory Week3
  imports Main
begin 


(*McGee against MP*)
lemma
  assumes A
  assumes "\<not>B" 
  assumes "\<not>C" 
  shows "A \<longrightarrow> B \<longrightarrow> C"
proof (rule impI)
  show "B \<longrightarrow> C"
  proof (rule impI)
    assume B
   (* with `\<not>B` show C by (rule notE) *)
    then have False using `\<not>B` by blast
    from `\<not>C` show C using `False` by blast
  qed
qed


lemma
assumes A
assumes "\<not>B" 
assumes "\<not>C" 
shows "B \<longrightarrow> C"
proof(rule impI)
  assume B
  with `\<not>B` show C by (rule notE)
qed


(*Conjunction Elimination*)
  thm conjE
lemma "A \<and> B \<longrightarrow> A"
proof(rule impI)
  assume "A \<and> B"
  then show A by (rule conjE)
qed


lemma "A \<and> B \<longrightarrow> B"
proof(rule impI)
  assume "A \<and> B"
  then show B by (rule conjE)
qed

(* Exercise 2.1 *)
lemma import:"(A \<longrightarrow> B\<longrightarrow> C) \<longrightarrow>((A \<and> B)\<longrightarrow>C)"
proof(rule impI)
  assume "(A \<longrightarrow> B\<longrightarrow> C)"
  show "(A \<and> B)\<longrightarrow>C"
  proof (rule impI)
    assume "A \<and> B"
    then have A by (rule conjE)
    from `A \<longrightarrow> B\<longrightarrow> C` have "B\<longrightarrow> C" using `A` by (rule mp)
    from `A \<and> B` have B by (rule conjE)
    from `B\<longrightarrow> C` have C using `B` by (rule mp)
    thus C.
  qed
qed

(*Conjunction Introduction*)
lemma "A \<and> B \<longrightarrow> B \<and> A" 
proof
  assume "A \<and> B"
  then have A by (rule conjE)
  from `A \<and> B` have B by (rule conjE)
  from `B` show "B \<and> A" using `A` by (rule conjI)
qed


(* Exercise 3.1 *)
lemma export: "((A \<and> B)\<longrightarrow>C)\<longrightarrow> (A \<longrightarrow> B\<longrightarrow> C)" 
proof (rule impI)
  assume "(A \<and> B)\<longrightarrow>C"
  show "A \<longrightarrow> B\<longrightarrow> C"
  proof (rule impI)
    assume A
    show "B\<longrightarrow> C"
    proof (rule impI)
      assume B
      then have "A \<and> B" using `A` by auto (*rule conjI not working*)
      from `(A \<and> B)\<longrightarrow>C` show C using `A \<and> B` by (rule mp)
      qed
    qed
  qed

(* Biconditional Introduction *)
print_statement iffI
lemma
  assumes "A \<longrightarrow> B" 
  assumes "B \<longrightarrow> A" 
  shows "B \<longleftrightarrow> A"
proof (rule iffI)
  assume A
  with `A \<longrightarrow> B` show B by (rule mp)
next 
  assume B
  with `B \<longrightarrow> A` show A by (rule mp)
qed


(* Exercise 4.1 *)
lemma "A \<longleftrightarrow> A"
proof
qed (* How is this valid ?*)




(* Biconditional Elimination *)

print_statement iffD1
lemma "(A \<longleftrightarrow> B) \<longrightarrow> A \<longrightarrow> B" 
proof(rule impI)
  assume "A \<longleftrightarrow> B"
  show "A \<longrightarrow>B"
  proof(rule impI)
    assume A
    then show B using `A \<longleftrightarrow> B` by blast
  qed
qed

lemma "(A \<longleftrightarrow> B) \<longrightarrow> B \<longrightarrow> A" 
proof(rule impI)
  assume "A \<longleftrightarrow> B"
  show "B \<longrightarrow> A"
  proof(rule impI)
    assume B
    with `A \<longleftrightarrow> B` show A by (rule iffD2)
  qed
qed


(* Exercise 5.1 *)

lemma "\<not>(A \<longleftrightarrow> \<not>A)"
proof(rule notI) (* alternative *)
  assume "A \<longleftrightarrow> \<not>A"
  then have A by blast
  from `A \<longleftrightarrow> \<not>A` have "\<not>A" by blast
  then show False using `A` by blast 
qed



(* Exercises *)

lemma import_export: "((A \<and> B) \<longrightarrow> C) \<longleftrightarrow> (A \<longrightarrow> B\<longrightarrow> C)" 
proof (rule iffI)
  assume "(A \<and> B) \<longrightarrow> C"
  then show "A \<longrightarrow> B \<longrightarrow> C" by blast (* rule Week3.export not working *)
next
  assume "A \<longrightarrow> B \<longrightarrow> C"
  then show "(A \<and> B) \<longrightarrow> C" by blast (* rule Week3.import not working *)
qed

lemma
  assumes "(A \<and> B) \<longrightarrow> C"
  assumes A
  shows "B \<longrightarrow> C" 
proof (rule impI)
  assume B
  then have "A \<and> B" using `A` by blast (* conjI not working *)
  (*then show C using `(A \<and> B) \<longrightarrow> C` by blast (* mp not working*)*)
  with `(A \<and> B) \<longrightarrow> C` show C by (rule mp)

qed

lemma
  assumes  A
  assumes "\<not>B" 
  assumes "\<not>C" 
  shows "(A \<and> B) \<longrightarrow> C" 
proof(rule impI)
  assume "A \<and> B"
  then have B by (rule conjE)
  then have False using `\<not>B` by blast
  then show C using `\<not>C` by blast
qed


lemma equivalence_left_to_right: "(A \<longrightarrow> B) \<longrightarrow> (\<not> (A \<and> \<not> B))" 
proof(rule impI)
  assume "A \<longrightarrow> B"
  show "\<not>(A \<and> \<not>B)"
  proof (rule notI)
    assume "A \<and> \<not> B"
    then have "\<not>B" by (rule conjE)
    from `A \<and> \<not>B` have A by (rule conjE)
    then have B using `A \<longrightarrow> B` by blast
    then show False using `\<not>B` by blast
  qed
qed

lemma equivalence_right_to_left: "\<not>(A \<and> \<not>B) \<longrightarrow> (A \<longrightarrow> B)" 
proof (rule impI)
  assume "\<not>(A \<and> \<not>B)"
  show "A \<longrightarrow> B"
  proof (rule impI)
    assume A
    then show B using `\<not>(A \<and> \<not>B)` by blast
  qed
qed


lemma the_equivalence_thesis: "(A \<longrightarrow> B) \<longleftrightarrow> (\<not>(A \<and> \<not> B))" 
proof(rule iffI)
  assume "A \<longrightarrow> B"
  then show "\<not>(A \<and> \<not> B)" by blast
      next
        assume "\<not>(A \<and> \<not> B)"
        then show "A \<longrightarrow> B" by blast 
      qed


lemma the_equivalence_thesis2: "(A \<longrightarrow> B) \<longleftrightarrow> (\<not>(A \<and> \<not> B))" 
proof(rule iffI)
  assume "A \<longrightarrow> B"
  with Week3.equivalence_left_to_right show "\<not>(A \<and> \<not> B)" by (rule mp)
next
  assume "\<not>(A \<and> \<not> B)"
  with Week3.equivalence_right_to_left show "A \<longrightarrow> B" by (rule mp)
qed

 


end