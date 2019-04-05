theory Week4
  imports Main
begin


lemma modus_tollens: 
  assumes "A \<longrightarrow> B" 
  assumes "\<not> B" 
  shows "\<not> A"
proof(rule notI)
  assume A
  with `A \<longrightarrow> B` have B by (rule mp) (* works with two dots `..` as well*)
  with `\<not>B` show False by (rule notE)
qed


lemma
  assumes major_premise: "A \<longrightarrow> B\<longrightarrow> C" 
  assumes minor_premise: A
  shows conclusion: "B \<longrightarrow> C"
proof
  assume B
  from major_premise have "B \<longrightarrow> C" using minor_premise by (rule mp) 
(* difference between from and with ?? *)
  then show C using `B` by (rule mp)
qed

lemma
  assumes major_premise: "A \<longrightarrow> B \<longrightarrow> C" 
  assumes wide_scope: "\<not>(B \<longrightarrow> C)"  
  shows notA: "\<not>A"
proof
  assume A
  with Week4.modus_tollens show False by blast  (*? ?*)
qed



lemma
  assumes major_premise: "A \<longrightarrow> B\<longrightarrow> C" 
  assumes narrow_scope: "B \<longrightarrow> \<not>C"  
  shows notA: "\<not>A"
  oops


lemma conditional_noncontradiction: "\<not> ((A \<longrightarrow> B) \<and> (A \<longrightarrow> \<not> B))" oops


(* IMPORTATNT *)
lemma conditional_excluded_middle: "(A \<longrightarrow> B) \<or> (A \<longrightarrow> \<not> B)"
proof cases
  assume B
  hence "A \<longrightarrow> B"..
  thus "(A \<longrightarrow> B) \<or> (A \<longrightarrow> \<not> B)"..
      next
        assume "\<not>B"
        then have "A \<longrightarrow> \<not> B"..
        then show "(A \<longrightarrow> B) \<or> (A \<longrightarrow> \<not> B)"..
      qed


lemma  "(A \<longrightarrow> B) \<or> (B \<longrightarrow>  A)" oops (* ToDo*)

(* Disjunction Introduction *)

lemma "A \<longrightarrow> (A \<or> B)" 
proof (rule impI)
  assume A
  show "A \<or> B"
  proof (rule disjI1)
    from `A` show A.
    qed
  qed

lemma "B \<longrightarrow> (A \<or> B)" 
proof (rule impI)
  assume B
  thus "A \<or> B" by (rule disjI2)
qed


lemma "(A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> B \<or> C)" 
proof (rule impI)
  assume "A \<longrightarrow> B"
  show "A \<longrightarrow> B \<or> C"
  proof (rule impI)
    assume A
    show "B \<or> C"
    proof (rule disjI1)
      from `A \<longrightarrow> B` show B using `A` by (rule mp)
    qed
  qed
qed


(* Disjunction Elimination *)
lemma "A \<or> A \<longrightarrow> A" 
proof
assume "A \<or> A"
  thus A 
  proof (rule disjE)
    assume A
    thus A.
        next
          assume A
          thus A. 
              qed
            qed



(* IMPORTANT *)
lemma "A \<or> B \<and> C \<longrightarrow> (A \<or> B) \<and> (A \<or> C)" (* precedence given to conj *) 
proof (rule impI)
  assume "A \<or> B \<and> C"
  then show "(A \<or> B) \<and> (A \<or> C)"    
  proof (rule disjE)
    assume A
    then have "A \<or> B" by (rule disjI1)
    moreover from `A` have "A \<or> C" by (rule disjI1) 
    ultimately show "(A \<or> B) \<and> (A \<or> C)" by (rule conjI) 
  next 
    assume "B \<and> C"
    then have B by (rule conjunct1) (* or conjE *)
    then have "A \<or> B" by (rule disjI2)
    then show "(A \<or> B) \<and> (A \<or> C)"
    proof (rule conjI)
      from `B \<and> C` have C by (rule conjE)
      thus "A \<or> C" by (rule disjI2)
    qed
  qed
qed



(* Proof by Cases *)

lemma excluded_middle: "A \<or> \<not> A"
proof cases
  assume A
  then show "A \<or> \<not>A" ..
  next 
    assume "\<not>A"
    then show "A \<or> \<not>A"..
  qed


lemma excluded_middle2: "A \<or> \<not> A"
proof(rule ccontr)
  assume "\<not>(A \<or> \<not> A)"
  have "\<not>A" (* consequeces of using then ?*)
    proof
      assume A
      then have "A \<or> \<not> A" by (rule disjI1)
      with `\<not>(A \<or> \<not> A)` show False by (rule notE)
          qed
          hence "A \<or> \<not> A" by (rule disjI2)
          with `\<not> (A \<or> \<not> A)` show False by (rule notE)
        qed
          
  





end



