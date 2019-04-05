(* Positive paradox of material implication*)

theory Week1

imports Main

begin

(*If-Introduction*)

print_statement impI (*thm impI*)


lemma "A \<longrightarrow> A"
proof (rule impI)
  assume A (*assuming the antecedent*)
  then show A.
qed

(*Paradox of Material Implication*)

lemma positive_paradox : "A \<longrightarrow> (B \<longrightarrow> A)"
proof (rule impI)
  assume A 
  show "B \<longrightarrow> A"
  proof (rule impI)
    assume B (*irrelevant*)
    from `A` show A. (* 'from `A`' can be abb. as 'then' *)
  qed
qed


(*2.1 Exercise*)

lemma "A \<longrightarrow> B \<longrightarrow> B" 
proof(rule impI)
  assume A (*irrelevant*)
  show "B \<longrightarrow> B"
  proof (rule impI)
    assume B
    then show B.(* 'thus' is an abb. for 'then show' *)
  qed
qed

(*Modus Ponens*)

lemma "A \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> B"
proof(rule impI)
  assume A
  show "(A \<longrightarrow> B) \<longrightarrow> B"
  proof
    assume "(A \<longrightarrow> B)"
    then show  B using `A` by (rule mp)
  qed 
qed

(*3.1 Exercise*)

print_statement mp


lemma contraction: "(A \<longrightarrow> A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> B)"
proof (rule impI)
  assume "(A \<longrightarrow> A \<longrightarrow> B)"
  show  "(A \<longrightarrow> B)"
  proof (rule impI)
    assume A
    with `A \<longrightarrow> A \<longrightarrow> B` have "(A \<longrightarrow> B)" by (rule mp) (*get the consequent () for further use*)
    thus B using `A` by (rule mp)
    qed
  qed


(* EXERCISES *)

(*1*)
lemma mingle: "A \<longrightarrow> A \<longrightarrow> A" 

proof (rule impI)
  assume A
  show "A \<longrightarrow> A"
  proof
    assume A
    from `A` show A. (*A from line 2 used.*)
(* To use A from line 5, type `thus A.` 
In either case, one of the A's will be unused, hence not sound.*)
    qed
  qed


(*2*)
lemma prefixing: "(A \<longrightarrow> B) \<longrightarrow> (C \<longrightarrow> A) \<longrightarrow> (C \<longrightarrow> B)" 
proof (rule impI)
  assume "(A \<longrightarrow> B)"
  show "(C \<longrightarrow> A) \<longrightarrow> (C \<longrightarrow> B)"
  proof (rule impI)
    assume "(C \<longrightarrow> A)"
    show "C \<longrightarrow> B"
    proof 
      assume C
      with `(A \<longrightarrow> B)` and `(C \<longrightarrow> A)` have "(C \<longrightarrow> B)" by blast
      thus B using `C` by blast
    qed
  qed
qed


(*3*)
(*NOTE: Solution can be implemented using the method above as well*)
lemma suffixing: "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)" 
proof (rule impI)
  assume "(A \<longrightarrow> B)"
  show "(B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)"
  proof (rule impI)
    assume "(B \<longrightarrow> C)"
    show "A \<longrightarrow> C"
    proof 
      assume A
      with `(A \<longrightarrow> B)` have B by (rule mp)
      with `(B \<longrightarrow> C)` show C by (rule mp)
    qed
  qed
qed


(*4*)
lemma "(A\<longrightarrow> B\<longrightarrow> C)\<longrightarrow> (B\<longrightarrow> A\<longrightarrow> C)" 
proof 
  assume "(A\<longrightarrow> B\<longrightarrow> C)"
  show "(B\<longrightarrow> A\<longrightarrow> C)"
  proof 
    assume B
    show "(A\<longrightarrow> C)"
      proof
        assume A
        with `(A\<longrightarrow> B\<longrightarrow> C)` have "(B\<longrightarrow> C)" by blast (*rule mp*)
        then show C using `B` by blast (*rule mp*)
      qed
    qed
  qed


(*5*)
lemma hypothetical_syllogism: "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)" 
proof (rule Week1.suffixing)
qed

(*Not mentioned*)
lemma "(A\<longrightarrow> B)\<longrightarrow> A\<longrightarrow> C\<longrightarrow> B" 
proof(rule impI)
  assume "A \<longrightarrow> B"
  show "A\<longrightarrow> C\<longrightarrow> B"
  proof (rule impI)
    assume A
    show "C\<longrightarrow> B"
    proof (rule impI)
      assume C
      from `A \<longrightarrow> B` have B using `A` by (rule mp)
      from `B` show B.
    qed
  qed
qed



lemma "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> C)"
proof (rule impI)
  assume "A\<longrightarrow> B \<longrightarrow> C"
  show "(A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> C)"
  proof (rule impI)
    assume "A \<longrightarrow> B" 
    show "A \<longrightarrow> C" 
    proof (rule impI)
      assume A
      from `A \<longrightarrow> B` have B using `A` by (rule mp)
      from `A\<longrightarrow> B \<longrightarrow>C` have "B\<longrightarrow> C" using `A` by (rule mp) 
      thus C using `B` by (rule mp)
    qed 
  qed
qed

end

