(* Exercise 2.5.1 
Define the datatype of binary trees:
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

Define a function mirror that mirrors a binary tree by swapping subtrees recursively. Prove
lemma mirror_mirror: "mirror(mirror t) = t"

Define a function flatten that flattens a tree into a list by traversing it in
infix order. Prove 
lemma "flatten(mirror t) = rev(flatten t)"
*)

theory BTree
  imports Main

begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

(* datatype even_nat = Even_Zero | Even_Succ odd_nat and odd_nat = Odd_Succ even_nat
 *)

primrec mirror :: "'a tree \<Rightarrow> 'a tree" where 
"mirror Tip = Tip" | 
"mirror (Node leftTree val rightTree) = (Node (mirror rightTree) val (mirror leftTree))"

primrec flatten :: "'a tree \<Rightarrow> 'a list" where 
"flatten Tip = []" |
"flatten (Node leftTree val rightTree) = ((flatten leftTree) @ [val] @ (flatten rightTree)) "


lemma mirror_mirror: "mirror(mirror t) = t"
  apply (induct)
   apply (auto)
  done

lemma "flatten(mirror t) = rev(flatten t)"
  apply (induct)
   apply (auto)
  done

definition "myTree = Node (Node Tip 2 Tip) (1::int) (Node Tip 3 Tip)"
value "flatten myTree"


end
