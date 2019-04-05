theory demoDT
  imports Main
begin 

datatype 'a tree= Leaf | Node 'a  "'a tree"  "'a tree"

fun numNodes:: "'a tree \<Rightarrow> nat"
where
"numNodes Leaf = 0" |
"numNodes (Node e t1 t2) = 1+(numNodes t1)+(numNodes t2)"

fun subTree:: "'a tree \<Rightarrow> 'a tree \<Rightarrow> bool"
where
"subTree Leaf Leaf = True" |
"subTree t Leaf = False" |
"subTree t (Node e t1 t2) = ((t=(Node e t1 t2)) \<or> (subTree t t1) \<or> (subTree t t2))"


definition "myTree= Node (1::int) (Node 2 (Node 9 Leaf Leaf) Leaf) (Node 3 Leaf Leaf)" 

value "numNodes myTree"
value "subTree (Node 9 Leaf Leaf) myTree"  

export_code  numNodes subTree in Haskell


end

