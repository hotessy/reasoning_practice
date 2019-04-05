(* Exercise 2.5.2
 We strengthen the definition of a normal If-expression as follows: 
the first argument of all IFs must be a variable. 
Adapt the above development to this changed requirement. 

(Hint: you may need to formulate some of the goals as implications (\<longrightarrow>) 
rather than equalities (=).) 
*)



theory Boolean
  imports Main 
begin

datatype ifex  = CIF bool | VIF nat | IF ifex ifex ifex


 
end
