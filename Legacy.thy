(* 

This theory contains the things that are still needed for qrhl-tool but should be removed eventually from here.

*)

theory Legacy
imports Bounded_Operators Complex_L2 "HOL-Library.Adhoc_Overloading"
begin

type_synonym ('a,'b) l2bounded = "('a ell2, 'b ell2) bounded"
abbreviation "applyOp == Rep_bounded"

consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)

adhoc_overloading
  cdot timesOp applyOp applyOpSpace

end
