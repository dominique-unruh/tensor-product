theory Tensor_Product_Code
  imports Tensor_Product Complex_Bounded_Operators.Cblinfun_Code
begin

unbundle cblinfun_notation

definition "matrix_tensor (A::'a::times mat) (B::'a mat) =
  mat (dim_row A*dim_row B) (dim_col A*dim_col B) 
  (\<lambda>(r,c). index_mat A (r div dim_row B, c div dim_col B) *
           index_mat B (r mod dim_row B, c mod dim_col B))"

lemma bounded_of_mat_tensorOp[code]:
  "mat_of_cblinfun (tensorOp A B) = matrix_tensor (mat_of_cblinfun A) (mat_of_cblinfun B)"
  for A :: "('a::enum,'b::enum) l2bounded"
    and B :: "('c::enum,'d::enum) l2bounded"
  sorry


lemma bounded_of_mat_assoc_op[code]: 
  "mat_of_cblinfun (assoc_op :: ('a::enum*'b::enum*'c::enum,_) l2bounded) = one_mat (Enum.card_UNIV TYPE('a)*Enum.card_UNIV TYPE('b)*Enum.card_UNIV TYPE('c))"
  sorry

definition "comm_op_mat TYPE('a::enum) TYPE('b::enum) =
  (let da = Enum.card_UNIV TYPE('a); db = Enum.card_UNIV TYPE('b) in
  mat (da*db) (da*db)
  (\<lambda>(r,c). (if (r div da = c mod db \<and>
                r mod da = c div db) then 1 else 0)))"

lemma bounded_of_mat_comm_op[code]:
  "mat_of_cblinfun (comm_op :: ('a::enum*'b::enum,_) l2bounded) = comm_op_mat TYPE('a) TYPE('b)"
  sorry

definition "vec_tensor (A::'a::times vec) (B::'a vec) =
  vec (dim_vec A*dim_vec B) 
  (\<lambda>r. vec_index A (r div dim_vec B) *
       vec_index B (r mod dim_vec B))"

lemma tensorVec_code[code]: "vec_of_ell2 (\<psi> \<otimes> \<phi>) = vec_tensor (vec_of_ell2 \<psi>) (vec_of_ell2 \<phi>)"
  for \<psi>::"'a::enum ell2" and \<phi>::"'b::enum ell2"
  sorry

(* See comment at definition of remove_qvar_unit_op before proving *)
lemma mat_of_cblinfun_remove_qvar_unit_op[code]:
  "mat_of_cblinfun (remove_qvar_unit_op::(_,'a::enum) l2bounded) = mat_of_cblinfun (id_cblinfun::(_,'a) l2bounded)" 
  sorry

(* TODO: more direct code equation (w/o remove_qvar_unit_op) *)
lemma addState_remove_qvar_unit_op[code]: "addState \<psi> = id_cblinfun \<otimes> (vector_to_cblinfun \<psi>) o\<^sub>C\<^sub>L remove_qvar_unit_op*"
  sorry

lemma tensorSpace_SPAN[code]: "tensorSpace (SPAN A) (SPAN B) = SPAN [vec_tensor a b. a<-A, b<-B]"
  sorry

unbundle no_cblinfun_notation

end
