theory ToDo_Tensor
  imports Tensor_Product 
begin

lemma cinner_tensor: "\<langle>\<gamma> \<otimes> \<psi>, \<delta> \<otimes> \<phi>\<rangle> = \<langle>\<psi>, \<phi>\<rangle> * \<langle>\<gamma>, \<delta>\<rangle>"
  sorry

lemma addState_adj_times_addState[simp]: 
  includes cblinfun_notation no_blinfun_notation
  fixes \<psi> \<phi> :: "'a ell2"
  shows "addState \<psi>* o\<^sub>C\<^sub>L addState \<phi> = \<langle>\<psi>, \<phi>\<rangle> *\<^sub>C (idOp::('b ell2,'b ell2) cblinfun)"
proof -
  have "\<langle>\<gamma>, (addState \<psi>* o\<^sub>C\<^sub>L addState \<phi>) *\<^sub>V \<delta>\<rangle> = \<langle>\<gamma>, (\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C idOp) *\<^sub>V \<delta>\<rangle>" for \<gamma> \<delta> :: "'b ell2"
    apply (simp add: times_applyOp adjoint_I')
    apply (transfer fixing: \<psi> \<phi> \<delta> \<gamma>)
    by (rule cinner_tensor)
  hence "(addState \<psi>* o\<^sub>C\<^sub>L addState \<phi>) *\<^sub>V \<delta> = (\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C idOp) *\<^sub>V \<delta>" for \<delta> :: "'b ell2"
    by (metis (no_types, lifting) adjoint_D adjoint_I adjoint_twice)
  thus ?thesis
    by (rule cblinfun_ext)
qed

lemma [simp]: "norm \<psi>=1 \<Longrightarrow> isometry (addState \<psi>)"
  unfolding isometry_def 
  by (simp add: cinner_norm_sq)

lemma ket_product: "ket (a,b) = ket a \<otimes> ket b"
  sorry

lemma tensorOp_applyOp_distr:
  includes cblinfun_notation no_blinfun_notation
  shows "(A \<otimes> B) *\<^sub>V (\<psi> \<otimes> \<phi>) = (A *\<^sub>V \<psi>) \<otimes> (B *\<^sub>V \<phi>)"
  sorry

lemma assoc_op_apply_tensor[simp]:
  includes cblinfun_notation no_blinfun_notation
  shows "assoc_op *\<^sub>V (\<psi>\<otimes>(\<phi>\<otimes>\<tau>)) = (\<psi>\<otimes>\<phi>)\<otimes>\<tau>"
  sorry

lemma comm_op_apply_tensor[simp]: 
  includes cblinfun_notation no_blinfun_notation
  shows "comm_op *\<^sub>V (\<psi>\<otimes>\<phi>) = (\<phi>\<otimes>\<psi>)"
  sorry

lemma assoc_op_adj_apply_tensor[simp]:
  includes cblinfun_notation no_blinfun_notation
  shows "assoc_op* *\<^sub>V ((\<psi>\<otimes>\<phi>)\<otimes>\<tau>) = \<psi>\<otimes>(\<phi>\<otimes>\<tau>)"
  sorry

lemma span_tensor: "Span G \<otimes> Span H = Span {g\<otimes>h|g h. g\<in>G \<and> h\<in>H}"
  sorry

lemma span_tensors:
  "closure (span {C1 \<otimes> C2| (C1::(_,_) l2bounded) (C2::(_,_) l2bounded). True}) = UNIV"
  sorry


end
