theory Tensor_Product_Code_Examples
  imports Tensor_Product_Code Bounded_Operators.Bounded_Operators_Code_Examples
begin

value "tensorOp (id_cblinfun :: (bool ell2,_) cblinfun) (id_cblinfun :: (bool ell2,_) cblinfun)"

value "assoc_op :: ((bool*bool*bool) ell2,_) cblinfun"

value "comm_op :: ((bool*bool) ell2,_) cblinfun"

value "tensorVec (ket False) (ket False)"

end
