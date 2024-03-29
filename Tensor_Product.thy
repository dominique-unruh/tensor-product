(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Tensor_Product
  imports
    "Complex_Bounded_Operators.Complex_L2"
    "HOL-Library.Adhoc_Overloading" 
    Completion
    Algebraic_Tensor_Product
    Registers.Finite_Tensor_Product
begin
unbundle cblinfun_notation

section \<open>Hilbert tensor product\<close>

text\<open>Hilbert tensor product as defined in Helemskii chapter 2, section 8\<close>
typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) htensor
  = \<open>(UNIV::(('a \<otimes>\<^sub>a 'b) completion) set)\<close>
  ..

setup_lifting type_definition_htensor

(* "h" is for Hilbert *)
type_notation 
  htensor  ("(_ \<otimes>\<^sub>h/ _)" [21, 20] 20)


instantiation htensor :: (chilbert_space, chilbert_space) complex_inner
begin
lift_definition cinner_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> complex\<close>
  is "\<lambda> x y. (x \<bullet>\<^sub>C y)".

lift_definition scaleC_htensor :: \<open>complex \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>
  is "\<lambda> c x. c *\<^sub>C x".

lift_definition uminus_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>
  is "\<lambda> x. -x".

lift_definition zero_htensor :: \<open>'a \<otimes>\<^sub>h 'b\<close>
  is "0".

lift_definition minus_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>
  is \<open>\<lambda> x y. x - y\<close>.

lift_definition plus_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>
  is \<open>\<lambda> x y. x + y\<close>.

lift_definition sgn_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>
  is \<open>\<lambda> x.  x /\<^sub>R (norm x)\<close>.

lift_definition norm_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> real\<close>
  is \<open>\<lambda> x. norm x\<close>.

lift_definition scaleR_htensor :: \<open>real \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>
  is "\<lambda> c x. c *\<^sub>R x".

lift_definition dist_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> real\<close>
  is \<open>\<lambda> x y. dist x y\<close>.

definition uniformity_htensor :: \<open>(('a \<otimes>\<^sub>h 'b) \<times> 'a \<otimes>\<^sub>h 'b) filter\<close> where
  "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a \<otimes>\<^sub>h 'b) y < e})"

definition open_htensor :: \<open>('a \<otimes>\<^sub>h 'b) set \<Rightarrow> bool\<close> where
  "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a \<otimes>\<^sub>h 'b) = x \<longrightarrow> y \<in> U)"
instance
proof
  (* TODO: more readable to fix variable names via "fix" once and for all throught the proof, imho *)
  (* TODO: clean up superfluous type information *)
  show "((*\<^sub>R) r::'a \<otimes>\<^sub>h 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
    apply transfer
    by (simp add: scaleR_scaleC)

  show "(a::'a \<otimes>\<^sub>h 'b) + b + c = a + (b + c)"
    for a :: "'a \<otimes>\<^sub>h 'b"
      and b :: "'a \<otimes>\<^sub>h 'b"
      and c :: "'a \<otimes>\<^sub>h 'b"
    by (metis (mono_tags, lifting) Rep_htensor_inject ab_semigroup_add_class.add_ac(1) plus_htensor.rep_eq)

  show "(a::'a \<otimes>\<^sub>h 'b) + b = b + a"
    for a :: "'a \<otimes>\<^sub>h 'b"
      and b :: "'a \<otimes>\<^sub>h 'b"
    by (metis (mono_tags, lifting) Rep_htensor_inject Tensor_Product.plus_htensor.rep_eq ordered_field_class.sign_simps(2))

  show "(0::'a \<otimes>\<^sub>h 'b) + a = a"
    for a :: "'a \<otimes>\<^sub>h 'b"
    using Rep_htensor_inject plus_htensor.rep_eq zero_htensor.rep_eq by fastforce

  show "- (a::'a \<otimes>\<^sub>h 'b) + a = 0"
    for a :: "'a \<otimes>\<^sub>h 'b"
    using Rep_htensor_inject plus_htensor.rep_eq uminus_htensor.rep_eq zero_htensor.rep_eq by fastforce

  show "(a::'a \<otimes>\<^sub>h 'b) - b = a + - b"
    for a :: "'a \<otimes>\<^sub>h 'b"
      and b :: "'a \<otimes>\<^sub>h 'b"
    by (metis (mono_tags, lifting) Rep_htensor_inverse Tensor_Product.minus_htensor.rep_eq Tensor_Product.plus_htensor.rep_eq Tensor_Product.uminus_htensor.rep_eq pth_2)

  show "a *\<^sub>C ((x::'a \<otimes>\<^sub>h 'b) + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
    by (metis (mono_tags, lifting) Rep_htensor_inject plus_htensor.rep_eq scaleC_add_right scaleC_htensor.rep_eq)

  show "(a + b) *\<^sub>C (x::'a \<otimes>\<^sub>h 'b) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<otimes>\<^sub>h 'b"
    by (metis (mono_tags, lifting) Rep_htensor_inverse Tensor_Product.plus_htensor.abs_eq Tensor_Product.scaleC_htensor.rep_eq scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C (x::'a \<otimes>\<^sub>h 'b) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<otimes>\<^sub>h 'b"
    using Rep_htensor_inject scaleC_htensor.rep_eq by fastforce

  show "1 *\<^sub>C (x::'a \<otimes>\<^sub>h 'b) = x"
    for x :: "'a \<otimes>\<^sub>h 'b"
    using Rep_htensor_inject scaleC_htensor.rep_eq by fastforce

  show "dist (x::'a \<otimes>\<^sub>h 'b) y = norm (x - y)"
    for x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: dist_htensor.rep_eq dist_norm minus_htensor.rep_eq norm_htensor.rep_eq)

  show "sgn (x::'a \<otimes>\<^sub>h 'b) = inverse (norm x) *\<^sub>R x"
    for x :: "'a \<otimes>\<^sub>h 'b"
    using Rep_htensor_inject norm_htensor.rep_eq scaleR_htensor.rep_eq sgn_htensor.rep_eq 
    by fastforce

  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a \<otimes>\<^sub>h 'b) y < e})"
    by (simp add: Tensor_Product.uniformity_htensor_def)

  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a \<otimes>\<^sub>h 'b) = x \<longrightarrow> y \<in> U)"
    for U :: "('a \<otimes>\<^sub>h 'b) set"
    by (simp add: Tensor_Product.open_htensor_def)

  show "(x::'a \<otimes>\<^sub>h 'b) \<bullet>\<^sub>C y = cnj (y \<bullet>\<^sub>C x)"
    for x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: cinner_htensor.rep_eq)

  show "((x::'a \<otimes>\<^sub>h 'b) + y) \<bullet>\<^sub>C z = (x \<bullet>\<^sub>C z) + (y \<bullet>\<^sub>C z)"
    for x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
      and z :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: Tensor_Product.cinner_htensor.rep_eq Tensor_Product.plus_htensor.rep_eq cinner_add_left)

  show "(r *\<^sub>C (x::'a \<otimes>\<^sub>h 'b)) \<bullet>\<^sub>C y = cnj r * (x \<bullet>\<^sub>C y)"
    for r :: complex
      and x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: Tensor_Product.cinner_htensor.rep_eq Tensor_Product.scaleC_htensor.rep_eq)

  show "0 \<le> (x::'a \<otimes>\<^sub>h 'b) \<bullet>\<^sub>C x"
    for x :: "'a \<otimes>\<^sub>h 'b"
    using cinner_ge_zero cinner_htensor.rep_eq by auto

  show "(x::'a \<otimes>\<^sub>h 'b) \<bullet>\<^sub>C x = 0 \<longleftrightarrow> x = 0"
    for x :: "'a \<otimes>\<^sub>h 'b"
    using Rep_htensor_inject Tensor_Product.zero_htensor.rep_eq cinner_htensor.rep_eq by fastforce

  show "norm (x::'a \<otimes>\<^sub>h 'b) = sqrt (cmod (x \<bullet>\<^sub>C x))"
    for x :: "'a \<otimes>\<^sub>h 'b"
    using cinner_htensor.rep_eq norm_eq_sqrt_cinner norm_htensor.rep_eq by auto

qed
end

instantiation htensor :: (chilbert_space, chilbert_space) chilbert_space
begin 
instance
proof
  show "convergent X"
    if "Cauchy X"
    for X :: "nat \<Rightarrow> 'a \<otimes>\<^sub>h 'b"
  proof-
    from \<open>Cauchy X\<close>
    have \<open>Cauchy (\<lambda> n. Rep_htensor (X n))\<close>
      unfolding Cauchy_def dist_htensor_def
      by auto
    hence \<open>convergent (\<lambda> n. Rep_htensor (X n))\<close>
      using Cauchy_convergent by auto
    hence \<open>\<exists> l. \<forall> e>0. \<exists> N. \<forall> n\<ge>N. dist (Rep_htensor (X n)) l < e\<close>
      unfolding convergent_def
      using metric_LIMSEQ_D by blast
    then obtain l where \<open>\<forall> e>0. \<exists> N. \<forall> n\<ge>N. dist (Rep_htensor (X n)) l < e\<close>
      by blast
    have \<open>\<exists> L. Rep_htensor L = l\<close>
      by (metis Rep_htensor_inverse dist_eq_0_iff dist_htensor.abs_eq)
    then obtain L where \<open>Rep_htensor L = l\<close> by blast
    have \<open>\<forall> e>0. \<exists> N. \<forall> n\<ge>N. dist (Rep_htensor (X n)) (Rep_htensor L) < e\<close>
      by (simp add: \<open>Rep_htensor L = l\<close> \<open>\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (Rep_htensor (X n)) l < e\<close>)
    hence \<open>\<forall> e>0. \<exists> N. \<forall> n\<ge>N. dist (X n) L < e\<close>
      by (simp add: dist_htensor.rep_eq)
    hence \<open>X \<longlonglongrightarrow> L\<close>
      by (simp add: metric_LIMSEQ_I)
    thus ?thesis unfolding convergent_def by blast
  qed
qed
end

lift_definition htensor_op:: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>  (infixl "\<otimes>\<^sub>h" 70)
  is \<open>\<lambda> x::'a. \<lambda> y::'b. inclusion_completion (x \<otimes>\<^sub>a y)\<close>.

lemma htensor_distr_right:
  fixes x :: "'a::chilbert_space" and y z :: "'b::chilbert_space"
  shows  \<open>x \<otimes>\<^sub>h (y+z) =  x \<otimes>\<^sub>h y  +  x \<otimes>\<^sub>h z\<close>
  apply transfer
  by (simp add: atensor_distr_right inclusion_completion_add)  

lemma htensor_distr_right_sum:
  fixes x :: "'a::chilbert_space" and y :: "'c \<Rightarrow> 'b::chilbert_space"
    and I :: \<open>'c set\<close>
  shows  \<open>x \<otimes>\<^sub>h (\<Sum> i \<in> I. y i) = (\<Sum> i \<in> I. x \<otimes>\<^sub>h (y i))\<close>
  using htensor_distr_right
  by (metis Modules.additive_def additive.sum) 

lemma htensor_distr_left:
  fixes y z :: "'a::chilbert_space" and x :: "'b::chilbert_space"
  shows  \<open>(y+z) \<otimes>\<^sub>h x =  y \<otimes>\<^sub>h x  +  z \<otimes>\<^sub>h x\<close>
  apply transfer
  by (simp add: atensor_distr_left inclusion_completion_add)

lemma htensor_distr_left_sum:
  fixes  x :: "'c \<Rightarrow> 'a::chilbert_space" and y :: "'b::chilbert_space"
    and I :: \<open>'c set\<close>
  shows  \<open>(\<Sum> i \<in> I. x i) \<otimes>\<^sub>h y = (\<Sum> i \<in> I. (x i) \<otimes>\<^sub>h y)\<close>
proof-
  define f::\<open>'a \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close> where \<open>f t = t \<otimes>\<^sub>h y\<close> for t
  have \<open>Modules.additive f\<close>
    unfolding f_def
    using htensor_distr_left
    by (simp add: htensor_distr_left Modules.additive_def)    
  show ?thesis 
    using additive.sum \<open>Modules.additive f\<close> \<open>f \<equiv> \<lambda>t. t \<otimes>\<^sub>h y\<close> by auto
qed

lemma htensor_mult_right:
  fixes x :: "'a::chilbert_space" and y :: "'b::chilbert_space" and c :: complex
  shows \<open>x \<otimes>\<^sub>h (c *\<^sub>C y) = c *\<^sub>C (x \<otimes>\<^sub>h y)\<close>
  apply transfer
  by (simp add: atensor_mult_right inclusion_completion_scaleC) 

lemma htensor_mult_left:
  fixes x :: "'a::chilbert_space" and y :: "'b::chilbert_space" and c :: complex
  shows \<open>(c *\<^sub>C x) \<otimes>\<^sub>h y  = c *\<^sub>C (x \<otimes>\<^sub>h y)\<close>
  apply transfer
  by (simp add: atensor_mult_left inclusion_completion_scaleC)


lemma htensor_product_cartesian_product:
  assumes \<open>finite t\<close> and \<open>finite t'\<close>
  shows \<open>(\<Sum>i\<in>t. r i *\<^sub>C i) \<otimes>\<^sub>h (\<Sum>j\<in>t'. r' j *\<^sub>C j)
 = (\<Sum>(a, b)\<in>t\<times>t'. (r a * r' b) *\<^sub>C (a \<otimes>\<^sub>h b))\<close>
proof-
  have \<open>(\<Sum>i\<in>t. r i *\<^sub>C i) \<otimes>\<^sub>h (\<Sum>j\<in>t'. r' j *\<^sub>C j) = (\<Sum>i\<in>t. (r i *\<^sub>C i) \<otimes>\<^sub>h (\<Sum>j\<in>t'. r' j *\<^sub>C j) )\<close>
    using htensor_distr_left_sum by force    
  also have \<open>\<dots> = (\<Sum>i\<in>t. (\<Sum>j\<in>t'. (r i *\<^sub>C i) \<otimes>\<^sub>h (r' j *\<^sub>C j)) )\<close>
    by (metis (mono_tags, lifting) Finite_Cartesian_Product.sum_cong_aux htensor_distr_right_sum)    
  also have \<open>\<dots> = (\<Sum>i\<in>t. (\<Sum>j\<in>t'. r i *\<^sub>C ( i \<otimes>\<^sub>h (r' j *\<^sub>C j) ) ) )\<close>
    by (meson htensor_mult_left sum.cong)
  also have \<open>\<dots> = (\<Sum>i\<in>t. (\<Sum>j\<in>t'. r i *\<^sub>C ( r' j *\<^sub>C (i \<otimes>\<^sub>h j) ) ) )\<close>
    by (metis (no_types, lifting) htensor_mult_right sum.cong)
  also have \<open>\<dots> = (\<Sum>i\<in>t. (\<Sum>j\<in>t'. (r i * r' j) *\<^sub>C (i \<otimes>\<^sub>h j) ) )\<close>
    by auto
  also have \<open>\<dots> = (\<Sum>z\<in>t\<times>t'. (r (fst z) * r' (snd z)) *\<^sub>C ((fst z) \<otimes>\<^sub>h (snd z)))\<close>
    using Groups_Big.comm_monoid_add_class.sum.cartesian_product [where A = "t" 
        and B = "t'" and g = "\<lambda> i j. (r i * r' j) *\<^sub>C (i \<otimes>\<^sub>h j)"]
    by (metis (no_types, lifting) case_prod_beta' sum.cong)
  finally have \<open>(\<Sum>i\<in>t. r i *\<^sub>C i) \<otimes>\<^sub>h (\<Sum>j\<in>t'. r' j *\<^sub>C j) =
  (\<Sum>z\<in>t \<times> t'. (r (fst z) * r' (snd z)) *\<^sub>C (fst z \<otimes>\<^sub>h snd z))\<close>
    by blast
  thus ?thesis
    by (metis (mono_tags, lifting) case_prod_beta' sum.cong) 
qed


(* TODO:
- Develop htensorVec (not sure about the name) htensorOp as you proposed. (In Tensor_Product.thy.)
- Derive all relevant laws with respect to htensorOp. (In Tensor_Product.thy.)
- Define and prove the isomorphism i ('a ell2 \otimes 'b ell2) -> ('a*'b) ell2). (In Tensor_Product_L2.thy.)
- Define tensorVec as "tensorVec a b = i (htensorVec a b)" and "tensorOp A B psi = i (htensorOp a b (inv i))". (In Tensor_Product_L2.thy.)
- Define some suitable transfer rules (we can discuss that in more details when you reach that point).
- Derive properties of tensorVec and tensorOp directly from those in Tensor_Product.thy using the transfer method.

*)

text \<open>Theorem 1, page 189 in Helemskii\<close>
  (* TODO: Restructure proofs

 - remove hilbert_tensor_existence'_uniqueness
 - remove htensorOp_existence 
 - show htensorOp_existence inside proof of htensorOp_separation
   (we don't need htensorOp_existence then because htensorOp_separation implies existence)
 - show the uniqueness without existence as
   (H satisfies the property) \<Longrightarrow> H=htensorOp

 (Alternatively, if the existence proof is constructive, define htensorOp constructively (without SOME))

*)

(* TODO: define using lift_definition (?) *)
definition htensor_map::
  \<open>(('a::chilbert_space \<otimes>\<^sub>a 'b::chilbert_space) completion 
      \<Rightarrow> ('c::chilbert_space \<otimes>\<^sub>a 'd::chilbert_space) completion) 
    \<Rightarrow> (('a \<otimes>\<^sub>h 'b) \<Rightarrow> ('c \<otimes>\<^sub>h 'd))\<close> where
  \<open>htensor_map f z = Abs_htensor (f (Rep_htensor z))\<close>

lift_definition htensor_bounded::
  \<open>(('a::chilbert_space \<otimes>\<^sub>a 'b::chilbert_space) completion,
   ('c::chilbert_space \<otimes>\<^sub>a 'd::chilbert_space) completion) cblinfun 
\<Rightarrow> (('a \<otimes>\<^sub>h 'b), ('c \<otimes>\<^sub>h 'd)) cblinfun\<close> is htensor_map
proof
  fix f :: "('a \<otimes>\<^sub>a 'b) completion \<Rightarrow> ('c \<otimes>\<^sub>a 'd) completion"
  fix r :: complex and b b1 b2 :: \<open>'a \<otimes>\<^sub>h 'b\<close>
  assume "bounded_clinear f"
  show \<open>htensor_map f (r *\<^sub>C b) = r *\<^sub>C htensor_map f b\<close>
    unfolding htensor_map_def apply (transfer fixing: f)
    using \<open>bounded_clinear f\<close> by (simp add: bounded_clinear.clinear complex_vector.linear_scale)
  show \<open>htensor_map f (b1 + b2) = htensor_map f b1 + htensor_map f b2\<close>
    unfolding htensor_map_def apply (transfer fixing: f)
    using \<open>bounded_clinear f\<close> bounded_clinear_def complex_vector.linear_add by blast
  show "\<exists>K. \<forall>x. norm (htensor_map f (x::'a \<otimes>\<^sub>h 'b)::'c \<otimes>\<^sub>h 'd) \<le> norm x * K"
    if "bounded_clinear (f::('a \<otimes>\<^sub>a 'b) completion \<Rightarrow> ('c \<otimes>\<^sub>a 'd) completion)"
    by (metis (no_types, opaque_lifting) bounded_clinear.bounded htensor_map_def norm_htensor.abs_eq norm_htensor.rep_eq that)
qed


lemma Abs_htensor_continuous:
  fixes a :: \<open>('a::chilbert_space \<otimes>\<^sub>a 'b::chilbert_space) completion\<close>
  shows \<open>isCont Abs_htensor a\<close>
proof-
  have \<open>x \<longlonglongrightarrow> a \<Longrightarrow> (\<lambda> n. Abs_htensor (x n)) \<longlonglongrightarrow> Abs_htensor a\<close>
    for x::\<open>nat \<Rightarrow> ('a::chilbert_space \<otimes>\<^sub>a 'b::chilbert_space) completion\<close>
    using LIMSEQ_def[where X = "x" and L = "a"]
      LIMSEQ_def[where X = "(\<lambda> n. Abs_htensor (x n))" and L = "Abs_htensor a"]
    unfolding dist_htensor_def
    apply auto
    by (metis dist_htensor.abs_eq dist_htensor.rep_eq)
  thus ?thesis
    by (simp add: continuous_at_sequentiallyI)
qed



text\<open>Proposition 2 in Helemskii, page 187\<close>
lemma htensor_continuous:
  fixes x::\<open>nat \<Rightarrow> 'a::chilbert_space\<close> and y::\<open>nat \<Rightarrow> 'b::chilbert_space\<close>
  assumes \<open>x \<longlonglongrightarrow> a\<close> and \<open>y \<longlonglongrightarrow> b\<close>
  shows \<open>(\<lambda> n. (x n) \<otimes>\<^sub>h (y n) ) \<longlonglongrightarrow> a \<otimes>\<^sub>h b\<close>
proof-
  have Abs_htensor1: \<open>z \<longlonglongrightarrow> t \<Longrightarrow> (\<lambda> n. Abs_htensor (z n)) \<longlonglongrightarrow> Abs_htensor t\<close>
    for z::\<open>nat \<Rightarrow> ('a \<otimes>\<^sub>a 'b) completion\<close>
      and t::\<open>('a \<otimes>\<^sub>a 'b) completion\<close>
  proof-
    assume \<open>z \<longlonglongrightarrow> t\<close>
    moreover have \<open>\<forall>x. x \<longlonglongrightarrow> t \<longrightarrow> (Abs_htensor \<circ> x) \<longlonglongrightarrow> Abs_htensor t\<close>
      for t::\<open>('a \<otimes>\<^sub>a 'b) completion\<close>
      using Abs_htensor_continuous[where a = "t"] continuous_at_sequentially[where f = "Abs_htensor" and a = "t"]
      by auto    
    ultimately have \<open>(Abs_htensor \<circ> z) \<longlonglongrightarrow> Abs_htensor t\<close>
      by auto
    moreover have \<open>Abs_htensor \<circ> z = (\<lambda> n. Abs_htensor (z n))\<close>
      by auto
    ultimately show ?thesis by simp
  qed
  have \<open>(\<lambda>n. x n \<otimes>\<^sub>a y n) \<longlonglongrightarrow> a \<otimes>\<^sub>a b\<close>
    by (simp add: assms(1) assms(2) atensor_continuous)    
  moreover have \<open>isCont inclusion_completion (a \<otimes>\<^sub>a b)\<close>
    by (simp add: inclusion_completion_continuous)    
  ultimately have \<open>(\<lambda>n. inclusion_completion (x n \<otimes>\<^sub>a y n)) \<longlonglongrightarrow> inclusion_completion (a \<otimes>\<^sub>a b)\<close>
    using Elementary_Topology.continuous_at_sequentially[where f = "inclusion_completion" and a = "a \<otimes>\<^sub>a b"]
    by (simp add: comp_def)    
  thus ?thesis 
    unfolding htensor_op_def
    apply auto
    using Abs_htensor1 
    by auto
qed

lemma htensor_cinner_mult:
  \<open>(x\<^sub>1 \<otimes>\<^sub>h y\<^sub>1) \<bullet>\<^sub>C (x\<^sub>2 \<otimes>\<^sub>h y\<^sub>2) = (x\<^sub>1 \<bullet>\<^sub>C x\<^sub>2) * (y\<^sub>1 \<bullet>\<^sub>C y\<^sub>2)\<close>
  apply transfer
  by (simp add: atensor_cinner_mult inclusion_completion_cinner)

lemma htensor_norm_mult:
  \<open>norm (x \<otimes>\<^sub>h y) = norm x * norm y\<close>
proof -
  have "norm x * norm y = sqrt (cmod (x \<bullet>\<^sub>C x)) * sqrt (cmod (y \<bullet>\<^sub>C y))"
    by (metis norm_eq_sqrt_cinner)
  thus ?thesis
    by (metis htensor_cinner_mult norm_eq_sqrt_cinner norm_mult real_sqrt_mult)
qed 

(* Ask to Dominique: how to prove this *)
text\<open>Hilbert tensor product of bounded operators\<close>
lift_definition htensorOp :: \<open>('a::chilbert_space, 'b::chilbert_space) cblinfun
 \<Rightarrow> ('c::chilbert_space, 'd::chilbert_space) cblinfun \<Rightarrow> (('a \<otimes>\<^sub>h 'c), ('b \<otimes>\<^sub>h 'd)) cblinfun\<close>   (infixl "\<^sub>H\<otimes>" 70)
  is \<open>\<lambda> f::('a, 'b) cblinfun. \<lambda> g::('c, 'd) cblinfun. \<lambda> z::('a \<otimes>\<^sub>a 'c) completion. (completion_map (f \<^sub>A\<otimes> g)) *\<^sub>V z\<close>
  sorry

section \<open>Tensor product ell2\<close>

(* Widening type to allow infinite tensor products *)
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>tensor_op\<close>, SOME \<^typ>\<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<Rightarrow> 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2 \<Rightarrow> ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b \<times> 'd) ell2\<close>)\<close>
abbreviation (input) "tensorOp == tensor_op"

(* consts "tensorOp" :: "('a ell2,'b ell2) cblinfun \<Rightarrow> ('c ell2,'d ell2) cblinfun \<Rightarrow> (('a*'c) ell2,('b*'d) ell2) cblinfun" *)

type_synonym ('a, 'b) l2bounded = "('a ell2,'b ell2) cblinfun"

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>tensor_ell2\<close>, SOME \<^typ>\<open>'a ell2 \<Rightarrow> 'b ell2 \<Rightarrow> ('a \<times> 'b) ell2\<close>)\<close>
abbreviation (input) "tensorVec == tensor_ell2"

(* lift_definition "tensorVec" :: "'a ell2 \<Rightarrow> 'c ell2 \<Rightarrow> ('a*'c) ell2" is
  "\<lambda>\<psi> \<phi> (x,y). \<psi> x * \<phi> y"
  sorry *)

definition tensorSpace :: "'a ell2 ccsubspace \<Rightarrow> 'b ell2 ccsubspace \<Rightarrow> ('a*'b) ell2 ccsubspace" (infixr "\<otimes>\<^sub>S" 70) where
  "tensorSpace A B = ccspan {tensorVec \<psi> \<phi>| \<psi> \<phi>. \<psi> \<in> space_as_set A \<and> \<phi> \<in> space_as_set B}"

consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr "\<otimes>" 71)
adhoc_overloading tensor "\<lambda>x. tensorOp x" "\<lambda>x. tensorSpace x" "\<lambda>x. tensorVec x"

lemma id_tensor_id[simp]: "id_cblinfun \<otimes> id_cblinfun = id_cblinfun"
  sorry

definition "comm_op" :: "(('a*'b) ell2, ('b*'a) ell2) cblinfun" where
  "comm_op = classical_operator (\<lambda>(a,b). Some (b,a))"

lemma adj_comm_op[simp]: "adj comm_op = comm_op"
  sorry

lemma
  comm_op_swap[simp]: "comm_op o\<^sub>C\<^sub>L (A\<otimes>B) o\<^sub>C\<^sub>L comm_op = B\<otimes>A"
  for A::"('a ell2,'b ell2) cblinfun" and B::"('c ell2,'d ell2) cblinfun"
  sorry

lemma comm_op_times_comm_op[simp]: "comm_op  o\<^sub>C\<^sub>L comm_op = id_cblinfun"
proof -
  have "comm_op  o\<^sub>C\<^sub>L (id_cblinfun \<otimes> id_cblinfun)  o\<^sub>C\<^sub>L comm_op = id_cblinfun \<otimes> id_cblinfun" 
    by (simp del: id_tensor_id)
  thus ?thesis by simp
qed

lemma unitary_comm_op[simp]: "unitary comm_op"
  unfolding unitary_def sorry

definition "assoc_op" :: "(('a*('b*'c)) ell2, (('a*'b)*'c) ell2) cblinfun" where
  "assoc_op = classical_operator (\<lambda>(a,(b,c)). Some ((a,b),c))"

lemma unitary_assoc_op[simp]: "unitary assoc_op"
  sorry

lemma tensor_scalar_mult1[simp]: "(a *\<^sub>C A) \<otimes> B = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  sorry
lemma tensor_scalar_mult1_ell2[simp]: "(a *\<^sub>C A) \<otimes> B = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"_ ell2" and B::"_ ell2"
  sorry
lemma tensor_scalar_mult2[simp]: "A \<otimes> (a *\<^sub>C B) = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  sorry
lemma tensor_scalar_mult2_ell2[simp]: "A \<otimes> (a *\<^sub>C B) = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"_ ell2" and B::"_ ell2"
  sorry
lemma tensor_plus: "(A+B) \<otimes> C = A \<otimes> C + B \<otimes> C" for A B C :: "(_,_) cblinfun"
  sorry
lemma tensor_plus_ell2: "(A+B) \<otimes> C = A \<otimes> C + B \<otimes> C" for A B C :: "_ ell2"
  sorry
lemma tensor_norm_ell2: "norm (\<psi> \<otimes> \<phi>) = norm \<psi> * norm \<phi>" for \<psi> \<phi> :: "_ ell2"
  sorry

lemma tensor_times[simp]: "(U1 \<otimes> U2) o\<^sub>C\<^sub>L (V1 \<otimes> V2) = (U1 o\<^sub>C\<^sub>L V1) \<otimes> (U2 o\<^sub>C\<^sub>L V2)"
  for V1 :: "('a1,'b1) l2bounded" and U1 :: "('b1,'c1) l2bounded"
    and V2 :: "('a2,'b2) l2bounded" and U2 :: "('b2,'c2) l2bounded"
  sorry

lift_definition addState :: "'a ell2 \<Rightarrow> ('b ell2,('b*'a) ell2) cblinfun" is
  \<open>\<lambda>\<psi> \<phi>. tensorVec \<phi> \<psi>\<close>
  apply (rule_tac K="norm ell2" in bounded_clinear_intro)
  by (auto simp: tensor_norm_ell2 tensor_plus_ell2)


(* TODO: this is simply the adj of addState (1::unit ell2), and addState y is best defined as x \<rightarrow> x \<otimes> y (lifted).
   Do we even use remove_qvar_unit_op then? *)
consts remove_qvar_unit_op :: "(('a*unit) ell2,'a ell2) cblinfun"


(* definition addState :: "'a ell2 \<Rightarrow> ('b,'b*'a) l2bounded" where
  "addState \<psi> = id_cblinfun \<otimes> (ell2_to_bounded \<psi>) \<cdot> remove_qvar_unit_op*" *)

lemma addState_times_scalar[simp]: "addState (a *\<^sub>C \<psi>) = a *\<^sub>C addState \<psi>"
  for a::complex and \<psi>::"'a ell2"
  sorry

lemma tensor_adjoint[simp]: "adj (U\<otimes>V) = (adj U) \<otimes> (adj V)"
  for U :: "('a,'b) l2bounded" and V :: "('c,'d) l2bounded"
  sorry

lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  using assms unfolding unitary_def by simp

lemma tensor_isometry[simp]: 
  assumes "isometry U" and "isometry V"
  shows "isometry (U\<otimes>V)"
  using assms unfolding isometry_def by simp

unbundle no_cblinfun_notation

end
