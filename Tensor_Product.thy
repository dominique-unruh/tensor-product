(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Tensor_Product
  imports
    Bounded_Operators
    Complex_L2 
    "HOL-Library.Adhoc_Overloading" 
    Completion
    Algebraic_Tensor_Product

begin
unbundle bounded_notation

section \<open>Hilbert tensor product\<close>

text\<open>Hilbert tensor product as defined in @{cite Helemskii} chapter 2, section 8\<close>
typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) htensor
  = \<open>(UNIV::(('a \<otimes>\<^sub>a 'b) completion) set)\<close>
  by auto

setup_lifting type_definition_htensor

(* "h" is for Hilbert *)
type_notation 
  htensor  ("(_ \<otimes>\<^sub>h/ _)" [21, 20] 20)


instantiation htensor :: (chilbert_space, chilbert_space) complex_inner
begin
lift_definition cinner_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> complex\<close>
  is "\<lambda> x y. \<langle> x, y \<rangle>".

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

  show "\<langle>x::'a \<otimes>\<^sub>h 'b, y\<rangle> = cnj \<langle>y, x\<rangle>"
    for x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: cinner_htensor.rep_eq)

  show "\<langle>(x::'a \<otimes>\<^sub>h 'b) + y, z\<rangle> = \<langle>x, z\<rangle> + \<langle>y, z\<rangle>"
    for x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
      and z :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: Tensor_Product.cinner_htensor.rep_eq Tensor_Product.plus_htensor.rep_eq cinner_left_distrib)

  show "\<langle>r *\<^sub>C (x::'a \<otimes>\<^sub>h 'b), y\<rangle> = cnj r * \<langle>x, y\<rangle>"
    for r :: complex
      and x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: Tensor_Product.cinner_htensor.rep_eq Tensor_Product.scaleC_htensor.rep_eq)

  show "0 \<le> \<langle>x::'a \<otimes>\<^sub>h 'b, x\<rangle>"
    for x :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: cinner_htensor.rep_eq)

  show "(\<langle>x::'a \<otimes>\<^sub>h 'b, x\<rangle> = 0) = (x = 0)"
    for x :: "'a \<otimes>\<^sub>h 'b"
  proof
    show "x = 0"
      if "\<langle>x, x\<rangle> = 0"
      using that
      using Rep_htensor_inject cinner_htensor.rep_eq zero_htensor.rep_eq by fastforce 
    show "\<langle>x, x\<rangle> = 0"
      if "x = 0"
      using that
      by (simp add: cinner_htensor.abs_eq zero_htensor_def) 
  qed
  show "norm (x::'a \<otimes>\<^sub>h 'b) = sqrt (cmod \<langle>x, x\<rangle>)"
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

text \<open>Theorem 1, page 189 in @{cite Helemskii}\<close>
  (* TODO: Restructure proofs

 - remove hilbert_tensor_existence'_uniqueness
 - remove htensorOp_existence 
 - show htensorOp_existence inside proof of htensorOp_separation
   (we don't need htensorOp_existence then because htensorOp_separation implies existence)
 - show the uniqueness without existence as
   (H satisfies the property) \<Longrightarrow> H=htensorOp

 (Alternatively, if the existence proof is constructive, define htensorOp constructively (without SOME))

*)

definition htensor_map::
  \<open>(('a::chilbert_space \<otimes>\<^sub>a 'b::chilbert_space) completion 
\<Rightarrow> ('c::chilbert_space \<otimes>\<^sub>a 'd::chilbert_space) completion) 
\<Rightarrow> (('a \<otimes>\<^sub>h 'b) \<Rightarrow> ('c \<otimes>\<^sub>h 'd))\<close> where
  \<open>htensor_map f z = Abs_htensor (f (Rep_htensor z))\<close>

lift_definition htensor_bounded::
  \<open>(('a::chilbert_space \<otimes>\<^sub>a 'b::chilbert_space) completion,
   ('c::chilbert_space \<otimes>\<^sub>a 'd::chilbert_space) completion) bounded 
\<Rightarrow> (('a \<otimes>\<^sub>h 'b), ('c \<otimes>\<^sub>h 'd)) bounded\<close> is htensor_map
proof
  show "clinear (htensor_map f::'a \<otimes>\<^sub>h 'b \<Rightarrow> 'c \<otimes>\<^sub>h 'd)"
    if "bounded_clinear (f::('a \<otimes>\<^sub>a 'b) completion \<Rightarrow> ('c \<otimes>\<^sub>a 'd) completion)"
    for f :: "('a \<otimes>\<^sub>a 'b) completion \<Rightarrow> ('c \<otimes>\<^sub>a 'd) completion"
    using that
    by (smt bounded_clinear.is_clinear clinearI complex_vector.linear_add complex_vector.linear_scale htensor_map_def plus_htensor.abs_eq plus_htensor.rep_eq scaleC_htensor.abs_eq scaleC_htensor.rep_eq) 
  show "\<exists>K. \<forall>x. norm (htensor_map f (x::'a \<otimes>\<^sub>h 'b)::'c \<otimes>\<^sub>h 'd) \<le> norm x * K"
    if "bounded_clinear (f::('a \<otimes>\<^sub>a 'b) completion \<Rightarrow> ('c \<otimes>\<^sub>a 'd) completion)"
    for f :: "('a \<otimes>\<^sub>a 'b) completion \<Rightarrow> ('c \<otimes>\<^sub>a 'd) completion"
  proof-
    have \<open>\<exists> K. \<forall> x. norm (f x) \<le> norm x * K\<close>
      using that unfolding bounded_clinear_def
      by simp 
    then obtain K where \<open>\<And> x. norm (f x) \<le> norm x * K\<close>
      by blast
    have \<open>norm (htensor_map f x) \<le> norm x * K\<close>
      for x::\<open>'a \<otimes>\<^sub>h 'b\<close>
      by (metis \<open>\<And>x. norm (f x) \<le> norm x * K\<close> htensor_map_def norm_htensor.abs_eq norm_htensor.rep_eq)      
    thus ?thesis by blast
  qed
qed


lemma htensor_norm_mult:
  \<open>norm (x \<otimes>\<^sub>h y) = norm x * norm y\<close>
  sorry

lemma hilbert_tensor_existence'_left':
  fixes S :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close>
  assumes \<open>bounded_clinear S\<close> 
  shows \<open>\<exists> H :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h ('c::chilbert_space).
  bounded_clinear H \<and> (\<forall> x y. H (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy) \<and> onorm H \<le> onorm S\<close>
proof-
  define k::\<open>'a \<Rightarrow> 'c \<Rightarrow> 'b\<otimes>\<^sub>h'c\<close> where \<open>k x y = (S x) \<otimes>\<^sub>h y\<close> for x y
  have \<open>cbilinear k\<close>
    unfolding k_def cbilinear_def
  proof
    show "\<forall>y. clinear (\<lambda>x. S x \<otimes>\<^sub>h (y::'c))"
    proof
      show "clinear (\<lambda>x. S x \<otimes>\<^sub>h (y::'c))"
        for y :: 'c
        unfolding clinear_def proof
        show "S (b1 + b2) \<otimes>\<^sub>h y = S b1 \<otimes>\<^sub>h y + S b2 \<otimes>\<^sub>h y"
          for b1 :: 'a
            and b2 :: 'a
        proof-
          have \<open>S (b1 + b2) = S b1 + S b2\<close>
            using \<open>bounded_clinear S\<close>
            unfolding bounded_clinear_def clinear_def Vector_Spaces.linear_def module_hom_def 
              module_hom_axioms_def by auto
          thus ?thesis
            by (simp add: htensor_distr_left)             
        qed

        show "S (r *\<^sub>C b) \<otimes>\<^sub>h y = r *\<^sub>C (S b \<otimes>\<^sub>h y)"
          for r :: complex
            and b :: 'a
        proof-
          have \<open>S (r *\<^sub>C b) = r *\<^sub>C (S b)\<close>
            using \<open>bounded_clinear S\<close>
            unfolding bounded_clinear_def clinear_def
            by (simp add: assms bounded_clinear.is_clinear complex_vector.linear_scale)
          thus ?thesis
            by (simp add: htensor_mult_left) 
        qed
      qed
    qed
    show "\<forall>x. clinear ((\<otimes>\<^sub>h) (S x)::'c \<Rightarrow> 'b \<otimes>\<^sub>h _)"
      unfolding clinear_def proof
      show "Vector_Spaces.linear ((*\<^sub>C)::complex \<Rightarrow> 'c \<Rightarrow> _) (*\<^sub>C) ((\<otimes>\<^sub>h) (S x))"
        for x :: 'a
      proof
        show "S x \<otimes>\<^sub>h ((b1::'c) + b2) = S x \<otimes>\<^sub>h b1 + S x \<otimes>\<^sub>h b2"
          for b1 :: 'c
            and b2 :: 'c
          by (simp add: htensor_distr_right)

        show "S x \<otimes>\<^sub>h r *\<^sub>C (b::'c) = r *\<^sub>C (S x \<otimes>\<^sub>h b)"
          for r :: complex
            and b :: 'c
          by (simp add: htensor_mult_right)
      qed
    qed
  qed

  hence \<open>\<exists>! K :: 'a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'c. clinear K \<and> (\<forall> x y. k x y = K (x \<otimes>\<^sub>a y))\<close>
    by (simp add: atensor_universal_property)
  then obtain K::\<open>'a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'c\<close> where \<open>clinear K\<close> and \<open>\<forall> x y. k x y = K (x \<otimes>\<^sub>a y)\<close>
    by blast
  have \<open>\<exists> H. bounded_clinear H \<and> (\<forall> x y. H (x \<otimes>\<^sub>h y) = K (x \<otimes>\<^sub>a y))\<close> 
    sorry
  then obtain H where \<open>bounded_clinear H\<close> and \<open>\<forall> x y. H (x \<otimes>\<^sub>h y) = K (x \<otimes>\<^sub>a y)\<close>
    by blast
  have \<open>bounded_clinear H\<close>
    sorry
  moreover have \<open>\<forall> x y. H (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy\<close> 
    sorry
  moreover have \<open>onorm H \<le> onorm S\<close>
    sorry
  ultimately show ?thesis by blast
qed

lemma hilbert_tensor_existence'_right':
  fixes T :: \<open>'c::chilbert_space \<Rightarrow> 'd::chilbert_space\<close>
  assumes \<open>bounded_clinear T\<close> 
  shows \<open>\<exists> H :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> ('a::chilbert_space) \<otimes>\<^sub>h 'd. 
  bounded_clinear H \<and> (\<forall> x y. H (x \<otimes>\<^sub>h y) = x\<otimes>\<^sub>h(T y)) \<and> onorm H \<le> onorm T\<close>
  sorry


lemma hilbert_tensor_existence'':
  fixes S :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close> and 
    T :: \<open>'c::chilbert_space \<Rightarrow> 'd::chilbert_space\<close>
  assumes \<open>bounded_clinear S\<close> and  \<open>bounded_clinear T\<close>
  shows \<open>\<exists> H :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd. 
  bounded_clinear H \<and> (\<forall> x y. H (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>h(T y)) \<and> onorm H \<le> onorm S * onorm T\<close>
proof-
  have \<open>\<exists> HS :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h ('c::chilbert_space). 
  bounded_clinear HS \<and> (\<forall> x y. HS (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy) \<and> onorm HS \<le> onorm S\<close>
    by (simp add: hilbert_tensor_existence'_left' assms(1))
  then obtain HS::\<open>'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'c\<close> where \<open>bounded_clinear HS\<close> and 
    \<open>\<forall> x y. HS (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy\<close> and \<open>onorm HS \<le> onorm S\<close> by blast
  have \<open>\<exists> HT :: 'b \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd. 
  bounded_clinear HT \<and> (\<forall> x y. HT (x \<otimes>\<^sub>h y) = x\<otimes>\<^sub>h(T y)) \<and> onorm HT \<le> onorm T\<close>
    by (simp add: hilbert_tensor_existence'_right' assms(2))
  then obtain HT::\<open>'b \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd\<close> where \<open>bounded_clinear HT\<close> and 
    \<open>\<forall> x y. HT (x \<otimes>\<^sub>h y) = x\<otimes>\<^sub>h(T y)\<close> and \<open>onorm HT \<le> onorm T\<close> by blast
  define H where \<open>H = HT \<circ> HS\<close>
  have \<open>bounded_clinear H\<close>
    unfolding H_def
    using \<open>bounded_clinear HT\<close> \<open>bounded_clinear HS\<close>
      Complex_Vector_Spaces.comp_bounded_clinear[where A = "HT" and B = "HS"]
    by blast
  moreover have \<open>\<forall> x y. H (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>h(T y)\<close>
    using \<open>\<forall> x y. HS (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy\<close> \<open>\<forall> x y. HT (x \<otimes>\<^sub>h y) = x\<otimes>\<^sub>h(T y)\<close> H_def 
    by auto
  moreover have \<open>onorm H \<le> onorm S * onorm T\<close>
    using \<open>onorm HS \<le> onorm S\<close> \<open>onorm HT \<le> onorm T\<close>
    by (smt H_def \<open>bounded_clinear HS\<close> \<open>bounded_clinear HT\<close> bounded_clinear.bounded_linear mult_mono' onorm_compose onorm_pos_le ordered_field_class.sign_simps(5))
  ultimately show ?thesis by blast
qed


lemma hilbert_tensor_existence':
  fixes S :: \<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> and 
    T :: \<open>('c::chilbert_space, 'd::chilbert_space) bounded\<close>
  shows \<open>\<exists> H :: ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded.  (\<forall> x y. H *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and> 
          norm H \<le> norm S * norm T\<close>
proof-
  have \<open>bounded_clinear (times_bounded_vec S)\<close>
    using times_bounded_vec by blast
  moreover have \<open>bounded_clinear (times_bounded_vec T)\<close>
    using times_bounded_vec by blast
  ultimately have \<open>\<exists> h :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd. 
  bounded_clinear h \<and> (\<forall> x y. h (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and>
      onorm h \<le> onorm (times_bounded_vec S) * onorm (times_bounded_vec T)\<close>
    using hilbert_tensor_existence'' by blast
  then obtain h :: \<open>'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd\<close> where
    \<open>bounded_clinear h\<close> and \<open>\<forall> x y. h (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)\<close>
    and \<open>onorm h \<le> onorm (times_bounded_vec S) * onorm (times_bounded_vec T)\<close>
    by blast
  from \<open>bounded_clinear h\<close>
  have \<open>\<exists> H. times_bounded_vec H = h\<close>
    using times_bounded_vec_cases by auto
  then obtain H where \<open>times_bounded_vec H = h\<close>
    by blast
  have \<open>\<forall>x y. H *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y)\<close>
    using \<open>times_bounded_vec H = h\<close> \<open>\<forall> x y. h (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)\<close>
    by auto
  moreover have \<open>norm H \<le> norm S * norm T\<close>
    using \<open>times_bounded_vec H = h\<close> \<open>onorm h \<le> onorm (times_bounded_vec S) * onorm (times_bounded_vec T)\<close>
    by (simp add: norm_bounded.rep_eq)
  ultimately show ?thesis by blast
qed

lemma htensorOp_existence_leq:
  \<open>\<exists> H :: ('a::chilbert_space, 'b::chilbert_space) bounded \<Rightarrow>
  ('c::chilbert_space, 'd::chilbert_space) bounded \<Rightarrow>
  ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded. \<forall> S T.
   (\<forall> x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and> norm (H S T) \<le> norm S * norm T\<close>
  using hilbert_tensor_existence' by metis

lemma htensorOp_existence_eq:
  assumes \<open>(UNIV::'a set) \<noteq> 0\<close> and \<open>(UNIV::'c set) \<noteq> 0\<close>
  shows \<open>\<exists> H :: ('a::chilbert_space, 'b::chilbert_space) bounded \<Rightarrow>
  ('c::chilbert_space, 'd::chilbert_space) bounded \<Rightarrow>
  ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded. \<forall> S T.
   (\<forall> x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and> norm (H S T) = norm S * norm T\<close>
proof-
  have \<open>\<exists> H :: ('a::chilbert_space, 'b::chilbert_space) bounded \<Rightarrow>
  ('c::chilbert_space, 'd::chilbert_space) bounded \<Rightarrow>
  ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded. \<forall> S T.
   (\<forall> x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and> norm (H S T) \<le> norm S * norm T\<close>
    using htensorOp_existence_leq
    by blast
  then obtain H::\<open>('a::chilbert_space, 'b::chilbert_space) bounded \<Rightarrow>
  ('c::chilbert_space, 'd::chilbert_space) bounded \<Rightarrow>
  ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded\<close> where 
    \<open>\<And> S T x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)\<close> and
    \<open>\<And> S T. norm (H S T) \<le> norm S * norm T\<close>
    by blast
  have \<open>norm (H S T) \<ge> norm S * norm T\<close>
    for S T
  proof-
    have \<open>norm z < 1 \<Longrightarrow> norm ((H S T) *\<^sub>v z) \<le> norm  (H S T)\<close>
      for z
      using norm_of_bounded2[where z = "z" and L = "H S T"]
      by auto
    hence separable: \<open>norm (x \<otimes>\<^sub>h y) < 1 \<Longrightarrow> norm ((H S T) *\<^sub>v (x \<otimes>\<^sub>h y)) \<le> norm  (H S T)\<close>
      for x y
      by auto
    moreover have \<open>{norm ((H S T) *\<^sub>v (x \<otimes>\<^sub>h y))| x y. norm (x \<otimes>\<^sub>h y) < 1} \<noteq> {}\<close>
    proof-
      have \<open>(0::'a) \<otimes>\<^sub>h (0::'c) = (0::'a \<otimes>\<^sub>h 'c)\<close>
        by (simp add: additive_imples_zero htensor_distr_right)        
      hence \<open>norm ((0::'a) \<otimes>\<^sub>h (0::'c)) = 0\<close>
        by simp
      hence \<open>norm ((0::'a) \<otimes>\<^sub>h (0::'c)) < 1\<close>
        by simp
      thus ?thesis
        by blast 
    qed
    ultimately have \<open>Sup {norm ((H S T) *\<^sub>v (x \<otimes>\<^sub>h y))| x y. norm (x \<otimes>\<^sub>h y) < 1} \<le> norm  (H S T)\<close>
      using mem_Collect_eq cSup_least[where X = "{norm ((H S T) *\<^sub>v (x \<otimes>\<^sub>h y))| x y. norm (x \<otimes>\<^sub>h y) < 1}"
          and z = "norm  (H S T)"] by auto
    moreover have \<open>Sup {norm ((H S T) *\<^sub>v (x \<otimes>\<^sub>h y))| x y. norm (x \<otimes>\<^sub>h y) < 1} \<ge> norm S * norm T\<close>
    proof-
      have \<open>Sup {norm ((H S T) *\<^sub>v (x \<otimes>\<^sub>h y))| x y. norm (x \<otimes>\<^sub>h y) < 1} 
          = Sup {norm ((S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y))| x y. norm (x \<otimes>\<^sub>h y) < 1}\<close>
      proof-
        have \<open>(H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y)\<close>
          for x y
          by (simp add: \<open>\<And>y x T S. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y)\<close>)
        thus ?thesis
          by simp
      qed
      also have \<open>\<dots> 
          = Sup {norm (S *\<^sub>v x) * norm (T *\<^sub>v y)| x y. norm (x \<otimes>\<^sub>h y) < 1}\<close>
      proof-
        have \<open>norm ((S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y)) = norm (S *\<^sub>v x) * norm (T *\<^sub>v y)\<close>
          for x y
          using htensor_norm_mult by blast
        thus ?thesis by simp
      qed
      also have \<open>\<dots> 
          = Sup {norm (S *\<^sub>v x) * norm (T *\<^sub>v y)| x y. norm x * norm y < 1}\<close>
      proof-
        have \<open>norm (x \<otimes>\<^sub>h y) = norm x * norm y\<close>
          for x::'a and y::'c
          using htensor_norm_mult by blast
        thus ?thesis by simp
      qed
      also have \<open>\<dots> 
          \<ge> Sup {norm (S *\<^sub>v x) * norm (T *\<^sub>v y)| x y. norm x < 1 \<and> norm y < 1}\<close>
      proof-
        have \<open>norm x < 1 \<and> norm y < 1 \<Longrightarrow>  norm x * norm y < 1\<close>
          for x::'a and  y::'c
          using mult_less_cancel_right1 norm_eq_zero norm_le_zero_iff
          by (metis dual_order.strict_trans1 less_le_not_le not_le_imp_less)          
        hence \<open>{norm (S *\<^sub>v x) * norm (T *\<^sub>v y)| x y. norm x < 1 \<and> norm y < 1} \<subseteq> {norm (S *\<^sub>v x) * norm (T *\<^sub>v y)| x y. norm x * norm y < 1}\<close>
          by auto
        moreover have \<open>{norm (S *\<^sub>v x) * norm (T *\<^sub>v y)| x y. norm x < 1 \<and> norm y < 1} \<noteq> {}\<close>
        proof-
          have \<open>norm (0::'a) < 1 \<and> norm (0::'c) < 1\<close>
            by simp
          thus ?thesis 
            using Collect_empty_eq_bot bot_empty_eq empty_iff
            by smt
        qed
        moreover have \<open>bdd_above {norm (S *\<^sub>v x) * norm (T *\<^sub>v y)| x y. norm x * norm y < 1}\<close>
        proof-
          have \<open>norm (x \<otimes>\<^sub>h y) = norm x * norm y\<close>
            for x::'a and y::'c
            by (simp add: htensor_norm_mult)
          hence \<open>norm x * norm y < 1 \<Longrightarrow> norm (S *\<^sub>v x) * norm (T *\<^sub>v y) \<le> norm (H S T)\<close>
            for x and y
            using separable
            by (smt \<open>\<And>y x T S. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y)\<close> htensor_norm_mult) 
          thus ?thesis
            by fastforce 
        qed
        ultimately show ?thesis
          by (simp add: cSup_subset_mono) 
      qed
      also have \<open>\<dots> 
          \<ge> Sup {norm S * norm (T *\<^sub>v y)| y. norm y < 1}\<close>
      proof-
        have \<open>norm S = Sup {norm (S *\<^sub>v x)| x. norm x < 1}\<close>
          using \<open>(UNIV::'a set) \<noteq> 0\<close> norm_of_bounded3 by auto
        thus ?thesis sorry
      qed
      show ?thesis sorry
    qed
    ultimately show ?thesis by simp
  qed
  thus ?thesis
    using \<open>\<And> S T. norm (H S T) \<le> norm S * norm T\<close>
      \<open>\<And>y x T S. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y)\<close> dual_order.antisym 
    by blast
qed

section \<open>Tensor product ell2\<close>

unbundle bounded_notation

consts "tensorOp" :: "('a ell2,'b ell2) bounded \<Rightarrow> ('c ell2,'d ell2) bounded \<Rightarrow> (('a*'c) ell2,('b*'d) ell2) bounded"

type_synonym ('a, 'b) l2bounded = "('a ell2,'b ell2) bounded"

lift_definition "tensorVec" :: "'a ell2 \<Rightarrow> 'c ell2 \<Rightarrow> ('a*'c) ell2" is
  "\<lambda>\<psi> \<phi> (x,y). \<psi> x * \<phi> y"
  by (cheat tensorVec)

definition tensorSpace :: "'a ell2 linear_space \<Rightarrow> 'b ell2 linear_space \<Rightarrow> ('a*'b) ell2 linear_space" where
  "tensorSpace A B = Span {tensorVec \<psi> \<phi>| \<psi> \<phi>. \<psi> \<in> space_as_set A \<and> \<phi> \<in> space_as_set B}"

consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr "\<otimes>" 71)
adhoc_overloading tensor tensorOp tensorSpace tensorVec

lemma idOp_tensor_idOp[simp]: "idOp\<otimes>idOp = idOp"
  by (cheat TODO2)

definition "comm_op" :: "(('a*'b) ell2, ('b*'a) ell2) bounded" where
  "comm_op = classical_operator (\<lambda>(a,b). Some (b,a))"

lemma adj_comm_op[simp]: "adjoint comm_op = comm_op"
  by (cheat TODO2)

lemma
  comm_op_swap[simp]: "comm_op *\<^sub>o (A\<otimes>B) *\<^sub>o comm_op = B\<otimes>A"
  for A::"('a ell2,'b ell2) bounded" and B::"('c ell2,'d ell2) bounded"
  by (cheat TODO3)

lemma comm_op_times_comm_op[simp]: "comm_op  *\<^sub>o comm_op = idOp"
proof -
  have "comm_op  *\<^sub>o (idOp \<otimes> idOp)  *\<^sub>o comm_op = idOp \<otimes> idOp" by (simp del: idOp_tensor_idOp)
  then show ?thesis by simp
qed

lemma unitary_comm_op[simp]: "unitary comm_op"
  unfolding unitary_def by (cheat TODO)

definition "assoc_op" :: "(('a*('b*'c)) ell2, (('a*'b)*'c) ell2) bounded" where
  "assoc_op = classical_operator (\<lambda>(a,(b,c)). Some ((a,b),c))"

lemma unitary_assoc_op[simp]: "unitary assoc_op"
  by (cheat TODO5)

lemma tensor_scalar_mult1[simp]: "(a *\<^sub>C A) \<otimes> B = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  by (cheat TODO3)
lemma tensor_scalar_mult1_ell2[simp]: "(a *\<^sub>C A) \<otimes> B = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"_ ell2" and B::"_ ell2"
  by (cheat TODO3)
lemma tensor_scalar_mult2[simp]: "A \<otimes> (a *\<^sub>C B) = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  by (cheat TODO3)
lemma tensor_scalar_mult2_ell2[simp]: "A \<otimes> (a *\<^sub>C B) = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"_ ell2" and B::"_ ell2"
  by (cheat TODO3)
lemma tensor_plus: "(A+B) \<otimes> C = A \<otimes> C + B \<otimes> C" for A B C :: "(_,_)bounded"
  by (cheat tensor_plus)
lemma tensor_plus_ell2: "(A+B) \<otimes> C = A \<otimes> C + B \<otimes> C" for A B C :: "_ ell2"
  by (cheat tensor_plus)
lemma tensor_norm_ell2: "norm (\<psi> \<otimes> \<phi>) = norm \<psi> * norm \<phi>" for \<psi> \<phi> :: "_ ell2"
  by (cheat tensor_norm_ell2)

lemma tensor_times[simp]: "(U1 \<otimes> U2) *\<^sub>o (V1 \<otimes> V2) = (U1 *\<^sub>o V1) \<otimes> (U2 *\<^sub>o V2)"
  for V1 :: "('a1,'b1) l2bounded" and U1 :: "('b1,'c1) l2bounded"
    and V2 :: "('a2,'b2) l2bounded" and U2 :: "('b2,'c2) l2bounded"
  by (cheat TODO3)

lift_definition addState :: "'a ell2 \<Rightarrow> ('b ell2,('b*'a) ell2) bounded" is
  \<open>\<lambda>\<psi> \<phi>. tensorVec \<phi> \<psi>\<close>
  apply (rule_tac K="norm ell2" in bounded_clinear_intro)
  by (auto simp: tensor_norm_ell2 tensor_plus_ell2)


(* TODO: this is simply the adjoint of addState (1::unit ell2), and addState y is best defined as x \<rightarrow> x \<otimes> y (lifted).
   Do we even use remove_qvar_unit_op then? *)
consts remove_qvar_unit_op :: "(('a*unit) ell2,'a ell2) bounded"


(* definition addState :: "'a ell2 \<Rightarrow> ('b,'b*'a) l2bounded" where
  "addState \<psi> = idOp \<otimes> (ell2_to_bounded \<psi>) \<cdot> remove_qvar_unit_op*" *)

lemma addState_times_scalar[simp]: "addState (a *\<^sub>C \<psi>) = a *\<^sub>C addState \<psi>"
  for a::complex and \<psi>::"'a ell2"
  by (cheat TODO)

lemma tensor_adjoint[simp]: "adjoint (U\<otimes>V) = (adjoint U) \<otimes> (adjoint V)"
  for U :: "('a,'b) l2bounded" and V :: "('c,'d) l2bounded"
  by (cheat TODO3)

lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  using assms unfolding unitary_def by simp

lemma tensor_isometry[simp]: 
  assumes "isometry U" and "isometry V"
  shows "isometry (U\<otimes>V)"
  using assms unfolding isometry_def by simp

unbundle no_bounded_notation

end
