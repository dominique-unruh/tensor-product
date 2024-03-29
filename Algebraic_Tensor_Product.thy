(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Algebraic_Tensor_Product
  imports
    Complex_Bounded_Operators.Complex_Bounded_Linear_Function
    "HOL-Library.Adhoc_Overloading"
    Free_Vector_Spaces
begin

unbundle free_notation

definition atensor_kernel_generator::\<open>( (('a::complex_vector) \<times> ('b::complex_vector)) free ) set\<close> where
  \<open>atensor_kernel_generator = {inclusion_free (x, (y+z)) - inclusion_free (x, y) - inclusion_free (x, z) |  x y z. True}
\<union> { inclusion_free ((y+z), x) - inclusion_free (y, x) - inclusion_free (z, x) |  x y z. True}
\<union> { inclusion_free (x, (c *\<^sub>C y)) -  c *\<^sub>C inclusion_free (x, y) |  x y c. True} 
\<union> { inclusion_free ((c *\<^sub>C x), y) -  c *\<^sub>C inclusion_free (x, y) |  x y c. True}\<close>

definition atensor_kernel::\<open>( (('a::complex_vector) \<times> ('b::complex_vector)) free ) set\<close> where
  \<open>atensor_kernel = cspan atensor_kernel_generator\<close>

lemma subspace_atensor_kernel:
  \<open>complex_vector.subspace atensor_kernel\<close>
  unfolding atensor_kernel_def
  using complex_vector.subspace_span
  by blast

definition atensor_rel :: "(('a::complex_vector) \<times> ('b::complex_vector)) free \<Rightarrow> ('a \<times> 'b) free \<Rightarrow> bool"
  where "atensor_rel = (\<lambda>x y. x - y \<in> atensor_kernel)"


text\<open>Tensor product as defined in Helemskii, chapter 2, section 8\<close>
quotient_type (overloaded) ('a, 'b) atensor
  = "(('a::complex_vector) \<times> ('b::complex_vector)) free" /  atensor_rel
proof-
  have "\<forall>y. atensor_rel (x::('a \<times> 'b) free) y = (atensor_rel x = atensor_rel y)"
    for x :: "('a \<times> 'b) free"
  proof
    show "atensor_rel x y = (atensor_rel x = atensor_rel y)"
      for y :: "('a \<times> 'b) free"
    proof
      show "atensor_rel x = atensor_rel y"
        if "atensor_rel x y"
        using that unfolding atensor_rel_def
      proof-
        assume \<open>x - y \<in> atensor_kernel\<close>
        hence \<open>x - z \<in> atensor_kernel \<longleftrightarrow> y - z \<in> atensor_kernel\<close> 
          for z
        proof (cases \<open>x - z \<in> atensor_kernel\<close>)
          show "(x - z \<in> atensor_kernel) = (y - z \<in> atensor_kernel)"
            if "x - y \<in> atensor_kernel"
              and "x - z \<in> atensor_kernel"
          proof-
            have \<open>complex_vector.subspace atensor_kernel\<close>
              using subspace_atensor_kernel
              by blast
            hence \<open>(x - z) - (y - z) \<in> atensor_kernel\<close>
              using that 
              by auto 
            thus ?thesis
              by (metis (no_types, lifting) atensor_kernel_def complex_vector.span_add_eq diff_add_cancel)
          qed
          show "(x - z \<in> atensor_kernel) = (y - z \<in> atensor_kernel)"
            if "x - y \<in> atensor_kernel"
              and "x - z \<notin> atensor_kernel"
          proof-
            have \<open>y - z \<notin> atensor_kernel\<close>
            proof(rule classical)
              assume \<open>\<not>(y - z \<notin> atensor_kernel)\<close>
              hence  \<open>y - z \<in> atensor_kernel\<close>
                by blast
              moreover have \<open>x - z = (x - y) + (y - z)\<close>
                by simp
              moreover have \<open>complex_vector.subspace atensor_kernel\<close>
                using subspace_atensor_kernel
                by blast
              ultimately have \<open>x - z \<in> atensor_kernel\<close>
                by (smt complex_vector.subspace_add that(1))                
              thus ?thesis
                using that(2) by blast 
            qed
            thus ?thesis
              using that(2) by auto 
          qed
        qed
        thus \<open>(\<lambda>p. x - p \<in> atensor_kernel) = (\<lambda>q. y - q \<in> atensor_kernel)\<close>
          by simp          
      qed
      show "atensor_rel x y"
        if "atensor_rel x = atensor_rel y"
        using that unfolding atensor_rel_def 
      proof-
        assume \<open>(\<lambda>p. x - p \<in> atensor_kernel) = (\<lambda>q. y - q \<in> atensor_kernel)\<close>
        hence \<open>x - z \<in> atensor_kernel \<longleftrightarrow> y - z \<in> atensor_kernel\<close> 
          for z
          by meson
        hence \<open>x - y \<in> atensor_kernel \<longleftrightarrow> y - y \<in> atensor_kernel\<close> 
          by blast
        moreover have \<open>y - y \<in> atensor_kernel\<close>
        proof-
          have \<open>0 \<in> atensor_kernel\<close>
            unfolding atensor_kernel_def
            by (simp add: complex_vector.span_zero)
          moreover have \<open>y - y = 0\<close>
            by simp
          ultimately show ?thesis by simp
        qed
        ultimately show \<open>x - y \<in> atensor_kernel\<close>
          by blast
      qed
    qed
  qed
  thus ?thesis
    unfolding equivp_def by blast
qed


type_notation
  atensor  ("(_ \<otimes>\<^sub>a/ _)" [21, 20] 20)

lift_definition atensor_op:: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>  (infixl "\<otimes>\<^sub>a" 70)
  is \<open>\<lambda> x::'a. \<lambda> y::'b. inclusion_free (x, y)\<close>.


instantiation atensor :: (complex_vector,complex_vector) complex_vector
begin

lift_definition plus_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>
  is \<open>\<lambda> x y. x + y\<close>
  unfolding atensor_rel_def
proof-
  fix p1 p2 p3 p4 :: \<open>('a \<times> 'b) free\<close>
  assume \<open>p1 - p2 \<in> atensor_kernel\<close> and \<open>p3 - p4 \<in> atensor_kernel\<close>
  moreover have \<open>complex_vector.subspace atensor_kernel\<close>
    using subspace_atensor_kernel by blast
  ultimately have \<open>(p1 - p2) + (p3 - p4) \<in> atensor_kernel\<close>
    using complex_vector.subspace_add by blast
  moreover have \<open>(p1 - p2) + (p3 - p4) = (p1 + p3) - (p2 + p4)\<close>
    by simp
  ultimately show \<open>(p1 + p3) - (p2 + p4) \<in> atensor_kernel\<close>
    by simp
qed

lift_definition minus_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>
  is \<open>\<lambda> x y. x - y\<close>
  unfolding atensor_rel_def
proof-
  fix p1 p2 p3 p4 :: \<open>('a \<times> 'b) free\<close>
  assume \<open>p1 - p2 \<in> atensor_kernel\<close> and \<open>p3 - p4 \<in> atensor_kernel\<close>
  moreover have \<open>complex_vector.subspace atensor_kernel\<close>
    using subspace_atensor_kernel by blast
  ultimately have \<open>(p1 - p2) - (p3 - p4) \<in> atensor_kernel\<close>
    using complex_vector.subspace_diff by blast
  moreover have \<open>(p1 - p2) - (p3 - p4) = (p1 - p3) - (p2 - p4)\<close>
    by simp
  ultimately show \<open>(p1 - p3) - (p2 - p4) \<in> atensor_kernel\<close>
    by simp
qed

lift_definition zero_atensor :: \<open>'a \<otimes>\<^sub>a 'b\<close>
  is \<open>0\<close>.

lift_definition scaleR_atensor :: \<open>real \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>
  is \<open>\<lambda> c x. c *\<^sub>R x\<close>
  unfolding atensor_rel_def
proof-
  fix p1 p2::\<open>('a \<times> 'b) free\<close> and c::real
  assume \<open>p1 - p2 \<in> atensor_kernel\<close> 
  moreover have \<open>complex_vector.subspace atensor_kernel\<close>
    using subspace_atensor_kernel
    by blast
  ultimately have \<open>c *\<^sub>R (p1 - p2) \<in> atensor_kernel\<close>
    by (simp add: \<open>complex_vector.subspace atensor_kernel\<close> complex_vector.subspace_scale scaleR_scaleC)
  show \<open>c *\<^sub>R p1 - c *\<^sub>R p2 \<in> atensor_kernel\<close>
    by (metis \<open>c *\<^sub>R (p1 - p2) \<in> atensor_kernel\<close> ordered_field_class.sign_simps(27))
    
qed

lift_definition scaleC_atensor :: \<open>complex \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>
  is \<open>\<lambda> c x. c *\<^sub>C x\<close>
  unfolding atensor_rel_def
proof-
  fix p1 p2::\<open>('a \<times> 'b) free\<close> and c::complex
  assume \<open>p1 - p2 \<in> atensor_kernel\<close> 
  moreover have \<open>complex_vector.subspace atensor_kernel\<close>
    using subspace_atensor_kernel
    by blast
  ultimately have \<open>c *\<^sub>C (p1 - p2) \<in> atensor_kernel\<close>
    by (simp add: \<open>complex_vector.subspace atensor_kernel\<close> complex_vector.subspace_scale)
  show \<open>c *\<^sub>C p1 - c *\<^sub>C p2 \<in> atensor_kernel\<close>
    by (metis (no_types) \<open>c *\<^sub>C (p1 - p2) \<in> atensor_kernel\<close> complex_vector.scale_right_diff_distrib)
qed

lift_definition uminus_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>
  is \<open>\<lambda> x. -x\<close>
  unfolding atensor_rel_def
proof-
  fix p1 p2 :: \<open>('a \<times> 'b) free\<close>
  assume \<open>p1 - p2 \<in> atensor_kernel\<close>
  moreover have \<open>complex_vector.subspace atensor_kernel\<close>
    using subspace_atensor_kernel
    by blast
  ultimately have \<open>-(p1 - p2) \<in> atensor_kernel\<close>
    using complex_vector.subspace_neg by blast    
  thus \<open>- p1 - - p2 \<in> atensor_kernel\<close>
    by simp
qed

instance
proof
  show "((*\<^sub>R) r::'a \<otimes>\<^sub>a 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
    unfolding scaleC_atensor_def scaleR_atensor_def 
    apply auto
  proof-
    have \<open>((*\<^sub>R) r) = ((*\<^sub>C) (complex_of_real r))\<close>
      by (simp add: scaleR_scaleC)      
    show \<open>map_fun rep_atensor abs_atensor ((*\<^sub>R) r) =
    map_fun rep_atensor abs_atensor
     ((*\<^sub>C) (complex_of_real r))\<close>
      by (simp add: \<open>(*\<^sub>R) r = (*\<^sub>C) (complex_of_real r)\<close>)
  qed

  show "(a::'a \<otimes>\<^sub>a 'b) + b + c = a + (b + c)"
    for a :: "'a \<otimes>\<^sub>a 'b"
      and b :: "'a \<otimes>\<^sub>a 'b"
      and c :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    apply auto 
    using subspace_atensor_kernel 
    unfolding complex_vector.subspace_def
    by blast

  show "(a::'a \<otimes>\<^sub>a 'b) + b = b + a"
    for a :: "'a \<otimes>\<^sub>a 'b"
      and b :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    apply auto 
    using subspace_atensor_kernel 
    unfolding complex_vector.subspace_def
    by blast

  show "(0::'a \<otimes>\<^sub>a 'b) + a = a"
    for a :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    apply auto 
    using subspace_atensor_kernel 
    unfolding complex_vector.subspace_def
    by blast

  show "- (a::'a \<otimes>\<^sub>a 'b) + a = 0"
    for a :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    apply auto 
    using subspace_atensor_kernel 
    unfolding complex_vector.subspace_def
    by blast

  show "(a::'a \<otimes>\<^sub>a 'b) - b = a + - b"
    for a :: "'a \<otimes>\<^sub>a 'b"
      and b :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    apply auto 
    using subspace_atensor_kernel 
    unfolding complex_vector.subspace_def
    by blast

  show "a *\<^sub>C ((x::'a \<otimes>\<^sub>a 'b) + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    using subspace_atensor_kernel
    by (simp add: subspace_atensor_kernel complex_vector.subspace_0 scaleC_add_right) 

  show "(a + b) *\<^sub>C (x::'a \<otimes>\<^sub>a 'b) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    using subspace_atensor_kernel
    by (simp add: subspace_atensor_kernel complex_vector.subspace_0 scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C (x::'a \<otimes>\<^sub>a 'b) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    using subspace_atensor_kernel
    by (simp add: subspace_atensor_kernel complex_vector.subspace_0)

  show "1 *\<^sub>C (x::'a \<otimes>\<^sub>a 'b) = x"
    for x :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    using subspace_atensor_kernel
    by (simp add: subspace_atensor_kernel complex_vector.subspace_0)

qed
end


lemma atensor_distr_right:
  fixes x :: "'a::complex_vector" and y z :: "'b::complex_vector"
  shows  \<open>x \<otimes>\<^sub>a (y+z) =  x \<otimes>\<^sub>a y  +  x \<otimes>\<^sub>a z\<close>
proof (transfer, unfold atensor_rel_def)
  fix x::'a and y z::'b
  have \<open>inclusion_free (x, y + z) - (inclusion_free (x, y) + inclusion_free (x, z))
  \<in> {inclusion_free (x, y + z) - inclusion_free (x, y) - inclusion_free (x, z) |x y z. True}\<close>
    by (metis (mono_tags, lifting) diff_diff_add mem_Collect_eq)    
  hence \<open>inclusion_free (x, y + z) - (inclusion_free (x, y) + inclusion_free (x, z))
  \<in> atensor_kernel_generator\<close>
    unfolding atensor_kernel_generator_def by simp
  hence \<open>inclusion_free (x, y + z) - (inclusion_free (x, y) + inclusion_free (x, z))
       \<in> atensor_kernel\<close>
    unfolding atensor_kernel_def
    by (simp add: complex_vector.span_base)
  thus \<open>\<And>x y z. inclusion_free (x, y + z) - (inclusion_free (x, y) + inclusion_free (x, z))
       \<in> atensor_kernel\<close>
  proof - (* sledgehammer *)
    fix xb :: 'c and yb :: 'd and zb :: 'd
    have "\<And>f fa fb. (f::('c \<times> 'd) free) - (fa + fb) = f - (fb + fa)"
      by simp
    hence "\<exists>c d da. inclusion_free (xb, yb + zb) - (inclusion_free (xb, yb) + inclusion_free (xb, zb)) = inclusion_free (c, d + da) - (inclusion_free (c, da) + inclusion_free (c, d))"
      by meson
    thus "inclusion_free (xb, yb + zb) - (inclusion_free (xb, yb) + inclusion_free (xb, zb)) \<in> atensor_kernel"
      by (simp add: atensor_kernel_def atensor_kernel_generator_def complex_vector.span_base diff_add_eq_diff_diff_swap)
  qed 
qed

lemma atensor_distr_right_sum:
  fixes x :: "'a::complex_vector" and y :: "'c \<Rightarrow> 'b::complex_vector"
    and I :: \<open>'c set\<close>
  shows  \<open>x \<otimes>\<^sub>a (\<Sum> i \<in> I. y i) =  (\<Sum> i \<in> I. x \<otimes>\<^sub>a (y i))\<close>
  using atensor_distr_right
  by (metis Modules.additive_def additive.sum) 

lemma atensor_distr_left:
  fixes y z :: "'a::complex_vector" and x :: "'b::complex_vector"
  shows  \<open>(y+z) \<otimes>\<^sub>a x =  y \<otimes>\<^sub>a x  +  z \<otimes>\<^sub>a x\<close>
proof(transfer, unfold atensor_rel_def atensor_kernel_def)
  fix y z::'a and x::'b
  have \<open>inclusion_free (y + z, x) - (inclusion_free (y, x) + inclusion_free (z, x))
       \<in> {inclusion_free (y + z, x) - inclusion_free (y, x) - inclusion_free (z, x) |x y z. True}\<close>
    by (metis (mono_tags, lifting) diff_diff_add mem_Collect_eq)
  hence \<open>inclusion_free (y + z, x) - (inclusion_free (y, x) + inclusion_free (z, x))
       \<in> atensor_kernel_generator\<close>
    unfolding atensor_kernel_generator_def
    by simp
  thus \<open>inclusion_free (y + z, x) - (inclusion_free (y, x) + inclusion_free (z, x))
       \<in> cspan atensor_kernel_generator\<close>
    by (simp add: complex_vector.span_base atensor_kernel_generator_def)
qed

lemma atensor_distr_left_sum:
  fixes  x :: "'c \<Rightarrow> 'a::complex_vector" and y :: "'b::complex_vector"
    and I :: \<open>'c set\<close>
  shows  \<open>(\<Sum> i \<in> I. x i) \<otimes>\<^sub>a y = (\<Sum> i \<in> I. (x i) \<otimes>\<^sub>a y)\<close>
proof-
  define f::\<open>'a \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close> where \<open>f t = t \<otimes>\<^sub>a y\<close> for t
  have \<open>Modules.additive f\<close>
    unfolding f_def
    using atensor_distr_left
    by (simp add: atensor_distr_left Modules.additive_def)    
  show ?thesis 
    using additive.sum \<open>Modules.additive f\<close> \<open>f \<equiv> \<lambda>t. t \<otimes>\<^sub>a y\<close> by auto
qed

lemma atensor_mult_right:
  fixes x :: "'a::complex_vector" and y :: "'b::complex_vector" and c :: complex
  shows \<open>x \<otimes>\<^sub>a (c *\<^sub>C y) = c *\<^sub>C (x \<otimes>\<^sub>a y)\<close>
proof(transfer, unfold atensor_rel_def atensor_kernel_def)
  fix x::'a and y::'b and c::complex
  have \<open>inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y)
       \<in> {inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y) |x y c. True}\<close>
    by (metis (mono_tags, lifting) mem_Collect_eq)
  hence \<open>inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y)
       \<in> atensor_kernel_generator\<close>
    unfolding atensor_kernel_generator_def
    by simp
  thus \<open>inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y)
       \<in> cspan atensor_kernel_generator\<close>
    by (simp add: complex_vector.span_base atensor_kernel_generator_def)
qed


lemma atensor_distr_minus_left:
  fixes y z :: "'a::complex_vector" and x :: "'b::complex_vector"
  shows  \<open>(y-z) \<otimes>\<^sub>a x =  y \<otimes>\<^sub>a x  -  z \<otimes>\<^sub>a x\<close>
  by (metis add_right_cancel atensor_distr_left diff_add_cancel)

lemma atensor_distr_minus_right:
  fixes y z :: "'a::complex_vector" and x :: "'b::complex_vector"
  shows  \<open>x \<otimes>\<^sub>a (y-z) =  x \<otimes>\<^sub>a y  -  x \<otimes>\<^sub>a z\<close>
  by (simp add: additive.diff additive.intro atensor_distr_right)


lemma atensor_mult_left:
  fixes x :: "'a::complex_vector" and y :: "'b::complex_vector" and c :: complex
  shows \<open>(c *\<^sub>C x) \<otimes>\<^sub>a y  = c *\<^sub>C (x \<otimes>\<^sub>a y)\<close>
  apply transfer unfolding atensor_rel_def atensor_kernel_def atensor_kernel_generator_def
  apply auto
  by (metis (mono_tags, lifting) Un_iff complex_vector.span_base mem_Collect_eq)


lemma abs_atensor_inclusion_free:
  \<open>abs_atensor (inclusion_free u) = (case_prod (\<otimes>\<^sub>a)) u\<close>
proof-
  have \<open>complex_vector.subspace atensor_kernel\<close>
    by (simp add: subspace_atensor_kernel)
  hence \<open>atensor_rel (Abs_free (\<lambda>x. if x = u then 1 else 0))
          (inclusion_free (fst u, snd u))\<close>
    unfolding atensor_rel_def inclusion_free_def apply auto
    by (simp add: \<open>complex_vector.subspace atensor_kernel\<close> complex_vector.subspace_0) 
  thus ?thesis
    by (simp add: atensor_op.abs_eq prod.case_eq_if) 
qed

lemma abs_atensor_sum:
  \<open>abs_atensor (x + y) = abs_atensor x + abs_atensor y\<close>
  by (simp add: plus_atensor.abs_eq)

lemma abs_atensor_sum_general:
  assumes \<open>finite S\<close>
  shows \<open>(\<Sum> x\<in>S. abs_atensor (f x)) = abs_atensor (\<Sum> x\<in>S. f x)\<close>
  using abs_atensor_sum
  by (smt Finite_Cartesian_Product.sum_cong_aux Modules.additive_def additive.sum assms)

lemma free_explicit:
  fixes  X :: \<open>('a::complex_vector \<times> 'b::complex_vector) free\<close>
  shows \<open>abs_atensor X = (\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}.  (X \<down> z) *\<^sub>C ((case_prod (\<otimes>\<^sub>a)) z) )\<close>
proof-                                        
  have \<open>X = (\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}. (X \<down> z) *\<^sub>C (inclusion_free z))\<close>
    using free_explicit by auto
  hence  \<open>abs_atensor X = abs_atensor (\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}. (X \<down> z) *\<^sub>C (inclusion_free z))\<close>
    by simp
  also have \<open>\<dots> = (\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}. abs_atensor ((X \<down> z) *\<^sub>C (inclusion_free z)))\<close>
    by (metis (mono_tags, lifting) abs_atensor_sum_general sum.cong sum.infinite zero_atensor.abs_eq)
  also have \<open>\<dots> = (\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}.  (X \<down> z) *\<^sub>C (abs_atensor (inclusion_free z)))\<close>
    by (metis scaleC_atensor.abs_eq)
  also have \<open>\<dots> = (\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}.  ( X \<down> z) *\<^sub>C ( (fst z) \<otimes>\<^sub>a (snd z) ) )\<close>
    by (metis (mono_tags, lifting) case_prod_unfold abs_atensor_inclusion_free)
  finally have \<open> abs_atensor X = (\<Sum>z\<in>{u |u. X \<down> u \<noteq> 0}. (X \<down> z) *\<^sub>C (fst z \<otimes>\<^sub>a snd z))\<close>
    by blast
  thus ?thesis
    by (metis (no_types, lifting) case_prod_unfold sum.cong) 
qed

lemma atensor_onto_explicit:
  fixes  x :: \<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)\<close>
  shows \<open>\<exists> S f. finite S \<and> (\<forall> z\<in>S. f z \<noteq> 0) \<and> x = (\<Sum>z\<in>S. (f z) *\<^sub>C ( (case_prod (\<otimes>\<^sub>a)) z ) )\<close>
proof-
  have \<open>\<exists> X. x = abs_atensor X\<close>
    apply transfer
    using atensor.abs_eq_iff by blast
  then obtain X where \<open>x = abs_atensor X\<close> by blast
  moreover have \<open>abs_atensor X = (\<Sum>z\<in>{u | u.  X \<down> u \<noteq> 0}.  (X \<down> z) *\<^sub>C ( (fst z) \<otimes>\<^sub>a (snd z) ) )\<close>
    using free_explicit
    by (metis (mono_tags, lifting) case_prod_unfold sum.cong) 
  moreover have \<open>finite {u | u.  X \<down> u \<noteq> 0}\<close>
    using times_free_vec by blast
  ultimately show ?thesis
    using Algebraic_Tensor_Product.free_explicit by blast
qed

lemma atensor_product_cartesian_product:
  assumes \<open>finite t\<close> and \<open>finite t'\<close>
  shows \<open>(\<Sum>i\<in>t. r i *\<^sub>C i) \<otimes>\<^sub>a (\<Sum>j\<in>t'. r' j *\<^sub>C j)
 = (\<Sum>(a, b)\<in>t\<times>t'. (r a * r' b) *\<^sub>C (a \<otimes>\<^sub>a b))\<close>
proof-
  have \<open>(\<Sum>i\<in>t. r i *\<^sub>C i) \<otimes>\<^sub>a (\<Sum>j\<in>t'. r' j *\<^sub>C j) = (\<Sum>i\<in>t. (r i *\<^sub>C i) \<otimes>\<^sub>a (\<Sum>j\<in>t'. r' j *\<^sub>C j) )\<close>
    using atensor_distr_left_sum by force    
  also have \<open>\<dots> = (\<Sum>i\<in>t. (\<Sum>j\<in>t'. (r i *\<^sub>C i) \<otimes>\<^sub>a (r' j *\<^sub>C j)) )\<close>
    by (metis (mono_tags, lifting) Finite_Cartesian_Product.sum_cong_aux atensor_distr_right_sum)    
  also have \<open>\<dots> = (\<Sum>i\<in>t. (\<Sum>j\<in>t'. r i *\<^sub>C ( i \<otimes>\<^sub>a (r' j *\<^sub>C j) ) ) )\<close>
    by (meson atensor_mult_left sum.cong)
  also have \<open>\<dots> = (\<Sum>i\<in>t. (\<Sum>j\<in>t'. r i *\<^sub>C ( r' j *\<^sub>C (i \<otimes>\<^sub>a j) ) ) )\<close>
    by (metis (no_types, lifting) atensor_mult_right sum.cong)
  also have \<open>\<dots> = (\<Sum>i\<in>t. (\<Sum>j\<in>t'. (r i * r' j) *\<^sub>C (i \<otimes>\<^sub>a j) ) )\<close>
    by auto
  also have \<open>\<dots> = (\<Sum>z\<in>t\<times>t'. (r (fst z) * r' (snd z)) *\<^sub>C ((fst z) \<otimes>\<^sub>a (snd z)))\<close>
    using Groups_Big.comm_monoid_add_class.sum.cartesian_product [where A = "t" 
        and B = "t'" and g = "\<lambda> i j. (r i * r' j) *\<^sub>C (i \<otimes>\<^sub>a j)"]
    by (metis (no_types, lifting) case_prod_beta' sum.cong)
  finally have \<open>(\<Sum>i\<in>t. r i *\<^sub>C i) \<otimes>\<^sub>a (\<Sum>j\<in>t'. r' j *\<^sub>C j) =
  (\<Sum>z\<in>t \<times> t'. (r (fst z) * r' (snd z)) *\<^sub>C (fst z \<otimes>\<^sub>a snd z))\<close>
    by blast
  thus ?thesis
    by (metis (mono_tags, lifting) case_prod_beta' sum.cong) 
qed


lemma atensor_onto_explicit_normalized:
  fixes  x :: \<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)\<close>
  shows \<open>\<exists> V \<phi>. finite V \<and> x = (\<Sum>v\<in>V. (\<phi> v) \<otimes>\<^sub>a v)\<close>
proof-
  have \<open>\<exists> S f. finite S \<and> (\<forall> z\<in>S. f z \<noteq> 0) \<and> x = (\<Sum>z\<in>S. (f z) *\<^sub>C ( (case_prod (\<otimes>\<^sub>a)) z ))\<close>
    using atensor_onto_explicit by blast
  then obtain S f where \<open>finite S\<close> and \<open>\<forall> z\<in>S. f z \<noteq> 0\<close> and
    \<open>x = (\<Sum>z\<in>S. (f z) *\<^sub>C ( (case_prod (\<otimes>\<^sub>a)) z ))\<close>
    by blast
  define \<phi> where \<open>\<phi> v = (\<Sum>u\<in>{u|u. (u,v)\<in>S}. ((f (u,v)) *\<^sub>C u))\<close> for v
  define B where \<open>B = snd ` S\<close>
  have \<open>(\<Sum>z\<in>S. (f z) *\<^sub>C ( (case_prod (\<otimes>\<^sub>a)) z ))
      = (\<Sum>(u,v)\<in>S. (f (u,v)) *\<^sub>C ( u \<otimes>\<^sub>a v ))\<close>
    apply auto
    by (metis (no_types, lifting) case_prod_beta' prod.collapse)
  also have \<open>\<dots> = (\<Sum>(u,v)\<in>S. ((f (u,v)) *\<^sub>C u) \<otimes>\<^sub>a v)\<close>
    by (metis atensor_mult_left)
  also have \<open>\<dots> = (\<Sum>v\<in>snd ` S. (\<Sum>u\<in>{u|u. (u,v)\<in>S}. ((f (u,v)) *\<^sub>C u) \<otimes>\<^sub>a v))\<close>
    using  \<open>finite S\<close> big_sum_reordering_snd[where S = "S" and f = "\<lambda> (u,v). ((f (u,v)) *\<^sub>C u) \<otimes>\<^sub>a v"]
    by auto
  also have \<open>\<dots> = (\<Sum>v\<in>snd ` S. (\<Sum>u\<in>{u|u. (u,v)\<in>S}. ((f (u,v)) *\<^sub>C u)) \<otimes>\<^sub>a v)\<close>
    by (metis (mono_tags, lifting) atensor_distr_left_sum sum.cong)
  also have \<open>\<dots> = (\<Sum>v\<in>snd ` S. (\<phi> v) \<otimes>\<^sub>a v)\<close>
    unfolding \<phi>_def by blast
  also have \<open>\<dots> = (\<Sum>v\<in>B. (\<phi> v) \<otimes>\<^sub>a v)\<close>
    unfolding B_def by blast
  finally have \<open>(\<Sum>z\<in>S. f z *\<^sub>C (case_prod (\<otimes>\<^sub>a)) z) = (\<Sum>v\<in>B. (\<phi> v) \<otimes>\<^sub>a v)\<close>
    by blast
  thus ?thesis
    using B_def \<open>finite S\<close> \<open>x = (\<Sum>z\<in>S. f z *\<^sub>C (case_prod (\<otimes>\<^sub>a)) z)\<close> by blast 
qed


lemma atensor_onto:
  \<open>cspan ( range (case_prod (\<otimes>\<^sub>a)) )
 = ( UNIV::(('a::complex_vector \<otimes>\<^sub>a 'b::complex_vector) set) )\<close>
proof
  show "cspan (range (case_prod (\<otimes>\<^sub>a))) \<subseteq> UNIV"
    by simp    
  show "(UNIV::('a \<otimes>\<^sub>a 'b) set) \<subseteq> cspan (range (case_prod (\<otimes>\<^sub>a)))"
  proof
    show "x \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))"
      for x :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>\<exists> R g. finite R \<and> (\<forall> z\<in>R. g z \<noteq> 0) \<and> x = (\<Sum>z\<in>R.  (g z) *\<^sub>C (case_prod (\<otimes>\<^sub>a)) z)\<close>
        using atensor_onto_explicit by blast
      then obtain R g where \<open>finite R\<close> and \<open>x = (\<Sum>z\<in>R.  (g z) *\<^sub>C (case_prod (\<otimes>\<^sub>a)) z)\<close>
        by blast
      thus ?thesis
        by (metis (no_types, lifting) complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset image_subset_iff iso_tuple_UNIV_I)        
    qed
  qed
qed

lemma atensor_reduction_right':
  fixes  x :: \<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)\<close>
  assumes \<open>finite V\<close> and \<open>complex_vector.dependent V\<close> 
    and \<open>x = (\<Sum>v\<in>V. (\<phi> v) \<otimes>\<^sub>a v )\<close>
  shows \<open>\<exists>\<psi>. \<exists>s\<in>V. x = (\<Sum>u\<in>V-{s}. (\<psi> u) \<otimes>\<^sub>a u)\<close>
proof-
  have \<open>\<exists> f. \<exists> s\<in>V. s = (\<Sum>v\<in>V-{s}. f v *\<^sub>C v)\<close>
    using \<open>finite V\<close> \<open>complex_vector.dependent V\<close> (* complex_dependent_isolation *)
    (* by blast *) sorry
  then obtain s and f where \<open>s \<in> V\<close> \<open>s = (\<Sum>v\<in>V-{s}. f v *\<^sub>C v)\<close>
    by blast
  define \<psi> where \<open>\<psi> v = (f v *\<^sub>C (\<phi> s)) + (\<phi> v)\<close> for v
  from \<open>x = (\<Sum>v\<in>V. (\<phi> v) \<otimes>\<^sub>a v )\<close> \<open>s \<in> V\<close>
  have \<open>x = (\<phi> s) \<otimes>\<^sub>a s + (\<Sum>v\<in>V-{s}. (\<phi> v) \<otimes>\<^sub>a v)\<close>
    by (meson \<open>finite V\<close> sum.remove)
  also have \<open>\<dots> = (\<phi> s) \<otimes>\<^sub>a (\<Sum>v\<in>V-{s}. f v *\<^sub>C v) + (\<Sum>v\<in>V-{s}. (\<phi> v) \<otimes>\<^sub>a v)\<close>
    using \<open>s = (\<Sum>v\<in>V-{s}. f v *\<^sub>C v)\<close>
    by simp
  also have \<open>\<dots> = (\<Sum>v\<in>V-{s}. (\<phi> s) \<otimes>\<^sub>a (f v *\<^sub>C v)) + (\<Sum>v\<in>V-{s}. (\<phi> v) \<otimes>\<^sub>a v)\<close>
    using atensor_distr_right_sum by auto
  also have \<open>\<dots> = (\<Sum>v\<in>V-{s}. f v *\<^sub>C ((\<phi> s) \<otimes>\<^sub>a v)) + (\<Sum>v\<in>V-{s}. (\<phi> v) \<otimes>\<^sub>a v)\<close>
    by (meson atensor_mult_right)
  also have \<open>\<dots> = (\<Sum>v\<in>V-{s}. (f v *\<^sub>C (\<phi> s)) \<otimes>\<^sub>a v) + (\<Sum>v\<in>V-{s}. (\<phi> v) \<otimes>\<^sub>a v)\<close>
    by (metis atensor_mult_left)
  also have \<open>\<dots> = (\<Sum>v\<in>V-{s}. (f v *\<^sub>C (\<phi> s)) \<otimes>\<^sub>a v + (\<phi> v) \<otimes>\<^sub>a v)\<close>
  proof-
    have \<open>(\<Sum>v\<in>V - {s}. f v *\<^sub>C \<phi> s \<otimes>\<^sub>a v + \<phi> v \<otimes>\<^sub>a v) = 
        (\<Sum>v\<in>V - {s}. f v *\<^sub>C \<phi> s \<otimes>\<^sub>a v) + (\<Sum>v\<in>V - {s}. \<phi> v \<otimes>\<^sub>a v)\<close>
      using Groups_Big.comm_monoid_add_class.sum.distrib
      by simp
    thus ?thesis by simp
  qed
  also have \<open>\<dots> = (\<Sum>v\<in>V-{s}. ((f v *\<^sub>C (\<phi> s)) + (\<phi> v)) \<otimes>\<^sub>a v  )\<close>
    by (simp add: atensor_distr_left)
  also have \<open>\<dots> = (\<Sum>v\<in>V-{s}. (\<psi> v) \<otimes>\<^sub>a v  )\<close>
    unfolding \<psi>_def by blast
  finally have \<open>x = (\<Sum>v\<in>V - {s}. \<psi> v \<otimes>\<^sub>a v)\<close>
    by blast
  thus ?thesis
    using \<open>s \<in> V\<close>
    by blast
qed

lemma atensor_reduction_right:
  fixes  x :: \<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)\<close>
    and S :: \<open>('a \<times> 'b) set\<close>
  assumes \<open>finite S\<close> and \<open>complex_vector.dependent (snd ` S)\<close>
    and \<open>x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z)\<close>
  shows \<open>\<exists> R. card (snd ` R) < card (snd ` S) \<and>
              card (fst ` R) \<le> card (snd ` R) \<and>
              x = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z)\<close>
proof-
  define \<phi> where \<open>\<phi> v = (\<Sum> u\<in>{u|u.(u,v)\<in>S}. u)\<close> for v
  define V where \<open>V = snd ` S\<close>
  have \<open>finite V\<close>
    unfolding V_def \<open>finite S\<close>
    by (simp add: assms(1))
  moreover have \<open>complex_vector.dependent V\<close>
    unfolding V_def 
    using \<open>complex_vector.dependent (snd ` S)\<close>
    by blast
  moreover have \<open>x = (\<Sum>v\<in>V. (\<phi> v) \<otimes>\<^sub>a v )\<close>
  proof-
    have \<open>x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z )\<close>
      using \<open>x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z)\<close> by blast
    also have \<open>\<dots> = (\<Sum>v\<in>V. (\<Sum>u\<in>{u|u.(u,v)\<in>S}. (case_prod (\<otimes>\<^sub>a)) (u, v)) )\<close>
      unfolding V_def
      using case_prod_unfold assms(1) big_sum_reordering_snd
      by blast
    also have \<open>\<dots> = (\<Sum>v\<in>V. (\<Sum>u\<in>{u|u.(u,v)\<in>S}. u \<otimes>\<^sub>a v) )\<close>
      by (metis (no_types, lifting) abs_atensor_inclusion_free atensor_op.abs_eq sum.cong)
    also have \<open>\<dots> = (\<Sum>v\<in>V. (\<Sum>u\<in>{u|u.(u,v)\<in>S}. u) \<otimes>\<^sub>a v )\<close>
      by (metis (mono_tags, lifting) Finite_Cartesian_Product.sum_cong_aux atensor_distr_left_sum)
    also have \<open>\<dots> = (\<Sum>v\<in>V. (\<phi> v) \<otimes>\<^sub>a v )\<close>
      unfolding \<phi>_def
      by blast
    finally show ?thesis by blast
  qed
  ultimately have \<open>\<exists>\<psi>. \<exists>s\<in>V. x = (\<Sum>u\<in>V-{s}. (\<psi> u) \<otimes>\<^sub>a u)\<close>
    using atensor_reduction_right' by blast
  then obtain s \<psi> where \<open>s\<in>V\<close> and \<open>x = (\<Sum>u\<in>V-{s}. (\<psi> u) \<otimes>\<^sub>a u)\<close>
    by blast
  define R where \<open>R = (\<lambda> u. (\<psi> u, u)) ` (V-{s})\<close>
  have \<open>card (snd ` R) < card (snd ` S)\<close>
  proof-
    have \<open>(snd ` (\<lambda>u. (\<psi> u, u)) ` (snd ` S - {s})) \<subset> (snd ` S)\<close>
    proof
      show "snd ` (\<lambda>u. (\<psi> u, u)) ` (snd ` S - {s}) \<subseteq> snd ` S"
        apply auto
        by (simp add: rev_image_eqI)
      show "snd ` (\<lambda>u. (\<psi> u, u)) ` (snd ` S - {s}) \<noteq> snd ` S"
      proof-
        have \<open>s \<in> snd ` S\<close>
          using \<open>s \<in> V\<close>
          unfolding V_def by blast
        moreover have \<open>s \<notin> snd ` (\<lambda>u. (\<psi> u, u)) ` (snd ` S - {s})\<close>
        proof(rule classical)
          assume \<open>\<not>(s \<notin> snd ` (\<lambda>u. (\<psi> u, u)) ` (snd ` S - {s}))\<close>
          hence \<open>s \<in> snd ` (\<lambda>u. (\<psi> u, u)) ` (snd ` S - {s})\<close>
            by blast
          hence \<open>\<exists>z \<in>(snd ` S - {s}). s = snd ((\<lambda>u. (\<psi> u, u)) z)\<close>
            by blast
          then obtain z where \<open>z \<in>(snd ` S - {s})\<close>
            and \<open>s = snd ((\<lambda>u. (\<psi> u, u)) z)\<close>    
            by blast
          from \<open>\<exists>z \<in>(snd ` S - {s}). s = snd ((\<lambda>u. (\<psi> u, u)) z)\<close>
          have \<open>s = z\<close>
            by auto
          hence  \<open>s \<in>(snd ` S - {s})\<close>
            using \<open>z \<in>(snd ` S - {s})\<close>
            by blast
          thus ?thesis
            by blast 
        qed
        ultimately show ?thesis by blast
      qed
    qed
    hence \<open>card (snd ` (\<lambda>u. (\<psi> u, u)) ` (snd ` S - {s})) < card (snd ` S)\<close>
      using \<open>finite S\<close>
      by (simp add: psubset_card_mono) 
    thus ?thesis
      unfolding R_def V_def
      by auto
  qed
  moreover have \<open>x = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z)\<close>
  proof-
    have \<open>inj_on (\<lambda> u. (\<psi> u, u)) (V-{s})\<close>
      using inj_on_def by auto
    have \<open>x = (\<Sum>u\<in>V-{s}. (\<psi> u) \<otimes>\<^sub>a u)\<close>
      using \<open>x = (\<Sum>u\<in>V-{s}. (\<psi> u) \<otimes>\<^sub>a u)\<close>
      by blast
    also have \<open>\<dots> = (\<Sum>u\<in>V-{s}. (case_prod (\<otimes>\<^sub>a)) ((\<lambda> u. (\<psi> u, u)) u) )\<close>
      using case_prod_unfold 
      by auto
    also have \<open>\<dots> = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z )\<close>
      unfolding R_def
      using \<open>inj_on (\<lambda> u. (\<psi> u, u)) (V-{s})\<close>
      by (metis (no_types, lifting) sum.reindex_cong)
    finally show ?thesis
      by blast
  qed
  moreover have \<open>card (fst ` R) \<le> card (snd ` R)\<close>
  proof-
    have \<open>fst ` R = \<psi> ` (V-{s})\<close>
    proof-
      have \<open>fst \<circ> (\<lambda>u. (\<psi> u, u)) = \<psi>\<close>
        using comp_def by auto        
      thus ?thesis
        by (simp add: R_def image_comp) 
    qed
    moreover have \<open>snd ` R = V-{s}\<close>
    proof-
      have \<open>snd \<circ> (\<lambda>u. (\<psi> u, u)) = id\<close>
        using comp_def by auto        
      thus ?thesis
        by (simp add: R_def image_comp) 
    qed
    ultimately have \<open>fst ` R = \<psi> ` (snd ` R)\<close>
      by simp
    thus ?thesis
      by (simp add: \<open>finite V\<close> \<open>snd ` R = V - {s}\<close> card_image_le) 
  qed
  ultimately show ?thesis by blast
qed

lemma span_tensor_span:
  fixes A::\<open>'a::complex_vector set\<close> and  B::\<open>'b::complex_vector set\<close>
  assumes \<open>u \<in> cspan A\<close> and \<open>v \<in> cspan B\<close>
  shows \<open>u \<otimes>\<^sub>a v \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))\<close>
proof-
  have \<open>\<exists> t r. finite t \<and> t \<subseteq> A \<and> (\<Sum>a\<in>t. r a *\<^sub>C a) = u\<close>
  proof -
    have "\<forall>A. {a. \<exists>C f. (a::'a) = (\<Sum>a\<in>C. f a *\<^sub>C a) \<and> finite C \<and> C \<subseteq> A} = cspan A"
      by (simp add: complex_vector.span_explicit)
    hence "\<forall>A a. (\<exists>C f. (a::'a) = (\<Sum>a\<in>C. f a *\<^sub>C a) \<and> finite C \<and> C \<subseteq> A) \<or> a \<notin> cspan A"
      by blast
    thus ?thesis
      by (metis (no_types) assms(1))
  qed
  then obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> A\<close> and \<open>(\<Sum>a\<in>t. r a *\<^sub>C a) = u\<close>
    by blast
  have \<open>\<exists> t' r'. finite t' \<and> t' \<subseteq> B \<and> (\<Sum>a\<in>t'. r' a *\<^sub>C a) = v\<close>
    using  \<open>v \<in> cspan B\<close> complex_vector.span_explicit
  proof -
    have "\<exists>C f. v = (\<Sum>b\<in>C. f b *\<^sub>C b) \<and> finite C \<and> C \<subseteq> B"
      using assms(2) complex_vector.span_explicit by blast
    thus ?thesis
      by (metis (full_types, lifting))
  qed
  then obtain t' r' where \<open>finite t'\<close> and \<open>t' \<subseteq> B\<close> and \<open>(\<Sum>a\<in>t'. r' a *\<^sub>C a) = v\<close>
    by blast
  have \<open>u \<otimes>\<^sub>a v = (\<Sum>i\<in>t. r i *\<^sub>C i) \<otimes>\<^sub>a (\<Sum>j\<in>t'. r' j *\<^sub>C j)\<close>
    by (simp add: \<open>(\<Sum>a\<in>t'. r' a *\<^sub>C a) = v\<close> \<open>(\<Sum>a\<in>t. r a *\<^sub>C a) = u\<close>)
  also have \<open>\<dots> = (\<Sum>(a,b)\<in>t\<times>t'. (r a * r' b) *\<^sub>C (a \<otimes>\<^sub>a b))\<close>
    using atensor_product_cartesian_product \<open>finite t\<close> \<open>finite t'\<close> by blast
  finally have \<open>u \<otimes>\<^sub>a v = (\<Sum>(a,b)\<in>t\<times>t'. (r a * r' b) *\<^sub>C (a \<otimes>\<^sub>a b))\<close>
    by blast
  moreover have \<open>(a,b) \<in> t \<times> t' \<Longrightarrow> a \<otimes>\<^sub>a b  \<in> cspan ( (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B) )\<close>
    for a b
  proof-
    assume \<open>(a,b) \<in> t \<times> t'\<close>
    hence \<open>((case_prod (\<otimes>\<^sub>a)) (a,b)) \<in> (case_prod (\<otimes>\<^sub>a)) ` (t \<times> t')\<close>
      using case_prod_unfold
      by auto
    moreover have \<open>t \<times> t' \<subseteq> A \<times> B\<close>
      using \<open>t \<subseteq> A\<close> \<open>t' \<subseteq> B\<close>
      by auto
    ultimately have \<open>(case_prod (\<otimes>\<^sub>a)) (a,b) \<in> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
      by blast
    thus \<open>a \<otimes>\<^sub>a b \<in> cspan ( (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B) )\<close>
      by (simp add:  complex_vector.span_base) 
  qed
  ultimately show ?thesis
  proof - (* sledgehammer *)
    obtain aa :: "('a \<otimes>\<^sub>a 'b) set \<Rightarrow> ('a \<Rightarrow> 'a \<otimes>\<^sub>a 'b) \<Rightarrow> 'a set \<Rightarrow> 'a" where
      "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x2 \<and> x1 v3 \<notin> cspan x0) = (aa x0 x1 x2 \<in> x2 \<and> x1 (aa x0 x1 x2) \<notin> cspan x0)"
      by moura
    hence f1: "\<forall>A f Aa. aa Aa f A \<in> A \<and> f (aa Aa f A) \<notin> cspan Aa \<or> sum f A \<in> cspan Aa"
      by (metis (no_types) complex_vector.span_sum)
    have f2: "(\<Sum>a\<in>t. r a *\<^sub>C a \<otimes>\<^sub>a v) = u \<otimes>\<^sub>a v"
      by (metis (no_types) \<open>(\<Sum>a\<in>t. r a *\<^sub>C a) = u\<close> atensor_distr_left_sum)
    obtain bb :: "('a \<otimes>\<^sub>a 'b) set \<Rightarrow> ('b \<Rightarrow> 'a \<otimes>\<^sub>a 'b) \<Rightarrow> 'b set \<Rightarrow> 'b" where
      "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x2 \<and> x1 v3 \<notin> cspan x0) = (bb x0 x1 x2 \<in> x2 \<and> x1 (bb x0 x1 x2) \<notin> cspan x0)"
      by moura
    hence f3: "\<forall>B f A. bb A f B \<in> B \<and> f (bb A f B) \<notin> cspan A \<or> sum f B \<in> cspan A"
      by (meson complex_vector.span_sum)
    moreover
    { assume "bb ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>b. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) t' \<in> t'"
      moreover
      { assume "(aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t, bb ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>b. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) t') \<in> t \<times> t'"
        hence "r' (bb ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>b. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) t') *\<^sub>C (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a bb ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>b. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) t') \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))"
          using \<open>\<And>b a. (a, b) \<in> t \<times> t' \<Longrightarrow> a \<otimes>\<^sub>a b \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))\<close> complex_vector.span_scale by blast
        hence "aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' (bb ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>b. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) t') *\<^sub>C bb ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>b. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) t' \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))"
          by (simp add: atensor_mult_right)
        hence "r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' (bb ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>b. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) t') *\<^sub>C bb ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>b. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) t') \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))"
          using complex_vector.span_scale by blast
        hence "bb ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>b. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) t' \<notin> t' \<or> r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' (bb ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>b. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) t') *\<^sub>C bb ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>b. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) t' \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))"
          by (simp add: atensor_mult_left)
        hence "(\<Sum>b\<in>t'. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))"
          using f3 by meson }
      ultimately have "(\<Sum>b\<in>t'. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) \<or> (\<Sum>a\<in>t. r a *\<^sub>C a \<otimes>\<^sub>a v) \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))"
        using f1 by (meson SigmaI) }
    moreover
    { assume "(\<Sum>b\<in>t'. r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a r' b *\<^sub>C b) \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))"
      hence "aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<notin> t \<or> r (aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t) *\<^sub>C aa ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) (\<lambda>a. r a *\<^sub>C a \<otimes>\<^sub>a v) t \<otimes>\<^sub>a v \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))"
        by (metis (no_types) \<open>(\<Sum>a\<in>t'. r' a *\<^sub>C a) = v\<close> atensor_distr_right_sum)
      hence "(\<Sum>a\<in>t. r a *\<^sub>C a \<otimes>\<^sub>a v) \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))"
        using f1 by meson }
    ultimately show ?thesis
      using f2 by auto
  qed 
qed

lemma basis_atensor_complex_generator:
  fixes A::\<open>'a::complex_vector set\<close> and  B::\<open>'b::complex_vector set\<close>
  assumes \<open>cspan A = UNIV\<close> and  \<open>cspan B = UNIV\<close>
  shows \<open>cspan ( (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B) ) = UNIV\<close>
proof-
  have \<open>x \<in> cspan ( (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B) )\<close>
    for x
  proof-
    have \<open>x \<in> cspan (range (case_prod (\<otimes>\<^sub>a)) )\<close>
      by (simp add: atensor_onto)
    hence \<open>\<exists> t r. finite t \<and> t \<subseteq> (range (case_prod (\<otimes>\<^sub>a))) \<and>
         x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
    proof -
      have "\<exists>f. x = (\<Sum>a | f a \<noteq> 0. f a *\<^sub>C a) \<and> {a. f a \<noteq> 0} \<subseteq> range (case_prod (\<otimes>\<^sub>a)) \<and> finite {a. f a \<noteq> 0}"
        using \<open>x \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close> complex_vector.span_alt by blast
      thus ?thesis
        by (metis (no_types))
    qed
    then obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> (range (case_prod (\<otimes>\<^sub>a)) )\<close> and
      \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      by blast
    have \<open>t \<subseteq> cspan  ( (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B) )\<close>
    proof
      show "x \<in> cspan ( (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))"
        if "x \<in> t"
        for x :: "'a \<otimes>\<^sub>a 'b"
      proof-
        from \<open>t \<subseteq> (range (case_prod (\<otimes>\<^sub>a)) )\<close>
        have \<open>\<exists> u v. x = u \<otimes>\<^sub>a v\<close>
          using that case_prod_unfold
          by fastforce 
        then obtain u v where \<open>x = u \<otimes>\<^sub>a v\<close> by blast
        have \<open>u \<in> cspan A\<close>
          by (simp add: assms(1))
        moreover have \<open>v \<in> cspan B\<close>
          by (simp add: assms(2))
        ultimately have \<open>u \<otimes>\<^sub>a v \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))\<close>
          using span_tensor_span by blast
        thus ?thesis
          using \<open>x = u \<otimes>\<^sub>a v\<close>
          by simp
      qed
    qed
    thus ?thesis
      by (simp add: \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> complex_vector.span_scale complex_vector.span_sum subset_iff)
  qed
  thus ?thesis
    by blast
qed

lemma quot_atensor:
  fixes G ::\<open>('v::complex_vector \<times> 'w::complex_vector) free \<Rightarrow> 'z\<close>
  assumes \<open>\<And> x y. atensor_rel x y \<Longrightarrow> G x = G y\<close>
  shows \<open>\<exists>! H :: 'v \<otimes>\<^sub>a 'w \<Rightarrow> 'z. \<forall> S. \<forall> s \<in> Rep_atensor S. H S = G s\<close>
proof-
  define H where \<open>H S = G (SOME s. s \<in> Rep_atensor S)\<close>
    for S
  have \<open>\<forall>S. \<forall>s\<in>Rep_atensor S. H S = G s\<close>
  proof-
    have \<open>s\<in>Rep_atensor S \<Longrightarrow> H S = G s\<close>
      for s S
    proof-
      assume \<open>s\<in>Rep_atensor S\<close>
      hence \<open>atensor_rel s (SOME s. s \<in> Rep_atensor S)\<close>
        by (smt Rep_atensor atensor_equivp equivp_symp equivp_transp mem_Collect_eq some_eq_ex)
      hence \<open>G s = G (SOME s. s \<in> Rep_atensor S)\<close>
        using \<open>\<And> x y. atensor_rel x y \<Longrightarrow> G x = G y\<close>
        by auto
      thus \<open>H S = G s\<close> 
        using \<open>H S = G (SOME s. s \<in> Rep_atensor S)\<close>
        by simp
    qed
    thus ?thesis by blast
  qed
  moreover have \<open>K = H\<close>
    if "\<forall>S. \<forall>s\<in>Rep_atensor S. K S = G s"
    for K :: "'v \<otimes>\<^sub>a 'w \<Rightarrow> 'z"
  proof-
    have \<open>K S = H S\<close>
      for S
    proof-
      have \<open>K S = G (SOME s. s \<in> Rep_atensor S)\<close>
        using that Rep_atensor some_in_eq by force 
      thus ?thesis 
        using \<open>H S = G (SOME s. s \<in> Rep_atensor S)\<close>
        by auto
    qed
    thus ?thesis by blast
  qed
  ultimately show ?thesis by blast
qed

definition atensor_of_pair_map::
  \<open>(('a::complex_vector \<times> 'b::complex_vector) free \<Rightarrow> 'c)
 \<Rightarrow> ('a \<otimes>\<^sub>a 'b \<Rightarrow> 'c)\<close> where 
  \<open>atensor_of_pair_map G S = G (rep_atensor S)\<close>

lemma atensor_of_pair_map_atensor_rel:
  fixes G ::\<open>('a::complex_vector \<times> 'b::complex_vector) free \<Rightarrow> 'c\<close>
  assumes \<open>\<And> x y. atensor_rel x y \<Longrightarrow> G x = G y\<close>
  shows \<open>atensor_rel s (rep_atensor S) \<longrightarrow> atensor_of_pair_map G S = G s\<close>
  by (simp add: assms atensor_of_pair_map_def)

lemma atensor_of_pair_map_uniq:
  fixes G :: \<open>('a::complex_vector \<times> 'b::complex_vector) free \<Rightarrow> 'c\<close>
    and H :: \<open>('a \<otimes>\<^sub>a 'b) \<Rightarrow> 'c\<close>
  assumes \<open>\<And> x y. atensor_rel x y \<Longrightarrow> G x = G y\<close> and 
    \<open>\<forall>S s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
  shows \<open>H = atensor_of_pair_map G\<close>
proof-
  have \<open>H S = atensor_of_pair_map G S\<close>
    for S
    by (metis Quotient_atensor Quotient_rel_rep assms(2) atensor_of_pair_map_def)    
  thus ?thesis by blast
qed

lemma quot_atensor2:
  fixes G ::\<open>('a::complex_vector \<times> 'b::complex_vector) free \<Rightarrow> 'c\<close>
  assumes \<open>\<And> x y. atensor_rel x y \<Longrightarrow> G x = G y\<close>
  shows \<open>\<exists>! H :: 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'c. \<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
proof
  show "\<forall>S s. atensor_rel s (rep_atensor S) \<longrightarrow> atensor_of_pair_map G S = G s"
    by (simp add: assms atensor_of_pair_map_def)

  show "H = atensor_of_pair_map G"
    if "\<forall>S s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s"
    for H :: "'a \<otimes>\<^sub>a 'b \<Rightarrow> 'c"
    using that atensor_of_pair_map_uniq assms by blast 
qed


lemma atensor_universal_free_atensor_rel:
  fixes h :: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'c::complex_vector\<close>
  assumes \<open>cbilinear h\<close> \<open>atensor_rel x y\<close>
  shows \<open>universal_free (\<lambda>z. h (fst z) (snd z)) x =
         universal_free (\<lambda>z. h (fst z) (snd z)) y\<close>
proof-
  have \<open>x - y \<in> atensor_kernel\<close>
    unfolding atensor_rel_def
    by (meson assms(2) atensor_rel_def)      
  moreover have \<open>\<forall> z \<in> atensor_kernel. (universal_free (\<lambda>z. h (fst z) (snd z))) z = 0\<close>
  proof-
    have \<open>\<forall> z \<in> atensor_kernel_generator. (universal_free (\<lambda>z. h (fst z) (snd z))) z = 0\<close>
    proof-
      have \<open>w \<in> {inclusion_free (x, y + z) - inclusion_free (x, y) -
           inclusion_free (x, z) | x y z. True} \<Longrightarrow> (universal_free (\<lambda>z. h (fst z) (snd z))) w = 0\<close>
        for w
      proof-
        assume \<open>w \<in> {inclusion_free (x, y + z) - inclusion_free (x, y) -
           inclusion_free (x, z) | x y z. True}\<close>
        hence \<open>\<exists> x y z. w = inclusion_free (x, y + z) - inclusion_free (x, y) -
           inclusion_free (x, z)\<close>
          by blast
        then obtain x y z where \<open>w = inclusion_free (x, y + z) - inclusion_free (x, y) -
           inclusion_free (x, z)\<close>
          by blast
        hence \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = 
           (universal_free (\<lambda>z. h (fst z) (snd z))) (inclusion_free (x, y + z))
         - (universal_free (\<lambda>z. h (fst z) (snd z))) (inclusion_free (x, y)) -
           (universal_free (\<lambda>z. h (fst z) (snd z))) (inclusion_free (x, z))\<close>
        proof-
          have \<open>clinear (universal_free (\<lambda>z. h (fst z) (snd z)))\<close>
            by (simp add: universal_free_clinear)              
          thus ?thesis
            by (simp add: \<open>w = inclusion_free (x, y + z) - inclusion_free (x, y) - inclusion_free (x, z)\<close> complex_vector.linear_diff)
        qed
        hence \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = h x (y + z) - h x y - h x z\<close>
        proof-
          have  \<open>(\<lambda> z. h (fst z) (snd z)) = (universal_free (\<lambda>z. h (fst z) (snd z))) \<circ> inclusion_free\<close>
            by (simp add: inclusion_free_comp)              
          thus ?thesis
            using comp_apply fst_conv snd_conv
            by (metis (no_types, lifting) \<open>universal_free (\<lambda>z. h (fst z) (snd z)) w = universal_free (\<lambda>z. h (fst z) (snd z)) (inclusion_free (x, y + z)) - universal_free (\<lambda>z. h (fst z) (snd z)) (inclusion_free (x, y)) - universal_free (\<lambda>z. h (fst z) (snd z)) (inclusion_free (x, z))\<close>)

        qed
        hence \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = h x y + h x z - h x y - h x z\<close>
          using \<open>cbilinear h\<close> unfolding cbilinear_def
          by (simp add: complex_vector.linear_add)
        thus ?thesis
          by simp            
      qed
      moreover have \<open>w \<in> {inclusion_free (y + z, x) - inclusion_free (y, x) -
           inclusion_free (z, x) | x y z. True} \<Longrightarrow> (universal_free (\<lambda>z. h (fst z) (snd z))) w = 0\<close>
        for w
      proof-
        assume \<open>w \<in> {inclusion_free (y + z, x) - inclusion_free (y, x) -
           inclusion_free (z, x) | x y z. True}\<close>
        hence \<open>\<exists> x y z. w = inclusion_free (y + z, x) - inclusion_free (y, x) -
           inclusion_free (z, x)\<close>
          by blast
        then obtain x y z where \<open>w = inclusion_free (y + z, x) - inclusion_free (y, x) -
           inclusion_free (z, x)\<close>
          by blast
        hence \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = (universal_free (\<lambda>z. h (fst z) (snd z))) (inclusion_free (y + z, x))
       - (universal_free (\<lambda>z. h (fst z) (snd z))) (inclusion_free (y, x)) -
           (universal_free (\<lambda>z. h (fst z) (snd z))) (inclusion_free (z, x))\<close>
        proof-
          have \<open>clinear (universal_free (\<lambda>z. h (fst z) (snd z)))\<close>
            by (simp add: universal_free_clinear)              
          thus ?thesis
            by (simp add: \<open>w = inclusion_free (y + z, x) - inclusion_free (y, x) - inclusion_free (z, x)\<close> complex_vector.linear_diff)              
        qed
        hence f1: \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = h (y + z) x - h y x - h z x\<close>
        proof-
          have  \<open>(\<lambda> z. h (fst z) (snd z)) = (universal_free (\<lambda>z. h (fst z) (snd z))) \<circ> inclusion_free\<close>
            by (simp add: inclusion_free_comp)              
          thus ?thesis
            by (metis (no_types, lifting) \<open>universal_free (\<lambda>z. h (fst z) (snd z)) w = universal_free (\<lambda>z. h (fst z) (snd z)) (inclusion_free (y + z, x)) - universal_free (\<lambda>z. h (fst z) (snd z)) (inclusion_free (y, x)) - universal_free (\<lambda>z. h (fst z) (snd z)) (inclusion_free (z, x))\<close> comp_apply fst_conv snd_conv)               
        qed
        hence \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = h y x + h z x - h y x - h z x\<close>
          using \<open>cbilinear h\<close> unfolding cbilinear_def
        proof -
          assume "(\<forall>y. clinear (\<lambda>x. h x y)) \<and> (\<forall>x. clinear (h x))"
          thus ?thesis
            by (metis (no_types) f1 add_diff_cancel_left' complex_vector.linear_diff)
        qed
        thus \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = 0\<close> by simp
      qed
      moreover have \<open>w \<in> {inclusion_free (x, c *\<^sub>C y) -
           c *\<^sub>C inclusion_free (x, y) | x y c. True} \<Longrightarrow> (universal_free (\<lambda>z. h (fst z) (snd z))) w = 0\<close>
        for w
      proof-
        assume \<open>w \<in> {inclusion_free (x, c *\<^sub>C y) -
           c *\<^sub>C inclusion_free (x, y) | x y c. True}\<close>
        have \<open>\<exists> x y c. w = inclusion_free (x, c *\<^sub>C y) -
           c *\<^sub>C inclusion_free (x, y)\<close>
          using \<open>w \<in> {inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y) | x y c. True}\<close> by auto
        then obtain x y c where \<open>w = inclusion_free (x, c *\<^sub>C y) -
           c *\<^sub>C inclusion_free (x, y)\<close>         
          by blast
        hence \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w =
             (universal_free (\<lambda>z. h (fst z) (snd z))) (inclusion_free (x, c *\<^sub>C y)) -
           (universal_free (\<lambda>z. h (fst z) (snd z))) (c *\<^sub>C inclusion_free (x, y))\<close>
        proof-
          have \<open>clinear (universal_free (\<lambda>z. h (fst z) (snd z)))\<close>
            by (simp add: universal_free_clinear)              
          thus ?thesis
            by (simp add: \<open>w = inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y)\<close> complex_vector.linear_diff)              
        qed
        hence \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = (universal_free (\<lambda>z. h (fst z) (snd z))) (inclusion_free (x, c *\<^sub>C y)) -
           c *\<^sub>C (universal_free (\<lambda>z. h (fst z) (snd z))) (inclusion_free (x, y))\<close>
        proof-
          have \<open>clinear (universal_free (\<lambda>z. h (fst z) (snd z)))\<close>
            by (simp add: universal_free_clinear)              
          thus ?thesis
            by (simp add: complex_vector.linear_scale \<open>universal_free (\<lambda>z. h (fst z) (snd z)) w = universal_free (\<lambda>z. h (fst z) (snd z)) (inclusion_free (x, c *\<^sub>C y)) - universal_free (\<lambda>z. h (fst z) (snd z)) (c *\<^sub>C inclusion_free (x, y))\<close>) 
        qed
        hence \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = (h x (c *\<^sub>C y)) - c *\<^sub>C (h x y)\<close>
        proof-
          have \<open>(\<lambda>z. h (fst z) (snd z)) = (universal_free (\<lambda>z. h (fst z) (snd z))) \<circ> inclusion_free\<close>
            by (simp add: inclusion_free_comp)
          thus ?thesis
            using  comp_apply fst_eqD snd_eqD
            by (metis (no_types, lifting) \<open>universal_free (\<lambda>z. h (fst z) (snd z)) w = universal_free (\<lambda>z. h (fst z) (snd z)) (inclusion_free (x, c *\<^sub>C y)) - c *\<^sub>C universal_free (\<lambda>z. h (fst z) (snd z)) (inclusion_free (x, y))\<close>)
        qed
        moreover have \<open>(h x (c *\<^sub>C y)) = c *\<^sub>C (h x y)\<close>
          using \<open>cbilinear h\<close>
          unfolding cbilinear_def
          by (simp add: complex_vector.linear_scale) 
        ultimately have \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = c *\<^sub>C (h x y) - c *\<^sub>C (h x y)\<close>
          by simp
        thus \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = 0\<close>
          by simp
      qed
        (* TODO: 
   By writing
moreover have \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = 0\<close> if \<open>w \<in> {inclusion_free (c *\<^sub>C x, y) - c *\<^sub>C inclusion_free (x, y) | x y c. True}\<close>,
you do not have to repeat the "w \<in> {\<dots>}" part in the assume command inside the subproof.
(It is automatically assumed, refer to it via "that")

 *)
      moreover have \<open>w \<in> {inclusion_free (c *\<^sub>C x, y) - c *\<^sub>C inclusion_free (x, y) | x y c. True} 
        \<Longrightarrow> (universal_free (\<lambda>z. h (fst z) (snd z))) w = 0\<close>
        for w
      proof-
        assume \<open>w \<in> {inclusion_free (c *\<^sub>C x, y) - c *\<^sub>C inclusion_free (x, y) | x y c. True}\<close>
        hence \<open>\<exists> x y c. w = inclusion_free (c *\<^sub>C x, y) -
           c *\<^sub>C inclusion_free (x, y)\<close>
          by blast
        then obtain x y c where \<open>w = inclusion_free (c *\<^sub>C x, y) -
           c *\<^sub>C inclusion_free (x, y)\<close>
          by blast
        hence \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = 
           (universal_free (\<lambda>z. h (fst z) (snd z))) (inclusion_free (c *\<^sub>C x, y)) -
           (universal_free (\<lambda>z. h (fst z) (snd z))) (c *\<^sub>C inclusion_free (x, y))\<close>
        proof-
          have \<open>clinear (universal_free (\<lambda>z. h (fst z) (snd z)))\<close>
            by (simp add: universal_free_clinear)
          thus ?thesis
            by (simp add: \<open>w = inclusion_free (c *\<^sub>C x, y) - c *\<^sub>C inclusion_free (x, y)\<close> complex_vector.linear_diff)
        qed
        also have \<open>\<dots> = (universal_free (\<lambda>z. h (fst z) (snd z))) (inclusion_free (c *\<^sub>C x, y)) -
           c *\<^sub>C (universal_free (\<lambda>z. h (fst z) (snd z))) (inclusion_free (x, y))\<close>
        proof-
          have \<open>clinear (universal_free (\<lambda>z. h (fst z) (snd z)))\<close>
            by (simp add: universal_free_clinear)
          thus ?thesis
            by (simp add: complex_vector.linear_scale)
        qed
        also have \<open>\<dots> = h (c *\<^sub>C x) y - c *\<^sub>C (h x y)\<close>
        proof-
          have  \<open>(\<lambda>z. h (fst z) (snd z)) = (universal_free (\<lambda>z. h (fst z) (snd z))) \<circ> inclusion_free\<close>
            by (simp add: inclusion_free_comp)            
          thus ?thesis
            by (metis (no_types, lifting) comp_apply fst_conv snd_conv)
        qed
        also have \<open>\<dots> = c *\<^sub>C (h x y) - c *\<^sub>C (h x y)\<close>
          using \<open>cbilinear h\<close> unfolding cbilinear_def
          using complex_vector.linear_scale by auto 
        also have \<open>\<dots> = 0\<close>
          by simp
        finally show \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) w = 0\<close>
          by blast
      qed
      ultimately show ?thesis unfolding atensor_kernel_generator_def
        by blast
    qed
    moreover have \<open>clinear (universal_free (\<lambda>z. h (fst z) (snd z)))\<close>
      by (simp add: universal_free_clinear)        
    ultimately show ?thesis unfolding atensor_kernel_def
      using complex_vector.linear_eq_0_on_span by blast
  qed
  ultimately have \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) (x - y) = 0\<close>
    by blast
  moreover have \<open>clinear (universal_free (\<lambda>z. h (fst z) (snd z)))\<close>
    by (simp add: universal_free_clinear)        
  ultimately show \<open>(universal_free (\<lambda>z. h (fst z) (snd z))) x = (universal_free (\<lambda>z. h (fst z) (snd z))) y\<close>
    using complex_vector.linear_diff by fastforce
qed


definition universal_atensor::\<open>('a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'c::complex_vector)
 \<Rightarrow> (('a \<otimes>\<^sub>a 'b) \<Rightarrow> 'c)\<close> where
  \<open>universal_atensor h = atensor_of_pair_map (universal_free (\<lambda> z. h (fst z) (snd z)))\<close>

lemma atensor_universal_property_clinear:
  fixes h :: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'c::complex_vector\<close>
  assumes \<open>cbilinear h\<close>
  shows \<open>clinear (universal_atensor h)\<close>
proof(unfold clinear_def)
  define G::\<open>('a \<times> 'b) free \<Rightarrow> 'c\<close> where
    \<open>G = universal_free (\<lambda> z. h (fst z) (snd z))\<close>
  define H where \<open>H = universal_atensor h\<close>
  have \<open>\<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
    by (simp add: G_def H_def assms atensor_of_pair_map_def atensor_universal_free_atensor_rel universal_atensor_def)
  have \<open>clinear G\<close>
    unfolding G_def
    by (simp add: universal_free_clinear)

  have "universal_atensor h (b1 + b2) = universal_atensor h b1 + universal_atensor h b2"
    for b1 :: "'a \<otimes>\<^sub>a 'b"
      and b2 :: "'a \<otimes>\<^sub>a 'b"
  proof-
    have \<open>\<forall> \<beta>1. atensor_rel \<beta>1 (rep_atensor b1) \<longrightarrow> (H b1) = (G \<beta>1)\<close>
      by (simp add: G_def H_def assms atensor_of_pair_map_def atensor_universal_free_atensor_rel universal_atensor_def)
    moreover have \<open>\<forall> \<beta>2. atensor_rel \<beta>2 (rep_atensor b2) \<longrightarrow> (H b2) = (G \<beta>2)\<close>
      by (simp add: G_def H_def assms atensor_of_pair_map_def atensor_universal_free_atensor_rel universal_atensor_def)
    ultimately have  \<open>\<forall> \<beta>1 \<beta>2. atensor_rel \<beta>1 (rep_atensor b1) \<and> atensor_rel \<beta>2 (rep_atensor b2) 
            \<longrightarrow> (H b1) + (H b2) = (G \<beta>1) + (G \<beta>2)\<close>
      by auto
    hence  \<open>\<forall> \<beta>1 \<beta>2. atensor_rel \<beta>1 (rep_atensor b1) \<and> atensor_rel \<beta>2 (rep_atensor b2) 
            \<longrightarrow> (H b1) + (H b2) = G (\<beta>1 + \<beta>2)\<close>
      using \<open>clinear G\<close> unfolding clinear_def
      by (simp add: \<open>clinear G\<close> complex_vector.linear_add)
    moreover have \<open>\<forall> \<beta>. atensor_rel \<beta> (rep_atensor (b1 + b2)) \<longrightarrow> (H (b1 + b2)) = G \<beta>\<close>
      using \<open>\<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
      by auto
    moreover have \<open>atensor_rel \<beta>1 (rep_atensor b1) \<Longrightarrow> atensor_rel \<beta>2 (rep_atensor b2)
            \<Longrightarrow> atensor_rel (\<beta>1 + \<beta>2) (rep_atensor (b1 + b2))\<close>
      for \<beta>1 \<beta>2
      by (metis Quotient3_abs_rep Quotient3_atensor atensor.abs_eq_iff plus_atensor.abs_eq)          
    ultimately have \<open>H (b1 + b2) = H b1 + H b2\<close>
      by (metis Quotient3_atensor Quotient3_rep_reflp)
    thus ?thesis
      by (simp add: H_def) 
  qed
  moreover have "universal_atensor h (r *\<^sub>C b) = r *\<^sub>C universal_atensor h b"
    for r :: complex
      and b :: "'a \<otimes>\<^sub>a 'b"
  proof-
    have \<open>\<forall> \<beta>. atensor_rel \<beta> (rep_atensor b) \<longrightarrow> r *\<^sub>C (H b) = r *\<^sub>C (G \<beta>)\<close>
      using \<open>\<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
      by auto
    hence \<open>\<forall> \<beta>. atensor_rel \<beta> (rep_atensor b) \<longrightarrow> r *\<^sub>C (H b) = G (r *\<^sub>C \<beta>)\<close>
      using \<open>clinear G\<close> unfolding clinear_def
      by (simp add: \<open>clinear G\<close> complex_vector.linear_scale)
    moreover have \<open>atensor_rel \<beta> (rep_atensor b) \<Longrightarrow> atensor_rel \<gamma> (rep_atensor (r *\<^sub>C b))
           \<Longrightarrow> atensor_rel (r *\<^sub>C \<beta>)  \<gamma>\<close>                                
      for \<beta> \<gamma>
      by (metis Quotient3_abs_rep Quotient3_atensor atensor.abs_eq_iff scaleC_atensor.abs_eq)        
    moreover have \<open>\<forall> \<gamma>.  atensor_rel \<gamma> (rep_atensor (r *\<^sub>C b)) \<longrightarrow> H (r *\<^sub>C b) = G \<gamma>\<close>
      by (simp add: \<open>\<forall>S s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>)
    ultimately show ?thesis
      using \<open>\<And>\<gamma> \<beta>. \<lbrakk>atensor_rel \<beta> (rep_atensor b); atensor_rel \<gamma> (rep_atensor (r *\<^sub>C b))\<rbrakk> \<Longrightarrow> atensor_rel (r *\<^sub>C \<beta>) \<gamma>\<close> \<open>\<forall>\<beta>. atensor_rel \<beta> (rep_atensor b) \<longrightarrow> r *\<^sub>C H b = G (r *\<^sub>C \<beta>)\<close> \<open>\<forall>\<gamma>. atensor_rel \<gamma> (rep_atensor (r *\<^sub>C b)) \<longrightarrow> H (r *\<^sub>C b) = G \<gamma>\<close> atensor.abs_eq_iff
      by (metis H_def)           
  qed
  ultimately show \<open>Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) (universal_atensor h)\<close>
    using clinearI clinear_def by blast    
qed

lemma atensor_universal_property_separation:
  fixes h :: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'c::complex_vector\<close>
  assumes \<open>cbilinear h\<close>
  shows \<open>\<forall> x y. h x y = universal_atensor h (x \<otimes>\<^sub>a y)\<close>
proof-
  define H where \<open>H = universal_atensor h\<close>
  define G::\<open>('a \<times> 'b) free \<Rightarrow> 'c\<close> where
    \<open>G = universal_free (\<lambda> z. h (fst z) (snd z))\<close>
  have "h x y = H (x \<otimes>\<^sub>a y)"
    for x y
  proof-
    have \<open>\<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
      by (simp add: G_def H_def assms atensor_of_pair_map_def atensor_universal_free_atensor_rel universal_atensor_def)
    have \<open>(\<lambda> z. h (fst z) (snd z)) = G \<circ> inclusion_free\<close>
      by (simp add: G_def inclusion_free_comp)
    hence \<open>h x y = G (inclusion_free (x, y))\<close>
      by (metis comp_apply fst_conv snd_conv)
    moreover have \<open>atensor_rel (inclusion_free (x, y)) (rep_atensor (x \<otimes>\<^sub>a y))\<close>
      by (metis (no_types) Quotient3_abs_rep Quotient3_atensor atensor.abs_eq_iff atensor_op.abs_eq)        
    ultimately show ?thesis
      using \<open>\<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
      by auto        
  qed
  thus ?thesis
    by (simp add: H_def) 
qed

lemma atensor_universal_property_uniq:
  fixes K :: \<open>('v::complex_vector) \<otimes>\<^sub>a ('w::complex_vector) \<Rightarrow> ('z::complex_vector)\<close>
  assumes \<open>cbilinear h\<close> and \<open>clinear K\<close> and \<open>\<And> x y. h x y = K (x \<otimes>\<^sub>a y)\<close>
  shows \<open>K = universal_atensor h\<close>
proof-
  define H where \<open>H = universal_atensor h\<close>
  have \<open>\<forall>x y. h x y = K (x \<otimes>\<^sub>a y)\<close>
    by (simp add: assms(3))
  moreover have \<open>\<forall>x y. h x y = universal_atensor h (x \<otimes>\<^sub>a y)\<close>
  proof-
    have \<open>clinear H\<close>
      unfolding H_def
      using \<open>cbilinear h\<close>
      by (simp add: atensor_universal_property_clinear)
    moreover have \<open>\<forall>x y. h x y = H (x \<otimes>\<^sub>a y)\<close>
      unfolding H_def
      using \<open>cbilinear h\<close>
      by (simp add: atensor_universal_property_separation)
    ultimately show ?thesis
      using H_def by auto 
  qed
  ultimately have \<open>K (x \<otimes>\<^sub>a y) = H (x \<otimes>\<^sub>a y)\<close>
    for x y
    unfolding H_def
    by simp
  have \<open>clinear K\<close>
    by (simp add: assms(2))      
  have \<open>clinear H\<close>
    by (simp add: H_def assms(1) atensor_universal_property_clinear)
  have \<open>K z = H z\<close>
    for z
  proof-
    have \<open>cspan (range (case_prod (\<otimes>\<^sub>a))) = UNIV\<close>
      by (simp add: atensor_onto)
    hence \<open>\<exists> t r. finite t \<and> t \<subseteq> (range (case_prod (\<otimes>\<^sub>a))) \<and> z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
    proof -
      have "\<forall>a. \<exists>A f. a = (\<Sum>a\<in>A. f a *\<^sub>C a) \<and> finite A \<and> A \<subseteq> ((range (case_prod (\<otimes>\<^sub>a)))::('v \<otimes>\<^sub>a 'w) set)"
        using \<open>cspan (range (case_prod (\<otimes>\<^sub>a))) = UNIV\<close> complex_vector.span_explicit
        by blast
      thus ?thesis
        by meson
    qed 
    then obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> (range (case_prod (\<otimes>\<^sub>a)))\<close>
      and \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      by blast
    from \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
    have \<open>K z = (\<Sum>a\<in>t. r a *\<^sub>C (K a))\<close>
      using \<open>clinear K\<close> unfolding clinear_def
      by (smt assms(2) complex_vector.linear_scale complex_vector.linear_sum sum.cong)
        (* > 1 sˇ*)
    also have \<open>\<dots> = (\<Sum>a\<in>t. r a *\<^sub>C (H a))\<close>
    proof-
      have  \<open>a \<in> t \<Longrightarrow> K a = H a\<close>
        for a
        using \<open>\<And> x y. K (x \<otimes>\<^sub>a y) = H (x \<otimes>\<^sub>a y)\<close>
          \<open>t \<subseteq> ((range (case_prod (\<otimes>\<^sub>a)))::('v \<otimes>\<^sub>a 'w) set)\<close>
        using case_prod_unfold image_iff subsetD by auto
      thus ?thesis
        by auto 
    qed
    also have \<open>\<dots> = H (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      by (smt \<open>clinear H\<close> complex_vector.linear_scale complex_vector.linear_sum sum.cong)
    also have \<open>\<dots> = H z\<close>
      using \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> by auto
    finally show ?thesis by blast
  qed
  thus ?thesis
    unfolding H_def by blast
qed

text\<open>Universal property of the tensor product. See chapter XVI in lang2004algebra\<close>
lemma atensor_universal_property:
  fixes h :: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'c::complex_vector\<close>
  assumes \<open>cbilinear h\<close>
  shows \<open>\<exists>! H :: 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'c. clinear H \<and> (\<forall> x y. h x y = H (x \<otimes>\<^sub>a y))\<close>
proof
  show "clinear (universal_atensor h) \<and> (\<forall>x y. h x y = universal_atensor h (x \<otimes>\<^sub>a y))"
    using assms atensor_universal_property_clinear atensor_universal_property_separation 
    by auto    
  show "H = universal_atensor h"
    if "clinear H \<and> (\<forall>x y. h x y = H (x \<otimes>\<^sub>a y))"
    for H :: "'a \<otimes>\<^sub>a 'b \<Rightarrow> 'c"
    using that assms atensor_universal_property_uniq 
    by auto 
qed

lemma swap_atensor_existence_unique:
  \<open>\<exists>!H. clinear H \<and> (\<forall>x::'a::complex_vector. \<forall> y::'b::complex_vector.  H (x \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a x)\<close>
proof-
  define h::\<open>'a \<Rightarrow> 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a\<close> where
    \<open>h x y = ((case_prod (\<otimes>\<^sub>a)) \<circ> prod.swap) (x,y)\<close> for x y
  have \<open>cbilinear h\<close>
    unfolding cbilinear_def proof
    show "\<forall>y. clinear (\<lambda>x. h x y)"
      unfolding clinear_def Vector_Spaces.linear_def apply auto
        apply (simp add: complex_vector.vector_space_axioms)
       apply (simp add: complex_vector.vector_space_axioms)
      unfolding module_hom_def apply auto
        apply (simp add: complex_vector.module_axioms)
       apply (simp add: complex_vector.module_axioms)
      unfolding module_hom_axioms_def apply auto unfolding h_def
       apply auto
       apply (simp add: atensor_distr_right)
      by (simp add: atensor_mult_right)
    show "\<forall>x. clinear (h x)"
      unfolding clinear_def Vector_Spaces.linear_def apply auto
        apply (simp add: complex_vector.vector_space_axioms)
       apply (simp add: complex_vector.vector_space_axioms)
      unfolding module_hom_def apply auto
        apply (simp add: complex_vector.module_axioms)
       apply (simp add: complex_vector.module_axioms)
      unfolding module_hom_axioms_def apply auto unfolding h_def
       apply auto
       apply (simp add: atensor_distr_left)
      by (simp add: atensor_mult_left)
  qed
  hence \<open>\<exists>!H. clinear H \<and> (\<forall>x y. h x y = H (x \<otimes>\<^sub>a y))\<close>
    using atensor_universal_property by blast
  hence \<open>\<exists>!H. clinear H \<and> (\<forall>x::'a. \<forall> y::'b. ((case_prod (\<otimes>\<^sub>a)) \<circ> prod.swap) (x, y) = H (x \<otimes>\<^sub>a y))\<close>
    unfolding h_def by auto
  hence \<open>\<exists>!H. clinear H \<and> (\<forall>x::'a. \<forall> y::'b. (case_prod (\<otimes>\<^sub>a)) (y, x) = H (x \<otimes>\<^sub>a y))\<close>
    by auto
  hence \<open>\<exists>!H. clinear H \<and> (\<forall>x::'a. \<forall> y::'b. y \<otimes>\<^sub>a x = H (x \<otimes>\<^sub>a y))\<close>
    by simp
  thus ?thesis by auto
qed

lemma swap_atensor_existence:
  \<open>\<exists>H. clinear H \<and> (\<forall>x::'a::complex_vector. \<forall> y::'b::complex_vector. 
  H (x \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a x)\<close>
  using swap_atensor_existence_unique by auto

definition swap_atensor::\<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector) \<Rightarrow> 'b \<otimes>\<^sub>a 'a\<close>
  where \<open>swap_atensor = (SOME H. 
  clinear H \<and>
  (\<forall>x. \<forall> y. H (x \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a x) 
)\<close>

lemma swap_atensorI1:
  \<open>clinear swap_atensor\<close>
  unfolding swap_atensor_def
  using swap_atensor_existence someI_ex
  by (simp add: \<open>\<exists>x. clinear x \<and> (\<forall>xa y. x (xa \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a xa) \<Longrightarrow> clinear (SOME x. clinear x \<and> (\<forall>xa y. x (xa \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a xa)) \<and> (\<forall>x y. (SOME x. clinear x \<and> (\<forall>xa y. x (xa \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a xa)) (x \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a x)\<close> swap_atensor_existence)


lemma swap_atensorI2:
  \<open>swap_atensor (x \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a x\<close>
  unfolding swap_atensor_def
  using swap_atensor_existence someI_ex
  by (simp add: \<open>\<exists>x. clinear x \<and> (\<forall>xa y. x (xa \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a xa) \<Longrightarrow> clinear (SOME x. clinear x \<and> (\<forall>xa y. x (xa \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a xa)) \<and> (\<forall>x y. (SOME x. clinear x \<and> (\<forall>xa y. x (xa \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a xa)) (x \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a x)\<close> swap_atensor_existence)

lemma swap_atensor_commute:
  \<open>swap_atensor \<circ> (case_prod (\<otimes>\<^sub>a)) = (case_prod (\<otimes>\<^sub>a)) \<circ> prod.swap\<close>
  by (auto simp:  o_def swap_atensorI2[rule_format] )

(* TODO: very confusing theorem because of the different implications of card
   (it encodes both the fact there are no duplicates in the list S/R,
   and the relationship between the lengths of S/R).

   Can this be stated more clearly?
 *)

lemma atensor_reduction_left:
  fixes  x :: \<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)\<close>
    and S :: \<open>('a \<times> 'b) set\<close>
  assumes \<open>finite S\<close> and \<open>complex_vector.dependent (fst ` S)\<close>
    and \<open>x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z)\<close>
  shows \<open>\<exists> R. card (fst ` R) < card (fst ` S) \<and>
              card (snd ` R) \<le> card (fst ` R) \<and>
              x = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z)\<close>
proof-
  define S' where \<open>S' = prod.swap ` S\<close>
  define x' where \<open>x' = (\<Sum>z\<in>S'. (case_prod (\<otimes>\<^sub>a)) z)\<close>
  have \<open>finite S'\<close>
    using S'_def assms(1) by auto    
  moreover have \<open>complex_vector.dependent (snd ` S')\<close>
    by (metis S'_def assms(2) swap_set_snd)
  ultimately have \<open>\<exists> R'. card (snd ` R') < card (snd ` S') \<and>
              card (fst ` R') \<le> card (snd ` R') \<and>
              x' = (\<Sum>z\<in>R'. (case_prod (\<otimes>\<^sub>a)) z)\<close>
    using \<open>x' = (\<Sum>z\<in>S'. (case_prod (\<otimes>\<^sub>a)) z)\<close>
      atensor_reduction_right[where x = "x'" and S = "S'"] by blast
  then obtain R' where \<open>card (snd ` R') < card (snd ` S')\<close> and
    \<open>card (fst ` R') \<le> card (snd ` R')\<close> and
    \<open>x' = (\<Sum>z\<in>R'. (case_prod (\<otimes>\<^sub>a)) z)\<close>
    by blast
  define R where \<open>R = prod.swap ` R'\<close>
  have \<open>snd ` R = fst ` R'\<close>
    by (metis R_def swap_set_snd)    
  have \<open>fst ` R = snd ` R'\<close>
    by (metis R_def swap_set_fst)
  have \<open>card (fst ` R) < card (fst ` S)\<close>
    using \<open>card (snd ` R') < card (snd ` S')\<close>
    by (metis S'_def \<open>fst ` R = snd ` R'\<close> swap_set_snd)
  moreover have \<open>card (snd ` R) \<le> card (fst ` R)\<close>
    using \<open>card (fst ` R') \<le> card (snd ` R')\<close>
    by (simp add: \<open>fst ` R = snd ` R'\<close> \<open>snd ` R = fst ` R'\<close>)
  moreover have \<open>x = sum (case_prod (\<otimes>\<^sub>a)) R\<close>
  proof-
    have \<open>x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z)\<close>
      using \<open>x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z)\<close> by blast
    also have \<open>\<dots> = (\<Sum>z\<in>prod.swap ` (prod.swap ` S). (case_prod (\<otimes>\<^sub>a)) z)\<close>
    proof-
      have \<open>prod.swap \<circ> prod.swap = id\<close>
        by (simp)
      hence \<open>prod.swap ` (prod.swap ` S) = S\<close>
        by (simp add: image_comp)        
      thus ?thesis by simp
    qed
    also have \<open>\<dots> = (\<Sum>z\<in>prod.swap ` (S'). (case_prod (\<otimes>\<^sub>a)) z)\<close>
      unfolding S'_def
      by blast 
    also have \<open>\<dots> = (\<Sum>z\<in>S'. ((case_prod (\<otimes>\<^sub>a)) \<circ> prod.swap) z)\<close>
    proof-
      have \<open>inj prod.swap\<close>
        by simp
      hence \<open>inj_on prod.swap S'\<close>
        by (metis injD inj_on_def)        
      thus ?thesis
        by (simp add: sum.reindex) 
    qed
    also have \<open>\<dots> = (\<Sum>z\<in>S'. (swap_atensor \<circ> (case_prod (\<otimes>\<^sub>a))) z)\<close>
      by (simp add: swap_atensor_commute)
    also have \<open>\<dots> = (\<Sum>z\<in>S'. swap_atensor ((case_prod (\<otimes>\<^sub>a)) z))\<close>
      by auto
    also have \<open>\<dots> = swap_atensor (\<Sum>z\<in>S'. ((case_prod (\<otimes>\<^sub>a)) z))\<close>
    proof-
      have \<open>clinear swap_atensor\<close>
        by (simp add: swap_atensorI1)
      thus ?thesis
        by (smt Finite_Cartesian_Product.sum_cong_aux complex_vector.linear_sum) 
    qed
    also have \<open>\<dots> = swap_atensor (\<Sum>z\<in>R'. ((case_prod (\<otimes>\<^sub>a)) z))\<close>
      using \<open>x' = sum (case_prod (\<otimes>\<^sub>a)) R'\<close> x'_def by presburger
    also have \<open>\<dots> = (\<Sum>z\<in>R'. swap_atensor ((case_prod (\<otimes>\<^sub>a)) z))\<close>
    proof-
      have \<open>clinear swap_atensor\<close>
        by (simp add: swap_atensorI1)
      thus ?thesis
        by (smt Finite_Cartesian_Product.sum_cong_aux complex_vector.linear_sum) 
    qed
    also have \<open>\<dots> = (\<Sum>z\<in>R'. (swap_atensor \<circ> (case_prod (\<otimes>\<^sub>a))) z)\<close>
      by simp
    also have \<open>\<dots> = (\<Sum>z\<in>R'. ((case_prod (\<otimes>\<^sub>a)) \<circ> prod.swap) z)\<close>
      by (simp add: swap_atensor_commute)
    also have \<open>\<dots> = (\<Sum>z\<in>R'. (case_prod (\<otimes>\<^sub>a)) (prod.swap z))\<close>
      by auto
    also have \<open>\<dots> = (\<Sum>z\<in>prod.swap ` R'. (case_prod (\<otimes>\<^sub>a)) z)\<close>
    proof-
      have \<open>inj_on prod.swap R'\<close>
        by simp
      thus ?thesis
        by (simp add: sum.reindex) 
    qed
    also have \<open>\<dots> = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z)\<close>
      unfolding R_def
      by blast
    finally show ?thesis by blast
  qed
  ultimately show ?thesis by blast
qed

definition max_complexity_pair::\<open>('a \<times> 'b) set \<Rightarrow> nat\<close> where
  \<open>max_complexity_pair S = max (card (fst ` S)) (card (snd ` S))\<close>

lemma atensor_reduction:
  fixes  x :: \<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)\<close>
    and S :: \<open>('a \<times> 'b) set\<close>
  assumes \<open>finite S\<close> 
    and \<open>complex_vector.dependent (fst ` S)
       \<or> complex_vector.dependent (snd ` S)\<close>
    and \<open>x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z)\<close>
  shows \<open>\<exists> R. max_complexity_pair R < max_complexity_pair S \<and>
              x = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z)\<close>
proof (cases \<open>complex_vector.dependent (fst ` S)\<close>)
  show "\<exists>R. max_complexity_pair R < max_complexity_pair S \<and> x = sum (case_prod (\<otimes>\<^sub>a)) R"
    if "complex_vector.dependent (fst ` S)"
    using that
    by (smt assms(1) assms(3) atensor_reduction_left dual_order.strict_trans le_eq_less_or_eq max_complexity_pair_def max_def)
      (* > 1 s *)
  show "\<exists>R. max_complexity_pair R < max_complexity_pair S \<and> x = sum (case_prod (\<otimes>\<^sub>a)) R"
    if "cindependent (fst ` S)"
    using that
    by (smt assms(1) assms(2) assms(3) atensor_reduction_right dual_order.strict_trans2 le_eq_less_or_eq max_complexity_pair_def max_def not_less_iff_gr_or_eq)
      (* > 1 s *)
qed


lemma atensor_expansion_existence:
  \<open>\<exists> R. finite R \<and> x = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z)\<close>
proof-
  from atensor_onto_explicit_normalized
  have \<open>\<exists>V \<phi>. finite V \<and> x = (\<Sum>v\<in>V. \<phi> v \<otimes>\<^sub>a v)\<close>
    by blast
  then obtain V \<phi> where \<open>finite V\<close> and \<open>x = (\<Sum>v\<in>V. \<phi> v \<otimes>\<^sub>a v)\<close>
    by blast
  define R where \<open>R = (\<lambda> v. (\<phi> v,  v)) ` V\<close>
  have \<open>finite R\<close>
    unfolding R_def using \<open>finite V\<close>
    by simp
  from \<open>x = (\<Sum>v\<in>V. \<phi> v \<otimes>\<^sub>a v)\<close>
  have \<open>x = (\<Sum>v\<in>V. (case_prod (\<otimes>\<^sub>a)) (\<phi> v,  v))\<close> 
    by auto
  also have \<open>\<dots> = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z)\<close>
  proof-
    have \<open>inj_on (\<lambda> v. (\<phi> v,  v)) V\<close>
      by (meson inj_onI prod.inject)
    thus ?thesis
      by (metis (mono_tags, lifting) R_def sum.reindex_cong) 
  qed
  finally have  \<open>x = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z)\<close>
    by blast
  thus ?thesis 
    using \<open>finite R\<close> by blast
qed

lemma orank_existence:
  \<open>{card S | S. finite S \<and> x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z)} \<noteq> {}\<close>
  using atensor_expansion_existence by blast

text \<open>Outer-product rank\<close>
text\<open>It is equivalent to Definition 2.2 in cite{ @de2008tensor } via lemma orank_def'\<close>
definition orank::\<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector) \<Rightarrow> nat\<close>
  where \<open>orank x = Inf { max_complexity_pair S | S. finite S \<and>  x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z)}\<close>

lemma orank_zero:
  \<open>orank (0::('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)) = 0\<close>
proof-
  have \<open>finite ({}::(('a \<times> 'b) set))\<close>
    by simp    
  moreover have \<open>(0::(('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)))
           = (\<Sum>z\<in>({}::(('a \<times> 'b) set)). (case_prod (\<otimes>\<^sub>a)) z)\<close>
    by simp    
  ultimately have \<open>max_complexity_pair ({}::(('a \<times> 'b) set)) \<in> { max_complexity_pair S | S. finite S \<and> 
    (0::(('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector))) = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z)}\<close>
    by blast
  moreover have \<open>max_complexity_pair ({}::(('a \<times> 'b) set)) = 0\<close>
  proof-
    have \<open>card (fst ` ({}::(('a \<times> 'b) set))) = 0\<close>
      by simp
    moreover have \<open>card (snd ` ({}::(('a \<times> 'b) set))) = 0\<close>
      by simp
    ultimately show ?thesis unfolding max_complexity_pair_def by auto
  qed
  ultimately show ?thesis
    by (smt Collect_cong cInf_eq_minimum less_induct orank_def zero_le)
qed

lemma orank_zero_ineq:
  \<open>finite S \<Longrightarrow> x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z) \<Longrightarrow> max_complexity_pair S \<ge> orank x\<close>
proof-
  assume \<open>finite S\<close> and \<open>x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z)\<close>
  hence \<open>max_complexity_pair S \<in> {max_complexity_pair S | S. finite S \<and> x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z)}\<close>
    by blast
  thus \<open>max_complexity_pair S \<ge> orank x\<close>
    unfolding orank_def
     sorry
  (* by (metis (no_types, lifting) cInf_eq_minimum equals0D nonempty_set_star_has_least_lemma) *)
qed

lemma atensor_expansion_orank_implies_independent:
  fixes  x :: \<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)\<close>
  assumes \<open>x \<noteq> 0\<close> and \<open>finite R\<close> and \<open>x = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z)\<close> and
    \<open>orank x = max_complexity_pair R\<close>
  shows \<open>complex_vector.independent (fst ` R) \<and>
         complex_vector.independent (snd ` R)\<close>
proof(rule classical)
  assume \<open>\<not>(complex_vector.independent (fst ` R) \<and>
         complex_vector.independent (snd ` R))\<close>
  hence \<open>complex_vector.dependent (fst ` R) \<or> 
         complex_vector.dependent (snd ` R)\<close>
    by (metis cdependent_raw_def)
  hence \<open>\<exists> T. max_complexity_pair T < max_complexity_pair R \<and> x = (\<Sum>z\<in>T. (case_prod (\<otimes>\<^sub>a)) z)\<close>
    using \<open>finite R\<close>  \<open>x = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z)\<close> 
      atensor_reduction[where S = "R" and x = "x"] by blast    
  then obtain T::\<open>('a \<times> 'b) set\<close> where \<open>x = (\<Sum>z\<in>T. (case_prod (\<otimes>\<^sub>a)) z)\<close> 
    and \<open>max_complexity_pair T < max_complexity_pair R\<close>
    by blast
  have  \<open>finite T\<close>
    using \<open>x = sum (case_prod (\<otimes>\<^sub>a)) T\<close> assms sum.infinite by blast
  from \<open>finite T\<close> \<open>x = (\<Sum>z\<in>T. (case_prod (\<otimes>\<^sub>a)) z)\<close>
  have \<open>max_complexity_pair T \<in> {max_complexity_pair S | S. finite S \<and> x = (\<Sum>z\<in>S. (case_prod (\<otimes>\<^sub>a)) z)}\<close>
    by auto
  hence \<open>max_complexity_pair T \<ge> orank x\<close>
    by (simp add: \<open>finite T\<close> \<open>x = sum (case_prod (\<otimes>\<^sub>a)) T\<close> orank_zero_ineq)
  thus ?thesis using \<open>max_complexity_pair T < max_complexity_pair R\<close> 
      \<open>orank x = max_complexity_pair R\<close> by simp
qed

lemma atensor_expansion_orank_existence:
  \<open>\<exists> R. finite R \<and> x = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z) \<and> orank x = max_complexity_pair R\<close>
proof -
  have "\<exists>n P. n = max_complexity_pair P \<and> finite P \<and> x = sum (case_prod (\<otimes>\<^sub>a)) P"
    by (simp add: atensor_expansion_existence)
  hence "{max_complexity_pair P |P. finite P \<and> x = sum (case_prod (\<otimes>\<^sub>a)) P} \<noteq> {}"
    by blast
  hence "Inf {max_complexity_pair P |P. finite P \<and> x = sum (case_prod (\<otimes>\<^sub>a)) P} \<in> {max_complexity_pair P |P. finite P \<and> x = sum (case_prod (\<otimes>\<^sub>a)) P}"
    using Inf_nat_def1 by presburger
  thus ?thesis
    unfolding orank_def
    by blast
qed

lemma atensor_expansion_independent_orank:
  fixes  x :: \<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)\<close>
  assumes \<open>x \<noteq> 0\<close>
  shows \<open>\<exists> R. finite R \<and> orank x = max_complexity_pair R \<and> 
              complex_vector.independent (fst ` R) \<and>
              complex_vector.independent (snd ` R) \<and>
              x = (\<Sum>z\<in>R. (case_prod (\<otimes>\<^sub>a)) z)\<close>
  using atensor_expansion_orank_existence atensor_expansion_orank_implies_independent
    assms by fastforce

lemma tensor_Kronecker_delta':
  fixes u::\<open>'a::complex_vector\<close> and v::\<open>'b::complex_vector\<close>
  assumes \<open>complex_vector.independent A\<close> and \<open>complex_vector.independent B\<close>
    and \<open>u \<in> A\<close> and \<open>v \<in> B\<close>
  shows \<open>\<exists> H::'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. clinear H \<and> H (u \<otimes>\<^sub>a v) = 1 \<and>
    (\<forall>x\<in>A. \<forall>y\<in>B. (x, y) \<noteq> (u, v) \<longrightarrow> H (x \<otimes>\<^sub>a y) = 0)\<close>
proof-
  have \<open>\<exists> h::_\<Rightarrow>_\<Rightarrow>complex. cbilinear h \<and> (h u v = 1) \<and>
    (\<forall>x\<in>A. \<forall>y\<in>B. (x,y) \<noteq> (u,v) \<longrightarrow> h x y = 0)\<close>
    (* using assms(1) assms(2) assms(3) assms(4) bilinear_Kronecker_delta by blast *) sorry
  then obtain h::\<open>_\<Rightarrow>_\<Rightarrow>complex\<close> where \<open>cbilinear h\<close> and \<open>h u v = 1\<close> and
    \<open>\<forall>x\<in>A. \<forall>y\<in>B. (x,y) \<noteq> (u,v) \<longrightarrow> h x y = 0\<close>
    by blast
  hence \<open>\<exists>!H. clinear H \<and> (\<forall>x y. h x y = H (x \<otimes>\<^sub>a y))\<close>
    using  atensor_universal_property[where h = "h"]
    by blast
  then obtain H where \<open>clinear H\<close> and \<open>\<forall>x y. h x y = H (x \<otimes>\<^sub>a y)\<close>
    by blast
  have \<open>H (u \<otimes>\<^sub>a v) = 1\<close>
    using \<open>\<forall>x y. h x y = H (x \<otimes>\<^sub>a y)\<close> \<open>h u v = 1\<close> by auto
  moreover have \<open>x\<in>A \<Longrightarrow> y\<in>B \<Longrightarrow> (x, y) \<noteq> (u, v) \<Longrightarrow> H (x \<otimes>\<^sub>a y) = 0\<close>
    for x y
  proof-
    assume \<open>x\<in>A\<close> and \<open>y\<in>B\<close> and \<open>(x, y) \<noteq> (u, v)\<close>
    from  \<open>(x, y) \<noteq> (u, v)\<close>
    have \<open>h x y = 0\<close>
      by (simp add: \<open>\<forall>x\<in>A. \<forall>y\<in>B. (x, y) \<noteq> (u, v) \<longrightarrow> h x y = 0\<close> \<open>x \<in> A\<close> \<open>y \<in> B\<close>)
    moreover have \<open>h x y = H (x \<otimes>\<^sub>a y)\<close>
      by (simp add: \<open>\<forall>x y. h x y = H (x \<otimes>\<^sub>a y)\<close>)
    ultimately show \<open>H (x \<otimes>\<^sub>a y) = 0\<close> by simp
  qed
  ultimately show ?thesis
    using \<open>clinear H\<close> by blast 
qed

lemma tensor_Kronecker_delta:
  fixes u::\<open>'a::complex_vector\<close> and v::\<open>'b::complex_vector\<close>
  assumes \<open>complex_vector.independent A\<close> and \<open>complex_vector.independent B\<close>
    and \<open>u \<in> A\<close> and \<open>v \<in> B\<close>
  shows \<open>\<exists> H::'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. clinear H \<and> H (u \<otimes>\<^sub>a v) = 1 \<and>
    (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes>\<^sub>a y \<noteq> u \<otimes>\<^sub>a v \<longrightarrow> H (x \<otimes>\<^sub>a y) = 0)\<close>
proof-
  have \<open>\<exists> h::_\<Rightarrow>_\<Rightarrow>complex. cbilinear h \<and> (h u v = 1) \<and>
    (\<forall>x\<in>A. \<forall>y\<in>B. (x,y) \<noteq> (u,v) \<longrightarrow> h x y = 0)\<close>
    (* using assms(1) assms(2) assms(3) assms(4) bilinear_Kronecker_delta by blast *) sorry
  then obtain h::\<open>_\<Rightarrow>_\<Rightarrow>complex\<close> where \<open>cbilinear h\<close> and \<open>h u v = 1\<close> and
    \<open>\<forall>x\<in>A. \<forall>y\<in>B. (x,y) \<noteq> (u,v) \<longrightarrow> h x y = 0\<close>
    by blast
  hence \<open>\<exists>!H. clinear H \<and> (\<forall>x y. h x y = H (x \<otimes>\<^sub>a y))\<close>
    using  atensor_universal_property[where h = "h"]
    by blast
  then obtain H where \<open>clinear H\<close> and \<open>\<forall>x y. h x y = H (x \<otimes>\<^sub>a y)\<close>
    by blast
  have \<open>H (u \<otimes>\<^sub>a v) = 1\<close>
    using \<open>\<forall>x y. h x y = H (x \<otimes>\<^sub>a y)\<close> \<open>h u v = 1\<close> by auto
  moreover have \<open>x\<in>A \<Longrightarrow> y\<in>B \<Longrightarrow> x \<otimes>\<^sub>a y \<noteq> u \<otimes>\<^sub>a v \<Longrightarrow> H (x \<otimes>\<^sub>a y) = 0\<close>
    for x y
  proof-
    assume \<open>x\<in>A\<close> and \<open>y\<in>B\<close> and \<open>x \<otimes>\<^sub>a y \<noteq> u \<otimes>\<^sub>a v\<close>
    from  \<open>x \<otimes>\<^sub>a y \<noteq> u \<otimes>\<^sub>a v\<close>
    have \<open>(x,y) \<noteq> (u,v)\<close>
      by blast
    hence \<open>h x y = 0\<close>
      by (simp add: \<open>\<forall>x\<in>A. \<forall>y\<in>B. (x, y) \<noteq> (u, v) \<longrightarrow> h x y = 0\<close> \<open>x \<in> A\<close> \<open>y \<in> B\<close>)
    moreover have \<open>h x y = H (x \<otimes>\<^sub>a y)\<close>
      by (simp add: \<open>\<forall>x y. h x y = H (x \<otimes>\<^sub>a y)\<close>)
    ultimately show \<open>H (x \<otimes>\<^sub>a y) = 0\<close> by simp
  qed
  ultimately show ?thesis
    using \<open>clinear H\<close> by blast 
qed

lemma atensor_cindependent:
  fixes A::\<open>'a::complex_vector set\<close> and B::\<open>'b::complex_vector set\<close>
  assumes \<open>complex_vector.independent A\<close> and \<open>complex_vector.independent B\<close>
  shows \<open>complex_vector.independent {a\<otimes>\<^sub>ab| a b. a\<in>A \<and> b\<in>B}\<close>
proof-
  have \<open>S \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B) \<Longrightarrow> finite S \<Longrightarrow>
   (\<Sum>s\<in>S. (f s) *\<^sub>C s) = 0 \<Longrightarrow> s\<in>S \<Longrightarrow> f s = 0\<close>
    for S s f
  proof-
    assume \<open>S \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close> and \<open>finite S\<close> and
      \<open>(\<Sum>s\<in>S. (f s) *\<^sub>C s) = 0\<close> and \<open>s\<in>S\<close>
    from \<open>S \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close> \<open>s\<in>S\<close>
    have \<open>s \<in> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
      by blast
    hence \<open>\<exists> u\<in>A. \<exists> v\<in>B. s = u \<otimes>\<^sub>a v\<close>
      by auto
    then obtain u v where \<open>u\<in>A\<close> and \<open>v\<in>B\<close> and \<open>s = u \<otimes>\<^sub>a v\<close>
      by blast
    hence \<open>\<exists> H::'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. clinear H \<and> H (u \<otimes>\<^sub>a v) = 1 \<and>
    (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes>\<^sub>a y \<noteq> u \<otimes>\<^sub>a v \<longrightarrow> H (x \<otimes>\<^sub>a y) = 0)\<close>
      by (simp add: assms(1) assms(2) tensor_Kronecker_delta)
    then obtain H::\<open>'a \<otimes>\<^sub>a 'b \<Rightarrow>complex\<close> where \<open>clinear H\<close> and \<open>H (u \<otimes>\<^sub>a v) = 1\<close>
      and \<open>\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes>\<^sub>a y \<noteq> u \<otimes>\<^sub>a v \<longrightarrow> H (x \<otimes>\<^sub>a y) = 0\<close>
      by blast
    have \<open>u \<otimes>\<^sub>a v \<in> S\<close>
      using \<open>s = u \<otimes>\<^sub>a v\<close> \<open>s \<in> S\<close> by auto
    have \<open>H (\<Sum>s\<in>S. (f s) *\<^sub>C s) = (\<Sum>s\<in>S. (f s) *\<^sub>C H s)\<close>
      using \<open>clinear H\<close>
      by (smt complex_vector.linear_scale complex_vector.linear_sum sum.cong)
    also have \<open>\<dots> = (f (u \<otimes>\<^sub>a v)) *\<^sub>C H (u \<otimes>\<^sub>a v) + (\<Sum>s\<in>S - {u \<otimes>\<^sub>a v}. (f s) *\<^sub>C H s)\<close>
      using \<open>u \<otimes>\<^sub>a v \<in> S\<close>
      by (meson \<open>finite S\<close> sum.remove)
    also have \<open>\<dots> = (f (u \<otimes>\<^sub>a v)) *\<^sub>C H (u \<otimes>\<^sub>a v)\<close>
    proof-
      have \<open>r\<in>S - {u \<otimes>\<^sub>a v} \<Longrightarrow> H r = 0\<close>
        for r
      proof-
        assume \<open>r\<in>S - {u \<otimes>\<^sub>a v}\<close>
        hence \<open>r \<in> S\<close>
          by blast
        hence \<open>r \<in> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
          using \<open>S \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
          by blast
        hence \<open>\<exists>x\<in>A. \<exists>y\<in>B. r = x \<otimes>\<^sub>a y\<close>
          using case_prod_unfold by auto
        then obtain x y where \<open>x\<in>A\<close> and \<open>y\<in>B\<close> and \<open>r = x \<otimes>\<^sub>a y\<close>
          by blast
        have \<open>x \<otimes>\<^sub>a y \<noteq> u \<otimes>\<^sub>a v\<close>
          using \<open>r = x \<otimes>\<^sub>a y\<close> \<open>r \<in> S - {u \<otimes>\<^sub>a v}\<close> by blast
        hence \<open>H(x \<otimes>\<^sub>a y) = 0\<close>
          by (simp add: \<open>\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes>\<^sub>a y \<noteq> u \<otimes>\<^sub>a v \<longrightarrow> H (x \<otimes>\<^sub>a y) = 0\<close> \<open>x \<in> A\<close> \<open>y \<in> B\<close>)
        thus ?thesis
          using \<open>r = x \<otimes>\<^sub>a y\<close> by auto
      qed
      hence \<open>(\<Sum>s\<in>S - {u \<otimes>\<^sub>a v}. (f s) *\<^sub>C H s) = 0\<close>
        by simp        
      thus ?thesis by simp
    qed
    also have \<open>\<dots>  = f (u \<otimes>\<^sub>a v)\<close>
      using \<open>H (u \<otimes>\<^sub>a v) = 1\<close>
      by simp
    finally have \<open>H (\<Sum>s\<in>S. f s *\<^sub>C s) = f (u \<otimes>\<^sub>a v)\<close>
      by blast
    hence \<open>f (u \<otimes>\<^sub>a v) = 0\<close>
      by (simp add: \<open>(\<Sum>s\<in>S. f s *\<^sub>C s) = 0\<close> \<open>clinear H\<close> complex_vector.linear_0)
    thus ?thesis
      by (simp add: \<open>s = u \<otimes>\<^sub>a v\<close>) 
  qed
  hence \<open>cindependent ( (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B) )\<close>
    using complex_vector.independent_explicit_finite_subsets by force
  moreover have \<open>( (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B) ) = {a\<otimes>\<^sub>ab| a b. a\<in>A \<and> b\<in>B}\<close>
    by auto
  ultimately show ?thesis
    by (simp add: cdependent_raw_def) 
    
qed

lemma atensor_cindependent_case_prod:
  fixes A::\<open>'a::complex_vector set\<close> and B::\<open>'b::complex_vector set\<close>
  assumes \<open>complex_vector.independent A\<close> and \<open>complex_vector.independent B\<close>
  shows \<open>complex_vector.independent (case_prod (\<otimes>\<^sub>a) ` (A \<times> B))\<close>
proof-
  have \<open>case_prod (\<otimes>\<^sub>a) ` (A \<times> B) = {a \<otimes>\<^sub>a b |a b. a \<in> A \<and> b \<in> B}\<close>
    by auto
  thus ?thesis
    using assms atensor_cindependent[where A = "A" and B = "B"]
    by auto
qed


lemma atensor_cindependent_family:
  fixes A::\<open>'i \<Rightarrow> 'a::complex_vector\<close> and B::\<open>'j \<Rightarrow> 'b::complex_vector\<close>
  assumes \<open>complex_vector.independent (range A)\<close> and \<open>inj A\<close>
    and \<open>complex_vector.independent (range B)\<close> and \<open>inj B\<close>
  shows \<open>complex_vector.independent (range (\<lambda> k::'i\<times>'j. (A (fst k))\<otimes>\<^sub>a(B (snd k))))\<close>
proof-
  have \<open>S \<subseteq> (range (\<lambda> k::'i\<times>'j. (A (fst k))\<otimes>\<^sub>a(B (snd k)))) \<Longrightarrow> finite S \<Longrightarrow>
   (\<Sum>s\<in>S. (f s) *\<^sub>C s) = 0 \<Longrightarrow> s\<in>S \<Longrightarrow> f s = 0\<close>
    for S s f
  proof-
    assume \<open>S \<subseteq> (range (\<lambda> k::'i\<times>'j. (A (fst k))\<otimes>\<^sub>a(B (snd k))))\<close> and \<open>finite S\<close> and
      \<open>(\<Sum>s\<in>S. (f s) *\<^sub>C s) = 0\<close> and \<open>s\<in>S\<close>
    from \<open>S \<subseteq> (range (\<lambda> k::'i\<times>'j. (A (fst k))\<otimes>\<^sub>a(B (snd k))))\<close> \<open>s\<in>S\<close>
    have \<open>s \<in> (range (\<lambda> k::'i\<times>'j. (A (fst k))\<otimes>\<^sub>a(B (snd k))))\<close>
      by blast
    hence \<open>\<exists> u. \<exists> v. s = A u \<otimes>\<^sub>a B v\<close>
      by blast
    then obtain u v where \<open>s = A u \<otimes>\<^sub>a B v\<close>
      by blast
    hence \<open>\<exists> H::'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. clinear H \<and> H (A u \<otimes>\<^sub>a B v) = 1 \<and>
    (\<forall>x. \<forall>y. A x \<otimes>\<^sub>a B y \<noteq> A u \<otimes>\<^sub>a B v \<longrightarrow> H (A x \<otimes>\<^sub>a B y) = 0)\<close>
      by (metis (mono_tags, lifting) assms(1) assms(3) range_eqI tensor_Kronecker_delta)
    then obtain H::\<open>'a \<otimes>\<^sub>a 'b \<Rightarrow>complex\<close> where \<open>clinear H\<close> and \<open>H (A u \<otimes>\<^sub>a B v) = 1\<close>
      and \<open>\<forall>x. \<forall>y. A x \<otimes>\<^sub>a B y \<noteq> A u \<otimes>\<^sub>a B v \<longrightarrow> H (A x \<otimes>\<^sub>a B y) = 0\<close>
      by blast
    have \<open>A u \<otimes>\<^sub>a B v \<in> S\<close>
      using \<open>s = A u \<otimes>\<^sub>a B v\<close> \<open>s \<in> S\<close> by auto
    have \<open>H (\<Sum>s\<in>S. (f s) *\<^sub>C s) = (\<Sum>s\<in>S. (f s) *\<^sub>C H s)\<close>
      using \<open>clinear H\<close>
      by (smt complex_vector.linear_scale complex_vector.linear_sum sum.cong)
    also have \<open>\<dots> = (f (A u \<otimes>\<^sub>a B v)) *\<^sub>C H (A u \<otimes>\<^sub>a B v) + (\<Sum>s\<in>S - {A u \<otimes>\<^sub>a B v}. (f s) *\<^sub>C H s)\<close>
      using \<open>A u \<otimes>\<^sub>a B v \<in> S\<close>
      by (meson \<open>finite S\<close> sum.remove)
    also have \<open>\<dots> = (f (A u \<otimes>\<^sub>a B v)) *\<^sub>C H (A u \<otimes>\<^sub>a B v)\<close>
    proof-
      have \<open>r\<in>S - {A u \<otimes>\<^sub>a B v} \<Longrightarrow> H r = 0\<close>
        for r
      proof-
        assume \<open>r\<in>S - {A u \<otimes>\<^sub>a B v}\<close>
        hence \<open>r \<in> S\<close>
          by blast
        hence \<open>r \<in> (range (\<lambda> k::'i\<times>'j. (A (fst k))\<otimes>\<^sub>a(B (snd k))))\<close>
          using \<open>S \<subseteq> (range (\<lambda> k::'i\<times>'j. (A (fst k))\<otimes>\<^sub>a(B (snd k))))\<close>
          by blast
        hence \<open>\<exists>x. \<exists>y. r = A x \<otimes>\<^sub>a B y\<close>
          by auto
        then obtain x y where \<open>r = A x \<otimes>\<^sub>a B y\<close>
          by blast
        have \<open>A x \<otimes>\<^sub>a B y \<noteq> A u \<otimes>\<^sub>a B v\<close>
          using \<open>r = A x \<otimes>\<^sub>a B y\<close> \<open>r \<in> S - {A u \<otimes>\<^sub>a B v}\<close> 
          by blast
        hence \<open>H(A x \<otimes>\<^sub>a B y) = 0\<close>
          by (simp add: \<open>\<forall>x y. A x \<otimes>\<^sub>a B y \<noteq> A u \<otimes>\<^sub>a B v \<longrightarrow> H (A x \<otimes>\<^sub>a B y) = 0\<close>)
        thus ?thesis
          using \<open>r = A x \<otimes>\<^sub>a B y\<close> by auto          
      qed
      hence \<open>(\<Sum>s\<in>S - {A u \<otimes>\<^sub>a B v}. (f s) *\<^sub>C H s) = 0\<close>
        by auto
      thus ?thesis
        using  \<open>A u \<otimes>\<^sub>a B v \<in> S\<close> \<open>finite S\<close> eq_iff_diff_eq_0 sum_diff1
        by auto
    qed
    also have \<open>\<dots>  = f (A u \<otimes>\<^sub>a B v)\<close>
      using \<open>H (A u \<otimes>\<^sub>a B v) = 1\<close>
      by simp
    finally have \<open>H (\<Sum>s\<in>S. f s *\<^sub>C s) = f (A u \<otimes>\<^sub>a B v)\<close>
      by blast
    hence \<open>f (A u \<otimes>\<^sub>a B v) = 0\<close>
      by (simp add: \<open>(\<Sum>s\<in>S. f s *\<^sub>C s) = 0\<close> \<open>clinear H\<close> complex_vector.linear_0)
    thus ?thesis
      by (simp add: \<open>s = A u \<otimes>\<^sub>a B v\<close>) 
  qed
  thus ?thesis
    using complex_vector.independent_explicit_finite_subsets
    by (smt cdependent_raw_def)     
qed

lemma atensor_complex_inj_family:
  fixes A::\<open>'i \<Rightarrow> 'a::complex_vector\<close> and B::\<open>'j \<Rightarrow> 'b::complex_vector\<close>
  assumes \<open>complex_vector.independent (range A)\<close> and \<open>inj A\<close>
    and \<open>complex_vector.independent (range B)\<close> and \<open>inj B\<close>
  shows \<open>inj (\<lambda> k::'i\<times>'j. (A (fst k))\<otimes>\<^sub>a(B (snd k)))\<close>
proof (rule injI)
  show "x = y"
    if "A (fst x) \<otimes>\<^sub>a B (snd x) = A (fst y) \<otimes>\<^sub>a B (snd y)"
    for x :: "'i \<times> 'j"
      and y :: "'i \<times> 'j"
  proof(rule classical)
    assume \<open>\<not>(x = y)\<close>
    hence  \<open>x \<noteq> y\<close>
      by blast
    have \<open>\<exists> H::'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. clinear H \<and> H (A (fst x) \<otimes>\<^sub>a B (snd x)) = 1 \<and>
    (\<forall>u. \<forall>v. (A u, B v) \<noteq> (A (fst x), B (snd x)) \<longrightarrow> H (A u \<otimes>\<^sub>a B v) = 0)\<close>
      using assms(1) assms(3) tensor_Kronecker_delta' by force
    then obtain H::\<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> complex\<close> where \<open>clinear H\<close>
      and \<open>H (A (fst x) \<otimes>\<^sub>a B (snd x)) = 1\<close> and
      \<open>\<forall>u. \<forall>v. (A u, B v) \<noteq> (A (fst x), B (snd x)) \<longrightarrow> H (A u \<otimes>\<^sub>a B v) = 0\<close>
      by blast
    have \<open>H (A (fst x) \<otimes>\<^sub>a B (snd x)) = 1\<close>
      by (simp add: \<open>H (A (fst x) \<otimes>\<^sub>a B (snd x)) = 1\<close>)
    moreover have \<open>H (A (fst y) \<otimes>\<^sub>a B (snd y)) = 0\<close>
    proof-
      have \<open>(A (fst y), B (snd y)) \<noteq> (A (fst x), B (snd x))\<close>
      proof (cases \<open>snd y = snd x\<close>)
        case True
        hence \<open>fst y \<noteq> fst x\<close>
          using \<open>x \<noteq> y\<close> prod_eqI by blast            
        thus ?thesis
          using assms(2) range_ex1_eq by fastforce 
      next
        case False
        thus ?thesis
          using assms(4) range_ex1_eq by fastforce 
      qed
      thus ?thesis
        using \<open>\<forall>u v. (A u, B v) \<noteq> (A (fst x), B (snd x)) \<longrightarrow> H (A u \<otimes>\<^sub>a B v) = 0\<close> 
        by blast 
    qed
    ultimately have \<open>A (fst x) \<otimes>\<^sub>a B (snd x) \<noteq> A (fst y) \<otimes>\<^sub>a B (snd y)\<close>
      by auto      
    thus ?thesis
      by (simp add: that) 
  qed
qed

lemma tensor_eq_independent1:
  \<open>v\<^sub>1 = 0 \<and> v\<^sub>2 = 0 \<Longrightarrow> v\<^sub>1 \<otimes>\<^sub>a w\<^sub>1 = v\<^sub>2 \<otimes>\<^sub>a w\<^sub>2\<close>
  by (metis atensor_mult_left complex_vector.scale_zero_left)

lemma tensor_no_zero_divisors:
  \<open>a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a \<otimes>\<^sub>a b \<noteq> 0\<close>
proof-
  assume \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close>
  define A where \<open>A = complex_vector.extend_basis {a}\<close>
  define B where \<open>B = complex_vector.extend_basis {b}\<close>
  have \<open>complex_vector.independent A\<close>
    using A_def \<open>a \<noteq> 0\<close> complex_vector.independent_extend_basis
    by (metis cdependent_raw_def complex_vector.dependent_single)
  moreover have \<open>complex_vector.independent B\<close>
    using B_def \<open>b \<noteq> 0\<close> complex_vector.dependent_single complex_vector.independent_extend_basis
    by (metis cdependent_raw_def)    
  ultimately have \<open>complex_vector.independent {a\<otimes>\<^sub>ab| a b. a\<in>A \<and> b\<in>B}\<close>
    by (simp add: atensor_cindependent)
  hence \<open>0 \<notin> {a\<otimes>\<^sub>ab| a b. a\<in>A \<and> b\<in>B}\<close>
    using complex_vector.dependent_zero
    by (metis (no_types, lifting) cdependent_raw_def)
  moreover have \<open>a \<otimes>\<^sub>a b \<in> {a\<otimes>\<^sub>ab| a b. a\<in>A \<and> b\<in>B}\<close>
  proof -
    have "cindependent {b}"
      by (metis \<open>b \<noteq> 0\<close> complex_vector.dependent_single)
    hence f1: "b \<in> B"
      using B_def complex_vector.extend_basis_superset by blast
    have "cindependent {a}"
      by (meson \<open>a \<noteq> 0\<close> complex_vector.dependent_single)
    hence "a \<in> A"
      using A_def complex_vector.extend_basis_superset by blast
    thus ?thesis
      using f1 by blast
  qed
  ultimately show ?thesis by auto
qed

lemma tensor_zero_divisors_left:
  \<open>0 \<otimes>\<^sub>a b = 0\<close>
  by (metis add_cancel_right_right atensor_distr_left)

lemma tensor_zero_divisors_right:
  \<open>a \<otimes>\<^sub>a 0 = 0\<close>
  by (metis swap_atensorI2 tensor_zero_divisors_left)


lemma tensor_inj_fst:
  fixes v\<^sub>1 v\<^sub>2 :: \<open>'a::complex_vector\<close> and w :: \<open>'b::complex_vector\<close>
  assumes \<open>v\<^sub>1 \<otimes>\<^sub>a w = v\<^sub>2 \<otimes>\<^sub>a w\<close> and \<open>w \<noteq> 0\<close>
  shows \<open>v\<^sub>1 = v\<^sub>2\<close>
proof-
  have \<open>(v\<^sub>1-v\<^sub>2) \<otimes>\<^sub>a w = v\<^sub>1 \<otimes>\<^sub>a w - v\<^sub>2 \<otimes>\<^sub>a w\<close>
    by (metis (no_types, lifting) add_diff_cancel_right' atensor_distr_left diff_conv_add_uminus diff_minus_eq_add)
  also have \<open>v\<^sub>1 \<otimes>\<^sub>a w - v\<^sub>2 \<otimes>\<^sub>a w = 0\<close>
    using \<open>v\<^sub>1 \<otimes>\<^sub>a w = v\<^sub>2 \<otimes>\<^sub>a w\<close> by simp
  finally have \<open>(v\<^sub>1-v\<^sub>2) \<otimes>\<^sub>a w = 0\<close>
    by blast
  thus ?thesis using \<open>w \<noteq> 0\<close>
    using eq_iff_diff_eq_0 tensor_no_zero_divisors by blast
qed

lemma tensor_eq_independent2:
  fixes v\<^sub>1 v\<^sub>2 :: \<open>'a::complex_vector\<close> and w\<^sub>1 w\<^sub>2 :: \<open>'b::complex_vector\<close>
  assumes \<open>complex_vector.independent {w\<^sub>1, w\<^sub>2}\<close>
    and \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close>
    and \<open>v\<^sub>1 \<otimes>\<^sub>a w\<^sub>1 = v\<^sub>2 \<otimes>\<^sub>a w\<^sub>2\<close>
  shows \<open>v\<^sub>1 = 0 \<and> v\<^sub>2 = 0\<close>
proof-
  have \<open>complex_vector.dependent {v\<^sub>1, v\<^sub>2}\<close>
  proof(rule classical)
    assume \<open>\<not>(complex_vector.dependent {v\<^sub>1, v\<^sub>2})\<close>
    hence \<open>complex_vector.independent {v\<^sub>1, v\<^sub>2}\<close>
      by (simp add: cdependent_raw_def)      
    have \<open>v\<^sub>1 \<noteq> v\<^sub>2\<close>
      by (metis \<open>cindependent {v\<^sub>1, v\<^sub>2}\<close> assms(2) assms(3) complex_vector.dependent_single insert_absorb singletonI swap_atensorI2 tensor_inj_fst)
    define A::\<open>bool \<Rightarrow> 'a\<close> where \<open>A x = (if x then v\<^sub>1 else v\<^sub>2)\<close> for x
    hence \<open>range A = {v\<^sub>1, v\<^sub>2}\<close>
      by (simp add: UNIV_bool doubleton_eq_iff)
    define B::\<open>bool \<Rightarrow> 'b\<close> where \<open>B x = (if x then w\<^sub>1 else w\<^sub>2)\<close> for x
    hence \<open>range B = {w\<^sub>1, w\<^sub>2}\<close>
      by (simp add: UNIV_bool doubleton_eq_iff)
    have \<open>inj A\<close>
      using \<open>v\<^sub>1 \<noteq> v\<^sub>2\<close>
      by (smt \<open>A \<equiv> \<lambda>x. if x then v\<^sub>1 else v\<^sub>2\<close> injI)
        (* > 1*)
    moreover have \<open>inj B\<close>
      using \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close>
      by (smt \<open>B \<equiv> \<lambda>x. if x then w\<^sub>1 else w\<^sub>2\<close> injI)
        (* > 1*)
    moreover have \<open>complex_vector.independent (range A)\<close>
      using \<open>range A = {v\<^sub>1, v\<^sub>2}\<close> \<open>complex_vector.independent {v\<^sub>1, v\<^sub>2}\<close>
      by simp
    moreover have \<open>complex_vector.independent (range B)\<close>
      using \<open>range B = {w\<^sub>1, w\<^sub>2}\<close> \<open>complex_vector.independent {w\<^sub>1, w\<^sub>2}\<close>
      by simp
    ultimately have \<open>inj (\<lambda> k. A (fst k) \<otimes>\<^sub>a B (snd k))\<close>
      using atensor_complex_inj_family by blast
    hence \<open>(\<lambda> k. A (fst k) \<otimes>\<^sub>a B (snd k)) (True, True) \<noteq> (\<lambda> k. A (fst k) \<otimes>\<^sub>a B (snd k)) (False, False)\<close>
      by (metis (no_types, lifting) UNIV_I inj_on_def old.prod.inject)
    thus ?thesis
      by (simp add: \<open>A \<equiv> \<lambda>x. if x then v\<^sub>1 else v\<^sub>2\<close> \<open>B \<equiv> \<lambda>x. if x then w\<^sub>1 else w\<^sub>2\<close> assms(3)) 
  qed
  show \<open>v\<^sub>1 = 0 \<and> v\<^sub>2 = 0\<close>
  proof-
    from \<open>complex_vector.dependent {v\<^sub>1, v\<^sub>2}\<close>
    have \<open>\<exists> c::complex. c *\<^sub>C v\<^sub>1 = v\<^sub>2\<close>
      sorry
(*
      by (metis (no_types, opaque_lifting) cdependent_raw_def assms(1) assms(3) complex_vector.dependent_single complex_vector.independent_insert complex_vector.scale_zero_left complex_vector.span_breakdown_eq empty_iff eq_iff_diff_eq_0 insert_commute tensor_eq_independent1 tensor_inj_fst)
*)
    then obtain c where \<open>c *\<^sub>C v\<^sub>1 = v\<^sub>2\<close>
      by blast
    from \<open>v\<^sub>1 \<otimes>\<^sub>a w\<^sub>1 = v\<^sub>2 \<otimes>\<^sub>a w\<^sub>2\<close>
    have \<open>v\<^sub>1 \<otimes>\<^sub>a w\<^sub>1 - (c *\<^sub>C v\<^sub>1) \<otimes>\<^sub>a w\<^sub>2 = 0\<close>
      using \<open>c *\<^sub>C v\<^sub>1 = v\<^sub>2\<close>
      by auto
    moreover have \<open>v\<^sub>1 \<otimes>\<^sub>a w\<^sub>1 - (c *\<^sub>C v\<^sub>1) \<otimes>\<^sub>a w\<^sub>2 = v\<^sub>1 \<otimes>\<^sub>a (w\<^sub>1 - c *\<^sub>C w\<^sub>2)\<close>
    proof-
      have \<open>v\<^sub>1 \<otimes>\<^sub>a w\<^sub>1 - (c *\<^sub>C v\<^sub>1) \<otimes>\<^sub>a w\<^sub>2 = v\<^sub>1 \<otimes>\<^sub>a w\<^sub>1 - v\<^sub>1 \<otimes>\<^sub>a (c *\<^sub>C w\<^sub>2)\<close>
        by (simp add: atensor_mult_left atensor_mult_right)
      also have \<open>\<dots> =  v\<^sub>1 \<otimes>\<^sub>a (w\<^sub>1 - c *\<^sub>C w\<^sub>2)\<close>
        by (metis (no_types, lifting) \<open>c *\<^sub>C v\<^sub>1 = v\<^sub>2\<close> assms(3) atensor_mult_left calculation cancel_comm_monoid_add_class.diff_cancel diff_eq_diff_eq scaleC_left.diff swap_atensorI2 tensor_eq_independent1 tensor_inj_fst)
      finally show ?thesis by blast
    qed
    ultimately have \<open>v\<^sub>1 \<otimes>\<^sub>a (w\<^sub>1 - c *\<^sub>C w\<^sub>2) = 0\<close>
      by simp
    moreover have \<open>w\<^sub>1 - c *\<^sub>C w\<^sub>2 \<noteq> 0\<close>
      by (metis cdependent_raw_def assms(1) assms(2) complex_vector.independent_insert complex_vector.span_breakdown_eq complex_vector.span_empty singletonD singletonI)      
    ultimately show ?thesis
      using \<open>c *\<^sub>C v\<^sub>1 = v\<^sub>2\<close> complex_vector.scale_eq_0_iff tensor_no_zero_divisors 
      by blast 
  qed
qed

lemma tensor_eq_independent_iff:
  assumes \<open>complex_vector.independent {w\<^sub>1, w\<^sub>2}\<close> and \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close>
  shows \<open>(v\<^sub>1 = 0 \<and> v\<^sub>2 = 0) \<longleftrightarrow> v\<^sub>1 \<otimes>\<^sub>a w\<^sub>1 = v\<^sub>2 \<otimes>\<^sub>a w\<^sub>2\<close>
  using tensor_eq_independent1 tensor_eq_independent2
    assms
  by fastforce 

lemma atensor_normal_independent_fst:
  fixes \<phi>::\<open>'b::complex_vector \<Rightarrow> 'a::complex_vector\<close>
    and  B::\<open>'b set\<close>
  assumes \<open>B \<noteq> {}\<close> and \<open>finite B\<close>
    and \<open>complex_vector.independent B\<close>
    and \<open>(\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b) = 0\<close>
    and \<open>v \<in> B\<close>
  shows \<open>\<phi> v = 0\<close>
proof(rule classical)
  assume \<open>\<not>(\<phi> v = 0)\<close>
  hence \<open>\<phi> v \<noteq> 0\<close>
    by blast
  define u where \<open>u = \<phi> v\<close>
  have \<open>u \<noteq> 0\<close>
    using \<open>\<phi> v \<noteq> 0\<close> unfolding u_def 
    by blast
  define A where \<open>A = complex_vector.extend_basis {u}\<close>
  have \<open>u \<in> A\<close>
    using A_def \<open>u \<noteq> 0\<close> complex_vector.dependent_single complex_vector.extend_basis_superset 
    by blast
  have \<open>complex_vector.independent A\<close>
    unfolding A_def
    using \<open>u \<noteq> 0\<close> complex_vector.independent_extend_basis
    by (metis cdependent_raw_def complex_vector.dependent_single)
  hence \<open>\<exists> H::'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. clinear H \<and> H (u \<otimes>\<^sub>a v) = 1 \<and>
    (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes>\<^sub>a y \<noteq> u \<otimes>\<^sub>a v \<longrightarrow> H (x \<otimes>\<^sub>a y) = 0)\<close>
    using \<open>complex_vector.independent B\<close> tensor_Kronecker_delta
      \<open>u \<in> A\<close> \<open>v \<in> B\<close>
    by blast
  then obtain H::\<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> complex\<close> where \<open>clinear H\<close> and
    \<open>H (u \<otimes>\<^sub>a v) = 1\<close> and \<open>\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes>\<^sub>a y \<noteq> u \<otimes>\<^sub>a v \<longrightarrow> H (x \<otimes>\<^sub>a y) = 0\<close>
    by blast
  have \<open>H (\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b) = (\<Sum>b\<in>B. H ((\<phi> b) \<otimes>\<^sub>a b))\<close>
    using \<open>clinear H\<close> complex_vector.linear_sum by auto
  also have \<open>\<dots> = H ((\<phi> v) \<otimes>\<^sub>a v) + (\<Sum>b\<in>B-{v}. H ((\<phi> b) \<otimes>\<^sub>a b))\<close>
    using \<open>v \<in> B\<close>
    by (meson assms(2) sum.remove)
  also have \<open>\<dots> = H ((\<phi> v) \<otimes>\<^sub>a v)\<close>
  proof-
    have \<open>b\<in>B-{v} \<Longrightarrow> H ((\<phi> b) \<otimes>\<^sub>a b) = 0\<close>
      for b
    proof-
      assume \<open>b\<in>B-{v}\<close>
      hence \<open>b \<in> B\<close>
        by blast
      have \<open>b \<noteq> v\<close>
        using \<open>b\<in>B-{v}\<close> by blast
      have  \<open>complex_vector.independent {b, v}\<close>
      proof -
        have "\<forall>B b c. {c::'b, b} \<subseteq> insert c (insert b B)"
          by blast
        thus ?thesis
          by (metis (full_types) cdependent_raw_def \<open>b \<in> B\<close> assms(3) assms(5) complex_vector.independent_mono insert_absorb)
      qed
      have \<open>(\<phi> b) \<otimes>\<^sub>a b \<noteq> u \<otimes>\<^sub>a v\<close>
        using \<open>b \<noteq> v\<close> \<open>complex_vector.independent {b, v}\<close> \<open>u \<noteq> 0\<close> tensor_eq_independent2 by blast
      have \<open>\<phi> b \<in> cspan A\<close>
        unfolding A_def
        by (simp add: \<open>u \<noteq> 0\<close>)
      hence \<open>\<exists> f. \<exists> A'. \<phi> b = (\<Sum> a \<in> A'. f a *\<^sub>C a) \<and> finite A' \<and> A' \<subseteq> A\<close>
        using complex_vector.span_explicit
        by blast
      then obtain f A' where \<open>\<phi> b = (\<Sum> a \<in> A'. f a *\<^sub>C a)\<close> 
        and \<open>finite A'\<close> and \<open>A' \<subseteq> A\<close>
        by blast
      have  \<open>H ((\<phi> b) \<otimes>\<^sub>a b) = (\<Sum> a \<in> A'. (f a) *\<^sub>C H (a \<otimes>\<^sub>a b))\<close> 
        using  \<open>clinear H\<close>
        by (smt \<open>\<phi> b = (\<Sum>a\<in>A'. f a *\<^sub>C a)\<close> atensor_distr_left_sum atensor_mult_left complex_vector.linear_scale complex_vector.linear_sum sum.cong)
      have \<open>a \<in> A' \<Longrightarrow> H (a \<otimes>\<^sub>a b) = 0\<close>
        for a
      proof-
        assume \<open>a \<in> A'\<close>
        hence \<open>a \<in> A\<close>
          using \<open>A' \<subseteq> A\<close> by blast
        thus ?thesis
          using \<open>\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes>\<^sub>a y \<noteq> u \<otimes>\<^sub>a v \<longrightarrow> H (x \<otimes>\<^sub>a y) = 0\<close>
           \<open>b \<in> B\<close> \<open>b \<noteq> v\<close> \<open>complex_vector.independent {b, v}\<close> \<open>u \<noteq> 0\<close> tensor_eq_independent2 by blast
      qed
      hence \<open>(\<Sum> a \<in> A'. (f a) *\<^sub>C H (a \<otimes>\<^sub>a b)) = 0\<close>
        by simp
      hence \<open>H (\<phi> b \<otimes>\<^sub>a b) = 0\<close>
        using   \<open>H ((\<phi> b) \<otimes>\<^sub>a b) = (\<Sum> a \<in> A'. (f a) *\<^sub>C H (a \<otimes>\<^sub>a b))\<close>
        by simp
      thus ?thesis
        by blast
    qed
    hence \<open>(\<Sum>b\<in>B-{v}. H ((\<phi> b) \<otimes>\<^sub>a b)) = 0\<close>
      by auto      
    thus ?thesis by simp
  qed
  finally have \<open>H (\<Sum>b\<in>B. \<phi> b \<otimes>\<^sub>a b) = H ((\<phi> v) \<otimes>\<^sub>a v)\<close>
    by blast
  hence \<open>H ((\<phi> v) \<otimes>\<^sub>a v) = 0\<close>
    by (simp add: \<open>clinear H\<close> assms(4) complex_vector.linear_0)
  moreover have \<open>H ((\<phi> v) \<otimes>\<^sub>a v) = 1\<close>
    using \<open>H (u \<otimes>\<^sub>a v) = 1\<close> u_def by auto
  ultimately show ?thesis by simp
qed

lemma span_cartesian_product':
  fixes A U::\<open>'a::complex_vector set\<close> and B V::\<open>'b::complex_vector set\<close>
  assumes \<open>cspan A = cspan U\<close>
    \<open>cspan B = cspan V\<close>
  shows \<open>cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))
       \<subseteq> cspan ((case_prod (\<otimes>\<^sub>a)) ` (U \<times> V))\<close>
proof
  show "x \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (U \<times> V))"
    if "x \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))"
    for x :: "'a \<otimes>\<^sub>a 'b"
  proof-
    have \<open>\<exists> r t. finite t \<and> x = (\<Sum>a\<in>t. r a *\<^sub>C a) \<and> t \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
      using that complex_vector.span_explicit
      by blast
    then obtain r t where \<open>finite t\<close> and \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> and \<open>t \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
      by blast
    from \<open>t \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
    have \<open>\<exists> s. s \<subseteq> A \<times> B \<and> t = (case_prod (\<otimes>\<^sub>a)) ` s \<and> inj_on (case_prod (\<otimes>\<^sub>a)) s\<close>
      by (meson subset_image_inj)      
    then obtain s where \<open>s \<subseteq> A \<times> B\<close> and \<open>t = (case_prod (\<otimes>\<^sub>a)) ` s\<close> and \<open>inj_on (case_prod (\<otimes>\<^sub>a)) s\<close>
      by blast
    have \<open>x = (\<Sum>a\<in>s. (r ((case_prod (\<otimes>\<^sub>a)) a)) *\<^sub>C ((case_prod (\<otimes>\<^sub>a)) a))\<close>
      using \<open>inj_on (case_prod (\<otimes>\<^sub>a)) s\<close> \<open>t = (case_prod (\<otimes>\<^sub>a)) ` s\<close> \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> 
      by (simp add: sum.reindex_cong)
    moreover have \<open>a \<in> s \<Longrightarrow> (case_prod (\<otimes>\<^sub>a)) a \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (U \<times> V))\<close>
      for a
    proof-
      assume \<open>a \<in> s\<close>
      hence \<open>a \<in> A \<times> B\<close>
        using \<open>s \<subseteq> A \<times> B\<close>
        by auto
      have \<open>fst a \<in> cspan U\<close>
      proof-
        have \<open>fst a \<in> A\<close>
          using \<open>a \<in> A \<times> B\<close> by auto
        hence \<open>fst a \<in> cspan A\<close>
          by (simp add: complex_vector.span_base)
        thus ?thesis
          by (simp add: assms(1)) 
      qed
      moreover have \<open>snd a \<in> cspan V\<close>
      proof-
        have \<open>snd a \<in> B\<close>
          using \<open>a \<in> A \<times> B\<close> by auto
        hence \<open>snd a \<in> cspan B\<close>
          by (simp add: complex_vector.span_base)
        thus ?thesis
          by (simp add: assms(2)) 
      qed
      ultimately show ?thesis
        by (metis case_prod_unfold span_tensor_span) 
    qed
    finally show ?thesis
      by (simp add: \<open>\<And>a. a \<in> s \<Longrightarrow> (case_prod (\<otimes>\<^sub>a)) a \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (U \<times> V))\<close> \<open>x = (\<Sum>a\<in>s. r ((case_prod (\<otimes>\<^sub>a)) a) *\<^sub>C (case_prod (\<otimes>\<^sub>a)) a)\<close> complex_vector.span_scale complex_vector.span_sum) 
  qed
qed

lemma span_cartesian_product:
  fixes A U::\<open>'a::complex_vector set\<close> and B V::\<open>'b::complex_vector set\<close>
  assumes \<open>cspan A = cspan U\<close>
    \<open>cspan B = cspan V\<close>
  shows \<open>cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))
       = cspan ((case_prod (\<otimes>\<^sub>a)) ` (U \<times> V))\<close>
  apply auto
  using  assms(1) assms(2) span_cartesian_product' apply blast
  using assms(1) assms(2) span_cartesian_product'[where A = "U" and B = "V" and U = "A" and B = "B"]
  by blast

definition separable :: \<open>('a::complex_vector \<otimes>\<^sub>a 'b::complex_vector) \<Rightarrow> bool\<close> where
  \<open>separable \<psi> = (\<exists> x y. \<psi> = x \<otimes>\<^sub>a y)\<close>

abbreviation entagled :: \<open>('a::complex_vector \<otimes>\<^sub>a 'b::complex_vector) \<Rightarrow> bool\<close> where 
  \<open>entagled \<equiv> (\<lambda> \<psi>. \<not>(separable \<psi>) )\<close>

text \<open>See proof of Proposition 1 on page 186 in Helemskii\<close>
definition g_atensor_cbilinear:: \<open>'a::complex_inner \<Rightarrow> 'b::complex_inner \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> complex\<close>
  where \<open>g_atensor_cbilinear x y x\<^sub>1 y\<^sub>1 = (x \<bullet>\<^sub>C x\<^sub>1) * (y \<bullet>\<^sub>C y\<^sub>1)\<close>

lemma g_atensor_cbilinear_cbilinear:
  \<open>cbilinear (g_atensor_cbilinear x y)\<close>
  unfolding cbilinear_def clinear_def Vector_Spaces.linear_def vector_space_def
    module_hom_def module_hom_axioms_def module_def g_atensor_cbilinear_def
  apply auto
                   apply (simp add: scaleC_add_right)
                  apply (simp add: scaleC_add_left)
                 apply (simp add: ring_class.ring_distribs(1))
  using ring_class.ring_distribs(2) apply auto[1]
               apply (simp add: scaleC_add_right)
              apply (simp add: scaleC_add_left)
             apply (simp add: ring_class.ring_distribs(1))
            apply (simp add: ring_class.ring_distribs(2))
           apply (simp add: cinner_add_right semiring_normalization_rules(1))
          apply (simp add: scaleC_add_right)
         apply (simp add: scaleC_add_left)
        apply (simp add: ring_class.ring_distribs(1))
       apply (simp add: ring_class.ring_distribs(2))
  using scaleC_add_right apply auto[1]
     apply (simp add: scaleC_add_left)
    apply (simp add: ring_class.ring_distribs(1))
  using ring_class.ring_distribs(2) apply auto[1]
  by (simp add: cinner_add_right semiring_normalization_rules(34))

lemma g_atensor_clinear_existence:
  \<open>\<exists> H::'a::complex_inner \<Rightarrow> 'b::complex_inner \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. \<forall> x. \<forall> y.
   clinear (H x y) \<and> (\<forall> x\<^sub>1 y\<^sub>1. g_atensor_cbilinear x y x\<^sub>1 y\<^sub>1 = H x y (x\<^sub>1 \<otimes>\<^sub>a y\<^sub>1))\<close>
proof-
  have \<open>cbilinear (g_atensor_cbilinear x y)\<close>
    for x::'a and y::'b
    using g_atensor_cbilinear_cbilinear 
    by blast
  hence \<open>\<forall> x. \<forall> y. \<exists> H::'a \<otimes>\<^sub>a 'b \<Rightarrow> complex.
   clinear H \<and> (\<forall> x\<^sub>1 y\<^sub>1. g_atensor_cbilinear x y x\<^sub>1 y\<^sub>1 = H (x\<^sub>1 \<otimes>\<^sub>a y\<^sub>1))\<close>
    using atensor_universal_property by blast
  thus \<open>\<exists> H::'a \<Rightarrow> 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. \<forall> x. \<forall> y.
   clinear (H x y) \<and> (\<forall> x\<^sub>1 y\<^sub>1. g_atensor_cbilinear x y x\<^sub>1 y\<^sub>1 = H x y (x\<^sub>1 \<otimes>\<^sub>a y\<^sub>1))\<close>
    by metis
qed

definition g_atensor_clinear::\<open>'a::complex_inner \<Rightarrow> 'b::complex_inner \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> complex\<close>
  where \<open>g_atensor_clinear = (SOME H. \<forall> x. \<forall> y.
   clinear (H x y) \<and> (\<forall> x\<^sub>1 y\<^sub>1. g_atensor_cbilinear x y x\<^sub>1 y\<^sub>1 = H x y (x\<^sub>1 \<otimes>\<^sub>a y\<^sub>1)))\<close>

lemma g_atensor_clinear_clinear:
  \<open>clinear (g_atensor_clinear x y)\<close>
  unfolding g_atensor_clinear_def
  using g_atensor_clinear_existence
  by (smt g_atensor_clinear_def verit_sko_ex')

lemma g_atensor_clinear_cbilinear:
  \<open>g_atensor_cbilinear x y x\<^sub>1 y\<^sub>1 = g_atensor_clinear x y (x\<^sub>1 \<otimes>\<^sub>a y\<^sub>1)\<close>
  unfolding g_atensor_clinear_def
  using g_atensor_clinear_existence
  by (smt g_atensor_cbilinear_def g_atensor_clinear_def someI_ex)

lemma g_atensor_clinear_cbilinear':
  \<open>(x \<bullet>\<^sub>C x\<^sub>1) * (y \<bullet>\<^sub>C y\<^sub>1) = g_atensor_clinear x y (x\<^sub>1 \<otimes>\<^sub>a y\<^sub>1)\<close>
  unfolding g_atensor_cbilinear_def
  by (metis g_atensor_cbilinear_def g_atensor_clinear_cbilinear)

lemma F_atensor_cbilinear_cbilinear_left_distr:
  \<open>(g_atensor_clinear (b1 + b2) y u) =
       (g_atensor_clinear b1 y u) +
       (g_atensor_clinear b2 y u)\<close>
proof-
  define F where 
    \<open>F z = (g_atensor_clinear (b1 + b2) y z) -
       (g_atensor_clinear b1 y z) -
       (g_atensor_clinear b2 y z)\<close>
  for z
  have \<open>F (p \<otimes>\<^sub>a q) = 0\<close>
    for p q
    using g_atensor_clinear_cbilinear'
    unfolding F_def
  proof -
    have "g_atensor_clinear (b1 + b2) y (p \<otimes>\<^sub>a q) = (y \<bullet>\<^sub>C q) * ((b2 \<bullet>\<^sub>C p) + (b1 \<bullet>\<^sub>C p))"
      by (metis add.commute cinner_add_left g_atensor_clinear_cbilinear' mult.commute)
    hence " (g_atensor_clinear (b1 + b2) y (p \<otimes>\<^sub>a q)) -   (g_atensor_clinear b1 y (p \<otimes>\<^sub>a q)) =  (g_atensor_clinear b2 y (p \<otimes>\<^sub>a q))"
      by (metis add_diff_cancel g_atensor_clinear_cbilinear' left_diff_distrib' mult.commute)
    thus " (g_atensor_clinear (b1 + b2) y (p \<otimes>\<^sub>a q)) -  (g_atensor_clinear b1 y (p \<otimes>\<^sub>a q)) -  (g_atensor_clinear b2 y (p \<otimes>\<^sub>a q)) = 0"
      by auto
  qed
  hence \<open>z \<in> range (case_prod (\<otimes>\<^sub>a)) \<Longrightarrow> F z = 0\<close>
    for z
    by auto
  moreover have \<open>clinear F\<close>
    unfolding clinear_def proof
    show "F (c1 + c2) = F c1 + F c2"
      for c1 :: "'a \<otimes>\<^sub>a 'b"
        and c2 :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>g_atensor_clinear (b1 + b2) y (c1 + c2) = g_atensor_clinear (b1 + b2) y c1 + g_atensor_clinear (b1 + b2) y c2\<close>
        by (simp add: g_atensor_clinear_clinear complex_vector.linear_add)
      moreover have \<open>g_atensor_clinear b1 y (c1 + c2) = g_atensor_clinear b1 y c1 +  g_atensor_clinear b1 y c2\<close>
        by (simp add: g_atensor_clinear_clinear complex_vector.linear_add)
      moreover have \<open>g_atensor_clinear b2 y (c1 + c2) = g_atensor_clinear b2 y c1 +  g_atensor_clinear b2 y c2\<close>
        by (simp add: g_atensor_clinear_clinear complex_vector.linear_add)
      ultimately show ?thesis
        unfolding F_def
        by simp
    qed
    show "F (r *\<^sub>C b) = r *\<^sub>C F b"
      for r :: complex
        and b :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>g_atensor_clinear (b1 + b2) y (r *\<^sub>C b) = r *\<^sub>C (g_atensor_clinear (b1 + b2) y b)\<close>
        by (simp add: complex_vector.linear_scale g_atensor_clinear_clinear)
      moreover have \<open>g_atensor_clinear b1 y (r *\<^sub>C b) = r *\<^sub>C (g_atensor_clinear b1 y b)\<close>
        by (simp add: complex_vector.linear_scale g_atensor_clinear_clinear)
      moreover have \<open>g_atensor_clinear b2 y (r *\<^sub>C b) = r *\<^sub>C (g_atensor_clinear b2 y b)\<close>
        by (simp add: complex_vector.linear_scale g_atensor_clinear_clinear)
      ultimately show ?thesis
        unfolding F_def
        by (metis complex_vector.scale_right_diff_distrib)
    qed
  qed
  moreover have \<open>u \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
    by (simp add: atensor_onto) 
  ultimately have \<open>F u = 0\<close>
    using complex_vector.linear_eq_0_on_span by auto
  thus ?thesis
    unfolding F_def
    by (metis diff_add_cancel eq_iff_diff_eq_0 semiring_normalization_rules(24)) 
qed

lemma F_atensor_cbilinear_cbilinear_left_scaleC:
  \<open>(g_atensor_clinear (r *\<^sub>C b) y u) =  (cnj r) * (g_atensor_clinear b y u)\<close>
proof-
  define F where 
    \<open>F z = (g_atensor_clinear (r *\<^sub>C b) y z) - (cnj r) * (g_atensor_clinear b y z)\<close>
  for z
  have \<open>F (p \<otimes>\<^sub>a q) = 0\<close>
    for p q
    using g_atensor_clinear_cbilinear'
    unfolding F_def
    by (metis (no_types, lifting) cinner_scaleC_left eq_iff_diff_eq_0 mult.assoc)
  hence \<open>z \<in> range (case_prod (\<otimes>\<^sub>a)) \<Longrightarrow> F z = 0\<close>
    for z
    by auto
  moreover have \<open>clinear F\<close>
    unfolding clinear_def proof
    show "F (c1 + c2) = F c1 + F c2"
      for c1 :: "'a \<otimes>\<^sub>a 'b"
        and c2 :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>g_atensor_clinear (r *\<^sub>C b) y (c1 + c2) = g_atensor_clinear (r *\<^sub>C b) y c1
          + g_atensor_clinear (r *\<^sub>C b) y c2\<close>
        by (simp add: g_atensor_clinear_clinear complex_vector.linear_add)
      moreover have \<open>g_atensor_clinear b y (c1 + c2) = g_atensor_clinear b y c1
          + g_atensor_clinear b y c2\<close>
        by (simp add: g_atensor_clinear_clinear complex_vector.linear_add)
      ultimately show ?thesis unfolding F_def
        by (simp add: semiring_normalization_rules(34)) 
    qed
    show "F (s *\<^sub>C c) = s *\<^sub>C F c"
      for s :: complex
        and c :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>g_atensor_clinear (r *\<^sub>C b) y (s *\<^sub>C c) = s *\<^sub>C (g_atensor_clinear (r *\<^sub>C b) y c)\<close>
        by (simp add: complex_vector.linear_scale g_atensor_clinear_clinear)
      moreover have \<open>g_atensor_clinear b y (s *\<^sub>C c) = s *\<^sub>C (g_atensor_clinear b y c)\<close>
        by (simp add: complex_vector.linear_scale g_atensor_clinear_clinear)
      ultimately show ?thesis unfolding F_def
        by (metis complex_vector.scale_right_diff_distrib mult_scaleC_right) 
    qed
  qed
  moreover have \<open>u \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
    by (simp add: atensor_onto) 
  ultimately have \<open>F u = 0\<close>
    using complex_vector.linear_eq_0_on_span by auto
  thus ?thesis
    unfolding F_def
    by auto
qed


lemma F_atensor_cbilinear_cbilinear_right_distr:
  \<open>(g_atensor_clinear x (b1 + b2) u) =
       (g_atensor_clinear x b1 u) + (g_atensor_clinear x b2 u)\<close>
proof-
  define F where 
    \<open>F z = (g_atensor_clinear x (b1 + b2) z) -
       (g_atensor_clinear x b1 z) -
       (g_atensor_clinear x b2 z)\<close> for z
  have \<open>F (p \<otimes>\<^sub>a q) = 0\<close> for p q
    by (metis (no_types, lifting) F_def cancel_comm_monoid_add_class.diff_cancel cinner_add_left diff_diff_add g_atensor_clinear_cbilinear' ordered_field_class.sign_simps(36))
  hence \<open>z \<in> range (case_prod (\<otimes>\<^sub>a)) \<Longrightarrow> F z = 0\<close>
    for z
    by auto
  moreover have \<open>clinear F\<close>
    unfolding clinear_def proof
    show "F (c1 + c2) = F c1 + F c2"
      for c1 :: "'a \<otimes>\<^sub>a 'b"
        and c2 :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>g_atensor_clinear x (b1 + b2) (c1 + c2) = g_atensor_clinear x (b1 + b2) c1 + g_atensor_clinear x (b1 + b2) c2\<close>
        by (simp add: g_atensor_clinear_clinear complex_vector.linear_add)
      moreover have \<open>g_atensor_clinear x b1 (c1 + c2) = g_atensor_clinear x b1 c1 +  g_atensor_clinear x b1 c2\<close>
        by (simp add: g_atensor_clinear_clinear complex_vector.linear_add)
      moreover have \<open>g_atensor_clinear x b2 (c1 + c2) = g_atensor_clinear x b2 c1 +  g_atensor_clinear x b2 c2\<close>
        by (simp add: g_atensor_clinear_clinear complex_vector.linear_add)
      ultimately show ?thesis
        unfolding F_def
        by simp
    qed
    show "F (r *\<^sub>C b) = r *\<^sub>C F b"
      for r :: complex
        and b :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>g_atensor_clinear x (b1 + b2) (r *\<^sub>C b) = r *\<^sub>C (g_atensor_clinear x (b1 + b2) b)\<close>
        by (simp add: complex_vector.linear_scale g_atensor_clinear_clinear)
      moreover have \<open>g_atensor_clinear x b1 (r *\<^sub>C b) = r *\<^sub>C (g_atensor_clinear x b1 b)\<close>
        by (simp add: complex_vector.linear_scale g_atensor_clinear_clinear)
      moreover have \<open>g_atensor_clinear x b2 (r *\<^sub>C b) = r *\<^sub>C (g_atensor_clinear x b2 b)\<close>
        by (simp add: complex_vector.linear_scale g_atensor_clinear_clinear)
      ultimately show ?thesis
        unfolding F_def
        by (metis complex_vector.scale_right_diff_distrib)
    qed
  qed
  moreover have \<open>u \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
    by (simp add: atensor_onto) 
  ultimately have \<open>F u = 0\<close>
    using complex_vector.linear_eq_0_on_span by auto
  thus ?thesis
    unfolding F_def
    by (metis diff_add_cancel eq_iff_diff_eq_0 semiring_normalization_rules(24)) 
qed


lemma F_atensor_cbilinear_cbilinear_right_scaleC:
  \<open>(g_atensor_clinear x (r *\<^sub>C b) u) = (cnj r) * (g_atensor_clinear x b u)\<close>
proof-
  define F where 
    \<open>F z = (g_atensor_clinear x (r *\<^sub>C b) z) - (cnj r) * (g_atensor_clinear x b z)\<close>
  for z
  have \<open>F (p \<otimes>\<^sub>a q) = 0\<close>
    for p q
    using g_atensor_clinear_cbilinear'
    unfolding F_def
  proof -
    have "g_atensor_clinear x (r *\<^sub>C b) (p \<otimes>\<^sub>a q) = (x \<bullet>\<^sub>C p) * (cnj r * (b \<bullet>\<^sub>C q))"
      by (metis (full_types) cinner_scaleC_left g_atensor_clinear_cbilinear')
    thus "g_atensor_clinear x (r *\<^sub>C b) (p \<otimes>\<^sub>a q) - cnj r * g_atensor_clinear x b (p \<otimes>\<^sub>a q) = 0"
      using g_atensor_clinear_cbilinear' by auto
  qed
  hence \<open>z \<in> range (case_prod (\<otimes>\<^sub>a)) \<Longrightarrow> F z = 0\<close>
    for z
    by auto
  moreover have \<open>clinear F\<close>
    unfolding clinear_def proof
    show "F (c1 + c2) = F c1 + F c2"
      for c1 :: "'a \<otimes>\<^sub>a 'b"
        and c2 :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>g_atensor_clinear x (r *\<^sub>C b) (c1 + c2) = g_atensor_clinear x (r *\<^sub>C b) c1
          + g_atensor_clinear x (r *\<^sub>C b) c2\<close>
        by (simp add: g_atensor_clinear_clinear complex_vector.linear_add)
      moreover have \<open>g_atensor_clinear x b (c1 + c2) = g_atensor_clinear x b c1
          + g_atensor_clinear x b c2\<close>
        by (simp add: g_atensor_clinear_clinear complex_vector.linear_add)
      ultimately show ?thesis unfolding F_def
        by (simp add: semiring_normalization_rules(34)) 
    qed
    show "F (s *\<^sub>C c) = s *\<^sub>C F c"
      for s :: complex
        and c :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>g_atensor_clinear x (r *\<^sub>C b) (s *\<^sub>C c) = s *\<^sub>C (g_atensor_clinear x (r *\<^sub>C b) c)\<close>
        by (simp add: complex_vector.linear_scale g_atensor_clinear_clinear)
      moreover have \<open>g_atensor_clinear x b (s *\<^sub>C c) = s *\<^sub>C (g_atensor_clinear x b c)\<close>
        by (simp add: complex_vector.linear_scale g_atensor_clinear_clinear)
      ultimately show ?thesis unfolding F_def
        by (metis complex_vector.scale_right_diff_distrib mult_scaleC_right) 
    qed
  qed
  moreover have \<open>u \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
    by (simp add: atensor_onto) 
  ultimately have \<open>F u = 0\<close>
    using complex_vector.linear_eq_0_on_span by auto
  thus ?thesis
    unfolding F_def
    by auto
qed

text \<open>See proof of Proposition 1 on page 186 in Helemskii\<close>
definition F_atensor_cbilinear::\<open>'a::complex_inner \<otimes>\<^sub>a 'b::complex_inner \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> complex\<close>
  where \<open>F_atensor_cbilinear u x y = cnj (g_atensor_clinear x y u)\<close>

lemma F_atensor_cbilinear_cbilinear:
  \<open>cbilinear (F_atensor_cbilinear u)\<close>
  unfolding cbilinear_def clinear_def Vector_Spaces.linear_def vector_space_def
    module_hom_def module_hom_axioms_def module_def F_atensor_cbilinear_def
  apply auto
                     apply (simp add: scaleC_add_right)
                    apply (simp add: scaleC_left.add)
                   apply (simp add: ring_class.ring_distribs(1))
                  apply (simp add: ring_class.ring_distribs(2))
                 apply (simp add: scaleC_add_right)
                apply (simp add: scaleC_add_left)
               apply (simp add: ring_class.ring_distribs(1))
              apply (simp add: ring_class.ring_distribs(2))
             apply (simp add: F_atensor_cbilinear_cbilinear_left_distr) 
            apply (simp add: F_atensor_cbilinear_cbilinear_left_scaleC)
           apply (simp add: scaleC_add_right)
  using scaleC_left.add apply auto[1]
         apply (simp add: ring_class.ring_distribs(1))
        apply (simp add: ring_class.ring_distribs(2))
       apply (simp add: scaleC_add_right)
      apply (simp add: scaleC_add_left)
     apply (simp add: ring_class.ring_distribs(1))
    apply (simp add: ring_class.ring_distribs(2))
   apply (simp add: F_atensor_cbilinear_cbilinear_right_distr)
  by (simp add: F_atensor_cbilinear_cbilinear_right_scaleC)

lemma F_atensor_clinear_existence:
  \<open>\<exists> K::'a::complex_inner \<otimes>\<^sub>a 'b::complex_inner \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. \<forall> u.
   clinear (K u) \<and> (\<forall> x y. F_atensor_cbilinear u x y = K u (x \<otimes>\<^sub>a y))\<close>
proof-
  have \<open>cbilinear (F_atensor_cbilinear u)\<close>
    for u::\<open>'a \<otimes>\<^sub>a 'b\<close>
    using F_atensor_cbilinear_cbilinear 
    by blast
  hence \<open>\<forall> u. \<exists> K::'a \<otimes>\<^sub>a 'b \<Rightarrow> complex.
   clinear K \<and> (\<forall> x y. F_atensor_cbilinear u x y = K (x \<otimes>\<^sub>a y))\<close>
    using atensor_universal_property by blast
  thus \<open>\<exists> K:: 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. \<forall> u.
   clinear (K u) \<and> (\<forall> x y. F_atensor_cbilinear u x y = K u (x \<otimes>\<^sub>a y))\<close>
    by metis
qed

definition F_atensor_clinear::\<open>'a::complex_inner \<otimes>\<^sub>a 'b::complex_inner \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> complex\<close>
  where \<open>F_atensor_clinear = (SOME K:: 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. \<forall> u.
   clinear (K u) \<and> (\<forall> x y. F_atensor_cbilinear u x y = K u (x \<otimes>\<^sub>a y)))\<close>

lemma F_atensor_clinear_clinear:
  \<open>clinear (F_atensor_clinear u)\<close>
  unfolding F_atensor_clinear_def
  using F_atensor_clinear_existence
  by (smt F_atensor_clinear_def verit_sko_ex')

lemma F_atensor_clinear_cbilinear:
  \<open>F_atensor_cbilinear u x y = F_atensor_clinear u (x \<otimes>\<^sub>a y)\<close>
  unfolding F_atensor_clinear_def
  using F_atensor_clinear_existence
  by (smt F_atensor_clinear_def verit_sko_ex')

lemma F_atensor_clinear_distr:
  \<open>F_atensor_clinear (b1 + b2) y =
       F_atensor_clinear b1 y + F_atensor_clinear b2 y\<close>
proof-
  define F where 
    \<open>F z = F_atensor_clinear (b1 + b2) z -
       F_atensor_clinear b1 z - F_atensor_clinear b2 z\<close>
  for z
  have \<open>F (p \<otimes>\<^sub>a q) = 0\<close>
    for p q
  proof-
    have \<open>g_atensor_clinear p q (b1 + b2) =
     g_atensor_clinear p q b1 + g_atensor_clinear p q b2\<close>
      using g_atensor_clinear_clinear[where x = "p" and y = "q"]
      unfolding clinear_def
      by (simp add: \<open>clinear (g_atensor_clinear p q)\<close> complex_vector.linear_add) 
    hence \<open>g_atensor_clinear p q (b1 + b2)  - g_atensor_clinear p q b1 -
    g_atensor_clinear p q b2 = 0\<close>
      by simp
    hence \<open>F_atensor_cbilinear (b1 + b2) p q - F_atensor_cbilinear b1 p q -
    F_atensor_cbilinear b2 p q = 0\<close>
      by (metis F_atensor_cbilinear_def complex_cnj_diff eq_iff_diff_eq_0)
    hence \<open>F_atensor_clinear (b1 + b2) (p \<otimes>\<^sub>a q) - F_atensor_clinear b1 (p \<otimes>\<^sub>a q) -
    F_atensor_clinear b2 (p \<otimes>\<^sub>a q) = 0\<close>
      by (simp add: F_atensor_clinear_cbilinear)      
    thus ?thesis
      unfolding F_def
      by blast
  qed
  hence \<open>z \<in> range (case_prod (\<otimes>\<^sub>a)) \<Longrightarrow> F z = 0\<close>
    for z
    by auto
  moreover have \<open>clinear F\<close>
    unfolding clinear_def proof
    show "F (c1 + c2) = F c1 + F c2"
      for c1 :: "'a \<otimes>\<^sub>a 'b"
        and c2 :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>F_atensor_clinear (b1 + b2) (c1 + c2) = F_atensor_clinear (b1 + b2) c1
          + F_atensor_clinear (b1 + b2) c2\<close>
        using F_atensor_clinear_clinear[where u = "b1 + b2"]
        unfolding clinear_def
        by (simp add: \<open>clinear (F_atensor_clinear (b1 + b2))\<close> complex_vector.linear_add)
      moreover have \<open>F_atensor_clinear b1 (c1 + c2) = F_atensor_clinear b1 c1
          + F_atensor_clinear b1 c2\<close>
        using F_atensor_clinear_clinear[where u = "b1"]
        unfolding clinear_def
        by (simp add: \<open>clinear (F_atensor_clinear b1)\<close> complex_vector.linear_add)
      moreover have \<open>F_atensor_clinear b2 (c1 + c2) = F_atensor_clinear b2 c1
          + F_atensor_clinear b2 c2\<close>
        using F_atensor_clinear_clinear[where u = "b2"]
        unfolding clinear_def
        by (simp add: \<open>clinear (F_atensor_clinear b2)\<close> complex_vector.linear_add)
      ultimately show ?thesis unfolding F_def
        by (simp add: add_diff_add)
    qed
    show "F (r *\<^sub>C b) = r *\<^sub>C F b"
      for r :: complex
        and b :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>F_atensor_clinear (b1 + b2) (r *\<^sub>C b) = r *\<^sub>C (F_atensor_clinear (b1 + b2) b)\<close>
        using F_atensor_clinear_clinear[where u = "b1 + b2"]
        unfolding clinear_def
        by (simp add: \<open>clinear (F_atensor_clinear (b1 + b2))\<close> complex_vector.linear_scale)
      moreover have \<open>F_atensor_clinear b1 (r *\<^sub>C b) = r *\<^sub>C (F_atensor_clinear b1 b)\<close>
        using F_atensor_clinear_clinear[where u = "b1"]
        unfolding clinear_def
        by (simp add: \<open>clinear (F_atensor_clinear b1)\<close> complex_vector.linear_scale)
      moreover have \<open>F_atensor_clinear b2 (r *\<^sub>C b) = r *\<^sub>C (F_atensor_clinear b2 b)\<close>
        using F_atensor_clinear_clinear[where u = "b2"]
        unfolding clinear_def
        by (simp add: \<open>clinear (F_atensor_clinear b2)\<close> complex_vector.linear_scale)
      ultimately show ?thesis 
        unfolding F_def
        by (metis complex_vector.scale_right_diff_distrib)        
    qed
  qed
  moreover have \<open>y \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
    by (simp add: atensor_onto) 
  ultimately have \<open>F y = 0\<close>
    using complex_vector.linear_eq_0_on_span by auto
  thus ?thesis
    unfolding F_def
    by (metis diff_add_cancel eq_iff_diff_eq_0 semiring_normalization_rules(24)) 
qed

lemma F_atensor_clinear_0:
  \<open>F_atensor_clinear 0 y = 0\<close>
proof-
  have \<open>F_atensor_clinear 0 y = F_atensor_clinear (0 + 0) y\<close>
    by simp
  also have \<open>\<dots> = F_atensor_clinear 0 y + F_atensor_clinear 0 y\<close>
    using F_atensor_clinear_distr by blast
  finally have \<open>F_atensor_clinear 0 y = F_atensor_clinear 0 y + F_atensor_clinear 0 y\<close>
    by blast
  thus ?thesis
    by auto 
qed

lemma F_atensor_clinear_distr_gen':
  \<open>\<forall> S. card S = n \<and> finite S \<longrightarrow> F_atensor_clinear (\<Sum> x\<in>S. f x) y
 = (\<Sum> x\<in>S. F_atensor_clinear (f x) y)\<close>
proof(induction n)
  case 0
  hence \<open>card S = 0 \<Longrightarrow> finite S \<Longrightarrow> F_atensor_clinear (\<Sum> x\<in>S. f x) y =
       (\<Sum> x\<in>S. F_atensor_clinear (f x) y)\<close>
    for S
  proof-
    assume \<open>card S = 0\<close> and \<open>finite S\<close>
    hence \<open>S = {}\<close>
      by auto
    have \<open>(\<Sum> x\<in>S. f x) = 0\<close>
      by (simp add: \<open>S = {}\<close>)      
    hence \<open>F_atensor_clinear (\<Sum> x\<in>S. f x) y = 0\<close>
      by (simp add: F_atensor_clinear_0)
    moreover have \<open>(\<Sum> x\<in>S. F_atensor_clinear (f x) y) = 0\<close>
      using \<open>S = {}\<close> by simp
    ultimately show ?thesis by simp
  qed
  thus ?case by blast
next
  case (Suc n)
  thus ?case
    by (smt F_atensor_clinear_distr Suc_inject card.insert_remove card_eq_SucD finite_Diff finite_insert sum.insert_remove)
qed


lemma F_atensor_clinear_distr_gen:
  \<open>finite S \<Longrightarrow> F_atensor_clinear (\<Sum> x\<in>S. f x) y =
       (\<Sum> x\<in>S. F_atensor_clinear (f x) y)\<close>
  using F_atensor_clinear_distr_gen' by blast

lemma F_atensor_clinear_scaleC:
  \<open>F_atensor_clinear (r *\<^sub>C b) y = (cnj r) * F_atensor_clinear b y\<close>
proof-
  define F where 
    \<open>F z = F_atensor_clinear (r *\<^sub>C b) z - (cnj r) * F_atensor_clinear b z\<close>
  for z
  have \<open>F (p \<otimes>\<^sub>a q) = 0\<close>
    for p q
  proof-
    have \<open>g_atensor_clinear p q (r *\<^sub>C b) = r *\<^sub>C g_atensor_clinear p q b\<close>
      using g_atensor_clinear_clinear[where x = "p" and y = "q"]
      unfolding clinear_def
      by (simp add: \<open>clinear (g_atensor_clinear p q)\<close> complex_vector.linear_scale)
    hence \<open>g_atensor_clinear p q (r *\<^sub>C b)  - r *\<^sub>C (g_atensor_clinear p q b) = 0\<close>
      by simp
    hence \<open>F_atensor_cbilinear (r *\<^sub>C b) p q - (cnj r) *\<^sub>C (F_atensor_cbilinear b p q) = 0\<close>
      using F_atensor_cbilinear_def complex_cnj_diff eq_iff_diff_eq_0
      by (metis complex_cnj_mult complex_scaleC_def)
    hence \<open>F_atensor_clinear (r *\<^sub>C b) (p \<otimes>\<^sub>a q) - (cnj r) *\<^sub>C (F_atensor_clinear b (p \<otimes>\<^sub>a q)) = 0\<close>
      by (simp add: F_atensor_clinear_cbilinear)      
    thus ?thesis
      unfolding F_def
      by simp
  qed
  hence \<open>z \<in> range (case_prod (\<otimes>\<^sub>a)) \<Longrightarrow> F z = 0\<close>
    for z
    by auto
  moreover have \<open>clinear F\<close>
    unfolding clinear_def proof
    show "F (c1 + c2) = F c1 + F c2"
      for c1 :: "'a \<otimes>\<^sub>a 'b"
        and c2 :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>F_atensor_clinear (r *\<^sub>C b) (c1 + c2) = F_atensor_clinear (r *\<^sub>C b) c1
         + F_atensor_clinear (r *\<^sub>C b) c2\<close>
        using F_atensor_clinear_clinear[where u = "r *\<^sub>C b"]
        unfolding clinear_def
        by (simp add: \<open>clinear (F_atensor_clinear (r *\<^sub>C b))\<close> complex_vector.linear_add)
      moreover have \<open>F_atensor_clinear b (c1 + c2) = F_atensor_clinear b c1
          + F_atensor_clinear b c2\<close>
        using F_atensor_clinear_clinear[where u = "b"]
        unfolding clinear_def
        by (simp add: \<open>clinear (F_atensor_clinear b)\<close> complex_vector.linear_add)
      ultimately show ?thesis unfolding F_def
        by (simp add: semiring_normalization_rules(34))        
    qed
    show "F (s *\<^sub>C c) = s *\<^sub>C F c"
      for s :: complex
        and c :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>F_atensor_clinear (r *\<^sub>C b) (s *\<^sub>C c) = s *\<^sub>C (F_atensor_clinear (r *\<^sub>C b) c)\<close>
        using F_atensor_clinear_clinear[where u = "r *\<^sub>C b"]
        unfolding clinear_def
        by (simp add: \<open>clinear (F_atensor_clinear (r *\<^sub>C b))\<close> complex_vector.linear_scale)
      moreover have \<open>F_atensor_clinear b (s *\<^sub>C c) = s *\<^sub>C (F_atensor_clinear b c)\<close>
        using F_atensor_clinear_clinear[where u = "b"]
        unfolding clinear_def
        using \<open>clinear (F_atensor_clinear b)\<close> complex_vector.linear_scale by blast
      ultimately show ?thesis 
        unfolding F_def
        by (metis complex_vector.scale_right_diff_distrib mult_scaleC_right)
    qed
  qed
  moreover have \<open>y \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
    by (simp add: atensor_onto) 
  ultimately have \<open>F y = 0\<close>
    using complex_vector.linear_eq_0_on_span by auto
  thus ?thesis
    unfolding F_def
    by auto
qed


text \<open>Proposition 1 on page 186 in Helemskii\<close>
instantiation atensor :: (complex_inner,complex_inner) complex_inner
begin
definition cinner_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> complex\<close>
  where  \<open>cinner_atensor = F_atensor_clinear\<close>

definition norm_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> real\<close> where
  \<open>norm_atensor z = sqrt (norm (z \<bullet>\<^sub>C z) )\<close> for z

definition sgn_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close> where
  \<open>sgn_atensor x = x /\<^sub>R norm x\<close> for x

definition dist_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> real\<close> where
  \<open>dist_atensor x y = norm (x - y)\<close> for x y

definition uniformity_atensor :: \<open>(('a \<otimes>\<^sub>a 'b) \<times> ('a \<otimes>\<^sub>a 'b)) filter\<close>
  where  \<open>uniformity_atensor = (INF e\<in>{0<..}. principal {((f::'a \<otimes>\<^sub>a 'b), (g::'a \<otimes>\<^sub>a 'b)). dist f g < e})\<close>

definition open_atensor :: \<open>('a \<otimes>\<^sub>a 'b) set \<Rightarrow> bool\<close>
  where \<open>open_atensor = (\<lambda> U::('a \<otimes>\<^sub>a 'b) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity))\<close>

instance
proof
  show "dist x y = norm (x - y)"
    for x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
    unfolding dist_atensor_def 
    by blast

  show "norm x = sqrt (norm (x \<bullet>\<^sub>C x))"
    for x :: "'a \<otimes>\<^sub>a 'b"
    unfolding norm_atensor_def 
    by blast

  show "sgn x = x /\<^sub>R norm x"
    for x :: "'a \<otimes>\<^sub>a 'b"
    unfolding sgn_atensor_def 
    by blast

  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a \<otimes>\<^sub>a 'b) y < e})"
    unfolding uniformity_atensor_def 
    by blast

  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a \<otimes>\<^sub>a 'b) = x \<longrightarrow> y \<in> U)"
    for U :: "('a \<otimes>\<^sub>a 'b) set"
    unfolding open_atensor_def 
    by blast

  show "((x + y) \<bullet>\<^sub>C z) = (x \<bullet>\<^sub>C z) + (y \<bullet>\<^sub>C z)"
    for x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
      and z :: "'a \<otimes>\<^sub>a 'b"
    unfolding cinner_atensor_def
    by (simp add: F_atensor_clinear_distr)

  show "((r *\<^sub>C x) \<bullet>\<^sub>C y) = cnj r * (x \<bullet>\<^sub>C y)"
    for r :: complex
      and x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
    unfolding cinner_atensor_def
    by (simp add: F_atensor_clinear_scaleC)

  have expansion_id: \<open>finite t \<Longrightarrow> finite t' \<Longrightarrow> 
        x = (\<Sum>a\<in>t. r a *\<^sub>C a) \<Longrightarrow> y = (\<Sum>a'\<in>t'. r' a' *\<^sub>C a') \<Longrightarrow>
       (x \<bullet>\<^sub>C y) = (\<Sum>a\<in>t. \<Sum>a'\<in>t'. cnj (r a) * r' a' *\<^sub>C (a \<bullet>\<^sub>C a'))\<close>
    for x y :: "'a \<otimes>\<^sub>a 'b"
      and t t'::"('a \<otimes>\<^sub>a 'b) set"
      and r r':: "'a \<otimes>\<^sub>a 'b \<Rightarrow> complex"
  proof-
    assume \<open>finite t\<close> and \<open>finite t'\<close> and 
      \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> and \<open>y = (\<Sum>a'\<in>t'. r' a' *\<^sub>C a')\<close>
    have \<open>(x \<bullet>\<^sub>C y) = ((\<Sum>a\<in>t. r a *\<^sub>C a) \<bullet>\<^sub>C y)\<close>
      using \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> by blast
    also have \<open>\<dots> = (\<Sum>a\<in>t. ((r a *\<^sub>C a) \<bullet>\<^sub>C y))\<close>
      unfolding cinner_atensor_def
      using F_atensor_clinear_distr_gen \<open>finite t\<close> by blast
    also have \<open>\<dots> = (\<Sum>a\<in>t. (cnj (r a)) *\<^sub>C (a \<bullet>\<^sub>C y))\<close>
      by (metis \<open>\<And>y:: 'a\<otimes>\<^sub>a'b. \<And> x r. ((r *\<^sub>C x) \<bullet>\<^sub>C y) = cnj r * (x \<bullet>\<^sub>C y)\<close> complex_scaleC_def)
    also have \<open>\<dots> = (\<Sum>a\<in>t. (cnj (r a)) *\<^sub>C (a \<bullet>\<^sub>C (\<Sum>a'\<in>t'. r' a' *\<^sub>C a')))\<close>
      using \<open>y = (\<Sum>a\<in>t'. r' a *\<^sub>C a)\<close> by blast
    also have \<open>\<dots> = (\<Sum>a\<in>t. (cnj (r a)) *\<^sub>C (\<Sum>a'\<in>t'. (a \<bullet>\<^sub>C (r' a' *\<^sub>C a'))) )\<close>
    proof-
      have \<open>(a \<bullet>\<^sub>C (\<Sum>a'\<in>t'. r' a' *\<^sub>C a')) = (\<Sum>a'\<in>t'. (a \<bullet>\<^sub>C (r' a' *\<^sub>C a')))\<close>
        for a
      proof-
        have \<open>clinear (F_atensor_clinear a)\<close>
          by (simp add: F_atensor_clinear_clinear)          
        thus ?thesis
          using cinner_atensor_def complex_vector.linear_sum by auto 
      qed
      thus ?thesis by simp
    qed
    also have \<open>\<dots> = (\<Sum>a\<in>t. (cnj (r a)) *\<^sub>C (\<Sum>a'\<in>t'. r' a' *\<^sub>C (a \<bullet>\<^sub>C a')) )\<close>
    proof-
      have \<open>(a \<bullet>\<^sub>C (r' a' *\<^sub>C  a'))  = r' a' *\<^sub>C (a \<bullet>\<^sub>C a')\<close>
        for a a'
        unfolding cinner_atensor_def
        by (simp add: F_atensor_clinear_clinear complex_vector.linear_scale)
      thus ?thesis by simp 
    qed
    also have \<open>\<dots> = (\<Sum>a\<in>t. (\<Sum>a'\<in>t'. (cnj (r a)) * r' a' *\<^sub>C (a \<bullet>\<^sub>C a')) )\<close>
    proof -
      have "\<forall>a. cnj (r a) *\<^sub>C (\<Sum>a'\<in>t'. r' a' *\<^sub>C (a \<bullet>\<^sub>C a')) = (\<Sum>a'\<in>t'. cnj (r a) * r' a' *\<^sub>C (a \<bullet>\<^sub>C a'))"
        by (simp add: vector_space_over_itself.scale_sum_right)
      thus ?thesis
        by meson
    qed
    finally show \<open>(x \<bullet>\<^sub>C y) = (\<Sum>a\<in>t. \<Sum>a'\<in>t'. cnj (r a) * r' a' *\<^sub>C (a \<bullet>\<^sub>C a'))\<close>
      by blast
  qed

  have expansion: \<open>\<exists> t t'::('a \<otimes>\<^sub>a 'b) set. \<exists> r r':: 'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. 
        finite t \<and> finite t' \<and> t \<subseteq> range (case_prod (\<otimes>\<^sub>a)) \<and> t' \<subseteq> range (case_prod (\<otimes>\<^sub>a)) \<and>
       (x \<bullet>\<^sub>C y) = (\<Sum>a\<in>t. \<Sum>a'\<in>t'. cnj (r a) * r' a' *\<^sub>C (a \<bullet>\<^sub>C a')) 
     \<and> x = (\<Sum>a\<in>t. r a *\<^sub>C a) \<and> y = (\<Sum>a'\<in>t'. r' a' *\<^sub>C a')\<close>
    for x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
  proof-
    have \<open>x \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
      by (simp add: atensor_onto)
    hence \<open>\<exists> t r. x = (\<Sum>a\<in>t. r a *\<^sub>C a) \<and> finite t \<and> t \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close>
      using complex_vector.span_explicit
      by fastforce
    then obtain t::\<open>('a \<otimes>\<^sub>a 'b) set\<close> and r::\<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> complex\<close>
      where \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> and \<open>finite t\<close> and \<open>t \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close>
      by blast
    have \<open>y \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
      by (simp add: atensor_onto)
    hence \<open>\<exists> t' r'. y = (\<Sum>a\<in>t'. r' a *\<^sub>C a) \<and> finite t' \<and> t' \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close>
      using complex_vector.span_explicit
      by fastforce
    then obtain t'::\<open>('a \<otimes>\<^sub>a 'b) set\<close> and r'::\<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> complex\<close> 
      where \<open>y = (\<Sum>a\<in>t'. r' a *\<^sub>C a)\<close> and \<open>finite t'\<close> and \<open>t' \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close>
      by blast
    have \<open>(x \<bullet>\<^sub>C y) = (\<Sum>a\<in>t. \<Sum>a'\<in>t'. cnj (r a) * r' a' *\<^sub>C (a \<bullet>\<^sub>C a'))\<close>
      using expansion_id[where t = "t" and t' = "t'" and x = "x" and y = "y"
          and r = "r" and r' = "r'"] \<open>finite t\<close> \<open>finite t'\<close>
        \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> \<open>y = (\<Sum>a'\<in>t'. r' a' *\<^sub>C a')\<close> by blast
    thus ?thesis 
      using \<open>finite t\<close> \<open>finite t'\<close> \<open>t \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close> \<open>t' \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close>
        \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> \<open>y = (\<Sum>a'\<in>t'. r' a' *\<^sub>C a')\<close> 
      by blast
  qed

  show "(x \<bullet>\<^sub>C y) = cnj (y \<bullet>\<^sub>C x)"
    for x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
  proof-
    have swap: \<open>x \<in> range (case_prod (\<otimes>\<^sub>a)) \<Longrightarrow> y \<in> range (case_prod (\<otimes>\<^sub>a)) \<Longrightarrow> (x \<bullet>\<^sub>C y) = cnj (y \<bullet>\<^sub>C x)\<close>
      for x y
    proof-
      assume \<open>x \<in> range (case_prod (\<otimes>\<^sub>a))\<close> and \<open>y \<in> range (case_prod (\<otimes>\<^sub>a))\<close>
      from \<open>x \<in> range (case_prod (\<otimes>\<^sub>a))\<close>
      obtain x\<^sub>1 x\<^sub>2 where \<open>x = x\<^sub>1 \<otimes>\<^sub>a x\<^sub>2\<close>
        by auto
      from \<open>y \<in> range (case_prod (\<otimes>\<^sub>a))\<close>
      obtain y\<^sub>1 y\<^sub>2 where \<open>y = y\<^sub>1 \<otimes>\<^sub>a y\<^sub>2\<close>
        by auto
      have \<open>(x \<bullet>\<^sub>C y) = F_atensor_clinear x y\<close>
        unfolding cinner_atensor_def
        by blast
      also have \<open>\<dots> = F_atensor_cbilinear x y\<^sub>1 y\<^sub>2\<close>
      proof-
        have \<open>F_atensor_cbilinear x y\<^sub>1 y\<^sub>2 = F_atensor_clinear x (y\<^sub>1 \<otimes>\<^sub>a y\<^sub>2)\<close>
          using  F_atensor_clinear_cbilinear[where u = "x" and x = "y\<^sub>1" and y = "y\<^sub>2"]
          by blast
        thus ?thesis
          by (simp add: \<open>y = y\<^sub>1 \<otimes>\<^sub>a y\<^sub>2\<close>)          
      qed
      also have \<open>\<dots> = cnj (g_atensor_clinear y\<^sub>1 y\<^sub>2 x)\<close>
        unfolding F_atensor_cbilinear_def
        by blast
      also have \<open>\<dots> = cnj (g_atensor_cbilinear y\<^sub>1 y\<^sub>2 x\<^sub>1 x\<^sub>2)\<close>
      proof-
        have \<open>g_atensor_clinear y\<^sub>1 y\<^sub>2 x = g_atensor_cbilinear y\<^sub>1 y\<^sub>2 x\<^sub>1 x\<^sub>2\<close>
          using  \<open>x = x\<^sub>1 \<otimes>\<^sub>a x\<^sub>2\<close>
          by (simp add: g_atensor_clinear_cbilinear)
        thus ?thesis by simp
      qed
      also have \<open>\<dots> = cnj (cnj (g_atensor_cbilinear x\<^sub>1 x\<^sub>2 y\<^sub>1 y\<^sub>2))\<close>
        unfolding g_atensor_cbilinear_def
        by simp
      also have \<open>\<dots> = cnj (cnj (g_atensor_clinear x\<^sub>1 x\<^sub>2 y))\<close>
        by (simp add: \<open>y = y\<^sub>1 \<otimes>\<^sub>a y\<^sub>2\<close> g_atensor_clinear_cbilinear)
      also have \<open>\<dots> = cnj (F_atensor_clinear y x)\<close>
        by (metis (full_types) F_atensor_cbilinear_def F_atensor_clinear_cbilinear \<open>x = x\<^sub>1 \<otimes>\<^sub>a x\<^sub>2\<close>)
      finally show \<open>(x \<bullet>\<^sub>C y) = cnj (y \<bullet>\<^sub>C x)\<close>
        using cinner_atensor_def 
        by simp 
    qed
    have \<open>\<exists> t t'::('a \<otimes>\<^sub>a 'b) set. \<exists> r r':: 'a \<otimes>\<^sub>a 'b \<Rightarrow> complex. 
        finite t \<and> finite t' \<and> t \<subseteq> range (case_prod (\<otimes>\<^sub>a)) \<and> t' \<subseteq> range (case_prod (\<otimes>\<^sub>a)) \<and>
       (x \<bullet>\<^sub>C y) = (\<Sum>a\<in>t. \<Sum>a'\<in>t'. cnj (r a) * r' a' *\<^sub>C (a \<bullet>\<^sub>C a')) 
     \<and> x = (\<Sum>a\<in>t. r a *\<^sub>C a) \<and> y = (\<Sum>a'\<in>t'. r' a' *\<^sub>C a')\<close>
      using expansion by blast
    then obtain t t' r r' where \<open>finite t\<close> and \<open>finite t'\<close> and \<open>t \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close>
      and \<open>t' \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close> and
      \<open>(x \<bullet>\<^sub>C y) = (\<Sum>a\<in>t. \<Sum>a'\<in>t'. cnj (r a) * r' a' *\<^sub>C (a \<bullet>\<^sub>C a'))\<close> and
      \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> and \<open>y = (\<Sum>a'\<in>t'. r' a' *\<^sub>C a')\<close>
      by blast
    from \<open>(x \<bullet>\<^sub>C y) = (\<Sum>a\<in>t. \<Sum>a'\<in>t'. cnj (r a) * r' a' *\<^sub>C (a \<bullet>\<^sub>C a'))\<close>
    have \<open>(x \<bullet>\<^sub>C y) = (\<Sum>a\<in>t. \<Sum>a'\<in>t'. cnj (r a) * r' a' *\<^sub>C (cnj (a' \<bullet>\<^sub>C a)))\<close>
      using swap  \<open>t \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close>  \<open>t' \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close>
      by (smt subset_eq sum.cong)
    also have \<open>\<dots> = (\<Sum>a\<in>t. \<Sum>a'\<in>t'. cnj ( r a * (cnj (r' a')) *\<^sub>C (a' \<bullet>\<^sub>C a)))\<close>
    proof-
      have \<open>cnj (r a) * r' a' *\<^sub>C (cnj (a' \<bullet>\<^sub>C a)) = cnj ( r a * (cnj (r' a')) *\<^sub>C (a' \<bullet>\<^sub>C a))\<close>
        for a a'
        by simp        
      thus ?thesis by simp
    qed
    also have \<open>\<dots> =  (\<Sum>a\<in>t. cnj (\<Sum>a'\<in>t'. ( r a * (cnj (r' a')) *\<^sub>C (a' \<bullet>\<^sub>C a))))\<close>
      by auto
    also have \<open>\<dots> = cnj (\<Sum>a\<in>t. (\<Sum>a'\<in>t'. ( r a * (cnj (r' a')) *\<^sub>C (a' \<bullet>\<^sub>C a))))\<close>
      by auto
    also have \<open>\<dots> = cnj (\<Sum>a\<in>t. (\<Sum>a'\<in>t'. ( (cnj (r' a')) * r a  *\<^sub>C (a' \<bullet>\<^sub>C a))))\<close>
    proof-
      have \<open>r a * (cnj (r' a')) = (cnj (r' a')) * r a\<close>
        for a a'
        by simp
      thus ?thesis
        by (metis (mono_tags, lifting) complex_scaleC_def mult_scaleC_right sum.cong) 
    qed
    also have \<open>\<dots> = cnj ((y \<bullet>\<^sub>C x))\<close>
    proof-
      have \<open>(y \<bullet>\<^sub>C x) = (\<Sum>a'\<in>t'. (\<Sum>a\<in>t. ( (cnj (r' a')) * r a  *\<^sub>C (a' \<bullet>\<^sub>C a))))\<close>
        using expansion_id[where t = "t'" and t' = "t" and x = "y" and y = "x"
            and r = "r'" and r' = "r"] \<open>finite t\<close> \<open>finite t'\<close>
          \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> \<open>y = (\<Sum>a'\<in>t'. r' a' *\<^sub>C a')\<close> 
        by blast
      also have \<open>\<dots> = (\<Sum>a\<in>t. (\<Sum>a'\<in>t'. ( (cnj (r' a')) * r a  *\<^sub>C (a' \<bullet>\<^sub>C a))))\<close>
      proof-
        define f where \<open>f a' a = ( (cnj (r' a')) * r a  *\<^sub>C (a' \<bullet>\<^sub>C a))\<close> for a a'
        have \<open>(\<Sum>a'\<in>t'. (\<Sum>a\<in>t. f a' a)) = (\<Sum>a\<in>t. (\<Sum>a'\<in>t'. f a' a))\<close>
          using \<open>finite t\<close> \<open>finite t'\<close>
          using sum.swap by blast          
        thus ?thesis
          unfolding f_def
          by blast          
      qed
      finally have \<open>(y \<bullet>\<^sub>C x) = (\<Sum>a\<in>t. (\<Sum>a'\<in>t'. ( (cnj (r' a')) * r a  *\<^sub>C (a' \<bullet>\<^sub>C a))))\<close>
        by blast        
      thus ?thesis by simp
    qed
    finally show ?thesis by blast
  qed

  have \<open>((x\<^sub>1\<otimes>\<^sub>ax\<^sub>2) \<bullet>\<^sub>C (y\<^sub>1\<otimes>\<^sub>ay\<^sub>2)) = cnj ((y\<^sub>1\<otimes>\<^sub>ay\<^sub>2) \<bullet>\<^sub>C (x\<^sub>1\<otimes>\<^sub>ax\<^sub>2))\<close>
    for x\<^sub>1 x\<^sub>2 y\<^sub>1 y\<^sub>2
  proof -
    have f1: "\<forall>b a c. (c \<bullet>\<^sub>C ((a::'a) \<otimes>\<^sub>a (b::'b))) = cnj (g_atensor_clinear a b c)"
      by (metis F_atensor_cbilinear_def F_atensor_clinear_cbilinear cinner_atensor_def)
    have "cnj ((y\<^sub>1 \<bullet>\<^sub>C x\<^sub>1) * (y\<^sub>2 \<bullet>\<^sub>C x\<^sub>2)) = (x\<^sub>1 \<bullet>\<^sub>C y\<^sub>1) * (x\<^sub>2 \<bullet>\<^sub>C y\<^sub>2)"
      by auto
    thus ?thesis
      using f1 by (simp add: g_atensor_clinear_cbilinear')
  qed

  have square: \<open>finite t \<Longrightarrow>  x = (\<Sum>a\<in>t. r a *\<^sub>C a) \<Longrightarrow>
         \<forall>a\<in>t. \<forall>a'\<in>t. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0 \<Longrightarrow>
       (x \<bullet>\<^sub>C x) = (\<Sum>a\<in>t. (norm (r a))^2 * (a \<bullet>\<^sub>C a))\<close>
    for x::\<open>'a \<otimes>\<^sub>a 'b\<close>
      and t::\<open>('a \<otimes>\<^sub>a 'b) set\<close>
      and r::\<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> complex\<close>
  proof-
    assume \<open>finite t\<close> and \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> and
      \<open>\<forall>a\<in>t. \<forall>a'\<in>t. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close>
    define D where \<open>D = {(a, a')| a a'. a \<in> t \<and> a' \<in> t \<and> a = a'}\<close>
    define f where \<open>f a a' = cnj (r a) * r a' *\<^sub>C (a \<bullet>\<^sub>C a')\<close> for a a'
    from  \<open>finite t\<close> and \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
    have \<open>(x \<bullet>\<^sub>C x) = (\<Sum>a\<in>t. \<Sum>a'\<in>t. cnj (r a) * r a' *\<^sub>C (a \<bullet>\<^sub>C a'))\<close>
      using expansion_id
      by blast
    also have \<open>\<dots> = (\<Sum>(a, a')\<in>t\<times>t. cnj (r a) * r a' *\<^sub>C (a \<bullet>\<^sub>C a'))\<close>
      using \<open>finite t\<close> sum.Sigma by fastforce
    also have \<open>\<dots> = (\<Sum>(a, a')\<in>t\<times>t. f a a')\<close>
      unfolding f_def by blast
    also have \<open>\<dots> = (\<Sum>(a, a')\<in>D. f a a')
        + (\<Sum>(a, a')\<in>t\<times>t-D. f a a')\<close>
    proof-
      have \<open>D \<subseteq> t\<times>t\<close>
        unfolding D_def
        by auto 
      thus ?thesis
        by (metis \<open>finite t\<close> finite_SigmaI ordered_field_class.sign_simps(2) sum.subset_diff) 
    qed
    also have \<open>\<dots> = (\<Sum>(a, a')\<in>D. f a a')\<close>
    proof-
      from  \<open>\<forall>a\<in>t. \<forall>a'\<in>t. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close>
      have \<open>(a, a')\<in>t\<times>t-D \<Longrightarrow> f a a' = 0\<close>
        for a a'
        unfolding f_def D_def
        by auto
      hence \<open>(\<Sum>(a, a')\<in>t\<times>t-D. f a a') = 0\<close>
        by (smt DiffD1 SigmaE case_prod_conv sum.not_neutral_contains_not_neutral)
          (* > 1 s *)
      thus ?thesis
        using add_cancel_left_right by blast 
    qed
    also have \<open>\<dots> = (\<Sum>a\<in>t. f a a)\<close>
    proof-
      have \<open>D = (\<lambda> t. (t, t)) ` t\<close>
        by (simp add: D_def Setcompr_eq_image)        
      thus ?thesis
        by (smt Pair_inject imageE imageI old.prod.case sum.eq_general)
          (* > 1 s*)
    qed
    finally have \<open>(x \<bullet>\<^sub>C x) = (\<Sum>a\<in>t. f a a)\<close>
      by blast
    thus ?thesis
      unfolding f_def
      by (smt complex_norm_square complex_scaleC_def mult_scaleC_left semiring_normalization_rules(7) sum.cong)
  qed
  have ortho_basis: \<open>\<exists> t r. finite t \<and> 
         (\<forall>a\<in>t. \<forall>a'\<in>t. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0) \<and>
         (\<forall>a\<in>t. (a \<bullet>\<^sub>C a) > 0) \<and> x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
    for x::\<open>'a \<otimes>\<^sub>a 'b\<close>
  proof-
    have \<open>\<exists> U. complex_vector.independent U \<and> cspan U = (UNIV::'a set)\<close>
      using complex_vector.independent_empty complex_vector.independent_extend_basis complex_vector.span_extend_basis
      by (metis cdependent_raw_def)      
    then obtain U where \<open>complex_vector.independent U\<close> and \<open>cspan U = (UNIV::'a set)\<close>
      by blast
    have \<open>\<exists> V. complex_vector.independent V \<and> cspan V = (UNIV::'b set)\<close>
      using complex_vector.independent_empty complex_vector.independent_extend_basis complex_vector.span_extend_basis
      by (metis cdependent_raw_def)      
    then obtain V where \<open>complex_vector.independent V\<close> and \<open>cspan V = (UNIV::'b set)\<close>
      by blast
    have \<open>x \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (U \<times> V))\<close>
      by (metis UNIV_I \<open>cspan U = UNIV\<close> \<open>cspan V = UNIV\<close> basis_atensor_complex_generator)
    hence \<open>\<exists> T R. finite T \<and> T \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (U \<times> V) \<and> 
         x = (\<Sum>a\<in>T. R a *\<^sub>C a)\<close>
      using complex_vector.span_explicit[where b = "(case_prod (\<otimes>\<^sub>a)) ` (U \<times> V)"]
      by blast
    then obtain T R where \<open>finite T\<close> and \<open>T \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (U \<times> V)\<close> and 
      \<open>x = (\<Sum>a\<in>T. R a *\<^sub>C a)\<close>
      by blast
    have \<open>x \<in> cspan T\<close>
      by (simp add: \<open>x = (\<Sum>a\<in>T. R a *\<^sub>C a)\<close> complex_vector.span_base complex_vector.span_scale complex_vector.span_sum)  
    have \<open>\<exists> U' V'. finite U' \<and> finite V' \<and> T \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (U' \<times> V')\<close>
    proof-
      from \<open>T \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (U \<times> V)\<close> \<open>finite T\<close>
      have \<open>\<exists>S. S \<subseteq> U \<times> V \<and> T = (case_prod (\<otimes>\<^sub>a)) ` S \<and> finite S\<close>
        by (meson finite_subset_image)
      then obtain S where \<open>S \<subseteq> U \<times> V\<close> and \<open>T = (case_prod (\<otimes>\<^sub>a)) ` S\<close> and \<open>finite S\<close>
        by blast
      define U' where \<open>U' = fst ` S\<close>
      define V' where \<open>V' = snd ` S\<close>
      have \<open>finite U'\<close>
        by (simp add: U'_def \<open>finite S\<close>)        
      moreover have \<open>finite V'\<close>
        using V'_def \<open>finite S\<close> by auto        
      moreover have \<open>T \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (U' \<times> V')\<close>
      proof-
        have \<open>S \<subseteq> U' \<times> V'\<close>
          unfolding U'_def V'_def apply auto
           apply (simp add: rev_image_eqI)
          by (simp add: rev_image_eqI)
        thus ?thesis 
          using \<open>T = (case_prod (\<otimes>\<^sub>a)) ` S\<close>
          by (simp add: image_mono)
      qed
      ultimately show ?thesis by blast
    qed
    then obtain U' V' where \<open>finite U'\<close> and \<open>finite V'\<close>
      and \<open>T \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (U' \<times> V')\<close>
      by blast
    have \<open>x \<in> cspan  ((case_prod (\<otimes>\<^sub>a)) ` (U' \<times> V'))\<close>
      using \<open>T \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (U' \<times> V')\<close> \<open>x \<in> cspan T\<close> complex_vector.span_mono 
      by auto
    obtain A where \<open>is_ortho_set A\<close> and \<open>cspan A = cspan U'\<close> and \<open>finite A\<close>
      using orthonormal_basis_of_cspan \<open>finite U'\<close> by blast
    obtain B where \<open>is_ortho_set B\<close> and \<open>cspan B = cspan V'\<close> and \<open>finite B\<close>
      using orthonormal_basis_of_cspan \<open>finite V'\<close> by blast
    from \<open>cspan A = cspan U'\<close>
      \<open>cspan B = cspan V'\<close>
    have \<open>cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))
       = cspan ((case_prod (\<otimes>\<^sub>a)) ` (U' \<times> V'))\<close>
      using span_cartesian_product by blast
    have \<open>x \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))\<close>
      by (simp add: \<open>cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)) = cspan ((case_prod (\<otimes>\<^sub>a)) ` (U' \<times> V'))\<close> \<open>x \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (U' \<times> V'))\<close>)
    hence \<open>\<exists> t r. finite t \<and> t \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B) \<and> 
         x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      using complex_vector.span_explicit[where b = "(case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)"]
      by blast
    then obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close> and 
      \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      by blast
    have \<open>a\<in>t \<Longrightarrow> (a \<bullet>\<^sub>C a) > 0\<close>
      for a
    proof-
      assume \<open>a\<in>t\<close>
      have \<open>a \<in> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
        using \<open>a\<in>t\<close> \<open>t \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
        by auto
      hence \<open>\<exists>x\<in>A. \<exists>y\<in>B. a = x\<otimes>\<^sub>ay\<close>
        by (simp add: image_iff)
      then obtain x y where \<open>x\<in>A\<close> and \<open>y\<in>B\<close> and \<open>a = x\<otimes>\<^sub>ay\<close>
        by blast
      have \<open>(a \<bullet>\<^sub>C a) = F_atensor_clinear a a\<close>
        unfolding cinner_atensor_def 
        by blast
      also have \<open>\<dots> = F_atensor_cbilinear a x y\<close>
        by (simp add: F_atensor_clinear_cbilinear \<open>a = x \<otimes>\<^sub>a y\<close>)
      also have \<open>\<dots> = g_atensor_clinear x y a\<close>
        sorry
      also have \<open>\<dots> = g_atensor_cbilinear x y x y\<close>
        by (simp add: \<open>a = x \<otimes>\<^sub>a y\<close> g_atensor_clinear_cbilinear)
      also have \<open>\<dots> =  (x \<bullet>\<^sub>C x) * (y \<bullet>\<^sub>C y)\<close>
        unfolding g_atensor_cbilinear_def
        by blast
      also have \<open>\<dots> > 0\<close>
        by (metis \<open>is_ortho_set A\<close> \<open>is_ortho_set B\<close> \<open>x \<in> A\<close> \<open>y \<in> B\<close> cinner_gt_zero_iff is_ortho_set_def ordered_semiring_strict_class.mult_pos_pos)
      finally show \<open>(a \<bullet>\<^sub>C a) > 0\<close>
        by blast
    qed
  moreover have \<open>a\<in>t \<Longrightarrow> a'\<in>t \<Longrightarrow> a \<noteq> a' \<Longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close>
      for a a'
    proof-
      assume \<open>a\<in>t\<close> and \<open>a'\<in>t\<close> and \<open>a \<noteq> a'\<close>
      have \<open>a \<in> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
        using \<open>a\<in>t\<close> \<open>t \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
        by auto
      hence \<open>\<exists>x\<in>A. \<exists>y\<in>B. a = x\<otimes>\<^sub>ay\<close>
        by (simp add: image_iff)
      then obtain x y where x: \<open>x\<in>A\<close> and y: \<open>y\<in>B\<close> and xy: \<open>a = x\<otimes>\<^sub>ay\<close>
        by blast
      have \<open>a' \<in> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
        using \<open>a'\<in>t\<close> \<open>t \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
        by auto
      hence \<open>\<exists>x'\<in>A. \<exists>y'\<in>B. a' = x'\<otimes>\<^sub>ay'\<close>
        by (simp add: image_iff)
      then obtain x' y' where \<open>x'\<in>A\<close> and \<open>y'\<in>B\<close> and \<open>a' = x'\<otimes>\<^sub>ay'\<close>
        by blast
      have \<open>(a \<bullet>\<^sub>C a') = F_atensor_clinear a a'\<close>
        unfolding cinner_atensor_def 
        by blast
      also have \<open>\<dots> = F_atensor_cbilinear a x' y'\<close>
        by (simp add: F_atensor_clinear_cbilinear \<open>a' = x' \<otimes>\<^sub>a y'\<close>)
      also have \<open>\<dots> = g_atensor_clinear x' y' a\<close>
        by (metis F_atensor_cbilinear_def \<open>\<exists>x\<in>A. \<exists>y\<in>B. a = x \<otimes>\<^sub>a y\<close> \<open>a \<noteq> a'\<close> \<open>a' = x' \<otimes>\<^sub>a y'\<close> \<open>is_ortho_set A\<close> \<open>is_ortho_set B\<close> \<open>x' \<in> A\<close> \<open>y' \<in> B\<close> complex_cnj_zero g_atensor_clinear_cbilinear' is_ortho_set_def mult_not_zero)
      also have \<open>\<dots> = g_atensor_cbilinear x' y' x y\<close>
        by (simp add: \<open>a = x \<otimes>\<^sub>a y\<close> g_atensor_clinear_cbilinear)
      also have \<open>\<dots> =  (x' \<bullet>\<^sub>C x) * (y' \<bullet>\<^sub>C y)\<close>
        unfolding g_atensor_cbilinear_def
        by blast
      also have \<open>\<dots> = 0\<close>
        using  \<open>a \<noteq> a'\<close>
        by (metis \<open>a' = x' \<otimes>\<^sub>a y'\<close> \<open>is_ortho_set A\<close> \<open>is_ortho_set B\<close> \<open>x' \<in> A\<close> \<open>y' \<in> B\<close> is_ortho_set_def mult_not_zero x xy y)
      finally show \<open>(a \<bullet>\<^sub>C a') = 0\<close>
        by blast
    qed
    ultimately show ?thesis
      using \<open>finite t\<close> \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> 
      by blast 
  qed

  show "0 \<le> (x \<bullet>\<^sub>C x)"
    for x :: "'a \<otimes>\<^sub>a 'b"
  proof-
    have \<open>\<exists> t r. finite t \<and> (\<forall>a\<in>t. \<forall>a'\<in>t. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0) \<and>
      (\<forall>a\<in>t. (a \<bullet>\<^sub>C a) > 0) \<and> x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      using ortho_basis by blast
    then obtain t r where \<open>finite t\<close> and \<open>\<forall>a\<in>t. \<forall>a'\<in>t. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close>
      and \<open>\<forall>a\<in>t. (a \<bullet>\<^sub>C a) > 0\<close> and \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      by blast
    have \<open>(x \<bullet>\<^sub>C x) = (\<Sum>a\<in>t. (norm (r a))^2 * (a \<bullet>\<^sub>C a))\<close>
      using square
      using \<open>\<forall>a\<in>t. \<forall>a'\<in>t. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close> \<open>finite t\<close> \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> 
      by blast 
    moreover have \<open>a\<in>t \<Longrightarrow> (norm (r a))^2 * (a \<bullet>\<^sub>C a) \<ge> 0\<close>
      for a
    proof-
      assume \<open>a\<in>t\<close>
      hence \<open>(a \<bullet>\<^sub>C a) > 0\<close>
        using \<open>\<forall>a\<in>t. 0 < (a \<bullet>\<^sub>C a)\<close> by fastforce
      hence \<open>(a \<bullet>\<^sub>C a) \<ge> 0\<close>
        by simp
      moreover have \<open>(norm (r a))^2 \<ge> 0\<close>
        by simp        
      ultimately show ?thesis
        using complex_of_real_nn_iff
        by (metis mult_left_mono mult_not_zero)        
    qed
    ultimately show ?thesis
      by (metis (no_types, lifting) sum_nonneg)
  qed

  show "((x \<bullet>\<^sub>C x) = 0) = (x = 0)"
    for x :: "'a \<otimes>\<^sub>a 'b"
  proof
    show "x = 0"
      if "(x \<bullet>\<^sub>C x) = 0"
    proof-
      have \<open>\<exists> t r. finite t \<and> (\<forall>a\<in>t. \<forall>a'\<in>t. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0) \<and>
      (\<forall>a\<in>t. (a \<bullet>\<^sub>C a) > 0) \<and> x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        using ortho_basis by blast
      then obtain t r where \<open>finite t\<close> and \<open>\<forall>a\<in>t. \<forall>a'\<in>t. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close>
        and \<open>\<forall>a\<in>t. (a \<bullet>\<^sub>C a) > 0\<close> and \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        by blast
      have \<open>(x \<bullet>\<^sub>C x) = (\<Sum>a\<in>t. (norm (r a))^2 * (a \<bullet>\<^sub>C a))\<close>
        using \<open>\<And>x::'a \<otimes>\<^sub>a 'b.  \<And> t r. \<lbrakk>finite t; x = (\<Sum>a\<in>t. r a *\<^sub>C a); \<forall>a\<in>t. \<forall>a'\<in>t. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<rbrakk> \<Longrightarrow> (x \<bullet>\<^sub>C x) = (\<Sum>a\<in>t. complex_of_real ((cmod (r a))\<^sup>2) * (a \<bullet>\<^sub>C a))\<close> \<open>\<forall>a\<in>t. \<forall>a'\<in>t. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close> \<open>finite t\<close> \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        by auto
      hence \<open>0 = (\<Sum>a\<in>t. (norm (r a))^2 * (a \<bullet>\<^sub>C a))\<close>
        using that by auto
      moreover have \<open>a\<in>t \<Longrightarrow> (norm (r a))^2 * (a \<bullet>\<^sub>C a) \<ge> 0\<close>
        for a
      proof-
        assume \<open>a\<in>t\<close>
        have \<open>(norm (r a))^2 \<ge> 0\<close>
          by simp          
        moreover have \<open>(a \<bullet>\<^sub>C a) \<ge> 0\<close>
          by (metis \<open>\<And>x::'a\<otimes>\<^sub>a'b. 0 \<le> (x \<bullet>\<^sub>C x)\<close>) 
        ultimately show ?thesis
          using complex_of_real_nn_iff mult_nonneg_nonneg 
          by blast 
      qed
      ultimately have zero: \<open>a\<in>t \<Longrightarrow> (norm (r a))^2 *\<^sub>C (a \<bullet>\<^sub>C a) = 0\<close>
        for a
        by (metis (mono_tags, lifting) \<open>finite t\<close> complex_scaleC_def sum_nonneg_0)
      hence \<open>a\<in>t \<Longrightarrow> r a = 0\<close>
        for a
      proof-
        assume \<open>a\<in>t\<close>
        hence \<open>(norm (r a))^2 *\<^sub>C (a \<bullet>\<^sub>C a) = 0\<close>
          using zero by blast
        moreover have \<open>(a \<bullet>\<^sub>C a) > 0\<close>
          using \<open>a\<in>t\<close>  \<open>\<forall>a\<in>t. (a \<bullet>\<^sub>C a) > 0\<close>
          by blast
        ultimately have \<open>(norm (r a))^2  = 0\<close>
          by auto
        hence \<open>norm (r a)  = 0\<close>
          by auto
        thus ?thesis
          by auto 
      qed
      thus ?thesis
        by (simp add: \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>)        
    qed

    show "(x \<bullet>\<^sub>C x) = 0"
      if "x = 0"
      using that unfolding cinner_atensor_def
      by (metis F_atensor_clinear_scaleC cinner_complex_def cinner_zero_left complex_vector.scale_zero_left)
  qed                                                             
qed

end

lemma atensorOp_existence:
  \<open>\<exists> T::('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> 
      ('c::complex_vector \<Rightarrow> 'd::complex_vector) \<Rightarrow>
      ('a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>a 'd).
\<forall> f g. clinear f \<and> clinear g \<longrightarrow> (clinear (T f g)) \<and> 
(\<forall> x y. (T f g) (x \<otimes>\<^sub>a y) = (f x) \<otimes>\<^sub>a (g y))\<close>
proof-
  have \<open>clinear f \<Longrightarrow> clinear g \<Longrightarrow> \<exists> T::('a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>a 'd).
     (clinear T) \<and> (\<forall> x y. T (x \<otimes>\<^sub>a y) = (f x) \<otimes>\<^sub>a (g y))\<close>
    for f::\<open>'a::complex_vector \<Rightarrow> 'b::complex_vector\<close> and
      g::\<open>'c::complex_vector \<Rightarrow> 'd::complex_vector\<close>
  proof-
    assume \<open>clinear f\<close> and \<open>clinear g\<close>
    define h::\<open>'a \<Rightarrow> 'c \<Rightarrow> 'b \<otimes>\<^sub>a 'd\<close>
      where \<open>h x y = (f x) \<otimes>\<^sub>a (g y)\<close> for x y
    have \<open>cbilinear h\<close>
      unfolding cbilinear_def
      using \<open>clinear f\<close>  \<open>clinear g\<close>
      by (simp add: \<open>clinear f\<close> atensor_distr_left atensor_distr_right atensor_mult_left atensor_mult_right clinearI complex_vector.linear_add complex_vector.linear_scale h_def)
    hence  \<open>\<exists>! H :: 'a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>a 'd. clinear H \<and> (\<forall> x y. h x y = H (x \<otimes>\<^sub>a y))\<close>
      by (simp add: atensor_universal_property)
    thus ?thesis
      using h_def by auto 
  qed
  hence \<open>\<forall> f::('a::complex_vector \<Rightarrow> 'b::complex_vector).
        \<forall> g::('c::complex_vector \<Rightarrow> 'd::complex_vector).
        \<exists> T::('a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>a 'd). clinear f \<and> clinear g \<longrightarrow>
     (clinear T) \<and> (\<forall> x y. T (x \<otimes>\<^sub>a y) = (f x) \<otimes>\<^sub>a (g y))\<close>
    by blast
  thus ?thesis by metis
qed

text\<open>Algebraic tensor product of bounded operators\<close>
definition atensorOp :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector)
 \<Rightarrow> ('c::complex_vector \<Rightarrow>'d::complex_vector ) \<Rightarrow> (('a \<otimes>\<^sub>a 'c) \<Rightarrow> ('b \<otimes>\<^sub>a 'd))\<close>   (infixl "\<otimes>\<^sub>A" 70)
  where \<open>atensorOp = (SOME T::('a \<Rightarrow> 'b) \<Rightarrow> 
      ('c \<Rightarrow> 'd) \<Rightarrow> ('a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>a 'd).
\<forall> f g. clinear f \<and> clinear g \<longrightarrow> (clinear (T f g)) \<and> 
(\<forall> x y. (T f g) (x \<otimes>\<^sub>a y) = (f x) \<otimes>\<^sub>a (g y)))\<close>

lemma atensorOp_clinear:
  \<open>clinear f \<Longrightarrow> clinear g \<Longrightarrow> clinear (f \<otimes>\<^sub>A g)\<close>
proof -
  assume \<open>clinear f\<close> and \<open>clinear g\<close>
  define P where \<open>P = (\<lambda> T::('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> 
      ('c::complex_vector \<Rightarrow> 'd::complex_vector) \<Rightarrow>
      ('a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>a 'd).
\<forall> f g. clinear f \<and> clinear g \<longrightarrow> (clinear (T f g)) \<and> 
(\<forall> x y. (T f g) (x \<otimes>\<^sub>a y) = (f x) \<otimes>\<^sub>a (g y)))\<close>
  have \<open>\<exists> T::('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> 
      ('c::complex_vector \<Rightarrow> 'd::complex_vector) \<Rightarrow>
      ('a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>a 'd). P T\<close>
    unfolding P_def
    using atensorOp_existence by blast
  hence \<open>P (\<lambda> f g. f \<otimes>\<^sub>A g)\<close>
    by (smt P_def atensorOp_def someI_ex)
      (* > 1 s*)
  hence   \<open>\<forall> f::'a::complex_vector \<Rightarrow> 'b::complex_vector. 
          \<forall> g::'c::complex_vector \<Rightarrow> 'd::complex_vector. 
      clinear f \<and> clinear g \<longrightarrow> (clinear (f \<otimes>\<^sub>A g)) \<and> 
      (\<forall> x y. (f \<otimes>\<^sub>A g) (x \<otimes>\<^sub>a y) = (f x) \<otimes>\<^sub>a (g y))\<close>
    unfolding P_def
    by blast
  thus ?thesis
    using \<open>clinear f\<close> \<open>clinear g\<close>
    by blast    
qed

lemma atensorOp_separation:
  \<open>clinear f \<Longrightarrow> clinear g \<Longrightarrow> (f \<otimes>\<^sub>A g) (x \<otimes>\<^sub>a y) = (f x) \<otimes>\<^sub>a (g y)\<close>
proof -
  assume \<open>clinear f\<close> and \<open>clinear g\<close>
  define P where \<open>P = (\<lambda> T::('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> 
      ('c::complex_vector \<Rightarrow> 'd::complex_vector) \<Rightarrow>
      ('a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>a 'd).
\<forall> f g. clinear f \<and> clinear g \<longrightarrow> (clinear (T f g)) \<and> 
(\<forall> x y. (T f g) (x \<otimes>\<^sub>a y) = (f x) \<otimes>\<^sub>a (g y)))\<close>
  have \<open>\<exists> T::('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> 
      ('c::complex_vector \<Rightarrow> 'd::complex_vector) \<Rightarrow>
      ('a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>a 'd). P T\<close>
    unfolding P_def
    using atensorOp_existence by blast
  hence \<open>P (\<lambda> f g. f \<otimes>\<^sub>A g)\<close>
    by (smt P_def atensorOp_def someI_ex)
      (* > 1 s*)
  hence   \<open>\<forall> f::'a::complex_vector \<Rightarrow> 'b::complex_vector. 
          \<forall> g::'c::complex_vector \<Rightarrow> 'd::complex_vector. 
      clinear f \<and> clinear g \<longrightarrow> (clinear (f \<otimes>\<^sub>A g)) \<and> 
      (\<forall> x y. (f \<otimes>\<^sub>A g) (x \<otimes>\<^sub>a y) = (f x) \<otimes>\<^sub>a (g y))\<close>
    unfolding P_def
    by blast
  thus ?thesis
    using \<open>clinear f\<close> \<open>clinear g\<close>
    by blast
qed

text \<open>A part of Proposition 1 on page 186 in Helemskii\<close>
lemma atensor_cinner_mult:
  fixes f1 g1 :: \<open>'a::complex_inner\<close> and f2 g2 :: \<open>'b::complex_inner\<close>
  shows \<open>((f1 \<otimes>\<^sub>a f2) \<bullet>\<^sub>C (g1 \<otimes>\<^sub>a g2)) = (f1 \<bullet>\<^sub>C g1) * (f2 \<bullet>\<^sub>C g2)\<close>
  by (metis F_atensor_cbilinear_def F_atensor_clinear_cbilinear cinner_atensor_def cinner_commute' complex_cnj_cnj g_atensor_clinear_cbilinear')

lemma atensor_norm_mult:
  fixes f :: \<open>'a::complex_inner\<close> and g :: \<open>'b::complex_inner\<close>
  shows \<open>norm (f \<otimes>\<^sub>a g) = norm f * norm g\<close>
proof -
  have "norm f * norm g = sqrt (cmod (f \<bullet>\<^sub>C f)) * sqrt (cmod (g \<bullet>\<^sub>C g))"
    by (metis norm_eq_sqrt_cinner)
  thus ?thesis
    by (metis atensor_cinner_mult norm_eq_sqrt_cinner norm_mult real_sqrt_mult)
qed 

lemma atensor_norm_ortho_left:
  fixes a c :: \<open>'a::chilbert_space\<close> and b d :: \<open>'a::chilbert_space\<close>
  assumes \<open>(a \<bullet>\<^sub>C c) = 0\<close> 
  shows \<open>((a\<otimes>\<^sub>ab) \<bullet>\<^sub>C (c\<otimes>\<^sub>ad)) = 0\<close>
  by (simp add: assms atensor_cinner_mult)

lemma atensor_norm_ortho_right:
  fixes a c :: \<open>'a::chilbert_space\<close> and b d :: \<open>'a::chilbert_space\<close>
  assumes \<open>(b \<bullet>\<^sub>C d) = 0\<close> 
  shows \<open>((a\<otimes>\<^sub>ab) \<bullet>\<^sub>C (c\<otimes>\<^sub>ad)) = 0\<close>
  by (simp add: assms atensor_cinner_mult)

lemma atensor_norm_expansion:
  fixes a c :: \<open>'a::chilbert_space\<close> and b d :: \<open>'a::chilbert_space\<close>
  assumes \<open>(a \<bullet>\<^sub>C c) = 0 \<or> (b \<bullet>\<^sub>C d) = 0\<close>
  shows \<open>(norm (a\<otimes>\<^sub>ab + c\<otimes>\<^sub>ad))^2 = (norm (a\<otimes>\<^sub>ab))^2 + (norm (c\<otimes>\<^sub>ad))^2\<close>
proof-
  have \<open>((a\<otimes>\<^sub>ab) \<bullet>\<^sub>C (c\<otimes>\<^sub>ad)) = 0\<close>
    by (meson assms atensor_norm_ortho_left atensor_norm_ortho_right)
  thus ?thesis
    by (simp add: pythagorean_theorem) 
qed


lemma span_finite_tensor:
  \<open>\<exists> A B. finite A  \<and> finite B \<and> (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0)
\<and> (\<forall>a\<in>B. \<forall>a'\<in>B. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0) \<and> 
z \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))\<close>
proof-
  have \<open>z \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
    by (simp add: atensor_onto)
  hence \<open>\<exists> W. finite W \<and> W \<subseteq> (range (case_prod (\<otimes>\<^sub>a))) \<and> z \<in> cspan W\<close>
    using Complex_Vector_Spaces.vector_finitely_spanned by blast
  then obtain W where \<open>finite W\<close> and \<open>W \<subseteq> (range (case_prod (\<otimes>\<^sub>a)))\<close> and 
    \<open>z \<in> cspan W\<close> by blast
  from \<open>W \<subseteq> (range (case_prod (\<otimes>\<^sub>a)))\<close>
  have \<open>\<exists> M. W = (case_prod (\<otimes>\<^sub>a)) ` M \<and> finite M\<close>
    by (meson \<open>finite W\<close> finite_subset_image)
  then obtain M where \<open>W = (case_prod (\<otimes>\<^sub>a)) ` M\<close> and \<open>finite M\<close>
    by blast
  have \<open>finite (fst ` M)\<close>
    by (simp add: \<open>finite M\<close>)
  then obtain A where \<open>is_ortho_set A\<close> and \<open>cspan A = cspan (fst ` M)\<close> and \<open>finite A\<close>
    using orthonormal_basis_of_cspan by blast
  have \<open>finite (snd ` M)\<close>
    by (simp add: \<open>finite M\<close>)
  then obtain B where \<open>is_ortho_set B\<close> and \<open>cspan B = cspan (snd ` M)\<close> and \<open>finite B\<close>
    using orthonormal_basis_of_cspan by blast
  define S where \<open>S = (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
  have \<open>z \<in> cspan S\<close>
  proof-
    from \<open>z \<in> cspan W\<close>
    have \<open>\<exists> L l. finite L \<and> L \<subseteq> W \<and> z = (\<Sum>a\<in>L. l a *\<^sub>C a)\<close>
      using complex_vector.span_explicit
      by (smt mem_Collect_eq)
    then obtain L l where \<open>finite L\<close> and \<open>L \<subseteq> W\<close> and \<open>z = (\<Sum>a\<in>L. l a *\<^sub>C a)\<close>
      by blast
    have \<open>a \<in> W \<Longrightarrow> a \<in> cspan S\<close>
      for a
    proof-
      assume \<open>a \<in> W\<close>
      have \<open>\<exists> m \<in> M. a = (case_prod (\<otimes>\<^sub>a)) m\<close>
        using \<open>W = (case_prod (\<otimes>\<^sub>a)) ` M\<close> \<open>a \<in> W\<close> 
        by blast
      then obtain m where \<open>m \<in> M\<close> and \<open>a = (case_prod (\<otimes>\<^sub>a)) m\<close>
        by blast
      have \<open>fst m \<in> cspan A\<close>
        using \<open>cspan A = cspan (fst ` M)\<close> \<open>m \<in> M\<close> complex_vector.span_superset
        by fastforce
      moreover have \<open>snd m \<in> cspan B\<close>
        using \<open>cspan B = cspan (snd ` M)\<close> \<open>m \<in> M\<close> complex_vector.span_superset 
        by fastforce
      ultimately have \<open>(fst m)\<otimes>\<^sub>a(snd m) \<in> cspan S\<close>
        unfolding S_def
        using span_tensor_span by fastforce
      thus ?thesis
        by (simp add: \<open>a = (case m of (x, xa) \<Rightarrow> x \<otimes>\<^sub>a xa)\<close> prod.case_eq_if) 
    qed
    thus ?thesis
      by (metis (no_types, opaque_lifting) \<open>z \<in> cspan W\<close> complex_vector.span_mono complex_vector.span_span subset_iff) 
  qed   
  show ?thesis
    using \<open>is_ortho_set A\<close> \<open>is_ortho_set B\<close> \<open>finite A\<close> \<open>finite B\<close> \<open>S = (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
          \<open>z \<in> cspan S\<close>
    by (metis is_ortho_set_def)
qed

lemma ortho_tensor_prod:
  assumes \<open>a\<in>(case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close> and \<open>a'\<in>(case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
    and \<open>a \<noteq> a'\<close> and \<open>finite A\<close> and \<open>finite B\<close> and 
    \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close> and
    \<open>\<forall>a\<in>B. \<forall>a'\<in>B. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close>
  shows \<open>(a \<bullet>\<^sub>C a') = 0\<close>
proof-
  have \<open>\<exists> x y. a = x \<otimes>\<^sub>a y \<and> x \<in> A \<and> y \<in> B\<close>
    using case_prod_beta assms(1) by auto
  then obtain x y where \<open>a = x \<otimes>\<^sub>a y\<close> and \<open>x \<in> A\<close> and \<open>y \<in> B\<close>
    by blast
  have \<open>\<exists> x' y'. a' = x' \<otimes>\<^sub>a y' \<and> x' \<in> A \<and> y' \<in> B\<close>
    using case_prod_beta assms(2) by auto
  then obtain x' y' where \<open>a' = x' \<otimes>\<^sub>a y'\<close> and \<open>x' \<in> A\<close> and \<open>y' \<in> B\<close>
    by blast
  have \<open>(a \<bullet>\<^sub>C a') = ((x \<otimes>\<^sub>a y) \<bullet>\<^sub>C (x' \<otimes>\<^sub>a y'))\<close>
    by (simp add: \<open>a = x \<otimes>\<^sub>a y\<close> \<open>a' = x' \<otimes>\<^sub>a y'\<close>)
  also have \<open>\<dots> = (x \<bullet>\<^sub>C x') * (y \<bullet>\<^sub>C y')\<close>
    by (simp add: atensor_cinner_mult)
  also have \<open>\<dots> = 0\<close>
  proof-
    have \<open>x \<noteq> x' \<or> y \<noteq> y'\<close>
      using \<open>a \<noteq> a'\<close> \<open>a = x \<otimes>\<^sub>a y\<close> \<open>a' = x' \<otimes>\<^sub>a y'\<close> by auto
    moreover have \<open>x \<noteq> x' \<Longrightarrow> (x \<bullet>\<^sub>C x') = 0\<close>
      by (simp add: \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close> \<open>x \<in> A\<close> \<open>x' \<in> A\<close>)        
    moreover have \<open>y \<noteq> y' \<Longrightarrow> (y \<bullet>\<^sub>C y') = 0\<close>
      by (simp add: \<open>\<forall>a\<in>B. \<forall>a'\<in>B. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close> \<open>y \<in> B\<close> \<open>y' \<in> B\<close>)        
    ultimately show ?thesis
      using mult_eq_0_iff by blast 
  qed
  finally show ?thesis by blast
qed


lemma tensor_prod_expansion:
  \<open>\<exists> A B S r. finite A  \<and> finite B \<and> (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0)
\<and> (\<forall>a\<in>B. \<forall>a'\<in>B. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0) \<and> S \<subseteq> A \<times> B \<and>
z = (\<Sum>(a,b)\<in>S. (r (a, b)) *\<^sub>C (a \<otimes>\<^sub>a b))\<close>
proof-
  obtain A B where \<open>finite A\<close> and \<open>finite B\<close> and 
    \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close> and
    \<open>\<forall>a\<in>B. \<forall>a'\<in>B. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close> and
    \<open>z \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))\<close>
    apply atomize_elim
    using span_finite_tensor by blast
  from \<open>z \<in> cspan ((case_prod (\<otimes>\<^sub>a)) ` (A \<times> B))\<close>
  have \<open>\<exists> T t. finite T \<and> T \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B) \<and> z = (\<Sum>u\<in>T. t u *\<^sub>C u)\<close>
    using complex_vector.span_explicit
    by (smt mem_Collect_eq) 
  then obtain T t where \<open>finite T\<close> and \<open>T \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close> and \<open>z = (\<Sum>u\<in>T. t u *\<^sub>C u)\<close>
    by blast
  from  \<open>T \<subseteq> (case_prod (\<otimes>\<^sub>a)) ` (A \<times> B)\<close>
  have \<open>\<exists> S. T = (case_prod (\<otimes>\<^sub>a)) ` S \<and> inj_on (case_prod (\<otimes>\<^sub>a)) S \<and> S \<subseteq> A \<times> B\<close>
    by (meson subset_image_inj)
  then obtain S where \<open>T = (case_prod (\<otimes>\<^sub>a)) ` S\<close> and \<open>inj_on (case_prod (\<otimes>\<^sub>a)) S\<close> and \<open>S \<subseteq> A \<times> B\<close>
    by blast
  define r where \<open>r u = (t ((case_prod (\<otimes>\<^sub>a)) u))\<close> for u
  from \<open>z = (\<Sum>u\<in>T. t u *\<^sub>C u)\<close>
  have \<open>z = (\<Sum>u\<in>S. (t ((case_prod (\<otimes>\<^sub>a)) u)) *\<^sub>C ((case_prod (\<otimes>\<^sub>a)) u))\<close>
    using \<open>inj_on (case_prod (\<otimes>\<^sub>a)) S\<close>
    by (metis (no_types, lifting) \<open>T = (\<lambda>(x, y). x \<otimes>\<^sub>a y) ` S\<close> sum.reindex_cong)
  hence \<open>z = (\<Sum>(a,b)\<in>S. (r (a, b)) *\<^sub>C (a \<otimes>\<^sub>a b))\<close>
    by (smt \<open>T = (\<lambda>(x, y). x \<otimes>\<^sub>a y) ` S\<close> \<open>inj_on (\<lambda>(x, y). x \<otimes>\<^sub>a y) S\<close> \<open>r \<equiv> \<lambda>u. t (case u of (x, xa) \<Rightarrow> x \<otimes>\<^sub>a xa)\<close> \<open>z = (\<Sum>u\<in>T. t u *\<^sub>C u)\<close> prod.case_distrib split_cong sum.reindex_cong)
  thus ?thesis 
    using \<open>finite A\<close>  \<open>finite B\<close>  \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close> 
      \<open>\<forall>a\<in>B. \<forall>a'\<in>B. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close> \<open>S \<subseteq> A \<times> B\<close> by auto
qed


lemma tensor_prod_expansion_right':
  \<open>\<exists> \<phi> B. finite B \<and> (\<forall>b\<in>B. \<forall>b'\<in>B. b \<noteq> b' \<longrightarrow> (b \<bullet>\<^sub>C b') = 0) \<and> finite B \<and> 0 \<notin> B
   \<and> (z::'a::complex_inner\<otimes>\<^sub>a'b::complex_inner) = (\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b)\<close>
proof-
  have \<open>\<exists> V \<psi>. finite V \<and> z = (\<Sum>b\<in>V. (\<psi> b) \<otimes>\<^sub>a b)\<close>
    using atensor_onto_explicit_normalized
    by blast
  then obtain V \<psi> where \<open>finite V\<close> and \<open>z = (\<Sum>b\<in>V. (\<psi> b) \<otimes>\<^sub>a b)\<close>
    by blast
  obtain B where \<open>is_ortho_set B\<close> and \<open>cspan B = cspan V\<close> and \<open>finite B\<close>
    using orthonormal_basis_of_cspan \<open>finite V\<close> by blast
  have \<open>V \<subseteq> cspan B\<close>
    using \<open>cspan B = cspan V\<close>
    by (simp add: complex_vector.span_superset)
  have f1: \<open>b \<in>  cspan B \<Longrightarrow> \<exists> t r. finite t \<and> t \<subseteq> B \<and> b = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
    for b
    using complex_vector.span_explicit
    by (smt complex_vector.span_base mem_Collect_eq) 
  have \<open>b \<in>  cspan B \<Longrightarrow> \<exists> r. b = (\<Sum>a\<in>B. r a *\<^sub>C a)\<close>
    for b
  proof-
    assume \<open>b \<in>  cspan B\<close>
    hence \<open>\<exists> t r'. finite t \<and> t \<subseteq> B \<and> b = (\<Sum>a\<in>t. r' a *\<^sub>C a)\<close>
      using f1 by blast
    then obtain t r' where \<open>finite t\<close> and \<open>t \<subseteq> B\<close> and \<open>b = (\<Sum>a\<in>t. r' a *\<^sub>C a)\<close>
      by blast
    define r where \<open>r a = (if a \<in> t then r' a else 0)\<close> for a
    have \<open>(\<Sum>a\<in>B-t. r a *\<^sub>C a) = 0\<close>
    proof-
      have \<open>a\<in>B-t \<Longrightarrow> r a *\<^sub>C a = 0\<close>
        for a
      proof-
        assume \<open>a\<in>B-t\<close>
        hence \<open>r a = 0\<close>
          by (simp add: r_def)
        thus ?thesis by simp
      qed
      thus ?thesis
        by (simp add: \<open>\<And>a. a \<in> B - t \<Longrightarrow> r a *\<^sub>C a = 0\<close>) 
    qed
    moreover have \<open>(\<Sum>a\<in>t. r' a *\<^sub>C a) = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
    proof-
      have \<open>a\<in>t \<Longrightarrow> r' a *\<^sub>C a = r a *\<^sub>C a\<close>
        for a
      proof-
        assume \<open>a\<in>t\<close>
        hence \<open>r' a = r a\<close>
          using r_def by auto
        thus ?thesis by simp
      qed
      thus ?thesis
        by (meson sum.cong) 
    qed
    ultimately have \<open>b = (\<Sum>a\<in>B. r a *\<^sub>C a)\<close>
      using  \<open>b = (\<Sum>a\<in>t. r' a *\<^sub>C a)\<close>
      by (metis (mono_tags, lifting) \<open>finite B\<close> \<open>t \<subseteq> B\<close> eq_iff_diff_eq_0 sum_diff)
    thus ?thesis by blast
  qed
  hence \<open>b \<in> V \<Longrightarrow> \<exists>r. b = (\<Sum>a\<in>B. r a *\<^sub>C a)\<close>
    for b
    using \<open>V \<subseteq> cspan B\<close>
    by blast
  hence \<open>\<forall> b. \<exists>r. b \<in> V \<longrightarrow> b = (\<Sum>a\<in>B. r a *\<^sub>C a)\<close>
    by blast
  hence \<open>\<exists>r. \<forall> b \<in> V. b = (\<Sum>a\<in>B. r b a *\<^sub>C a)\<close>
    by metis
  then obtain r where \<open>\<forall> b \<in> V. b = (\<Sum>a\<in>B. r b a *\<^sub>C a)\<close>
    by blast
  define \<phi> ::\<open>'b \<Rightarrow> 'a\<close> where \<open>\<phi> a = (\<Sum>b\<in>V. r b a *\<^sub>C (\<psi> b))\<close> for a
  have \<open>z = (\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b)\<close>
  proof-
    from  \<open>z = (\<Sum>b\<in>V. (\<psi> b) \<otimes>\<^sub>a b)\<close>
    have  \<open>z = (\<Sum>b\<in>V. (\<psi> b) \<otimes>\<^sub>a (\<Sum>a\<in>B. r b a *\<^sub>C a))\<close>
      using \<open>\<forall> b \<in> V. b = (\<Sum>a\<in>B. r b a *\<^sub>C a)\<close> 
      by auto
    also have  \<open>\<dots> = (\<Sum>b\<in>V. (\<Sum>a\<in>B. (\<psi> b) \<otimes>\<^sub>a (r b a *\<^sub>C a)))\<close>
      by (simp add: atensor_distr_right_sum)
    also have  \<open>\<dots> = (\<Sum>b\<in>V. (\<Sum>a\<in>B. r b a *\<^sub>C ( (\<psi> b) \<otimes>\<^sub>a a)  ))\<close>
      by (meson atensor_mult_right sum.cong)
    also have  \<open>\<dots> = (\<Sum>a\<in>B. (\<Sum>b\<in>V. r b a *\<^sub>C ( (\<psi> b) \<otimes>\<^sub>a a) ))\<close>
      using sum.swap[where A = "V" and B = "B" and g = "\<lambda> b a. r b a *\<^sub>C ((\<psi> b) \<otimes>\<^sub>a a)"]
      by auto
    also have  \<open>\<dots> = (\<Sum>a\<in>B. (\<Sum>b\<in>V. (r b a *\<^sub>C (\<psi> b) \<otimes>\<^sub>a a) ))\<close>
      by (metis (no_types, lifting) atensor_mult_left sum.cong)
    also have  \<open>\<dots> = (\<Sum>a\<in>B. (\<Sum>b\<in>V. r b a *\<^sub>C (\<psi> b)) \<otimes>\<^sub>a a )\<close>
      by (simp add: atensor_distr_left_sum)
    also have  \<open>\<dots> = (\<Sum>a\<in>B. \<phi> a \<otimes>\<^sub>a a )\<close>
      unfolding \<phi>_def
      by blast
    finally show ?thesis by blast
  qed
  thus ?thesis
    using \<open>is_ortho_set B\<close> \<open>finite B\<close>
    using is_ortho_set_def by blast
qed

lemma tensor_prod_expansion_right:
  \<open>\<exists> \<phi> B. finite B \<and> (\<forall>b\<in>B. \<forall>b'\<in>B. b \<noteq> b' \<longrightarrow> (b \<bullet>\<^sub>C b') = 0) \<and> (\<forall> b\<in>B. norm b = 1)
   \<and> (z::'a::complex_inner\<otimes>\<^sub>a'b::complex_inner) = (\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b)\<close>
proof-
  have  \<open>\<exists> \<phi>' B'. finite B' \<and> (\<forall>b\<in>B'. \<forall>b'\<in>B'. b \<noteq> b' \<longrightarrow> (b \<bullet>\<^sub>C b') = 0) \<and> finite B' \<and> 0 \<notin> B'
   \<and> z = (\<Sum>b\<in>B'. (\<phi>' b) \<otimes>\<^sub>a b)\<close>
    using tensor_prod_expansion_right'
    by blast
  then obtain \<phi>' B' where \<open>finite B'\<close> and \<open>\<forall>b\<in>B'. \<forall>b'\<in>B'. b \<noteq> b' \<longrightarrow> (b \<bullet>\<^sub>C b') = 0\<close> and \<open>finite B'\<close>
    and \<open>0 \<notin> B'\<close> and \<open>z = (\<Sum>b\<in>B'. (\<phi>' b) \<otimes>\<^sub>a b)\<close>
    by blast
  define B where \<open>B = (\<lambda> b. b/\<^sub>C(norm b)) ` B'\<close>
  have \<open>0 \<notin> B\<close>
    unfolding B_def
    using \<open>0 \<notin> B'\<close>
    by auto
  have \<open>inj_on (\<lambda> b. b/\<^sub>C(norm b)) B'\<close>
  proof
    show "x = y"
      if "x \<in> B'"
        and "y \<in> B'"
        and "(x::'b) /\<^sub>C complex_of_real (norm x) = y /\<^sub>C complex_of_real (norm y)"
      for x :: 'b
        and y :: 'b
    proof-
      have \<open>y \<noteq> 0\<close>
        using that(2) \<open>0 \<notin> B'\<close>
        by auto
      have \<open>x \<noteq> 0\<close>
        using that(1) \<open>0 \<notin> B'\<close>
        by auto
      have \<open>((x /\<^sub>C complex_of_real (norm x)) \<bullet>\<^sub>C y) = ((y /\<^sub>C complex_of_real (norm y)) \<bullet>\<^sub>C y)\<close>
        using that(3) by simp
      have \<open>(cnj (inverse (complex_of_real (norm x)))) * (x \<bullet>\<^sub>C y) 
          = (cnj (inverse (complex_of_real (norm y)))) * (y \<bullet>\<^sub>C y)\<close>
        using \<open>((x /\<^sub>C complex_of_real (norm x)) \<bullet>\<^sub>C y) = ((y /\<^sub>C complex_of_real (norm y)) \<bullet>\<^sub>C y)\<close> by auto
      moreover have \<open>(y \<bullet>\<^sub>C y) \<noteq> 0\<close>
        using \<open>y \<noteq> 0\<close>
        by simp
      moreover have \<open>(cnj (inverse (complex_of_real (norm y)))) \<noteq> 0\<close>
        using  \<open>y \<noteq> 0\<close>
        by simp
      moreover have \<open>(cnj (inverse (complex_of_real (norm x)))) \<noteq> 0\<close>
        using  \<open>x \<noteq> 0\<close>
        by simp
      ultimately have \<open>(x \<bullet>\<^sub>C y) \<noteq> 0\<close>
        by auto
      thus ?thesis
        using \<open>\<forall>b\<in>B'. \<forall>b'\<in>B'. b \<noteq> b' \<longrightarrow> (b \<bullet>\<^sub>C b') = 0\<close>
          that(1) that(2) by blast
    qed
  qed
  hence \<open>\<exists> f. \<forall> x \<in> B'. f (x/\<^sub>C(norm x)) = x\<close>
    by (metis (no_types, lifting) the_inv_into_f_eq)
  then obtain f where \<open>\<forall> x \<in> B'. f (x/\<^sub>C(norm x)) = x\<close>
    by blast
  hence \<open>inj_on f B\<close>
    unfolding B_def
    by (simp add: inj_on_def)
  define \<phi>::\<open>'b \<Rightarrow> 'a\<close> where \<open>\<phi> b = ((norm (f b)) *\<^sub>C (\<phi>' (f b)))\<close> for b
  have  \<open>b\<in>B' \<Longrightarrow> norm b \<noteq> 0\<close>
    for b
    using \<open>0 \<notin> B'\<close>
    by auto
  hence f1: \<open>b\<in>B' \<Longrightarrow>  b = (norm b) *\<^sub>C b/\<^sub>C(norm b)\<close>
    for b
    by simp
  have \<open>finite B\<close>
    unfolding B_def
    by (simp add: \<open>finite B'\<close>)
  moreover have \<open>b\<in>B \<Longrightarrow> b'\<in>B \<Longrightarrow> b \<noteq> b' \<Longrightarrow> (b \<bullet>\<^sub>C b') = 0\<close>
    for b b'
  proof-
    assume \<open>b\<in>B\<close> and \<open>b'\<in>B\<close> and \<open>b \<noteq> b'\<close>
    from \<open>b\<in>B\<close>
    have \<open>\<exists> bb \<in> B'. b = bb/\<^sub>C(norm bb)\<close>
      using B_def by blast
    then obtain bb where \<open>bb \<in> B'\<close> and \<open>b = bb/\<^sub>C(norm bb)\<close>
      by blast
    from \<open>b'\<in>B\<close>
    have \<open>\<exists> bb' \<in> B'. b' = bb'/\<^sub>C(norm bb')\<close>
      using B_def by blast
    then obtain bb' where \<open>bb' \<in> B'\<close> and \<open>b' = bb'/\<^sub>C(norm bb')\<close>
      by blast
    have \<open>(b \<bullet>\<^sub>C b') = (bb/\<^sub>C(norm bb)) \<bullet>\<^sub>C (bb'/\<^sub>C(norm bb'))\<close>
      by (simp add: \<open>b = bb /\<^sub>C complex_of_real (norm bb)\<close> \<open>b' = bb' /\<^sub>C complex_of_real (norm bb')\<close>)
    also have \<open>\<dots> = (cnj (inverse (norm bb))) * (inverse (norm bb')) * (bb \<bullet>\<^sub>C bb')\<close>
      by simp
    also have \<open>\<dots> = 0\<close>
    proof-
      have \<open>bb \<noteq> bb'\<close>
        using \<open>b = bb /\<^sub>C complex_of_real (norm bb)\<close> \<open>b \<noteq> b'\<close> \<open>b' = bb' /\<^sub>C complex_of_real (norm bb')\<close> 
        by auto
      hence \<open>(bb \<bullet>\<^sub>C bb') = 0\<close>
        using \<open>\<forall>b\<in>B'. \<forall>b'\<in>B'. b \<noteq> b' \<longrightarrow> (b \<bullet>\<^sub>C b') = 0\<close> \<open>bb \<in> B'\<close> \<open>bb' \<in> B'\<close> 
        by auto
      thus ?thesis by simp
    qed
    finally show ?thesis by blast
  qed
  moreover have \<open>b\<in>B \<Longrightarrow> norm b = 1\<close>
    for b
  proof-
    assume \<open>b\<in>B\<close>
    hence \<open>\<exists> bb\<in>B'. b = bb /\<^sub>C (norm bb)\<close>
      unfolding B_def by auto
    then obtain bb where \<open>bb\<in>B'\<close> and \<open>b = bb /\<^sub>C (norm bb)\<close>
      by blast
    have \<open>norm b = norm (bb /\<^sub>C (norm bb))\<close>
      using  \<open>b = bb /\<^sub>C (norm bb)\<close> by simp
    also have \<open>norm (bb /\<^sub>C (norm bb)) = (norm bb) /\<^sub>C (norm bb)\<close>
      by (simp add: norm_inverse)      
    finally have \<open>norm b = (norm bb) /\<^sub>C (norm bb)\<close>
      by blast
    moreover have \<open>norm bb \<noteq> 0\<close>
      using \<open>\<And>b. b \<in> B' \<Longrightarrow> norm b \<noteq> 0\<close> \<open>bb \<in> B'\<close> by auto
    ultimately show ?thesis by auto
  qed
  moreover have \<open>z = (\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b)\<close>
  proof-
    from  \<open>z = (\<Sum>b\<in>B'. (\<phi>' b) \<otimes>\<^sub>a b)\<close>
    have  \<open>z = (\<Sum>b\<in>B'. (\<phi>' b) \<otimes>\<^sub>a ((norm b) *\<^sub>C b/\<^sub>C(norm b)))\<close>
      using f1 by simp
    also have  \<open>\<dots> = (\<Sum>b\<in>B'. (norm b) *\<^sub>C ((\<phi>' b) \<otimes>\<^sub>a (b/\<^sub>C(norm b))))\<close>
      by (metis (no_types, lifting) atensor_mult_right complex_vector.scale_left_commute)
    also have  \<open>\<dots> = (\<Sum>b\<in>B'. ((norm b) *\<^sub>C (\<phi>' b)) \<otimes>\<^sub>a (b/\<^sub>C(norm b)))\<close>
      by (simp add: atensor_mult_left)
    also have  \<open>\<dots> = (\<Sum>b\<in>B'. ((norm (f (b/\<^sub>C(norm b)))) *\<^sub>C (\<phi>' (f (b/\<^sub>C(norm b))))) \<otimes>\<^sub>a (b/\<^sub>C(norm b)))\<close>
      using \<open>\<forall> x \<in> B'. f (x/\<^sub>C(norm x)) = x\<close>
      by auto
    also have  \<open>\<dots> = (\<Sum>b\<in>B. ((norm (f b)) *\<^sub>C (\<phi>' (f b))) \<otimes>\<^sub>a b)\<close>
      by (metis (no_types, lifting) B_def \<open>inj_on (\<lambda>b. b /\<^sub>C complex_of_real (norm b)) B'\<close> sum.reindex_cong)
    also have  \<open>\<dots> = (\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b)\<close>
      unfolding \<phi>_def by blast
    finally show ?thesis by blast
  qed
  ultimately show ?thesis by blast
qed

lemma algebraic_tensor_product_bounded_left:
  assumes \<open>bounded_clinear f\<close>
  shows \<open>bounded_clinear (f \<otimes>\<^sub>A (id::('c::complex_inner \<Rightarrow> _))) \<and> onorm (f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) \<le> onorm f\<close>
proof-
  define K where \<open>K = onorm f\<close>
  have f_clinear: \<open>clinear (f \<otimes>\<^sub>A (id::'c \<Rightarrow> _))\<close>
    using assms atensorOp_clinear bounded_clinear_def complex_vector.module_hom_id by blast
  moreover have  "\<forall>z. norm ((f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) z) \<le> norm z * K"
  proof-
    have id_clinear: \<open>clinear (id::'c \<Rightarrow> _)\<close>
      by (simp add: complex_vector.module_hom_id)
    have \<open>K \<ge> 0\<close>
      unfolding K_def
      using onorm_pos_le \<open>bounded_clinear f\<close>
      by (simp add: onorm_pos_le bounded_clinear.bounded_linear)
    have \<open>\<And> z. norm (f z) \<le> norm z * K\<close>
      unfolding K_def
      using \<open>bounded_clinear f\<close>
       bounded_clinear.bounded_linear onorm
      by (simp add: bounded_clinear.bounded_linear onorm algebra_simps)

    have \<open>z \<in> range (case_prod (\<otimes>\<^sub>a)) \<Longrightarrow> norm ((f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) z) \<le> norm z * K\<close>
      for z
    proof-
      assume \<open>z \<in> range (case_prod (\<otimes>\<^sub>a))\<close>
      hence \<open>\<exists> x y. z = x \<otimes>\<^sub>a y\<close>
        by (simp add: image_iff)
      then obtain x y where \<open>z = x \<otimes>\<^sub>a y\<close>
        by blast
      hence \<open>(f \<otimes>\<^sub>A id) z = (f x) \<otimes>\<^sub>a (id y)\<close>
        using f_clinear id_clinear
        by (simp add: assms atensorOp_separation bounded_clinear.clinear)
      also have \<open>\<dots> = (f x) \<otimes>\<^sub>a y\<close>
        by simp
      finally have \<open>(f \<otimes>\<^sub>A id) z = (f x) \<otimes>\<^sub>a y\<close>
        by blast
      hence \<open>norm ((f \<otimes>\<^sub>A id) z) = norm ((f x) \<otimes>\<^sub>a y)\<close>
        by simp
      also have \<open>\<dots> = norm (f x) * norm y\<close>
        by (simp add: atensor_norm_mult)
      also have \<open>\<dots> \<le> (norm x * K) * norm y\<close>
        by (simp add: \<open>\<And>z. norm (f z) \<le> norm z * K\<close> mult_mono')
      also have \<open>\<dots> = (norm x * norm y) * K\<close>
        by auto
      also have \<open>\<dots> = norm (x \<otimes>\<^sub>a y) * K\<close>
      proof-
        have \<open>norm (x \<otimes>\<^sub>a y) = norm x * norm y\<close>
          by (simp add: atensor_norm_mult)          
        thus ?thesis by simp
      qed
      also have \<open>\<dots> = norm z * K\<close>
        by (simp add: \<open>z = x \<otimes>\<^sub>a y\<close>)
      finally show ?thesis by blast
    qed
    have \<open>norm ((f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) z) \<le> norm z * K\<close>
      for z
    proof-
      have  \<open>\<exists> \<phi> B. finite B \<and> (\<forall>b\<in>B. \<forall>b'\<in>B. b \<noteq> b' \<longrightarrow> (b \<bullet>\<^sub>C b') = 0) \<and> (\<forall>b\<in>B. norm b = 1)
           \<and> z = (\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b)\<close>
        by (simp add: tensor_prod_expansion_right)
      then obtain \<phi> B where \<open>finite B\<close> and \<open>\<forall>b\<in>B. \<forall>b'\<in>B. b \<noteq> b' \<longrightarrow> (b \<bullet>\<^sub>C b') = 0\<close>
        and \<open>\<forall>b\<in>B. norm b = 1\<close> and \<open>z = (\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b)\<close>
        by blast
      from \<open>z = (\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b)\<close>
      have \<open>(f \<otimes>\<^sub>A id) z = (\<Sum>b\<in>B. (f \<otimes>\<^sub>A id) ((\<phi> b) \<otimes>\<^sub>a b))\<close>
        using \<open>clinear (f \<otimes>\<^sub>A id)\<close> complex_vector.linear_sum 
        by blast
      also have \<open>\<dots> = (\<Sum>b\<in>B. (f (\<phi> b)) \<otimes>\<^sub>a b)\<close>
      proof-
        have \<open>(f \<otimes>\<^sub>A id) ((\<phi> b) \<otimes>\<^sub>a b) = (f (\<phi> b)) \<otimes>\<^sub>a b\<close> for b
          by (simp add: assms atensorOp_separation bounded_clinear.clinear complex_vector.module_hom_id)
        thus ?thesis by simp
      qed
      finally have \<open>(f \<otimes>\<^sub>A id) z = (\<Sum>b\<in>B. (f (\<phi> b)) \<otimes>\<^sub>a b)\<close>
        by blast
      hence \<open>(norm ((f \<otimes>\<^sub>A id) z))^2 = (norm (\<Sum>b\<in>B. (f (\<phi> b)) \<otimes>\<^sub>a b))^2\<close>
        by simp
      also have \<open>\<dots>  = (\<Sum>b\<in>B. (f (\<phi> b)) \<otimes>\<^sub>a b) \<bullet>\<^sub>C (\<Sum>b'\<in>B. (f (\<phi> b')) \<otimes>\<^sub>a b')\<close>
        by (simp add: cdot_square_norm)
      also have \<open>\<dots>  = (\<Sum>b'\<in>B. (\<Sum>b\<in>B. (f (\<phi> b)) \<otimes>\<^sub>a b) \<bullet>\<^sub>C (f (\<phi> b') \<otimes>\<^sub>a b'))\<close>
        using cinner_sum_right by auto
      also have \<open>\<dots>  = (\<Sum>b'\<in>B. (\<Sum>b\<in>B. (f (\<phi> b) \<otimes>\<^sub>a b) \<bullet>\<^sub>C (f (\<phi> b') \<otimes>\<^sub>a b')))\<close>
        by (simp add: cinner_sum_left)
      also have \<open>\<dots>  = (\<Sum>b'\<in>B. (\<Sum>b\<in>B. (f (\<phi> b) \<bullet>\<^sub>C f (\<phi> b'))* (b \<bullet>\<^sub>C b')))\<close>
      proof-
        have \<open>(f (\<phi> b) \<otimes>\<^sub>a b) \<bullet>\<^sub>C (f (\<phi> b') \<otimes>\<^sub>a b') = (f (\<phi> b) \<bullet>\<^sub>C f (\<phi> b')) * (b \<bullet>\<^sub>C b')\<close>
          for b b'
          by (simp add: atensor_cinner_mult)
        thus ?thesis by simp
      qed
      also have \<open>\<dots>  = (\<Sum>b\<in>B. f (\<phi> b) \<bullet>\<^sub>C f (\<phi> b))\<close>
      proof-
        have \<open>b' \<in> B \<Longrightarrow> (\<Sum>b\<in>B. (f (\<phi> b)  \<bullet>\<^sub>C f (\<phi> b')) * (b \<bullet>\<^sub>C b')) = (f (\<phi> b') \<bullet>\<^sub>C f (\<phi> b'))\<close>
          for b'
        proof-
          assume \<open>b' \<in> B\<close>
          hence \<open>(\<Sum>b\<in>B. (f (\<phi> b) \<bullet>\<^sub>C f (\<phi> b'))*(b \<bullet>\<^sub>C b')) = 
             (f (\<phi> b') \<bullet>\<^sub>C f (\<phi> b'))* (b' \<bullet>\<^sub>C b')
          + (\<Sum>b\<in>B-{b'}. (f (\<phi> b) \<bullet>\<^sub>C f (\<phi> b'))*(b \<bullet>\<^sub>C b'))\<close>
            by (meson \<open>finite B\<close> sum.remove)
          moreover have \<open>(b' \<bullet>\<^sub>C b') = 1\<close>
          proof-
            have \<open>norm b' = 1\<close>
              using \<open>b' \<in> B\<close> \<open>\<forall>b\<in>B. norm b = 1\<close>
              by blast
            thus ?thesis
              by (meson \<open>norm b' = 1\<close> cnorm_eq_1)
          qed
          moreover have \<open>(\<Sum>b\<in>B-{b'}. (f (\<phi> b) \<bullet>\<^sub>C f (\<phi> b'))*(b \<bullet>\<^sub>C b')) = 0\<close>
          proof-
            have \<open>b\<in>B-{b'} \<Longrightarrow> (f (\<phi> b) \<bullet>\<^sub>C f (\<phi> b'))*(b \<bullet>\<^sub>C b') = 0\<close>
              for b
            proof-
              assume \<open>b\<in>B-{b'}\<close>
              hence \<open>b \<noteq> b'\<close>
                by simp
              hence \<open>(b \<bullet>\<^sub>C b') = 0\<close>
                using \<open>\<forall>b\<in>B. \<forall>b'\<in>B. b \<noteq> b' \<longrightarrow> (b \<bullet>\<^sub>C b') = 0\<close> \<open>b \<in> B - {b'}\<close> \<open>b' \<in> B\<close> 
                by auto
              thus ?thesis
                by simp 
            qed
            thus ?thesis
              by (meson sum.not_neutral_contains_not_neutral)
          qed
          ultimately show ?thesis by simp
        qed
        thus ?thesis by simp
      qed
      also have \<open>\<dots>  = (\<Sum>b\<in>B. (norm (f (\<phi> b)))^2 )\<close>
        by (metis (mono_tags, lifting) cdot_square_norm of_real_sum sum.cong)
      also have \<open>\<dots>  \<le> (\<Sum>b\<in>B. (norm (\<phi> b))^2 * K^2 )\<close>
      proof-
        have \<open>(norm (f (\<phi> b)))^2 \<le> (norm (\<phi> b))^2 * K^2\<close>
          for b
          by (metis \<open>\<And>z. norm (f z) \<le> norm z * K\<close> norm_ge_zero power_mono semiring_normalization_rules(30))          
        thus ?thesis
          by (smt (verit, best) Re_complex_of_real \<open>(\<Sum>b\<in>B. cinner (f (\<phi> b)) (f (\<phi> b))) = complex_of_real (\<Sum>b\<in>B. (norm (f (\<phi> b)))\<^sup>2)\<close> cinner_ge_zero complex_of_real_cmod complex_of_real_mono norm_of_real power2_norm_eq_cinner' sum_norm_le)
      qed
      also have \<open>\<dots>  = (\<Sum>b\<in>B. (norm (\<phi> b))^2) * K^2\<close>
        by (simp add: sum_distrib_right)
      also have \<open>\<dots>  = (norm z)^2 * K^2\<close>
      proof-
        have \<open>(norm z)^2 = (\<Sum>b\<in>B. (norm (\<phi> b))^2)\<close>
        proof-
          have \<open>(norm z)^2 = (norm (\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b))^2\<close>
            using \<open>z = (\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b)\<close> 
            by simp
          also have \<open>\<dots> = ((\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b) \<bullet>\<^sub>C (\<Sum>b\<in>B. (\<phi> b) \<otimes>\<^sub>a b))\<close>
            by (simp add: cdot_square_norm)
          also have \<open>\<dots> = (\<Sum>b\<in>B. ((\<phi> b) \<otimes>\<^sub>a b) \<bullet>\<^sub>C (\<Sum>b'\<in>B. (\<phi> b') \<otimes>\<^sub>a b'))\<close>
            using cinner_sum_left by auto
          also have \<open>\<dots> = (\<Sum>b\<in>B. (\<Sum>b'\<in>B. (\<phi> b \<otimes>\<^sub>a b) \<bullet>\<^sub>C (\<phi> b' \<otimes>\<^sub>a b')))\<close>
            by (metis (mono_tags, lifting) cinner_sum_right sum.cong)
          also have \<open>\<dots> = (\<Sum>b\<in>B. (\<Sum>b'\<in>B. (\<phi> b \<bullet>\<^sub>C \<phi> b')*(b \<bullet>\<^sub>C b')))\<close>
            by (meson atensor_cinner_mult sum.cong)
          also have \<open>\<dots> = (\<Sum>b\<in>B. (\<phi> b \<bullet>\<^sub>C \<phi> b))\<close>
          proof-
            have \<open>b \<in> B \<Longrightarrow> (\<Sum>b'\<in>B. (\<phi> b \<bullet>\<^sub>C \<phi> b')*(b \<bullet>\<^sub>C b')) = (\<phi> b \<bullet>\<^sub>C \<phi> b)\<close>
              for b
            proof-
              assume \<open>b \<in> B\<close>
              hence \<open>(\<Sum>b'\<in>B. (\<phi> b \<bullet>\<^sub>C \<phi> b')*(b \<bullet>\<^sub>C b')) = (\<phi> b \<bullet>\<^sub>C \<phi> b)*(b \<bullet>\<^sub>C b)
                + (\<Sum>b'\<in>B-{b}. (\<phi> b \<bullet>\<^sub>C \<phi> b')*(b \<bullet>\<^sub>C b'))\<close>
                by (meson \<open>finite B\<close> sum.remove)
              moreover have \<open>(b \<bullet>\<^sub>C b) = 1\<close>
              proof-
                have \<open>norm b = 1\<close>
                  by (simp add: \<open>\<forall>b\<in>B. norm b = 1\<close> \<open>b \<in> B\<close>)
                hence \<open>(norm b)^2 = 1\<close>
                  by simp
                thus ?thesis
                  by (simp add: cdot_square_norm)
              qed
              moreover have \<open>(\<Sum>b'\<in>B-{b}. (\<phi> b \<bullet>\<^sub>C \<phi> b')*(b \<bullet>\<^sub>C b')) = 0\<close>
              proof-
                have \<open>b'\<in>B-{b} \<Longrightarrow>  (\<phi> b \<bullet>\<^sub>C \<phi> b')*(b \<bullet>\<^sub>C b') = 0\<close>
                  for b'
                proof-
                  assume \<open>b'\<in>B-{b}\<close>
                  hence \<open>b' \<noteq> b\<close>
                    by simp
                  hence \<open>(b \<bullet>\<^sub>C b') = 0\<close>
                    using \<open>\<forall>b\<in>B. \<forall>b'\<in>B. b \<noteq> b' \<longrightarrow> (b \<bullet>\<^sub>C b') = 0\<close> \<open>b \<in> B\<close> \<open>b' \<in> B - {b}\<close> 
                    by auto
                  thus ?thesis by simp
                qed
                thus ?thesis
                  by (simp add: \<open>\<And>b'. b' \<in> B - {b} \<Longrightarrow> (\<phi> b \<bullet>\<^sub>C \<phi> b') * (b \<bullet>\<^sub>C b') = 0\<close>) 
              qed
              ultimately show ?thesis by simp
            qed
            thus ?thesis by simp
          qed
          also have \<open>\<dots> = (\<Sum>b\<in>B. (norm (\<phi> b))^2 )\<close>
          proof-
            have \<open>(\<phi> b \<bullet>\<^sub>C \<phi> b) = (norm (\<phi> b))^2\<close> for b
              by (simp add: cdot_square_norm)
            hence \<open>(\<Sum>b\<in>B. (\<phi> b \<bullet>\<^sub>C \<phi> b)) = (\<Sum>b\<in>B. complex_of_real ((norm (\<phi> b))\<^sup>2))\<close>
              by simp
            also have \<open>\<dots> = complex_of_real (\<Sum>b\<in>B. ((norm (\<phi> b))\<^sup>2))\<close>
              using \<open>finite B\<close>
              by simp
            finally show ?thesis by blast
          qed
          finally have \<open>complex_of_real ((norm z)\<^sup>2) =
            complex_of_real (\<Sum>b\<in>B. (norm (\<phi> b))\<^sup>2)\<close>
            by blast
          thus ?thesis
            using of_real_eq_iff by blast            
        qed
        thus ?thesis by simp
      qed
      also have \<open>\<dots>  = ((norm z) * K)^2\<close>
        by (simp add: power_mult_distrib)
      finally have \<open>(norm ((f \<otimes>\<^sub>A id) z))^2 \<le> ((norm z) * K)^2\<close>
        using complex_of_real_mono_iff by blast
      moreover have \<open>norm ((f \<otimes>\<^sub>A id) z) \<ge> 0\<close>
        by simp        
      moreover have \<open>(norm z) * K \<ge> 0\<close>
        using \<open>K \<ge> 0\<close> by auto        
      ultimately show ?thesis
        by (simp add: \<open>(norm ((f \<otimes>\<^sub>A id) z))\<^sup>2 \<le> (norm z * K)\<^sup>2\<close> \<open>0 \<le> norm z * K\<close> power2_le_imp_le) 
    qed
    thus ?thesis
      by blast 
  qed
  moreover have \<open>onorm (f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) \<le> onorm f\<close>
  proof-
    have "\<forall>z. norm ((f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) z) / norm z \<le>  K"      
      by (smt (verit, ccfv_SIG) K_def assms calculation(2) bounded_clinear.bounded_linear divide_le_eq norm_ge_zero onorm_pos_le ordered_field_class.sign_simps(5))
    moreover have \<open>{norm ((f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) z) / norm z| z. True} \<noteq> {}\<close>
      by auto        
    ultimately have "Sup {norm ((f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) z) / norm z| z. True} \<le> K"
        by (smt (verit, best) cSup_least mem_Collect_eq) 
    moreover have \<open>Sup {norm ((f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) z) / norm z| z. True} =  (SUP x. norm ((f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) x) / norm x)\<close>
      by (simp add: full_SetCompr_eq)        
    ultimately have "(SUP x. norm ((f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) x) / norm x) \<le> K"
      by simp
    moreover have \<open>onorm (f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) = (SUP x. norm ((f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) x) / norm x)\<close>
      by (simp add: onorm_def)
    ultimately have \<open>onorm (f \<otimes>\<^sub>A (id::'c \<Rightarrow> _)) \<le> K\<close>
      by simp
    thus ?thesis unfolding K_def
      by blast
  qed
  ultimately show ?thesis
    using bounded_clinear_axioms_def bounded_clinear_def by blast
qed

lemma algebraic_tensor_product_bounded_left_bounded_clinear:
  assumes \<open>bounded_clinear f\<close>
  shows \<open>bounded_clinear (f \<otimes>\<^sub>A (id::('c::complex_inner \<Rightarrow> _)))\<close>
  using assms algebraic_tensor_product_bounded_left
  by blast

lemma algebraic_tensor_product_bounded_left_onorm:
  assumes \<open>bounded_clinear f\<close>
  shows \<open>onorm (f \<otimes>\<^sub>A (id::('c::complex_inner \<Rightarrow> _))) \<le> onorm f\<close>
  using assms algebraic_tensor_product_bounded_left
  by blast

lemma swap_atensor_bounded_clinear':
  \<open>bounded_clinear (swap_atensor::(('a::complex_inner \<otimes>\<^sub>a 'b::complex_inner) \<Rightarrow> _))
      \<and> onorm (swap_atensor::(('a::complex_inner \<otimes>\<^sub>a 'b::complex_inner) \<Rightarrow> _)) \<le> 1\<close>
proof-
  have "clinear (swap_atensor::'a \<otimes>\<^sub>a 'b \<Rightarrow> _ \<otimes>\<^sub>a _)"
    by (simp add: swap_atensorI1)
  have f1: \<open>norm (swap_atensor (x \<otimes>\<^sub>a y)) = norm (x \<otimes>\<^sub>a y)\<close>
    for x::'a and y::'b
    by (simp add: atensor_norm_mult swap_atensorI2)      
  have f2: \<open>norm (swap_atensor (z::'a \<otimes>\<^sub>a 'b)) \<le> norm z\<close>
    for z
  proof-
    have \<open>z \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
      by (simp add: atensor_onto)
    have \<open>\<exists> A B S r. finite A  \<and> finite B \<and> (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0)
  \<and> (\<forall>a\<in>B. \<forall>a'\<in>B. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0) \<and> S \<subseteq> A \<times> B \<and>
  z = (\<Sum>(a,b)\<in>S. (r (a, b)) *\<^sub>C (a \<otimes>\<^sub>a b))\<close>
      using tensor_prod_expansion by blast
    then obtain A B S r where \<open>finite A\<close> and \<open>finite B\<close> and 
      \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close> and 
      \<open>\<forall>a\<in>B. \<forall>a'\<in>B. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close> and \<open>S \<subseteq> A \<times> B\<close> and
      \<open>z = (\<Sum>(a,b)\<in>S. (r (a, b)) *\<^sub>C (a \<otimes>\<^sub>a b))\<close>
      by blast
    have \<open>finite S\<close>
      using  \<open>finite A\<close>  \<open>finite B\<close> \<open>S \<subseteq> A \<times> B\<close>
      by (meson finite_SigmaI rev_finite_subset)
    have \<open>swap_atensor z = (\<Sum>(a,b)\<in>S. (r (a, b)) *\<^sub>C swap_atensor (a \<otimes>\<^sub>a b))\<close>
      using  \<open>z = (\<Sum>(a,b)\<in>S. (r (a, b)) *\<^sub>C (a \<otimes>\<^sub>a b))\<close>
      by (smt \<open>clinear swap_atensor\<close> complex_vector.linear_scale complex_vector.linear_sum prod.case_distrib split_cong sum.cong)
    also have \<open>\<dots> = (\<Sum>(a,b)\<in>S. (r (a, b)) *\<^sub>C (b \<otimes>\<^sub>a a))\<close>
    proof-
      have \<open>swap_atensor (a \<otimes>\<^sub>a b) = b \<otimes>\<^sub>a a\<close>
        for a::'a and b::'b
        by (simp add: swap_atensorI2)          
      thus ?thesis by simp
    qed
    finally have \<open>swap_atensor z = (\<Sum>(a, b)\<in>S. r (a, b) *\<^sub>C (b \<otimes>\<^sub>a a))\<close>
      by blast
    have \<open>complex_of_real ((norm (swap_atensor z))\<^sup>2) =
    (\<Sum>(a, b)\<in>S. (cnj (r (a, b))) * (r (a, b)) * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a \<otimes>\<^sub>a b)))\<close>
    proof-
      have \<open>(norm (swap_atensor z))^2 = (norm (\<Sum>(a, b)\<in>S. r (a, b) *\<^sub>C (b \<otimes>\<^sub>a a)))^2\<close>
        using \<open>swap_atensor z = (\<Sum>(a, b)\<in>S. r (a, b) *\<^sub>C (b \<otimes>\<^sub>a a))\<close>
        by simp
      also have \<open>\<dots> = (\<Sum>(a, b)\<in>S. r (a, b) *\<^sub>C (b \<otimes>\<^sub>a a)) \<bullet>\<^sub>C (\<Sum>(a, b)\<in>S. r (a, b) *\<^sub>C (b \<otimes>\<^sub>a a))\<close>
        by (simp add: cdot_square_norm)
      also have \<open>\<dots> = (\<Sum>(a, b)\<in>S. (r (a, b) *\<^sub>C (b \<otimes>\<^sub>a a)) \<bullet>\<^sub>C (\<Sum>(a, b)\<in>S. r (a, b) *\<^sub>C (b \<otimes>\<^sub>a a)))\<close>
        by (metis (mono_tags, lifting) case_prod_conv cinner_sum_left cond_case_prod_eta)
      also have \<open>\<dots> = (\<Sum>(a, b)\<in>S. (\<Sum>(a', b')\<in>S. (r (a, b) *\<^sub>C (b \<otimes>\<^sub>a a)) \<bullet>\<^sub>C (r (a', b') *\<^sub>C (b' \<otimes>\<^sub>a a'))))\<close>
        by (smt cinner_sum_right prod.case_distrib split_cong sum.cong)
          (* > 1 s *)
      also have \<open>\<dots> = (\<Sum>(a, b)\<in>S. (\<Sum>(a', b')\<in>S. (cnj (r (a, b))) * r (a', b') * ((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b' \<otimes>\<^sub>a a'))))\<close>
      proof-
        have \<open>(\<Sum>(a', b')\<in>S. (r (a, b) *\<^sub>C (b \<otimes>\<^sub>a a)) \<bullet>\<^sub>C (r (a', b') *\<^sub>C (b' \<otimes>\<^sub>a a')))
            = (\<Sum>(a', b')\<in>S. (cnj (r (a, b))) * r (a', b') * ((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b' \<otimes>\<^sub>a a')))\<close>
          for a b
        proof-
          have \<open>(r (a, b) *\<^sub>C (b \<otimes>\<^sub>a a)) \<bullet>\<^sub>C (r (a', b') *\<^sub>C (b' \<otimes>\<^sub>a a')) = 
              (cnj (r (a, b))) * r (a', b') * ((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b' \<otimes>\<^sub>a a'))\<close>
            for a' b'
            by simp            
          thus ?thesis
            by presburger 
        qed
        thus ?thesis by simp
      qed
      also have \<open>\<dots> = (\<Sum>(a, b)\<in>S. (cnj (r (a, b))) * r (a, b) * ((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b \<otimes>\<^sub>a a)))\<close>
      proof-
        have \<open>(a,b) \<in> S \<Longrightarrow> (\<Sum>(a', b')\<in>S. (cnj (r (a, b))) * r (a', b') * ((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b' \<otimes>\<^sub>a a'))) = 
              (cnj (r (a, b))) * r (a, b) * ((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b \<otimes>\<^sub>a a))\<close>
          for a b
        proof-
          assume \<open>(a,b) \<in> S\<close>
          hence \<open>(a, b) \<in> A\<times>B\<close>
            using \<open>S \<subseteq> A \<times> B\<close> by auto
          hence \<open>a \<in> A\<close>
            by simp
          from \<open>(a, b) \<in> A\<times>B\<close>
          have \<open>b \<in> B\<close>
            by simp
          have  \<open>(\<Sum>(a', b')\<in>S. (cnj (r (a, b))) * r (a', b') * ((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b' \<otimes>\<^sub>a a')))
  = (cnj (r (a, b))) * r (a, b) * ((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b \<otimes>\<^sub>a a))
  + (\<Sum>(a', b')\<in>S-{(a, b)}. (cnj (r (a, b))) * r (a', b') * ((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b' \<otimes>\<^sub>a a')))\<close>
            using \<open>finite S\<close> \<open>(a,b) \<in> S\<close>
            by (metis (no_types, lifting) case_prod_conv sum.remove)
          moreover have \<open>(\<Sum>(a', b')\<in>S-{(a, b)}. (cnj (r (a, b))) * r (a', b') * ((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b' \<otimes>\<^sub>a a'))) = 0\<close>
          proof-
            have \<open>(a', b')\<in>S-{(a, b)} \<Longrightarrow> (cnj (r (a, b))) * r (a', b') * ((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b' \<otimes>\<^sub>a a')) = 0\<close>
              for a' b'
            proof-
              assume \<open>(a', b')\<in>S-{(a, b)}\<close>
              hence \<open>(a', b') \<in> A\<times>B\<close>
                using \<open>S \<subseteq> A \<times> B\<close> by auto
              hence \<open>a' \<in> A\<close>
                by simp
              from \<open>(a', b') \<in> A\<times>B\<close>
              have \<open>b' \<in> B\<close>
                by simp
              have \<open>(a', b') \<noteq> (a, b)\<close>
                using \<open>(a', b')\<in>S-{(a, b)}\<close>
                by simp
              hence \<open>a' \<noteq> a \<or> b' \<noteq> b\<close>
                by simp
              moreover have \<open>((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b' \<otimes>\<^sub>a a')) = (b \<bullet>\<^sub>C b') * (a \<bullet>\<^sub>C a')\<close>
                by (simp add: atensor_cinner_mult)
              moreover have \<open>b \<noteq> b' \<Longrightarrow> (b \<bullet>\<^sub>C b') = 0\<close>
                using  \<open>b \<in> B\<close> \<open>b' \<in> B\<close> \<open>\<forall>a\<in>B. \<forall>a'\<in>B. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close>
                by simp
              moreover have \<open>a \<noteq> a' \<Longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close>
                using  \<open>a \<in> A\<close> \<open>a' \<in> A\<close> \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close>
                by simp
              ultimately have \<open>((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b' \<otimes>\<^sub>a a')) = 0\<close>
                by auto
              thus ?thesis
                by simp 
            qed
            hence \<open>\<forall> (a', b')\<in>S-{(a, b)}. (cnj (r (a, b))) * r (a', b') * ((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b' \<otimes>\<^sub>a a')) = 0\<close>
              by blast
            thus ?thesis
              by (smt case_prodE case_prod_conv sum.not_neutral_contains_not_neutral) 
          qed
          ultimately show ?thesis by simp
        qed
        thus ?thesis
          by (metis (no_types, lifting) split_cong sum.cong) 
      qed
      also have \<open>\<dots> =
  (\<Sum>(a, b)\<in>S. cnj (r (a, b)) * r (a, b) * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a \<otimes>\<^sub>a b)))\<close>
      proof-
        have \<open>((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b \<otimes>\<^sub>a a)) = ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a \<otimes>\<^sub>a b))\<close>
          for a::'a and b::'b
        proof-
          have \<open>((b \<otimes>\<^sub>a a) \<bullet>\<^sub>C (b \<otimes>\<^sub>a a)) = (b \<bullet>\<^sub>C b) * (a \<bullet>\<^sub>C a)\<close>
            by (simp add: atensor_cinner_mult)            
          moreover have \<open>((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a \<otimes>\<^sub>a b)) = (a \<bullet>\<^sub>C a) * (b \<bullet>\<^sub>C b)\<close>
            by (simp add: atensor_cinner_mult)            
          ultimately show ?thesis by simp
        qed
        thus ?thesis by simp
      qed
      finally show ?thesis by blast
    qed
    moreover have \<open>complex_of_real ((norm  z)\<^sup>2) =
  (\<Sum>(a, b)\<in>S. cnj (r (a, b)) * r (a, b) * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a \<otimes>\<^sub>a b)))\<close>
    proof-
      have \<open>(norm  z)^2 = (norm (\<Sum>(a, b)\<in>S. r (a, b) *\<^sub>C (a \<otimes>\<^sub>a b)))^2\<close>
        using \<open>z = (\<Sum>(a, b)\<in>S. r (a, b) *\<^sub>C (a \<otimes>\<^sub>a b))\<close>
        by simp
      also have \<open>\<dots> = (\<Sum>(a, b)\<in>S. r (a, b) *\<^sub>C (a \<otimes>\<^sub>a b)) \<bullet>\<^sub>C (\<Sum>(a, b)\<in>S. r (a, b) *\<^sub>C (a \<otimes>\<^sub>a b))\<close>
        by (simp add: cdot_square_norm)
      also have \<open>\<dots> = (\<Sum>(a, b)\<in>S. (r (a, b) *\<^sub>C (a \<otimes>\<^sub>a b)) \<bullet>\<^sub>C (\<Sum>(a, b)\<in>S. r (a, b) *\<^sub>C (a \<otimes>\<^sub>a b)))\<close>
        by (metis (mono_tags, lifting) case_prod_conv cinner_sum_left cond_case_prod_eta)
      also have \<open>\<dots> = (\<Sum>(a, b)\<in>S. (\<Sum>(a', b')\<in>S. (r (a, b) *\<^sub>C (a \<otimes>\<^sub>a b)) \<bullet>\<^sub>C r (a', b') *\<^sub>C (a' \<otimes>\<^sub>a b')))\<close>
        by (smt cinner_sum_right prod.case_distrib split_cong sum.cong)
          (* > 1 s *)
      also have \<open>\<dots> = (\<Sum>(a, b)\<in>S. (\<Sum>(a', b')\<in>S. (cnj (r (a, b))) * r (a', b') * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a' \<otimes>\<^sub>a b'))))\<close>
      proof-
        have \<open>(\<Sum>(a', b')\<in>S. (r (a, b) *\<^sub>C (a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (r (a', b') *\<^sub>C (a' \<otimes>\<^sub>a b'))))
            = (\<Sum>(a', b')\<in>S. (cnj (r (a, b))) * r (a', b') * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a' \<otimes>\<^sub>a b')))\<close>
          for a b
        proof-
          have \<open>(r (a, b) *\<^sub>C (a \<otimes>\<^sub>a b)) \<bullet>\<^sub>C (r (a', b') *\<^sub>C (a' \<otimes>\<^sub>a b')) = 
              (cnj (r (a, b))) * r (a', b') * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a' \<otimes>\<^sub>a b'))\<close>
            for a' b'
            by simp            
          thus ?thesis
            by presburger 
        qed
        thus ?thesis by simp
      qed
      also have \<open>\<dots> = (\<Sum>(a, b)\<in>S. (cnj (r (a, b))) * r (a, b) * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a \<otimes>\<^sub>a b)))\<close>
      proof-
        have \<open>(a,b) \<in> S \<Longrightarrow> (\<Sum>(a', b')\<in>S. (cnj (r (a, b))) * r (a', b') * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a' \<otimes>\<^sub>a b'))) = 
              (cnj (r (a, b))) * r (a, b) * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a \<otimes>\<^sub>a b))\<close>
          for a b
        proof-
          assume \<open>(a,b) \<in> S\<close>
          hence \<open>(a, b) \<in> A\<times>B\<close>
            using \<open>S \<subseteq> A \<times> B\<close> by auto
          hence \<open>a \<in> A\<close>
            by simp
          from \<open>(a, b) \<in> A\<times>B\<close>
          have \<open>b \<in> B\<close>
            by simp
          have  \<open>(\<Sum>(a', b')\<in>S. (cnj (r (a, b))) * r (a', b') * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a' \<otimes>\<^sub>a b')))
  = (cnj (r (a, b))) * r (a, b) * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a \<otimes>\<^sub>a b))
  + (\<Sum>(a', b')\<in>S-{(a, b)}. (cnj (r (a, b))) * r (a', b') * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a' \<otimes>\<^sub>a b')))\<close>
            using \<open>finite S\<close> \<open>(a,b) \<in> S\<close>
            by (metis (no_types, lifting) case_prod_conv sum.remove)
          moreover have \<open>(\<Sum>(a', b')\<in>S-{(a, b)}. (cnj (r (a, b))) * r (a', b') * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a' \<otimes>\<^sub>a b'))) = 0\<close>
          proof-
            have \<open>(a', b')\<in>S-{(a, b)} \<Longrightarrow> (cnj (r (a, b))) * r (a', b') * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a' \<otimes>\<^sub>a b')) = 0\<close>
              for a' b'
            proof-
              assume \<open>(a', b')\<in>S-{(a, b)}\<close>
              hence \<open>(a', b') \<in> A\<times>B\<close>
                using \<open>S \<subseteq> A \<times> B\<close> by auto
              hence \<open>a' \<in> A\<close>
                by simp
              from \<open>(a', b') \<in> A\<times>B\<close>
              have \<open>b' \<in> B\<close>
                by simp
              have \<open>(a', b') \<noteq> (a, b)\<close>
                using \<open>(a', b')\<in>S-{(a, b)}\<close>
                by simp
              hence \<open>a' \<noteq> a \<or> b' \<noteq> b\<close>
                by simp
              moreover have \<open>((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a' \<otimes>\<^sub>a b')) = (a \<bullet>\<^sub>C a') * (b \<bullet>\<^sub>C b')\<close>
                by (simp add: atensor_cinner_mult)
              moreover have \<open>b \<noteq> b' \<Longrightarrow> (b \<bullet>\<^sub>C b') = 0\<close>
                using  \<open>b \<in> B\<close> \<open>b' \<in> B\<close> \<open>\<forall>a\<in>B. \<forall>a'\<in>B. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close>
                by simp
              moreover have \<open>a \<noteq> a' \<Longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close>
                using  \<open>a \<in> A\<close> \<open>a' \<in> A\<close> \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> (a \<bullet>\<^sub>C a') = 0\<close>
                by simp
              ultimately have \<open>((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a' \<otimes>\<^sub>a b')) = 0\<close>
                by auto
              thus ?thesis
                by simp 
            qed
            hence \<open>\<forall> (a', b')\<in>S-{(a, b)}. (cnj (r (a, b))) * r (a', b') * ((a \<otimes>\<^sub>a b) \<bullet>\<^sub>C (a' \<otimes>\<^sub>a b')) = 0\<close>
              by blast
            thus ?thesis
              by (smt case_prodE case_prod_conv sum.not_neutral_contains_not_neutral) 
          qed
          ultimately show ?thesis by simp
        qed
        thus ?thesis
          by (metis (no_types, lifting) split_cong sum.cong) 
      qed
      finally show ?thesis by simp
    qed
    ultimately show ?thesis
      by (smt (verit) cnorm_le_square)
  qed

  have \<open>bounded_clinear (swap_atensor::(('a \<otimes>\<^sub>a 'b) \<Rightarrow> _))\<close>
    by (metis bounded_clinear_axioms.intro bounded_clinear_def f2 mult.commute mult.left_neutral swap_atensorI1)
  moreover have \<open>onorm (swap_atensor::(('a \<otimes>\<^sub>a 'b) \<Rightarrow> _)) \<le> 1\<close>
    using f2
    by (simp add: onorm_bound)
  ultimately show ?thesis by blast
qed

lemma swap_atensor_bounded_clinear:
  \<open>bounded_clinear (swap_atensor::(('a::complex_inner \<otimes>\<^sub>a 'b::complex_inner) \<Rightarrow> _))\<close>
  by (simp add: swap_atensor_bounded_clinear')

lemma swap_atensor_conjugation:
  assumes \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close>
  shows \<open>swap_atensor \<circ> (f \<otimes>\<^sub>A g) \<circ> swap_atensor = g \<otimes>\<^sub>A f\<close>
proof-
  define F where \<open>F z = (swap_atensor \<circ> (f \<otimes>\<^sub>A g) \<circ> swap_atensor) z  - (g \<otimes>\<^sub>A f) z\<close>
    for z
  have \<open>F (x \<otimes>\<^sub>a y) = 0\<close>
    for x y
    unfolding F_def
    by (simp add: assms atensorOp_separation bounded_clinear.clinear swap_atensorI2)
  moreover have \<open>clinear F\<close>
  proof-
    have \<open>clinear (swap_atensor \<circ> (f \<otimes>\<^sub>A g) \<circ> swap_atensor)\<close>
    proof-
      have \<open>clinear f\<close>
        by (simp add: assms bounded_clinear.clinear)          
      moreover have \<open>clinear swap_atensor\<close>
        by (simp add: swap_atensorI1)
      ultimately show ?thesis
        by (simp add: \<open>clinear swap_atensor\<close> clinear_compose assms(2) atensorOp_clinear bounded_clinear.clinear)
    qed
    moreover have \<open>clinear (g \<otimes>\<^sub>A f)\<close>
    proof-
      have \<open>clinear g\<close>
        by (simp add: assms bounded_clinear.clinear)          
      moreover have \<open>clinear f\<close>
        by (simp add: assms bounded_clinear.clinear)          
      ultimately show ?thesis
        by (simp add: atensorOp_clinear) 
    qed
    ultimately show ?thesis unfolding F_def
      using bounded_clinear.clinear complex_vector.linear_compose_sub 
      by blast
  qed
  ultimately have \<open>z \<in> range (case_prod (\<otimes>\<^sub>a)) \<Longrightarrow> F z = 0\<close>
    for z
    by auto
  moreover have \<open>cspan (range (case_prod (\<otimes>\<^sub>a))) = (UNIV::('a\<otimes>\<^sub>a'b) set)\<close>
    using atensor_onto by blast
  ultimately have \<open>(swap_atensor \<circ> (f \<otimes>\<^sub>A g) \<circ> swap_atensor) z  = (g \<otimes>\<^sub>A f) z\<close>
    for z
    using \<open>F \<equiv> \<lambda>z. (swap_atensor \<circ> (f \<otimes>\<^sub>A g) \<circ> swap_atensor) z - (g \<otimes>\<^sub>A f) z\<close> \<open>clinear F\<close>
      eq_iff_diff_eq_0  iso_tuple_UNIV_I
    by (metis (mono_tags, lifting) atensor_onto complex_vector.linear_eq_0_on_span)
  thus ?thesis by blast
qed


lemma algebraic_tensor_product_bounded_right:
  assumes \<open>bounded_clinear f\<close>
  shows \<open>bounded_clinear ((id::('a::complex_inner\<Rightarrow>'a)) \<otimes>\<^sub>A f)\<close>
proof-
  have \<open>bounded_clinear swap_atensor\<close>
    by (simp add: swap_atensor_bounded_clinear)    
  moreover have \<open>bounded_clinear (f \<otimes>\<^sub>A id)\<close>
    by (simp add: algebraic_tensor_product_bounded_left assms)    
  ultimately have \<open>bounded_clinear (swap_atensor \<circ> (f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)))\<close> 
    using Complex_Vector_Spaces.comp_bounded_clinear[where A = "swap_atensor" and B = "f \<otimes>\<^sub>A id"]
    by blast
  moreover have \<open>swap_atensor \<circ> (f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) \<circ> swap_atensor = (id::'a\<Rightarrow>'a) \<otimes>\<^sub>A f\<close>
    by (simp add: swap_atensor_conjugation assms bounded_clinear_id)
  thus ?thesis
    using \<open>bounded_clinear swap_atensor\<close> calculation comp_bounded_clinear 
    by fastforce 
qed

lemma tensor_from_id_comp:
  assumes \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close>
  shows \<open>((id::'b::complex_inner\<Rightarrow>'b) \<otimes>\<^sub>A g) \<circ> (f \<otimes>\<^sub>A (id::'c::complex_inner \<Rightarrow>'c)) = f \<otimes>\<^sub>A g\<close>
proof-
  define F where \<open>F z = (((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g) \<circ> (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c))) z - (f \<otimes>\<^sub>A g) z\<close>
    for z
  have \<open>z \<in> range (case_prod (\<otimes>\<^sub>a)) \<Longrightarrow> F z = 0\<close>
    for z
  proof-
    assume \<open>z \<in> range (case_prod (\<otimes>\<^sub>a))\<close>
    hence \<open>\<exists> x y. z = x \<otimes>\<^sub>a y\<close>
      by auto
    then obtain x::'a and y::'c where \<open>z = x \<otimes>\<^sub>a y\<close>
      by blast
    hence \<open>F z = F (x \<otimes>\<^sub>a y)\<close>
      by simp
    also have \<open>\<dots> = (id \<otimes>\<^sub>A g \<circ> f \<otimes>\<^sub>A id) (x \<otimes>\<^sub>a y) - (f \<otimes>\<^sub>A g) (x \<otimes>\<^sub>a y)\<close>
      unfolding F_def by blast
    also have \<open>\<dots> = (id \<otimes>\<^sub>A g \<circ> f \<otimes>\<^sub>A id) (x \<otimes>\<^sub>a y) - ((f x) \<otimes>\<^sub>a (g y))\<close>
    proof-
      have \<open>(f \<otimes>\<^sub>A g) (x \<otimes>\<^sub>a y) = ((f x) \<otimes>\<^sub>a (g y))\<close>
        by (simp add: assms(1) assms(2) atensorOp_separation bounded_clinear.clinear)
      thus ?thesis
        by simp 
    qed
    also have \<open>\<dots> = (id \<otimes>\<^sub>A g) ( (f \<otimes>\<^sub>A id) (x \<otimes>\<^sub>a y)) - ((f x) \<otimes>\<^sub>a (g y))\<close>
      by simp
    also have \<open>\<dots> = 0\<close>
    proof-
      have \<open>(id \<otimes>\<^sub>A g) ( (f \<otimes>\<^sub>A id) (x \<otimes>\<^sub>a y)) = ((f x) \<otimes>\<^sub>a (g y))\<close>
      proof-
        have \<open>(id \<otimes>\<^sub>A g) ( (f \<otimes>\<^sub>A id) (x \<otimes>\<^sub>a y)) = (id \<otimes>\<^sub>A g) ((f x) \<otimes>\<^sub>a (id y))\<close>
        proof-
          have \<open>clinear f\<close>
            by (simp add: assms(1) bounded_clinear.clinear)
          moreover have \<open>clinear (id::'c \<Rightarrow> 'c)\<close>
            using complex_vector.module_hom_id by blast
          ultimately have \<open>(f \<otimes>\<^sub>A (id::'c \<Rightarrow> 'c)) (x \<otimes>\<^sub>a y) = (f x) \<otimes>\<^sub>a ((id::'c \<Rightarrow> 'c) y)\<close>
            by (simp add: atensorOp_separation)                       
          thus ?thesis by auto
        qed
        also have \<open>\<dots> = (id \<otimes>\<^sub>A g) ((f x) \<otimes>\<^sub>a y)\<close>
          by simp
        also have \<open>\<dots> = ((id (f x)) \<otimes>\<^sub>a (g y))\<close>
        proof-
          have \<open>clinear (id::'b \<Rightarrow> 'b)\<close>
            by (simp add: complex_vector.module_hom_id)
          moreover have \<open>clinear f\<close>
            by (simp add: assms(1) bounded_clinear.clinear)
          ultimately show ?thesis
            by (simp add: assms(2) atensorOp_separation bounded_clinear.clinear) 
        qed
        also have \<open>\<dots> = ((f x) \<otimes>\<^sub>a (g y))\<close>
          by simp
        finally show ?thesis by blast
      qed
      thus ?thesis by simp
    qed
    finally show ?thesis by simp
  qed
  moreover have \<open>clinear F\<close>
  proof-
    have \<open>clinear (\<lambda> z. (((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g) \<circ> (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c))) z)\<close>
    proof-
      have \<open>clinear ((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g)\<close>
        using assms(2) atensorOp_clinear bounded_clinear.clinear complex_vector.module_hom_id by blast
      moreover have \<open>clinear (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c))\<close>
        by (simp add: assms(1) atensorOp_clinear bounded_clinear.clinear complex_vector.module_hom_id)
      ultimately show ?thesis
        using clinear_compose by blast
    qed
    moreover have \<open>clinear (f \<otimes>\<^sub>A g)\<close>
      by (simp add: assms(1) assms(2) atensorOp_clinear bounded_clinear.clinear)        
    ultimately have \<open>clinear (\<lambda> z. (((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g) \<circ> (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c))) z - (f \<otimes>\<^sub>A g) z)\<close>
      by (simp add: complex_vector.linear_compose_sub)
    thus ?thesis unfolding F_def by blast
  qed
  ultimately have f1: \<open>z \<in> cspan (range (case_prod (\<otimes>\<^sub>a))) \<Longrightarrow> F z = 0\<close>
    for z
    using complex_vector.linear_eq_0_on_span by auto
  hence \<open>F z = 0\<close>
    for z
  proof-
    have \<open>cspan (range (case_prod (\<otimes>\<^sub>a))) = (UNIV::('a \<otimes>\<^sub>a 'c) set)\<close>
      by (simp add: atensor_onto)
    hence \<open>z \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
      by simp
    thus ?thesis using f1 by blast
  qed
  hence \<open>(((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g) \<circ> (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c))) z = (f \<otimes>\<^sub>A g) z\<close>
    for z
    unfolding F_def
    by auto 
  thus ?thesis by blast
qed

lemma algebraic_tensor_product_bounded:
  fixes f::\<open>'a::complex_inner \<Rightarrow> 'b::complex_inner\<close> and g::\<open>'c::complex_inner \<Rightarrow> 'd::complex_inner\<close> 
  assumes \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close>
  shows \<open>bounded_clinear (f \<otimes>\<^sub>A g)\<close>
proof-
  have \<open>bounded_clinear (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c))\<close>
    by (simp add: algebraic_tensor_product_bounded_left assms(1))
  moreover have \<open>bounded_clinear ((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g)\<close>
    by (simp add: algebraic_tensor_product_bounded_right assms(2))
  ultimately have \<open>((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g) \<circ> (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c)) = f \<otimes>\<^sub>A g\<close>
    using tensor_from_id_comp
    by (simp add: tensor_from_id_comp assms(1) assms(2)) 
  thus ?thesis
    using \<open>bounded_clinear (f \<otimes>\<^sub>A id)\<close> \<open>bounded_clinear (id \<otimes>\<^sub>A g)\<close> comp_bounded_clinear 
    by fastforce 
qed

lemma onorm_swap_atensor_leq:
  \<open>onorm (swap_atensor::('a::complex_inner \<otimes>\<^sub>a 'b::complex_inner \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) \<le> 1\<close>
  by (simp add: swap_atensor_bounded_clinear')

lemma onorm_swap_atensor:
  assumes \<open>(UNIV::'a set)\<noteq>0\<close> and \<open>(UNIV::'b set)\<noteq>0\<close>
  shows \<open>onorm (swap_atensor::('a::complex_inner \<otimes>\<^sub>a 'b::complex_inner \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) = 1\<close>
proof-
  have \<open>onorm (swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) \<le> 1\<close>
    by (simp add: onorm_swap_atensor_leq)
  moreover have \<open>onorm (swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) \<ge> 1\<close>
  proof-
    have \<open>\<exists> x::'a. x \<noteq> 0\<close>
      using \<open>(UNIV::'a set)\<noteq>0\<close>
      by auto
    then obtain x::'a where \<open>x\<noteq>0\<close>
      by blast
    have \<open>\<exists> y::'b. y \<noteq> 0\<close>
      using \<open>(UNIV::'b set)\<noteq>0\<close>
      by auto
    then obtain y::'b where \<open>y\<noteq>0\<close>
      by blast
    have \<open>onorm (swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) = (SUP z::'a \<otimes>\<^sub>a 'b. (norm (swap_atensor z))/(norm z))\<close>
      using onorm_def by fastforce
    also have \<open>(SUP z::'a \<otimes>\<^sub>a 'b. (norm (swap_atensor z))/(norm z)) \<ge> (norm (swap_atensor (x \<otimes>\<^sub>a y)))/(norm (x \<otimes>\<^sub>a y))\<close>
    proof-
      have \<open>\<exists>K. \<forall>z. norm ((swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) z) \<le> norm z * K \<and> K \<ge> 0\<close>
      proof-
        have \<open>bounded_clinear (swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a))\<close>
          by (simp add: swap_atensor_bounded_clinear)
        hence \<open>\<exists>K. \<forall>z. norm ((swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) z) \<le> norm z * K\<close>
          by (simp add: bounded_clinear.bounded)
        then obtain K where \<open>\<And> z. norm ((swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) z) \<le> norm z * K\<close>
          by blast
        have \<open>norm ((swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) z) \<le> norm z * (abs K)\<close>
          for z
          using \<open>\<And> z. norm ((swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) z) \<le> norm z * K\<close>
          by (smt mult_less_cancel_left_disj norm_ge_zero)          
        moreover have \<open>(abs K) \<ge> 0\<close>
          by simp          
        ultimately show ?thesis
          by blast 
      qed
      then obtain K where \<open>\<And> z. norm ((swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) z) \<le> norm z * K\<close>
        and \<open>K \<ge> 0\<close>
        by blast    
      have \<open>(norm ((swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) z))/(norm z) \<le> K\<close>
        for z
      proof-
        have \<open>norm ((swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) z) \<le> norm z * K\<close>
          using \<open>\<And> z. norm ((swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) z) \<le> norm z * K\<close>
          by blast
        thus ?thesis
          by (smt \<open>0 \<le> K\<close> linordered_field_class.divide_nonneg_nonpos linordered_field_class.divide_right_mono nonzero_mult_div_cancel_left norm_ge_zero)          
      qed
      hence \<open>bdd_above {(norm ((swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) z))/(norm z) | z. True}\<close>
        unfolding bdd_above_def
        by blast
      thus ?thesis
      proof -
        have "bdd_above (range (\<lambda>a. norm (swap_atensor (a::'a \<otimes>\<^sub>a 'b)) / norm a))"
          by (metis \<open>bdd_above {norm (swap_atensor z) / norm z |z. True}\<close> full_SetCompr_eq)
        thus ?thesis
          by (meson UNIV_I cSUP_upper)
      qed 
    qed
    also have \<open>(norm (swap_atensor (x \<otimes>\<^sub>a y)))/(norm (x \<otimes>\<^sub>a y)) = 1\<close>
    proof-
      have \<open>norm (swap_atensor (x \<otimes>\<^sub>a y)) = norm (x \<otimes>\<^sub>a y)\<close>
      proof-
        have \<open>swap_atensor (x \<otimes>\<^sub>a y) = y \<otimes>\<^sub>a x\<close>
          using swap_atensorI2 by auto
        hence \<open>norm (swap_atensor (x \<otimes>\<^sub>a y)) = norm (y \<otimes>\<^sub>a x)\<close>
          by simp
        also have \<open>\<dots> = norm y * norm x\<close>
          by (simp add: atensor_norm_mult)
        also have \<open>\<dots> = norm x * norm y\<close>
          by simp
        also have \<open>\<dots> = norm (x \<otimes>\<^sub>a y)\<close>
          by (simp add: atensor_norm_mult)
        finally show ?thesis by blast
      qed
      moreover have \<open>norm (x \<otimes>\<^sub>a y) \<noteq> 0\<close>
      proof-
        have \<open>x \<otimes>\<^sub>a y \<noteq> 0\<close>
          by (simp add: \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> tensor_no_zero_divisors)
        thus ?thesis
          by simp 
      qed
      ultimately show ?thesis by auto
    qed
    finally show ?thesis by blast
  qed
  ultimately show ?thesis by simp
qed


lemma algebraic_tensor_product_bounded_right_onorm:
  fixes f :: \<open>'b::complex_inner \<Rightarrow> 'c::complex_inner\<close>
  assumes \<open>bounded_clinear f\<close> and \<open>(UNIV::'a set) \<noteq> 0\<close>
    and \<open>(UNIV::'b set) \<noteq> 0\<close> and \<open>(UNIV::'c set) \<noteq> 0\<close>
  shows \<open>onorm ((id::('a::complex_inner \<Rightarrow> _)) \<otimes>\<^sub>A f) \<le> onorm f\<close>
proof-
  have \<open>bounded_clinear (id::('a::complex_inner \<Rightarrow> _))\<close>
    by (simp add: bounded_clinear_id)
  hence \<open>swap_atensor \<circ> (f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) \<circ> swap_atensor = (id::'a\<Rightarrow>'a) \<otimes>\<^sub>A f\<close>    
    using \<open>bounded_clinear f\<close>
    by (simp add: swap_atensor_conjugation)
  hence f1: \<open>(id::'a\<Rightarrow>'a) \<otimes>\<^sub>A f = swap_atensor \<circ> (f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) \<circ> swap_atensor\<close>
    by simp
  have \<open>onorm ((id::'a\<Rightarrow>'a) \<otimes>\<^sub>A f) \<le> onorm (swap_atensor::'c \<otimes>\<^sub>a 'a \<Rightarrow> 'a \<otimes>\<^sub>a 'c) * onorm ( (f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a))) * onorm (swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a))\<close>
  proof-
    have \<open>bounded_clinear (swap_atensor::('c \<otimes>\<^sub>a 'a \<Rightarrow> 'a \<otimes>\<^sub>a 'c))\<close>
      by (simp add: swap_atensor_bounded_clinear)      
    moreover have \<open>bounded_clinear (swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a))\<close>
      by (simp add: swap_atensor_bounded_clinear)      
    moreover have \<open>bounded_clinear  ( (f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) \<circ> swap_atensor )\<close>
      by (simp add: algebraic_tensor_product_bounded_left_bounded_clinear assms calculation(2) comp_bounded_clinear)      
    ultimately have \<open>onorm (swap_atensor \<circ> ((f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) \<circ> swap_atensor))
        \<le> (onorm (swap_atensor::'c \<otimes>\<^sub>a 'a \<Rightarrow> 'a \<otimes>\<^sub>a 'c)) * onorm ( (f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) \<circ> swap_atensor)\<close>
      using f1 Operator_Norm.onorm_compose[where f = "swap_atensor"
          and g = "(f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) \<circ> swap_atensor"]
    proof -
      have "bounded_clinear (swap_atensor::'c \<otimes>\<^sub>a 'a \<Rightarrow> _ \<otimes>\<^sub>a _)"
        by (metis \<open>bounded_clinear (swap_atensor::('c \<otimes>\<^sub>a 'a \<Rightarrow> 'a \<otimes>\<^sub>a 'c))\<close>)
      thus ?thesis
        by (meson \<open>\<lbrakk>bounded_linear swap_atensor; bounded_linear (f \<otimes>\<^sub>A id \<circ> swap_atensor)\<rbrakk> \<Longrightarrow> onorm (swap_atensor \<circ> (f \<otimes>\<^sub>A id \<circ> swap_atensor)) \<le> onorm swap_atensor * onorm (f \<otimes>\<^sub>A id \<circ> swap_atensor)\<close> \<open>bounded_clinear (f \<otimes>\<^sub>A id \<circ> swap_atensor)\<close> bounded_clinear.bounded_linear)
    qed
    also have \<open>\<dots> \<le> (onorm (swap_atensor::'c \<otimes>\<^sub>a 'a \<Rightarrow> 'a \<otimes>\<^sub>a 'c)) * onorm (f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) * (onorm (swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)))\<close>
    proof-
      have \<open>onorm (swap_atensor::('c \<otimes>\<^sub>a 'a \<Rightarrow> 'a \<otimes>\<^sub>a 'c)) \<ge> 0\<close>
      proof-
        have \<open>bounded_clinear (swap_atensor::('c \<otimes>\<^sub>a 'a \<Rightarrow> 'a \<otimes>\<^sub>a 'c))\<close>
          by (simp add: swap_atensor_bounded_clinear)      
        thus ?thesis 
          using onorm_pos_le[where f = "swap_atensor::('c \<otimes>\<^sub>a 'a \<Rightarrow> 'a \<otimes>\<^sub>a 'c)"]
          by (smt bounded_clinear.bounded_linear)
      qed
      moreover have \<open>onorm ( (f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) \<circ> swap_atensor ) \<ge> 0\<close>
      proof-
        have \<open>bounded_clinear ((f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) \<circ> swap_atensor)\<close>
        proof-
          have \<open>bounded_clinear (f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a))\<close>
            using \<open>bounded_clinear f\<close>
            by (simp add: algebraic_tensor_product_bounded_left_bounded_clinear)
          moreover have \<open>bounded_clinear (swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a))\<close>
            by (simp add: swap_atensor_bounded_clinear)
          ultimately show ?thesis by (smt \<open>bounded_clinear (f \<otimes>\<^sub>A id \<circ> swap_atensor)\<close>)
        qed
        thus ?thesis 
          using onorm_pos_le[where f = "(f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) \<circ> swap_atensor"]
          by (smt bounded_clinear.bounded_linear)
      qed
      moreover  have \<open>onorm ( (f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) \<circ> swap_atensor ) \<le> onorm (f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a)) * (onorm (swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)))\<close>
        using Operator_Norm.onorm_compose[where f = "(f \<otimes>\<^sub>A (id::'a\<Rightarrow>'a))"
            and g = "swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)"]
        by (simp add: algebraic_tensor_product_bounded_left_bounded_clinear assms(1) bounded_clinear.bounded_linear swap_atensor_bounded_clinear)
      ultimately show ?thesis 
        using mult_mono
        by (smt assms(2) assms(4) mult_cancel_right2 onorm_swap_atensor)
    qed
    finally show ?thesis
      by (simp add: f1 fun.map_comp)           
  qed
  moreover have \<open>onorm (swap_atensor::('c \<otimes>\<^sub>a 'a \<Rightarrow> 'a \<otimes>\<^sub>a 'c)) = 1\<close>
    using \<open>(UNIV::'a set) \<noteq> 0\<close>  \<open>(UNIV::'c set) \<noteq> 0\<close> onorm_swap_atensor
    by blast
  moreover have \<open>onorm (swap_atensor::('a \<otimes>\<^sub>a 'b \<Rightarrow> 'b \<otimes>\<^sub>a 'a)) = 1\<close>
    using \<open>(UNIV::'a set) \<noteq> 0\<close>  \<open>(UNIV::'b set) \<noteq> 0\<close> onorm_swap_atensor
    by blast
  ultimately show ?thesis 
    by (smt algebraic_tensor_product_bounded_left_onorm assms mult_cancel_left1 mult_cancel_right1)
qed

lemma algebraic_tensor_product_bounded_norm':
  fixes f::\<open>'a::complex_inner \<Rightarrow> 'b::complex_inner\<close> and g::\<open>'c::complex_inner \<Rightarrow> 'd::complex_inner\<close> 
  assumes \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close> and \<open>(UNIV::'a set) \<noteq> 0\<close>
    and \<open>(UNIV::'b set) \<noteq> 0\<close> and \<open>(UNIV::'c set) \<noteq> 0\<close> and \<open>(UNIV::'d set) \<noteq> 0\<close> 
  shows \<open>onorm (f \<otimes>\<^sub>A g) \<le> onorm f * onorm g\<close>
proof-
  have \<open>bounded_clinear ((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g)\<close>
    by (simp add: algebraic_tensor_product_bounded assms(2) bounded_clinear_id)
  have \<open>bounded_clinear (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c))\<close>
    by (simp add: algebraic_tensor_product_bounded_left_bounded_clinear assms(1))
  have \<open>(((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g) \<circ> (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c))) z = (f \<otimes>\<^sub>A g) z\<close>
    for z
    by (simp add: assms(1) assms(2) tensor_from_id_comp)
  hence \<open>onorm (f \<otimes>\<^sub>A g) = onorm (((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g) \<circ> (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c)))\<close>
    by (simp add: assms(1) assms(2) tensor_from_id_comp)
  also have \<open>\<dots> \<le> onorm ((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g) * onorm (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c))\<close>
    using \<open>bounded_clinear (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c))\<close> \<open>bounded_clinear ((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g)\<close>
      Operator_Norm.onorm_compose
    by (simp add: onorm_compose bounded_clinear.bounded_linear)
  also have \<open>\<dots> \<le> onorm g * onorm f\<close>
  proof-
    have \<open>onorm ((id::'b\<Rightarrow>'b) \<otimes>\<^sub>A g) \<le> onorm g\<close>
      using \<open>bounded_clinear g\<close>
        algebraic_tensor_product_bounded_right_onorm[where f = "g"]
       \<open>(UNIV::'b set) \<noteq> 0\<close>  \<open>(UNIV::'c set) \<noteq> 0\<close>  \<open>(UNIV::'d set) \<noteq> 0\<close>
      by auto
    moreover have \<open>onorm (f \<otimes>\<^sub>A (id::'c \<Rightarrow>'c)) \<le> onorm f\<close>
      using \<open>bounded_clinear f\<close>
        algebraic_tensor_product_bounded_left_onorm[where f = "f"]
      by blast
    ultimately show ?thesis
      by (simp add: \<open>bounded_clinear (f \<otimes>\<^sub>A id)\<close> assms(2) bounded_clinear.bounded_linear mult_mono onorm_pos_le) 
  qed
  finally show ?thesis
    by (simp add: semiring_normalization_rules(7)) 
qed

lemma algebraic_tensor_product_bounded_norm_simplified:
  fixes f::\<open>'a::complex_inner \<Rightarrow> 'b::complex_inner\<close> and g::\<open>'c::complex_inner \<Rightarrow> 'd::complex_inner\<close> 
  assumes \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close> and \<open>(UNIV::'a set) \<noteq> 0\<close>
    and \<open>(UNIV::'b set) \<noteq> 0\<close> and \<open>(UNIV::'c set) \<noteq> 0\<close> and \<open>(UNIV::'d set) \<noteq> 0\<close>
  shows \<open>onorm (f \<otimes>\<^sub>A g) = onorm f * onorm g\<close>
proof-
  have \<open>onorm (f \<otimes>\<^sub>A g) \<le> onorm f * onorm g\<close>
    using \<open>(UNIV::'a set) \<noteq> 0\<close>
     \<open>(UNIV::'b set) \<noteq> 0\<close>  \<open>(UNIV::'c set) \<noteq> 0\<close>  \<open>(UNIV::'d set) \<noteq> 0\<close>
    by (simp add: algebraic_tensor_product_bounded_norm' assms(1) assms(2))    
  moreover have \<open>onorm (f \<otimes>\<^sub>A g) \<ge> onorm f * onorm g\<close>
  proof-
    have \<open>onorm f = (SUP x. (norm (f x))/(norm x) )\<close>
      using onorm_def by fastforce
    also have \<open>\<dots> = Sup { (norm (f x))/(norm x) | x. True }\<close>
      by (simp add: full_SetCompr_eq)
    finally have \<open>onorm f = Sup { (norm (f x))/(norm x) | x. True }\<close>
      by blast
    moreover have \<open>{ (norm (f x))/(norm x) | x. True } \<noteq> {}\<close>
      by auto
    moreover have \<open>bdd_above { (norm (f x))/(norm x) | x. True }\<close>
    proof-
      have \<open>\<exists> K. \<forall> x. norm (f x) \<le> norm x * K\<close>
        by (simp add: assms(1) bounded_clinear.bounded)
      hence \<open>\<exists> K. \<forall> x. norm (f x) \<le> norm x * K \<and> K \<ge> 0\<close>
        by (metis assms(1) bounded_linear.nonneg_bounded bounded_clinear.bounded_linear)
      then obtain K where \<open>\<And> x. norm (f x) \<le> norm x * K\<close> and \<open>K \<ge> 0\<close>
        by blast
      have \<open>(norm (f x))/(norm x) \<le>  K\<close>
        for x
      proof (cases \<open>x = 0\<close>)
        show "norm (f x) / norm x \<le> K"
          if "x = 0"
          using that
          by (simp add: \<open>0 \<le> K\<close>) 
        show "norm (f x) / norm x \<le> K"
          if "x \<noteq> 0"
          using that
          by (smt \<open>\<And>x. norm (f x) \<le> norm x * K\<close> nice_ordered_field_class.pos_less_divide_eq nonzero_mult_div_cancel_left norm_le_zero_iff) 
      qed
      thus ?thesis
        by fastforce 
    qed
    ultimately have \<open>onorm f \<in> closure { (norm (f x))/(norm x) | x. True}\<close>
      using closure_contains_Sup by auto
    hence \<open>\<exists> t. (\<forall> n. t n \<in> { (norm (f x))/(norm x) | x. True }) \<and> t \<longlonglongrightarrow> onorm f\<close>
      using closure_sequential by blast
    then obtain t::\<open>nat \<Rightarrow> _\<close> where \<open>\<forall> n. t n \<in> { (norm (f x))/(norm x) | x. True }\<close>
      and \<open>t \<longlonglongrightarrow> onorm f\<close>
      by blast
    from  \<open>\<forall> n. t n \<in> { (norm (f x))/(norm x) | x. True }\<close>
    have \<open>\<forall> n. \<exists> x.  t n = (norm (f x))/(norm x)\<close>
      by simp
    hence \<open>\<exists> x. \<forall> n. t n = (norm (f (x n)))/(norm (x n))\<close>
      by metis
    then obtain x where \<open>\<And> n. t n = (norm (f (x n)))/(norm (x n))\<close>
      by blast
    have \<open>onorm g = (SUP x. (norm (g x))/(norm x) )\<close>
      using onorm_def by fastforce
    also have \<open>\<dots> = Sup { (norm (g x))/(norm x) | x. True }\<close>
      by (simp add: full_SetCompr_eq)
    finally have \<open>onorm g = Sup { (norm (g x))/(norm x) | x. True }\<close>
      by blast
    moreover have \<open>{ (norm (g x))/(norm x) | x. True } \<noteq> {}\<close>
      by auto
    moreover have \<open>bdd_above { (norm (g x))/(norm x) | x. True }\<close>
    proof-
      have \<open>\<exists> K. \<forall> x. norm (g x) \<le> norm x * K\<close>
        using \<open>bounded_clinear g\<close>
        by (simp add: bounded_linear.bounded bounded_clinear.bounded_linear)
      hence \<open>\<exists> K. \<forall> x. norm (g x) \<le> norm x * K \<and> K \<ge> 0\<close>
      proof -
        have "\<exists>r. \<forall>c. 0 \<le> r \<and> norm (g c) \<le> norm c * r"
          by (metis \<open>\<exists>K. \<forall>x. norm (g x) \<le> norm x * K\<close> mult_eq_0_iff norm_le_zero_iff 
              norm_zero order.trans zero_le_mult_iff)          
        thus ?thesis
          by metis
      qed
      then obtain K where \<open>\<And> x. norm (g x) \<le> norm x * K\<close> and \<open>K \<ge> 0\<close>
        by blast
      have \<open>(norm (g x))/(norm x) \<le>  K\<close>
        for x
      proof (cases \<open>x = 0\<close>)
        show "norm (g x) / norm x \<le> K"
          if "x = 0"
          using that
          by (simp add: \<open>0 \<le> K\<close>) 
        show "norm (g x) / norm x \<le> K"
          if "x \<noteq> 0"
          using that
          by (smt \<open>\<And>x. norm (g x) \<le> norm x * K\<close> nice_ordered_field_class.pos_less_divide_eq nonzero_mult_div_cancel_left norm_le_zero_iff) 
      qed
      thus ?thesis
        by fastforce 
    qed
    ultimately have \<open>onorm g \<in> closure { (norm (g x))/(norm x) | x. True}\<close>
      using closure_contains_Sup by auto
    hence \<open>\<exists> t. (\<forall> n. t n \<in> { (norm (g x))/(norm x) | x. True }) \<and> t \<longlonglongrightarrow> onorm g\<close>
      using closure_sequential by blast
    then obtain s::\<open>nat \<Rightarrow> _\<close> where \<open>\<forall> n. s n \<in> { (norm (g x))/(norm x) | x. True }\<close>
      and \<open>s \<longlonglongrightarrow> onorm g\<close>
      by blast
    from  \<open>\<forall> n. s n \<in> { (norm (g x))/(norm x) | x. True }\<close>
    have \<open>\<forall> n. \<exists> x.  s n = (norm (g x))/(norm x)\<close>
      by simp
    hence \<open>\<exists> y. \<forall> n. s n = (norm (g (y n)))/(norm (y n))\<close>
      by metis
    then obtain y where \<open>\<And> n. s n = (norm (g (y n)))/(norm (y n))\<close>
      by blast
    have \<open>onorm (f \<otimes>\<^sub>A g) = (SUP z. (norm ((f \<otimes>\<^sub>A g) z))/(norm z))\<close>
      using onorm_def by fastforce
    moreover have \<open>(SUP z. (norm ((f \<otimes>\<^sub>A g) z))/(norm z)) = Sup {(norm ((f \<otimes>\<^sub>A g) z))/(norm z) | z. True}\<close>
      by (simp add: full_SetCompr_eq)      
    moreover have \<open>Sup {(norm ((f \<otimes>\<^sub>A g) z))/(norm z) | z. True} \<ge> (norm ((f \<otimes>\<^sub>A g) z))/(norm z)\<close>
      for z
    proof-
      have \<open>{(norm ((f \<otimes>\<^sub>A g) z))/(norm z) | z. True} \<noteq> {}\<close>
        by auto        
      moreover have \<open>bdd_above {(norm ((f \<otimes>\<^sub>A g) z))/(norm z) | z. True}\<close>
      proof-
        have \<open>bounded_clinear (f \<otimes>\<^sub>A g)\<close>
          by (simp add: algebraic_tensor_product_bounded assms(1) assms(2))
        hence \<open>\<exists>K. \<forall>x. norm ((f \<otimes>\<^sub>A g) x) \<le> norm x * K\<close>
          by (metis bounded_clinear.bounded_linear mult.commute onorm)
        hence \<open>\<exists>K. \<forall>x. norm ((f \<otimes>\<^sub>A g) x) \<le> norm x * K \<and> K \<ge> 0\<close>
          by (metis (no_types, opaque_lifting) linear mult.commute mult_nonneg_nonpos2 mult_zero_left norm_ge_zero order.trans)
        then obtain K where \<open>\<And> x. norm ((f \<otimes>\<^sub>A g) x) \<le> norm x * K\<close> and \<open>K \<ge> 0\<close>
          by blast
        have \<open>(norm ((f \<otimes>\<^sub>A g) t))/(norm t) \<le> K\<close>
          for t
        proof (cases \<open>t = 0\<close>)
          show "norm ((f \<otimes>\<^sub>A g) t) / norm t \<le> K"
            if "t = 0"
            using that
            by (simp add: \<open>0 \<le> K\<close>) 
          show "norm ((f \<otimes>\<^sub>A g) t) / norm t \<le> K"
            if "t \<noteq> 0"
            using that \<open>\<And> x. norm ((f \<otimes>\<^sub>A g) x) \<le> norm x * K\<close> mult_le_cancel_right nonzero_eq_divide_eq 
              norm_le_zero_iff ordered_field_class.sign_simps(28)
          proof -
            assume a1: "\<And>x. norm ((f \<otimes>\<^sub>A g) x) \<le> norm x * K"
            have f2: "\<And>r ra. (r::real) = 0 \<or> ra * r / r = ra"
              by auto
            have "\<And>r ra. (r::real) \<noteq> 0 \<or> (0::real) * ra = 0"
              by auto
            then have f3: "\<And>r ra. \<not> (r::real) \<le> 0 \<or> ra < 0 \<or> r * ra \<le> 0"
              by (metis (no_types) mult_le_cancel_right)
            have "\<And>r. (r::real) \<noteq> 0 \<or> \<not> 0 < r"
              by (metis less_imp_neq)
            moreover
            { assume "\<not> 0 < norm t"
              moreover
              { assume "\<exists>a. \<not> 0 < norm a \<and> (f \<otimes>\<^sub>A g) a \<noteq> 0"
                then have "\<exists>a. (a::'a \<otimes>\<^sub>a 'c) = 0 \<and> K < 0"
                  using f3 a1 by (metis (no_types) dual_order.strict_trans1 less_imp_neq norm_le_zero_iff not_le_imp_less)
                then have "K = 0"
                  by (meson \<open>0 \<le> K\<close> dual_order.strict_trans2 norm_le_zero_iff norm_not_less_zero) }
              ultimately have "K = 0 \<or> (f \<otimes>\<^sub>A g) t = 0"
                by meson }
            ultimately have "K = 0 \<or> (f \<otimes>\<^sub>A g) t = 0 \<or> norm ((f \<otimes>\<^sub>A g) t) / norm t \<le> K"
              using f2 a1 by (metis mult_le_cancel_right nonzero_mult_div_cancel_left times_divide_eq_left)
            then show ?thesis
              using a1 \<open>0 \<le> K\<close> by auto
          qed            
        qed
        thus ?thesis
          by fastforce 
      qed
      ultimately show ?thesis
        by (simp add: cSup_upper full_SetCompr_eq) 
    qed
    ultimately have \<open>onorm (f \<otimes>\<^sub>A g) \<ge> (norm ((f \<otimes>\<^sub>A g) z))/(norm z)\<close>
      for z::\<open>'a \<otimes>\<^sub>a 'c\<close>
      by simp
    hence \<open>onorm (f \<otimes>\<^sub>A g) \<ge> (norm ((f \<otimes>\<^sub>A g) ((x n)\<otimes>\<^sub>a(y n))))/(norm ((x n)\<otimes>\<^sub>a(y n)))\<close>
      for n
      by simp
    moreover have \<open>(norm ((f \<otimes>\<^sub>A g) ((x n)\<otimes>\<^sub>a(y n))))/(norm ((x n)\<otimes>\<^sub>a(y n))) = (norm (f (x n)) / norm (x n)) * (norm (g (y n)) / norm (y n))\<close>
      for n
    proof-
      have \<open>(f \<otimes>\<^sub>A g) ((x n)\<otimes>\<^sub>a(y n)) = (f (x n))\<otimes>\<^sub>a(g (y n))\<close>
        by (simp add: assms(1) assms(2) atensorOp_separation bounded_clinear.clinear)
      hence \<open>norm ((f \<otimes>\<^sub>A g) ((x n)\<otimes>\<^sub>a(y n))) = norm ((f (x n))\<otimes>\<^sub>a(g (y n)))\<close>
        by simp
      also have \<open>\<dots> = norm (f (x n)) * norm (g (y n))\<close>
        by (simp add: atensor_norm_mult)
      finally have \<open>norm ((f \<otimes>\<^sub>A g) ((x n)\<otimes>\<^sub>a(y n))) = norm (f (x n)) * norm (g (y n))\<close>
        by blast
      moreover have \<open>norm ((x n)\<otimes>\<^sub>a(y n)) = norm (x n) * norm (y n)\<close>
        by (simp add: atensor_norm_mult)
      ultimately have \<open>norm ((f \<otimes>\<^sub>A g) ((x n)\<otimes>\<^sub>a(y n))) / norm ((x n)\<otimes>\<^sub>a(y n)) 
        = (norm (f (x n)) * norm (g (y n)))/( norm (x n) * norm (y n))\<close>
        by simp
      also have \<open>\<dots> 
        = (norm (f (x n)) / norm (x n)) * (norm (g (y n)) / norm (y n))\<close>
        by simp
      finally show ?thesis by blast
    qed
    moreover have \<open>(norm (f (x n)) / norm (x n)) * (norm (g (y n)) / norm (y n))
          = t n * s n\<close>
      for n
      by (simp add: \<open>\<And>n. s n = norm (g (y n)) / norm (y n)\<close> \<open>\<And>n. t n = norm (f (x n)) / norm (x n)\<close>)
    ultimately have \<open>t n * s n \<le> onorm (f \<otimes>\<^sub>A g)\<close>
      for n
      by simp
    moreover have \<open>(\<lambda> n. t n * s n) \<longlonglongrightarrow> onorm f * onorm g\<close>
      using \<open>t \<longlonglongrightarrow> onorm f\<close> and \<open>s \<longlonglongrightarrow> onorm g\<close>
      using tendsto_mult by blast
    ultimately have \<open>onorm f * onorm g \<le> onorm (f \<otimes>\<^sub>A g)\<close>
      by (metis (no_types) LIMSEQ_le_const2 \<open>(\<lambda>n. t n * s n) \<longlonglongrightarrow> onorm f * onorm g\<close> \<open>\<And>n. t n * s n \<le> onorm (f \<otimes>\<^sub>A g)\<close>)
    thus ?thesis by blast
  qed
  ultimately show ?thesis by simp
qed

hide_fact algebraic_tensor_product_bounded_right_onorm
hide_fact algebraic_tensor_product_bounded_left_onorm
hide_fact algebraic_tensor_product_bounded_norm'

lemma fun_dom_zero:
  fixes f :: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector\<close>
  assumes \<open>clinear f\<close> and \<open>(UNIV::'a set) = 0\<close>
  shows \<open>f = (\<lambda>_. 0)\<close>
proof-
  have \<open>f z = 0\<close>
    for z
  proof-
    have \<open>z = 0\<close>
      using \<open>(UNIV::'a set) = 0\<close>
      by auto
    moreover have \<open>f 0 = 0\<close>
      using \<open>clinear f\<close>
      by (simp add: complex_vector.linear_0)
    ultimately show ?thesis by blast
  qed
  thus ?thesis by blast
qed

lemma fun_img_zero:
  fixes f :: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector\<close>
  assumes \<open>(UNIV::'b set) = 0\<close>
  shows \<open>f = (\<lambda>_. 0)\<close>
proof-
  have \<open>f z = 0\<close>
    for z
  proof(rule classical)
    assume \<open>\<not> (f z = 0)\<close>
    hence \<open>f z \<noteq> 0\<close>
      by blast
    moreover have \<open>f z \<in> (UNIV::'b set)\<close>
      by simp
    ultimately show ?thesis 
      using \<open>(UNIV::'b set) = 0\<close>
      by simp
  qed
  thus ?thesis by blast
qed

lemma UNIV_atensor_left:
  assumes \<open>(UNIV::('a::complex_inner) set) = 0\<close>
  shows \<open>(UNIV::('a\<otimes>\<^sub>a('b::complex_inner)) set) = 0\<close>
proof-
  have \<open>z = 0\<close>
    for z::\<open>'a\<otimes>\<^sub>a'b\<close>
  proof-
    have \<open>z \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
      by (simp add: atensor_onto)
    hence \<open>\<exists> t r. finite t \<and> t \<subseteq> range (case_prod (\<otimes>\<^sub>a)) \<and> z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      using complex_vector.span_explicit[where b = "range (case_prod (\<otimes>\<^sub>a))"]
      by (smt mem_Collect_eq)
    then obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close> 
      and \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      by blast
    have \<open>a\<in>t \<Longrightarrow> a = 0\<close>
      for a
    proof-
      assume \<open>a\<in>t\<close>
      hence \<open>a \<in> range (case_prod (\<otimes>\<^sub>a))\<close>
        using  \<open>t \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close>
        by blast
      hence \<open>\<exists> x y. a = x\<otimes>\<^sub>ay\<close>
        by auto
      then obtain x y where \<open>a = x\<otimes>\<^sub>ay\<close>
        by blast
      moreover have \<open>x = 0\<close>
        using \<open>(UNIV::('a::complex_inner) set) = 0\<close>
        by auto
      moreover have \<open>(0::'a)\<otimes>\<^sub>ay = 0\<close>
        using tensor_zero_divisors_left by auto        
      ultimately show \<open>a = 0\<close>
        by auto
    qed
    thus ?thesis using \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      by (metis (no_types, lifting) complex_vector.scale_zero_right sum.cong sum.neutral_const)      
  qed
  thus ?thesis by auto
qed

lemma UNIV_atensor_right:
  assumes \<open>(UNIV::('b::complex_inner) set) = 0\<close>
  shows \<open>(UNIV::(('a::complex_inner)\<otimes>\<^sub>a'b) set) = 0\<close>
proof-
  have \<open>z = 0\<close>
    for z::\<open>'a\<otimes>\<^sub>a'b\<close>
  proof-
    have \<open>z \<in> cspan (range (case_prod (\<otimes>\<^sub>a)))\<close>
      by (simp add: atensor_onto)
    hence \<open>\<exists> t r. finite t \<and> t \<subseteq> range (case_prod (\<otimes>\<^sub>a)) \<and> z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      using complex_vector.span_explicit[where b = "range (case_prod (\<otimes>\<^sub>a))"]
      by (smt mem_Collect_eq)
    then obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close> 
      and \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      by blast
    have \<open>a\<in>t \<Longrightarrow> a = 0\<close>
      for a
    proof-
      assume \<open>a\<in>t\<close>
      hence \<open>a \<in> range (case_prod (\<otimes>\<^sub>a))\<close>
        using  \<open>t \<subseteq> range (case_prod (\<otimes>\<^sub>a))\<close>
        by blast
      hence \<open>\<exists> x y. a = x\<otimes>\<^sub>ay\<close>
        by auto
      then obtain x y where \<open>a = x\<otimes>\<^sub>ay\<close>
        by blast
      moreover have \<open>y = 0\<close>
        using \<open>(UNIV::('b::complex_inner) set) = 0\<close>
        by auto
      moreover have \<open>x\<otimes>\<^sub>a(0::'b) = 0\<close>
        using tensor_zero_divisors_right by auto        
      ultimately show \<open>a = 0\<close>
        by auto
    qed
    thus ?thesis using \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      by (metis (no_types, lifting) complex_vector.scale_zero_right sum.cong sum.neutral_const)      
  qed
  thus ?thesis by auto
qed

lemma algebraic_tensor_product_bounded_norm_simplified_a:
  fixes f::\<open>'a::complex_inner \<Rightarrow> 'b::complex_inner\<close> 
    and g::\<open>'c::complex_inner \<Rightarrow> 'd::complex_inner\<close> 
  assumes \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close> 
    and \<open>(UNIV::'a set) = 0\<close> 
  shows \<open>onorm (f \<otimes>\<^sub>A g) = onorm f * onorm g\<close>
proof-
  have \<open>clinear f\<close>
    using \<open>bounded_clinear f\<close>
    unfolding bounded_clinear_def
    by blast
  hence \<open>f = (\<lambda> _. 0)\<close>
    using  \<open>(UNIV::'a set) = 0\<close> fun_dom_zero[where f = "f"]
    by auto
  hence \<open>onorm f = 0\<close>
    by (simp add: onorm_eq_0)
  have \<open>(UNIV::('a\<otimes>\<^sub>a'c) set) = 0\<close>
    using \<open>(UNIV::'a set) = 0\<close> UNIV_atensor_left
    by blast
  have \<open>bounded_clinear (f \<otimes>\<^sub>A g)\<close>
    using \<open>bounded_clinear f\<close>  \<open>bounded_clinear g\<close>
    by (simp add: algebraic_tensor_product_bounded)
  hence \<open>clinear (f \<otimes>\<^sub>A g)\<close>
    by (simp add: bounded_clinear_def)
  hence \<open>f \<otimes>\<^sub>A g = (\<lambda> _. 0)\<close>
    using  \<open>(UNIV::('a\<otimes>\<^sub>a'c) set) = 0\<close> fun_dom_zero[where f = "f \<otimes>\<^sub>A g"]
    by auto
  hence \<open>onorm (f \<otimes>\<^sub>A g) = 0\<close>
    using \<open>bounded_clinear f\<close>
    by (simp add: onorm_eq_0)
  thus ?thesis using \<open>onorm f = 0\<close> by auto
qed

lemma algebraic_tensor_product_bounded_norm_simplified_c:
  fixes f::\<open>'a::complex_inner \<Rightarrow> 'b::complex_inner\<close> 
    and g::\<open>'c::complex_inner \<Rightarrow> 'd::complex_inner\<close> 
  assumes \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close> 
    and \<open>(UNIV::'c set) = 0\<close> 
  shows \<open>onorm (f \<otimes>\<^sub>A g) = onorm f * onorm g\<close>
proof-
  have \<open>clinear g\<close>
    using \<open>bounded_clinear g\<close>
    unfolding bounded_clinear_def
    by blast
  hence \<open>g = (\<lambda> _. 0)\<close>
    using  \<open>(UNIV::'c set) = 0\<close> fun_dom_zero[where f = "g"]
    by auto
  hence \<open>onorm g = 0\<close>
    by (simp add: onorm_eq_0)
  have \<open>(UNIV::('a\<otimes>\<^sub>a'c) set) = 0\<close>
    using \<open>(UNIV::'c set) = 0\<close> UNIV_atensor_right
    by blast
  have \<open>bounded_clinear (f \<otimes>\<^sub>A g)\<close>
    using \<open>bounded_clinear f\<close>  \<open>bounded_clinear g\<close>
    by (simp add: algebraic_tensor_product_bounded)
  hence \<open>clinear (f \<otimes>\<^sub>A g)\<close>
    by (simp add: bounded_clinear_def)
  hence \<open>f \<otimes>\<^sub>A g = (\<lambda> _. 0)\<close>
    using  \<open>(UNIV::('a\<otimes>\<^sub>a'c) set) = 0\<close> fun_dom_zero[where f = "f \<otimes>\<^sub>A g"]
    by auto
  hence \<open>onorm (f \<otimes>\<^sub>A g) = 0\<close>
    using \<open>bounded_clinear f\<close>
    by (simp add: onorm_eq_0)
  thus ?thesis using \<open>onorm g = 0\<close> by auto
qed


lemma algebraic_tensor_product_bounded_norm_simplified_b:
  fixes f::\<open>'a::complex_inner \<Rightarrow> 'b::complex_inner\<close> 
    and g::\<open>'c::complex_inner \<Rightarrow> 'd::complex_inner\<close> 
  assumes \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close> 
    and \<open>(UNIV::'b set) = 0\<close> 
  shows \<open>onorm (f \<otimes>\<^sub>A g) = onorm f * onorm g\<close>
proof-
  have \<open>clinear f\<close>
    using \<open>bounded_clinear f\<close>
    unfolding bounded_clinear_def
    by blast
  hence \<open>f = (\<lambda> _. 0)\<close>
    using  \<open>(UNIV::'b set) = 0\<close> fun_img_zero[where f = "f"]
    by auto
  hence \<open>onorm f = 0\<close>
    by (simp add: onorm_eq_0)
  have \<open>(UNIV::('b\<otimes>\<^sub>a'd) set) = 0\<close>
    using \<open>(UNIV::'b set) = 0\<close> UNIV_atensor_left
    by blast
  have \<open>bounded_clinear (f \<otimes>\<^sub>A g)\<close>
    using \<open>bounded_clinear f\<close>  \<open>bounded_clinear g\<close>
    by (simp add: algebraic_tensor_product_bounded)
  hence \<open>clinear (f \<otimes>\<^sub>A g)\<close>
    by (simp add: bounded_clinear_def)
  hence \<open>f \<otimes>\<^sub>A g = (\<lambda> _. 0)\<close>
    using  \<open>(UNIV::('b\<otimes>\<^sub>a'd) set) = 0\<close> fun_dom_zero[where f = "f \<otimes>\<^sub>A g"]
    by auto
  hence \<open>onorm (f \<otimes>\<^sub>A g) = 0\<close>
    using \<open>bounded_clinear f\<close>
    by (simp add: onorm_eq_0)
  thus ?thesis using \<open>onorm f = 0\<close> by auto
qed

lemma algebraic_tensor_product_bounded_norm_simplified_d:
  fixes f::\<open>'a::complex_inner \<Rightarrow> 'b::complex_inner\<close> 
    and g::\<open>'c::complex_inner \<Rightarrow> 'd::complex_inner\<close> 
  assumes \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close> 
    and \<open>(UNIV::'d set) = 0\<close> 
  shows \<open>onorm (f \<otimes>\<^sub>A g) = onorm f * onorm g\<close>
proof-
  have \<open>clinear g\<close>
    using \<open>bounded_clinear g\<close>
    unfolding bounded_clinear_def
    by blast
  hence \<open>g = (\<lambda> _. 0)\<close>
    using  \<open>(UNIV::'d set) = 0\<close> fun_img_zero[where f = "g"]
    by auto
  hence \<open>onorm g = 0\<close>
    by (simp add: onorm_eq_0)
  have \<open>(UNIV::('b\<otimes>\<^sub>a'd) set) = 0\<close>
    using \<open>(UNIV::'d set) = 0\<close> UNIV_atensor_right
    by blast
  have \<open>bounded_clinear (f \<otimes>\<^sub>A g)\<close>
    using \<open>bounded_clinear f\<close>  \<open>bounded_clinear g\<close>
    by (simp add: algebraic_tensor_product_bounded)
  hence \<open>clinear (f \<otimes>\<^sub>A g)\<close>
    by (simp add: bounded_clinear_def)
  hence \<open>f \<otimes>\<^sub>A g = (\<lambda> _. 0)\<close>
    using  \<open>(UNIV::('b\<otimes>\<^sub>a'd) set) = 0\<close> fun_dom_zero[where f = "f \<otimes>\<^sub>A g"]
    by auto
  hence \<open>onorm (f \<otimes>\<^sub>A g) = 0\<close>
    using \<open>bounded_clinear f\<close>
    by (simp add: onorm_eq_0)
  thus ?thesis using \<open>onorm g = 0\<close> by auto
qed


lemma algebraic_tensor_product_bounded_norm:
  fixes f::\<open>'a::complex_inner \<Rightarrow> 'b::complex_inner\<close> and g::\<open>'c::complex_inner \<Rightarrow> 'd::complex_inner\<close> 
  assumes \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close>
  shows \<open>onorm (f \<otimes>\<^sub>A g) = onorm f * onorm g\<close>
proof(cases \<open>(UNIV::'a set) \<noteq> 0 \<and> (UNIV::'b set) \<noteq> 0 \<and> (UNIV::'c set) \<noteq> 0 \<and> (UNIV::'d set) \<noteq> 0\<close>)
case True
  thus ?thesis 
    using \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
      algebraic_tensor_product_bounded_norm_simplified[where f = "f" and g = "g"]
    by blast
next
  case False
  thus ?thesis 
    using \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
      algebraic_tensor_product_bounded_norm_simplified_a[where f = "f" and g = "g"]
      algebraic_tensor_product_bounded_norm_simplified_b[where f = "f" and g = "g"]
      algebraic_tensor_product_bounded_norm_simplified_c[where f = "f" and g = "g"]
      algebraic_tensor_product_bounded_norm_simplified_d[where f = "f" and g = "g"]
    by auto
qed

hide_fact algebraic_tensor_product_bounded_norm_simplified
hide_fact algebraic_tensor_product_bounded_norm_simplified_a
hide_fact algebraic_tensor_product_bounded_norm_simplified_b
hide_fact algebraic_tensor_product_bounded_norm_simplified_c
hide_fact algebraic_tensor_product_bounded_norm_simplified_d

lemma atensor_continuous:
  fixes x::\<open>nat \<Rightarrow> 'a::chilbert_space\<close> and y::\<open>nat \<Rightarrow> 'b::chilbert_space\<close>
  assumes \<open>x \<longlonglongrightarrow> a\<close> and \<open>y \<longlonglongrightarrow> b\<close>
  shows \<open>(\<lambda> n. (x n) \<otimes>\<^sub>a (y n) ) \<longlonglongrightarrow> a \<otimes>\<^sub>a b\<close>
proof-
  have \<open>dist ((x n) \<otimes>\<^sub>a (y n)) (a \<otimes>\<^sub>a b) = norm (((x n) \<otimes>\<^sub>a (y n)) - (a \<otimes>\<^sub>a b))\<close>
    for n
    by (simp add: dist_norm)    
  also have \<open>norm (((x n) \<otimes>\<^sub>a (y n)) - (a \<otimes>\<^sub>a b)) \<le> 
            norm ((x n - a) \<otimes>\<^sub>a b) + norm ((x n) \<otimes>\<^sub>a (y n - b))\<close>
    for n
  proof-
    have \<open>((x n) \<otimes>\<^sub>a (y n)) - (a \<otimes>\<^sub>a b) = (x n) \<otimes>\<^sub>a (y n - b) +  (x n - a) \<otimes>\<^sub>a b\<close>
    proof-
      have \<open>((x n) \<otimes>\<^sub>a (y n)) - ((x n) \<otimes>\<^sub>a b) = (x n) \<otimes>\<^sub>a (y n - b)\<close>
        by (simp add: atensor_distr_minus_right)
      moreover have \<open>(x n) \<otimes>\<^sub>a b - a \<otimes>\<^sub>a b = (x n - a) \<otimes>\<^sub>a b\<close>
        by (simp add: atensor_distr_minus_left)        
      ultimately show ?thesis
        by (metis add_diff_eq diff_add_cancel)         
    qed
    hence \<open>norm ((x n) \<otimes>\<^sub>a (y n) - a \<otimes>\<^sub>a b) = norm ((x n) \<otimes>\<^sub>a (y n - b) +  (x n - a) \<otimes>\<^sub>a b)\<close>
      by simp
    thus ?thesis
      by (smt norm_triangle_ineq) 
  qed
  also have \<open>norm ((x n - a) \<otimes>\<^sub>a b) + norm ((x n) \<otimes>\<^sub>a (y n - b)) =  
            norm (x n - a) * norm b + norm (x n) * norm (y n - b)\<close>
    for n
  proof-
    have \<open>norm ((x n - a) \<otimes>\<^sub>a b) = norm (x n - a) * norm b\<close>
      by (simp add: atensor_norm_mult)      
    moreover have \<open>norm ((x n) \<otimes>\<^sub>a (y n - b)) = norm (x n) * norm (y n - b)\<close>
      by (simp add: atensor_norm_mult)      
    ultimately show ?thesis by auto
  qed
  finally have \<open>dist (x n \<otimes>\<^sub>a y n) (a \<otimes>\<^sub>a b)
  \<le> norm (x n - a) * norm b +
     norm (x n) * norm (y n - b)\<close>
    for n
    by blast
  hence \<open>norm (dist (x n \<otimes>\<^sub>a y n) (a \<otimes>\<^sub>a b))
  \<le> norm (norm (x n - a) * norm b +
     norm (x n) * norm (y n - b)) \<close>
    for n
    by simp    
  moreover have \<open>(\<lambda> n. norm (x n - a) * norm b +
     norm (x n) * norm (y n - b)) \<longlonglongrightarrow> 0\<close>
  proof-
    have \<open>(\<lambda> n. norm (x n - a) * norm b) \<longlonglongrightarrow> 0\<close>
    proof-
      have \<open>(\<lambda> n. norm (x n - a)) \<longlonglongrightarrow> 0\<close>
        using \<open>x \<longlonglongrightarrow> a\<close>
        by (simp add: LIM_zero_iff tendsto_norm_zero) 
      thus ?thesis
        by (simp add: tendsto_mult_left_zero) 
    qed
    moreover have \<open>(\<lambda> n. norm (x n) * norm (y n - b)) \<longlonglongrightarrow> 0\<close>
    proof-
      have \<open>(\<lambda> n. norm (y n - b)) \<longlonglongrightarrow> 0\<close>
        using \<open>y \<longlonglongrightarrow> b\<close>
        by (simp add: LIM_zero_iff tendsto_norm_zero)
      thus ?thesis
        by (metis (full_types) assms(1) tendsto_mult tendsto_norm vector_space_over_itself.scale_zero_right) 
    qed
    ultimately show ?thesis
      by (simp add: tendsto_add_zero) 
  qed
  ultimately have \<open>(\<lambda> n. dist ((x n) \<otimes>\<^sub>a (y n)) (a \<otimes>\<^sub>a b) ) \<longlonglongrightarrow> 0\<close>
    using Limits.tendsto_0_le[where F = "sequentially" and g = "\<lambda> n. dist (x n \<otimes>\<^sub>a y n) (a \<otimes>\<^sub>a b)" and K = "1"
        and f = "(\<lambda> n. norm (x n - a) * norm b + norm (x n) * norm (y n - b))"]
    by auto
  thus ?thesis
    using tendsto_dist_iff by auto 
qed

lift_definition atensorOp_bounded :: \<open>('a::complex_inner, 'b::complex_inner) cblinfun
 \<Rightarrow> ('c::complex_inner, 'd::complex_inner ) cblinfun \<Rightarrow> ('a \<otimes>\<^sub>a 'c,  'b \<otimes>\<^sub>a 'd) cblinfun\<close> (infixl "\<^sub>A\<otimes>" 70)
  is \<open>\<lambda> f g. f \<otimes>\<^sub>A g\<close>
  using Algebraic_Tensor_Product.algebraic_tensor_product_bounded by blast

unbundle no_free_notation

end

