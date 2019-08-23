(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee


*)


theory Tensor_Product
  imports Bounded_Operators Complex_L2 "HOL-Library.Adhoc_Overloading" Completion

begin

section \<open>Algebraic tensor product\<close>

instantiation prod :: (complex_vector, complex_vector) complex_vector
begin
lift_definition scaleC_prod :: \<open>complex \<Rightarrow>  'a \<times> 'b \<Rightarrow>  'a \<times> 'b\<close>
  is \<open>\<lambda> c x. (c *\<^sub>C (fst x), c *\<^sub>C (snd x))\<close>.

instance
proof
  show "((*\<^sub>R) r::'a \<times> 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
    apply transfer
    by (metis scaleR_prod_def scaleR_scaleC)

  show "a *\<^sub>C ((x::'a \<times> 'b) + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "'a \<times> 'b"
      and y :: "'a \<times> 'b"
    apply transfer
    by (simp add: scaleC_add_right)

  show "(a + b) *\<^sub>C (x::'a \<times> 'b) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<times> 'b"
    apply transfer
    by (simp add: scaleC_add_left) 

  show "a *\<^sub>C b *\<^sub>C (x::'a \<times> 'b) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<times> 'b"
    apply transfer
    by simp

  show "1 *\<^sub>C (x::'a \<times> 'b) = x"
    for x :: "'a \<times> 'b"
    apply transfer
    by simp 
qed
end

definition atensor_kernel::\<open>(('a::complex_vector, 'b::complex_vector) prod) set\<close> where
  \<open>atensor_kernel = complex_vector.span 
({ Pair x (y+z) - Pair x y - Pair x z |  x y z. True}\<union>
 { Pair (y+z) x - Pair y x - Pair z x |  x y z. True}\<union>
 { Pair x (c *\<^sub>C y) -  c *\<^sub>C Pair x y |  x y c. True}\<union>
 { Pair (c *\<^sub>C x) y -  c *\<^sub>C Pair x y |  x y c. True})\<close>

lemma subspace_atensor_kernel:
  \<open>complex_vector.subspace atensor_kernel\<close>
  unfolding atensor_kernel_def
  using Complex_Vector_Spaces.complex_vector.subspace_span[where S = "{(x, y + z) - (x, y) - (x, z) |x y z. True} \<union>
      {(y + z, x) - (y, x) - (z, x) |x y z. True} \<union>
      {(x, c *\<^sub>C y) - c *\<^sub>C (x, y) |x y c. True} \<union>
      {(c *\<^sub>C x, y) - c *\<^sub>C (x, y) |x y c. True}"]
  by blast

definition atensor_rel :: "('a::complex_vector,'b::complex_vector) prod \<Rightarrow> ('a,'b) prod \<Rightarrow> bool"
  where "atensor_rel = (\<lambda>x y. x - y \<in> atensor_kernel)"

text\<open>Tensor product as defined in @Helemskii chapter 2, section 8\<close>
quotient_type (overloaded) ('a, 'b) atensor 
  = "('a::complex_vector,'b::complex_vector) prod" /  atensor_rel
  unfolding equivp_def proof
  show "\<forall>y. atensor_rel (x::'a \<times> 'b) y = (atensor_rel x = atensor_rel y)"
    for x :: "'a \<times> 'b"
  proof
    show "atensor_rel x y = (atensor_rel x = atensor_rel y)"
      for y :: "'a \<times> 'b"
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
qed


(* "a" is for algebraic *)
type_notation (xsymbols)
  atensor  ("(_ \<otimes>\<^sub>a/ _)" [21, 20] 20)
type_notation (HTML output)
  atensor  ("(_ \<otimes>\<^sub>a/ _)" [21, 20] 20)

lift_definition atensor_op:: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>  (infixl "\<otimes>\<^sub>a" 70)
  is \<open>\<lambda> x::'a. \<lambda> y::'b. Pair x y\<close>.

instantiation atensor :: (complex_vector,complex_vector) complex_vector
begin

lift_definition plus_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>
  is \<open>\<lambda> x y. x + y\<close>
  unfolding atensor_rel_def
proof-
  fix p1 p2 p3 p4 :: \<open>('a, 'b) prod\<close>
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
  fix p1 p2 p3 p4 :: \<open>('a, 'b) prod\<close>
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
  fix p1 p2::\<open>('a, 'b) prod\<close> and c::real
  assume \<open>p1 - p2 \<in> atensor_kernel\<close> 
  moreover have \<open>complex_vector.subspace atensor_kernel\<close>
    using subspace_atensor_kernel
    by blast
  ultimately have \<open>c *\<^sub>R (p1 - p2) \<in> atensor_kernel\<close>
    by (simp add: \<open>complex_vector.subspace atensor_kernel\<close> complex_vector.subspace_scale scaleR_scaleC)
  show \<open>c *\<^sub>R p1 - c *\<^sub>R p2 \<in> atensor_kernel\<close>
    by (metis \<open>c *\<^sub>R (p1 - p2) \<in> atensor_kernel\<close> ordered_field_class.sign_simps(26))
qed

lift_definition scaleC_atensor :: \<open>complex \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>
  is \<open>\<lambda> c x. c *\<^sub>C x\<close>
  unfolding atensor_rel_def
proof-
  fix p1 p2::\<open>('a, 'b) prod\<close> and c::complex
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
  fix p1 p2 :: \<open>('a, 'b) prod\<close>
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
\<open>x \<otimes>\<^sub>a (y+z) =  x \<otimes>\<^sub>a y  +  x \<otimes>\<^sub>a z\<close>
  apply transfer unfolding atensor_rel_def atensor_kernel_def
  apply auto
  by (simp add: complex_vector.span_base) 

lemma atensor_distr_left:
\<open>(y+z) \<otimes>\<^sub>a x =  y \<otimes>\<^sub>a x  +  z \<otimes>\<^sub>a x\<close>
  apply transfer unfolding atensor_rel_def atensor_kernel_def
  apply auto
  by (simp add: complex_vector.span_base) 

lemma atensor_mult_right:
\<open>x \<otimes>\<^sub>a (c *\<^sub>C y) = c *\<^sub>C (x \<otimes>\<^sub>a y)\<close>
  apply transfer unfolding atensor_rel_def atensor_kernel_def
  apply auto
  by (metis (mono_tags, lifting) Un_iff complex_vector.span_base mem_Collect_eq)

lemma atensor_mult_left:
\<open>(c *\<^sub>C x) \<otimes>\<^sub>a y   = c *\<^sub>C (x \<otimes>\<^sub>a y)\<close>
  apply transfer unfolding atensor_rel_def atensor_kernel_def
  apply auto
  by (metis (mono_tags, lifting) Un_iff complex_vector.span_base mem_Collect_eq)


text \<open>Proposition 1 on page 186 in @@Helemskii\<close>
instantiation atensor :: (complex_inner,complex_inner) complex_inner
begin 
lift_definition cinner_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> complex\<close>
is \<open>\<lambda> u v. \<langle>fst u, fst v\<rangle> * \<langle>snd u, snd v\<rangle>\<close>
proof-
  fix p1 p2 p3 p4 :: \<open>('a, 'b) prod\<close>
  assume \<open>atensor_rel p1 p2\<close> and \<open>atensor_rel p3 p4\<close>
  hence \<open>p1 - p2 \<in> atensor_kernel\<close> and \<open>p3 - p4 \<in> atensor_kernel\<close>
    unfolding atensor_rel_def by auto

  show \<open>\<langle>fst p1, fst p3\<rangle> * \<langle>snd p1, snd p3\<rangle> =
       \<langle>fst p2, fst p4\<rangle> * \<langle>snd p2, snd p4\<rangle>\<close>
    sorry
qed

definition norm_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> real\<close> where
\<open>norm_atensor z = sqrt (norm \<langle>z, z\<rangle> )\<close> for z

definition sgn_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close> where
\<open>sgn_atensor x = x /\<^sub>R norm x\<close> for x

definition dist_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> real\<close> where
\<open>dist_atensor x y = norm (x - y)\<close> for x y

definition uniformity_atensor :: \<open>(('a \<otimes>\<^sub>a 'b) \<times> ('a \<otimes>\<^sub>a 'b)) filter\<close>
  where  \<open>uniformity_atensor = (INF e:{0<..}. principal {((f::'a \<otimes>\<^sub>a 'b), (g::'a \<otimes>\<^sub>a 'b)). dist f g < e})\<close>

definition open_atensor :: \<open>('a \<otimes>\<^sub>a 'b) set \<Rightarrow> bool\<close>
  where \<open>open_atensor = (\<lambda> U::('a \<otimes>\<^sub>a 'b) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity))\<close>

instance
  proof
  show "dist (x::'a \<otimes>\<^sub>a 'b) y = norm (x - y)"
    for x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
    unfolding dist_atensor_def by blast
  show "sgn (x::'a \<otimes>\<^sub>a 'b) = x /\<^sub>R norm x"
    for x :: "'a \<otimes>\<^sub>a 'b"
    unfolding sgn_atensor_def by blast
  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a \<otimes>\<^sub>a 'b) y < e})"
    unfolding uniformity_atensor_def by blast
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a \<otimes>\<^sub>a 'b) = x \<longrightarrow> y \<in> U)"
    for U :: "('a \<otimes>\<^sub>a 'b) set"
    unfolding open_atensor_def by blast
  show "\<langle>x::'a \<otimes>\<^sub>a 'b, y\<rangle> = cnj \<langle>y, x\<rangle>"
    for x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
    sorry
  show "\<langle>(x::'a \<otimes>\<^sub>a 'b) + y, z\<rangle> = \<langle>x, z\<rangle> + \<langle>y, z\<rangle>"
    for x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
      and z :: "'a \<otimes>\<^sub>a 'b"
    sorry
  show "\<langle>r *\<^sub>C (x::'a \<otimes>\<^sub>a 'b), y\<rangle> = cnj r * \<langle>x, y\<rangle>"
    for r :: complex
      and x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
    sorry
  show "0 \<le> \<langle>x::'a \<otimes>\<^sub>a 'b, x\<rangle>"
    for x :: "'a \<otimes>\<^sub>a 'b"
    sorry
  show "(\<langle>x::'a \<otimes>\<^sub>a 'b, x\<rangle> = 0) = (x = 0)"
    for x :: "'a \<otimes>\<^sub>a 'b"
    sorry
  show "norm (x::'a \<otimes>\<^sub>a 'b) = sqrt (cmod \<langle>x, x\<rangle>)"
    for x :: "'a \<otimes>\<^sub>a 'b"
    unfolding norm_atensor_def by blast
qed


end

section \<open>Hilbert tensor product\<close>

text\<open>Hilbert tensor product as defined in @Helemskii chapter 2, section 8\<close>
typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) htensor
  = \<open>(UNIV::(('a \<otimes>\<^sub>a 'b) completion) set)\<close>
  by (rule Set.UNIV_witness)

(* "h" is for Hilbert *)
type_notation (xsymbols)
  htensor  ("(_ \<otimes>\<^sub>h/ _)" [21, 20] 20)
type_notation (HTML output)
  htensor  ("(_ \<otimes>\<^sub>h\<^sub>/ _)" [21, 20] 20)


instantiation htensor :: (chilbert_space, chilbert_space) chilbert_space
begin
instance 
  sorry
end


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
