(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee
*)

theory Completion
  imports 
    Complex_Bounded_Operators.Complex_Bounded_Linear_Function
begin

unbundle cblinfun_notation

(* TODO: I don't think this definition is necessary. Vanishes X is no shorter/clearer than X \<longlonglongrightarrow> 0 *)
definition Vanishes:: \<open>(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> bool\<close> where
  \<open>Vanishes x = (x \<longlonglongrightarrow> 0)\<close>

(* TODO: does not need real_normed_vector. Metric space should do (replace X n - Y n by dist (X n - Y n) then). *)
definition completion_rel :: "(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "completion_rel = (\<lambda>X Y. Cauchy X \<and> Cauchy Y \<and> Vanishes (\<lambda>n. X n - Y n))"

quotient_type  (overloaded) 'a completion = "nat \<Rightarrow> 'a::real_normed_vector" / partial: completion_rel
  (* TODO: using (rule part_equivpI) would lead to a clearer proof, I think *)
  unfolding part_equivp_def
proof
  show "\<exists>x. completion_rel (x::nat \<Rightarrow> 'a) x"
    unfolding completion_rel_def proof
    show "Cauchy (\<lambda> _. 0::'a) \<and> Cauchy (\<lambda> _. 0::'a) \<and> Vanishes (\<lambda>n. (\<lambda> _. 0::'a) n - (\<lambda> _. 0::'a) n)"
      apply auto
      unfolding Cauchy_def
       apply auto
      unfolding Vanishes_def
      by auto
  qed
  show "\<forall>x y. completion_rel (x::nat \<Rightarrow> 'a) y = (completion_rel x x \<and> completion_rel y y \<and> completion_rel x = completion_rel y)"
    apply auto
    unfolding completion_rel_def
  proof auto
    show \<open>Cauchy x \<Longrightarrow> Cauchy y \<Longrightarrow> Vanishes (\<lambda>n. x n - y n) \<Longrightarrow> Vanishes (\<lambda>n. 0)\<close>
      for x y :: \<open>nat \<Rightarrow> 'a\<close>
    proof-
      assume \<open>Cauchy x\<close> and \<open>Cauchy y\<close> and \<open>Vanishes (\<lambda>n. x n - y n)\<close>
      show \<open>Vanishes (\<lambda>n. 0)\<close>
        unfolding Vanishes_def
        by simp
    qed
    show \<open>Cauchy x \<Longrightarrow> Cauchy y \<Longrightarrow> Vanishes (\<lambda>n. x n - y n) \<Longrightarrow> Vanishes (\<lambda>n. 0)\<close>
      for x y :: \<open>nat \<Rightarrow> 'a\<close>
    proof-
      assume \<open>Cauchy x\<close> and \<open>Cauchy y\<close> and \<open>Vanishes (\<lambda>n. x n - y n)\<close>
      show \<open>Vanishes (\<lambda>n. 0)\<close>
        unfolding Vanishes_def
        by simp
    qed
    show  \<open>Cauchy x \<Longrightarrow>
           Cauchy y \<Longrightarrow>
           Vanishes (\<lambda>n. x n - y n) \<Longrightarrow>
           (\<lambda>Y. Cauchy Y \<and> Vanishes (\<lambda>n. x n - Y n)) =
           (\<lambda>Y. Cauchy Y \<and> Vanishes (\<lambda>n. y n - Y n))\<close>
      for x y :: \<open>nat \<Rightarrow> 'a\<close>
    proof
      show "(Cauchy z \<and> Vanishes (\<lambda>n. x n - z n)) = (Cauchy z \<and> Vanishes (\<lambda>n. y n - z n))"
        if "Cauchy x"
          and "Cauchy y"
          and "Vanishes (\<lambda>n. x n - y n)"
        for z :: "nat \<Rightarrow> 'a"
        using that proof auto
        show "Vanishes (\<lambda>n. y n - z n)"
          if "Cauchy x"
            and "Cauchy y"
            and "Vanishes (\<lambda>n. x n - y n)"
            and "Cauchy z"
            and "Vanishes (\<lambda>n. x n - z n)"
        proof-
          have \<open>(\<lambda>n. x n - y n) \<longlonglongrightarrow> 0\<close>
            using Vanishes_def that(3) by auto
          moreover have \<open>(\<lambda>n. x n - z n) \<longlonglongrightarrow> 0\<close>
            using Vanishes_def that(5) by auto
          ultimately have \<open>(\<lambda> m. (\<lambda>n. x n - z n) m - (\<lambda>n. x n - y n) m ) \<longlonglongrightarrow> 0\<close>
            using tendsto_diff by force
          hence \<open>(\<lambda>n. y n - z n) \<longlonglongrightarrow> 0\<close>
            by simp
          thus ?thesis unfolding Vanishes_def by blast
        qed
        show "Vanishes (\<lambda>n. x n - z n)"
          if "Cauchy x"
            and "Cauchy y"
            and "Vanishes (\<lambda>n. x n - y n)"
            and "Cauchy z"
            and "Vanishes (\<lambda>n. y n - z n)"
        proof-
          have \<open>(\<lambda>n. x n - y n) \<longlonglongrightarrow> 0\<close>
            using Vanishes_def that(3) by auto
          moreover have \<open>(\<lambda>n. y n - z n) \<longlonglongrightarrow> 0\<close>
            using Vanishes_def that(5) by auto
          ultimately have \<open>(\<lambda> m. (\<lambda>n. x n - y n) m + (\<lambda>n. y n - z n) m ) \<longlonglongrightarrow> 0\<close>
            using tendsto_add by force
          hence \<open>(\<lambda>n. x n - z n) \<longlonglongrightarrow> 0\<close>
            by simp
          thus ?thesis unfolding Vanishes_def by blast
        qed
      qed
    qed
  qed
qed

lemma Cauchy_rep_completion:
  \<open>Cauchy (rep_completion x)\<close>
  by (metis Quotient3_completion Quotient3_rel_rep completion_rel_def)


instantiation completion :: (real_normed_vector) real_normed_vector
begin
lift_definition uminus_completion :: \<open>'a completion \<Rightarrow> 'a completion\<close>
  is \<open>\<lambda> x. (\<lambda> n. - (x n))\<close>
  unfolding completion_rel_def proof
  show "Cauchy (\<lambda>n. - (f n::'a))"
    if "Cauchy f \<and> Cauchy g \<and> Vanishes (\<lambda>n. (f n::'a) - g n)"
    for f :: "nat \<Rightarrow> 'a"
      and g :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy f\<close>
      using that
      by blast
    thus ?thesis unfolding Cauchy_def
      by (simp add: dist_minus)
  qed
  show "Cauchy (\<lambda>n. - (g n::'a)) \<and> Vanishes (\<lambda>n. - f n - - g n)"
    if "Cauchy f \<and> Cauchy g \<and> Vanishes (\<lambda>n. (f n::'a) - g n)"
    for f :: "nat \<Rightarrow> 'a"
      and g :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy (\<lambda>n. - (g n))\<close>
    proof-
      have \<open>Cauchy g\<close>
        using that by blast
      thus ?thesis unfolding Cauchy_def by (simp add: dist_minus)
    qed
    moreover have \<open>Vanishes (\<lambda>n. - f n - - g n)\<close>
    proof-
      have \<open>Vanishes (\<lambda>n. (f n) - (g n))\<close>
        using that by blast
      hence \<open>Vanishes (\<lambda>n. - ((f n) - (g n)))\<close>
        unfolding Vanishes_def
        using tendsto_minus_cancel_left by fastforce
      thus ?thesis by simp
    qed
    ultimately show ?thesis by blast
  qed
qed

lift_definition zero_completion :: \<open>'a completion\<close>
  is \<open>\<lambda> n. 0\<close>
  unfolding completion_rel_def
  apply auto
   apply (simp add: convergent_Cauchy convergent_const)
  unfolding Vanishes_def by simp

lift_definition minus_completion :: \<open>'a completion \<Rightarrow> 'a completion \<Rightarrow> 'a completion\<close>
  is \<open>\<lambda> x y. (\<lambda> n. x n - y n)\<close>
  unfolding completion_rel_def
proof
  show "Cauchy (\<lambda>n. (f1 n::'a) - f3 n)"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
      and "Cauchy f3 \<and> Cauchy f4 \<and> Vanishes (\<lambda>n. (f3 n::'a) - f4 n)"
    for f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
      and f3 :: "nat \<Rightarrow> 'a"
      and f4 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy f1\<close>
      by (simp add: that(1))
    moreover have \<open>Cauchy f3\<close>
      by (simp add: that(2))
    ultimately show ?thesis 
       sorry
      (* using Cauchy_minus by blast *)
  qed
  show "Cauchy (\<lambda>n. (f2 n::'a) - f4 n) \<and> Vanishes (\<lambda>n. f1 n - f3 n - (f2 n - f4 n))"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
      and "Cauchy f3 \<and> Cauchy f4 \<and> Vanishes (\<lambda>n. (f3 n::'a) - f4 n)"
    for f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
      and f3 :: "nat \<Rightarrow> 'a"
      and f4 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy (\<lambda>n. (f2 n) - (f4 n))\<close>
    proof-
      have \<open>Cauchy f2\<close>
        by (simp add: that(1))
      moreover have \<open>Cauchy f4\<close>
        by (simp add: that(2))
      ultimately show ?thesis 
         sorry
        (* using Cauchy_minus by blast *)
    qed
    moreover have \<open>Vanishes (\<lambda>n. f1 n - f3 n - (f2 n - f4 n))\<close>
    proof-
      have \<open>Vanishes (\<lambda>n. (f1 n) - (f2 n))\<close>
        by (simp add: that(1))        
      moreover have \<open>Vanishes (\<lambda>n. (f3 n) - (f4 n))\<close>
        by (simp add: that(2))        
      ultimately have \<open>Vanishes (\<lambda>n. ((f1 n) - (f2 n)) -  ((f3 n) - (f4 n)) )\<close>
        unfolding Vanishes_def
        using tendsto_diff by fastforce
      moreover have \<open>((f1 n) - (f2 n)) -  ((f3 n) - (f4 n)) = f1 n - f3 n - (f2 n - f4 n)\<close>
        for n
        by simp
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by blast
  qed
qed

lift_definition plus_completion :: \<open>'a completion \<Rightarrow> 'a completion \<Rightarrow> 'a completion\<close>
  is \<open>\<lambda> x y. (\<lambda> n. x n + y n)\<close>
  unfolding completion_rel_def
proof
  show "Cauchy (\<lambda>n. (f1 n::'a) + f3 n)"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
      and "Cauchy f3 \<and> Cauchy f4 \<and> Vanishes (\<lambda>n. (f3 n::'a) - f4 n)"
    for f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
      and f3 :: "nat \<Rightarrow> 'a"
      and f4 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy f1\<close>
      by (simp add: that(1))      
    moreover have \<open>Cauchy f3\<close>
      by (simp add: that(2))      
    ultimately show ?thesis 
       sorry
      (* using Cauchy_add by blast *)
  qed
  show "Cauchy (\<lambda>n. (f2 n::'a) + f4 n) \<and> Vanishes (\<lambda>n. f1 n + f3 n - (f2 n + f4 n))"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
      and "Cauchy f3 \<and> Cauchy f4 \<and> Vanishes (\<lambda>n. (f3 n::'a) - f4 n)"
    for f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
      and f3 :: "nat \<Rightarrow> 'a"
      and f4 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy (\<lambda>n. (f2 n) + (f4 n))\<close>
    proof-
      have \<open>Cauchy f2\<close>
        by (simp add: that(1))        
      moreover have \<open>Cauchy f4\<close>
        by (simp add: that(2))        
      ultimately show ?thesis 
     sorry
        (* using Cauchy_add by blast *)
    qed
    moreover have \<open>Vanishes (\<lambda>n. f1 n + f3 n - (f2 n + f4 n))\<close>
    proof-
      have \<open>Vanishes (\<lambda>n. (f1 n) - (f2 n))\<close>
        by (simp add: that(1))        
      moreover have \<open>Vanishes (\<lambda>n. (f3 n) - (f4 n))\<close>
        by (simp add: that(2))        
      ultimately have \<open>Vanishes (\<lambda>n. ((f1 n) - (f2 n)) + ((f3 n) - (f4 n)))\<close>
        unfolding Vanishes_def
        by (simp add: tendsto_add_zero)
      moreover have \<open>((f1 n) - (f2 n)) + ((f3 n) - (f4 n)) =  f1 n + f3 n - (f2 n + f4 n)\<close>
        for n
        by simp
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by blast
  qed
qed

lift_definition  norm_completion :: \<open>'a completion \<Rightarrow> real\<close>
  is \<open>\<lambda> x. lim (\<lambda> n. norm (x n))\<close>
  unfolding completion_rel_def
   sorry
(* proof-
  include nsa_notation
  fix f1 f2 :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assume \<open>Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. f1 n - f2 n)\<close>
  have \<open>Cauchy f1\<close> and \<open>Cauchy f2\<close> and \<open>Vanishes (\<lambda>n. f1 n - f2 n)\<close>
      apply (simp add: \<open>Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. f1 n - f2 n)\<close>)
     apply (simp add: \<open>Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. f1 n - f2 n)\<close>)
    by (simp add: \<open>Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. f1 n - f2 n)\<close>)
  have \<open>Cauchy (\<lambda>n. norm (f1 n))\<close>
    using \<open>Cauchy f1\<close>
    by (simp add: Cauchy_convergent_norm)
  hence \<open>convergent (\<lambda>n. norm (f1 n))\<close>
    by (simp add: real_Cauchy_convergent)
  have \<open>Cauchy (\<lambda>n. norm (f2 n))\<close>
    using \<open>Cauchy f2\<close>
    by (simp add: Cauchy_convergent_norm)
  hence \<open>convergent (\<lambda>n. norm (f2 n))\<close>
    by (simp add: real_Cauchy_convergent)

  have \<open>(\<lambda>n. f1 n - f2 n) \<longlonglongrightarrow> 0\<close>
    using \<open>Vanishes (\<lambda>n. f1 n - f2 n)\<close>
    unfolding Vanishes_def by blast
  hence \<open>(\<lambda>n. f1 n - f2 n) \<longlonglongrightarrow>\<^sub>N\<^sub>S 0\<close>
    by (simp add: LIMSEQ_NSLIMSEQ)
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> ( *f* f1) N - ( *f* f2) N \<approx> 0\<close>
    for N
    using NSLIMSEQ_D by fastforce
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> ( *f* f1) N \<approx> ( *f* f2) N\<close>
    for N
    using approx_minus_iff by auto
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> hnorm (( *f* f1) N) \<approx> hnorm (( *f* f2) N)\<close>
    for N
    by (simp add: approx_hnorm)
  moreover have \<open>N \<in> HNatInfinite \<Longrightarrow> hnorm (( *f* f1) N) \<approx> star_of (lim (\<lambda>n. norm (f1 n)))\<close>
    for N
  proof-
    assume \<open>N \<in> HNatInfinite\<close>
    have \<open>(\<lambda>n. norm (f1 n)) \<longlonglongrightarrow> (lim (\<lambda>n. norm (f1 n)))\<close>
      using \<open>convergent (\<lambda>n. norm (f1 n))\<close> convergent_LIMSEQ_iff by auto
    hence \<open>(\<lambda>n. norm (f1 n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S (lim (\<lambda>n. norm (f1 n)))\<close>
      by (simp add: LIMSEQ_NSLIMSEQ)
    hence \<open>N \<in> HNatInfinite \<Longrightarrow> ( *f* (\<lambda>n. norm (f1 n))) N \<approx> star_of (lim (\<lambda>n. norm (f1 n)))\<close>
      for N
      by (simp add: NSLIMSEQ_D)
    moreover have \<open>hnorm (( *f* f1) N) = ( *f* (\<lambda>n. norm (f1 n))) N\<close>
      for N
      by (simp add: starfun_hnorm)
    ultimately show  ?thesis
      by (simp add: \<open>N \<in> HNatInfinite\<close>) 
  qed
  moreover have \<open>N \<in> HNatInfinite \<Longrightarrow> hnorm (( *f* f2) N) \<approx> star_of (lim (\<lambda>n. norm (f2 n)))\<close>
    for N
  proof-
    assume \<open>N \<in> HNatInfinite\<close>
    have \<open>(\<lambda>n. norm (f2 n)) \<longlonglongrightarrow> (lim (\<lambda>n. norm (f2 n)))\<close>
      using \<open>convergent (\<lambda>n. norm (f2 n))\<close> convergent_LIMSEQ_iff by auto
    hence \<open>(\<lambda>n. norm (f2 n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S (lim (\<lambda>n. norm (f2 n)))\<close>
      by (simp add: LIMSEQ_NSLIMSEQ)
    hence \<open>N \<in> HNatInfinite \<Longrightarrow> ( *f* (\<lambda>n. norm (f2 n))) N \<approx> star_of (lim (\<lambda>n. norm (f2 n)))\<close>
      for N
      by (simp add: NSLIMSEQ_D)
    moreover have \<open>hnorm (( *f* f2) N) = ( *f* (\<lambda>n. norm (f2 n))) N\<close>
      for N
      by (simp add: starfun_hnorm)
    ultimately show  ?thesis
      by (simp add: \<open>N \<in> HNatInfinite\<close>) 
  qed    
  ultimately have \<open>star_of (lim (\<lambda>n. norm (f1 n))) \<approx> star_of (lim (\<lambda>n. norm (f2 n)))\<close>
  proof-
    assume a1: "\<And>N. N \<in> HNatInfinite \<Longrightarrow> hnorm (( *f* f1) N) \<approx> hnorm (( *f* f2) N)"
    assume a2: "\<And>N. N \<in> HNatInfinite \<Longrightarrow> hnorm (( *f* f1) N) \<approx> hypreal_of_real (lim (\<lambda>n. norm (f1 n)))"
    assume a3: "\<And>N. N \<in> HNatInfinite \<Longrightarrow> hnorm (( *f* f2) N) \<approx> hypreal_of_real (lim (\<lambda>n. norm (f2 n)))"
    have "(\<exists>f r. lim f \<noteq> (r::real)) \<or> hypreal_of_real (lim (\<lambda>n. norm (f1 n))) \<approx> hypreal_of_real (lim (\<lambda>n. norm (f2 n)))"
      by fastforce
    thus ?thesis
      using a3 a2 a1 by (meson NSLIMSEQ_LIMSEQ NSLIMSEQ_def approx_trans3 limI)
  qed 
  thus \<open>lim (\<lambda>n. norm (f1 n)) = lim (\<lambda>n. norm (f2 n))\<close>
    by simp
qed *)

lift_definition sgn_completion :: \<open>'a completion \<Rightarrow> 'a completion\<close>
  is \<open>\<lambda> x. (\<lambda> n. (x n) /\<^sub>R lim (\<lambda> n. norm (x n)) )\<close>
  unfolding completion_rel_def proof
  show "Cauchy (\<lambda>n. (f1 n::'a) /\<^sub>R lim (\<lambda>n. norm (f1 n)))"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
    for f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy f1\<close>
      by (simp add: that)
    thus ?thesis
      by (simp add: bounded_linear.Cauchy bounded_linear_scaleR_right)
  qed
  show "Cauchy (\<lambda>n. (f2 n::'a) /\<^sub>R lim (\<lambda>n. norm (f2 n))) \<and> 
      Vanishes (\<lambda>n. f1 n /\<^sub>R lim (\<lambda>n. norm (f1 n)) - f2 n /\<^sub>R lim (\<lambda>n. norm (f2 n)))"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
    for f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy (\<lambda>n. (f2 n) /\<^sub>R lim (\<lambda>n. norm (f2 n)))\<close>
    proof-
      have \<open>Cauchy f2\<close>
        by (simp add: that)
      thus ?thesis 
        using bounded_linear.Cauchy bounded_linear_scaleR_right by blast
    qed
    moreover have \<open>Vanishes (\<lambda>n. f1 n /\<^sub>R lim (\<lambda>n. norm (f1 n)) - f2 n /\<^sub>R lim (\<lambda>n. norm (f2 n)))\<close>
    proof-
      have \<open>Cauchy f1\<close>
        by (simp add: that)
      have \<open>Cauchy f2\<close>
        by (simp add: that)

      have \<open>Vanishes (\<lambda>n. (f1 n) - (f2 n))\<close>
        by (simp add: that)
      hence \<open>lim (\<lambda>n. norm (f1 n)) = lim (\<lambda>n. norm (f2 n))\<close>
        using \<open>Cauchy f1\<close> \<open>Cauchy f2\<close> norm_completion_def
        (* by (metis (full_types) Quotient3_completion Quotient3_def norm_completion.abs_eq completion_rel_def) *)
        sorry
      define L where \<open>L = lim (\<lambda>n. norm (f1 n))\<close>
      have \<open>Vanishes (\<lambda>n. (f1 n - f2 n) /\<^sub>R L)\<close>
      proof-
        have \<open>(\<lambda>n. (f1 n - f2 n)) \<longlonglongrightarrow> 0\<close>
          using \<open>Vanishes (\<lambda>n. (f1 n - f2 n))\<close>
          unfolding Vanishes_def by blast
        moreover have \<open>(\<lambda>n. (inverse L)) \<longlonglongrightarrow> (inverse L)\<close>
          by simp            
        ultimately have \<open>(\<lambda>n. (inverse L) *\<^sub>R (f1 n - f2 n)) \<longlonglongrightarrow> (inverse L) *\<^sub>R 0\<close>
          using Limits.tendsto_scaleR by blast
        thus ?thesis
          unfolding Vanishes_def by simp
      qed
      moreover have \<open>(f1 n - f2 n) /\<^sub>R L =  f1 n /\<^sub>R L - f2 n /\<^sub>R L\<close>
        for n
        using scale_right_diff_distrib
        by (simp add: ordered_field_class.sign_simps(27))        
      ultimately have \<open>Vanishes (\<lambda>n. f1 n /\<^sub>R L - f2 n /\<^sub>R L)\<close>
        by simp
      thus ?thesis unfolding L_def using \<open>lim (\<lambda>n. norm (f1 n)) = lim (\<lambda>n. norm (f2 n))\<close>
        by simp
    qed
    ultimately show ?thesis by blast
  qed
qed

lift_definition scaleR_completion :: \<open>real \<Rightarrow> 'a completion \<Rightarrow> 'a completion\<close>
  is \<open>\<lambda> r x. (\<lambda> n. r *\<^sub>R (x n))\<close>
  unfolding completion_rel_def proof
  show "Cauchy (\<lambda>n. r *\<^sub>R (f1 n::'a))"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
    for r :: real
      and f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy f1\<close>
      using that by blast
    thus ?thesis
      using bounded_linear.Cauchy bounded_linear_scaleR_right by blast
  qed
  show "Cauchy (\<lambda>n. r *\<^sub>R (f2 n::'a)) \<and> Vanishes (\<lambda>n. r *\<^sub>R f1 n - r *\<^sub>R f2 n)"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
    for r :: real
      and f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy (\<lambda>n. r *\<^sub>R (f2 n))\<close>
    proof-
      have \<open>Cauchy f2\<close>
        using that by blast
      thus ?thesis
        using bounded_linear.Cauchy bounded_linear_scaleR_right by blast
    qed
    moreover have \<open>Vanishes (\<lambda>n. r *\<^sub>R f1 n - r *\<^sub>R f2 n)\<close>
    proof-
      have \<open>Vanishes (\<lambda>n. (f1 n) - (f2 n))\<close>
        using that by blast
      hence \<open>(\<lambda>n. (f1 n) - (f2 n)) \<longlonglongrightarrow> 0\<close>
        unfolding Vanishes_def by blast
      moreover have \<open>(\<lambda>n. r) \<longlonglongrightarrow> r\<close>
        by simp
      ultimately have \<open>(\<lambda>n. r *\<^sub>R (f1 n - f2 n)) \<longlonglongrightarrow> r *\<^sub>R 0\<close>
        using Limits.tendsto_scaleR by blast
      moreover have \<open>r *\<^sub>R (f1 n - f2 n) = r *\<^sub>R f1 n - r *\<^sub>R f2 n\<close>
        for n
        using scale_right_diff_distrib
        by (simp add: ordered_field_class.sign_simps(27))
      ultimately show ?thesis unfolding Vanishes_def
        by auto 
    qed
    ultimately show ?thesis by blast
  qed
qed     

lift_definition dist_completion :: \<open>'a completion \<Rightarrow> 'a completion \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. lim (\<lambda> n. norm (f n - g n))\<close>
  unfolding completion_rel_def
   sorry
(* proof-
  include nsa_notation
  fix f1 f2 f3 f4 :: \<open>nat \<Rightarrow> 'a\<close>
  assume \<open>Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. f1 n - f2 n)\<close> and
    \<open>Cauchy f3 \<and> Cauchy f4 \<and> Vanishes (\<lambda>n. f3 n - f4 n)\<close> 
  have \<open>Cauchy f1\<close> and \<open>Cauchy f2\<close> and \<open>Vanishes (\<lambda>n. f1 n - f2 n)\<close>
    using \<open>Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. f1 n - f2 n)\<close>
    by auto 
  have \<open>Cauchy f3\<close> and \<open>Cauchy f4\<close> and \<open>Vanishes (\<lambda>n. f3 n - f4 n)\<close>
    using \<open>Cauchy f3 \<and> Cauchy f4 \<and> Vanishes (\<lambda>n. f3 n - f4 n)\<close>
    by auto
  have \<open>N \<in> HNatInfinite \<Longrightarrow> ( *f* (\<lambda>n. norm (f1 n - f3 n))) N \<approx> star_of (lim (\<lambda>n. norm (f1 n - f3 n)))\<close>
    for N
  proof-
    assume \<open>N \<in> HNatInfinite\<close>
    have \<open>Cauchy (\<lambda>n. (f1 n - f3 n))\<close>
      using \<open>Cauchy f1\<close> \<open>Cauchy f3\<close>
      by (simp add: Cauchy_minus)
    hence \<open>Cauchy (\<lambda>n. norm (f1 n - f3 n))\<close>
      using Cauchy_convergent_norm by auto
    hence \<open>convergent (\<lambda>n. norm (f1 n - f3 n))\<close>
      by (simp add: real_Cauchy_convergent)
    hence \<open>NSconvergent (\<lambda>n. norm (f1 n - f3 n))\<close>
      using convergent_NSconvergent_iff by auto
    thus ?thesis
      using \<open>N \<in> HNatInfinite\<close>
      by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff lim_nslim_iff)
  qed
  moreover have \<open>N \<in> HNatInfinite \<Longrightarrow> ( *f* (\<lambda>n. norm (f2 n - f4 n))) N \<approx> star_of (lim (\<lambda>n. norm (f2 n - f4 n)))\<close>
    for N
  proof-
    assume \<open>N \<in> HNatInfinite\<close>
    have \<open>Cauchy (\<lambda>n. (f2 n - f4 n))\<close>
      using \<open>Cauchy f2\<close> \<open>Cauchy f4\<close>
      by (simp add: Cauchy_minus)
    hence \<open>Cauchy (\<lambda>n. norm (f2 n - f4 n))\<close>
      using Cauchy_convergent_norm by auto
    hence \<open>convergent (\<lambda>n. norm (f2 n - f4 n))\<close>
      by (simp add: real_Cauchy_convergent)
    hence \<open>NSconvergent (\<lambda>n. norm (f2 n - f4 n))\<close>
      using convergent_NSconvergent_iff by auto
    thus ?thesis
      using \<open>N \<in> HNatInfinite\<close>
      by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff lim_nslim_iff)
  qed
  moreover have \<open>N \<in> HNatInfinite \<Longrightarrow> ( *f* (\<lambda>n. norm (f1 n - f3 n))) N \<approx> ( *f* (\<lambda>n. norm (f2 n - f4 n))) N\<close>
    for N
  proof-
    assume \<open>N \<in> HNatInfinite\<close>
    from  \<open>Vanishes (\<lambda>n. f1 n - f2 n)\<close> \<open>Vanishes (\<lambda>n. f3 n - f4 n)\<close>
    have  \<open>Vanishes (\<lambda>n. (f1 n - f2 n) - (f3 n - f4 n))\<close>
      unfolding Vanishes_def
      using tendsto_diff by fastforce
    hence  \<open>(\<lambda>n. (f1 n - f2 n) - (f3 n - f4 n))\<longlonglongrightarrow>\<^sub>N\<^sub>S 0\<close>
      unfolding Vanishes_def
      by (simp add: LIMSEQ_NSLIMSEQ_iff)
    moreover have \<open>(f1 n - f2 n) - (f3 n - f4 n) = (f1 n - f3 n) - (f2 n - f4 n)\<close>
      for n
      by simp
    ultimately have \<open>(\<lambda>n. (f1 n - f3 n) - (f2 n - f4 n))\<longlonglongrightarrow>\<^sub>N\<^sub>S 0\<close>
      by simp
    hence \<open>( *f* (\<lambda>n. (f1 n - f3 n) - (f2 n - f4 n))) N \<approx> 0\<close>
      using NSLIMSEQ_D \<open>N \<in> HNatInfinite\<close> by fastforce
    hence \<open>( *f* (\<lambda>n. (f1 n - f3 n))) N - ( *f* (\<lambda> n. (f2 n - f4 n))) N \<approx> 0\<close>
      by auto
    hence \<open>( *f* (\<lambda>n. (f1 n - f3 n))) N \<approx> ( *f* (\<lambda> n. (f2 n - f4 n))) N\<close>
      using approx_minus_iff by auto
    hence \<open>hnorm (( *f* (\<lambda>n. (f1 n - f3 n))) N) \<approx> hnorm (( *f* (\<lambda> n. (f2 n - f4 n))) N)\<close>
      by (simp add: approx_hnorm)      
    thus \<open>( *f* (\<lambda>n. norm (f1 n - f3 n))) N \<approx> ( *f* (\<lambda>n. norm (f2 n - f4 n))) N\<close>
      by (simp add: starfun_norm)      
  qed
  ultimately have \<open>N \<in> HNatInfinite \<Longrightarrow> star_of (lim (\<lambda>n. norm (f1 n - f3 n))) \<approx> star_of (lim (\<lambda>n. norm (f2 n - f4 n)))\<close>
    for N
    by (meson approx_trans3)
  hence \<open>star_of (lim (\<lambda>n. norm (f1 n - f3 n))) \<approx> star_of (lim (\<lambda>n. norm (f2 n - f4 n)))\<close>
    using HNatInfinite_whn by blast  
  thus \<open>lim (\<lambda>n. norm (f1 n - f3 n)) = lim (\<lambda>n. norm (f2 n - f4 n))\<close>
    by simp
qed *)

definition uniformity_completion :: \<open>('a completion \<times> 'a completion) filter\<close>
  where  \<open>uniformity_completion = (INF e\<in>{0<..}. principal {((f::'a completion), (g::'a completion)). dist f g < e})\<close>

definition open_completion :: \<open>('a completion) set \<Rightarrow> bool\<close>
  where \<open>open_completion = (\<lambda> U::('a completion) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity))\<close>

instance 
proof
  show "dist (x::'a completion) y = norm (x - y)"
    for x :: "'a completion"
      and y :: "'a completion"
    apply transfer
    by simp
  show "(a::'a completion) + b + c = a + (b + c)"
    for a :: "'a completion"
      and b :: "'a completion"
      and c :: "'a completion"
    apply transfer
    unfolding completion_rel_def proof
    show "Cauchy (\<lambda>n. (a n::'a) + b n + c n)"
      if "Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. (a n::'a) - a n)"
        and "Cauchy b \<and> Cauchy b \<and> Vanishes (\<lambda>n. (b n::'a) - b n)"
        and "Cauchy c \<and> Cauchy c \<and> Vanishes (\<lambda>n. (c n::'a) - c n)"
      for a :: "nat \<Rightarrow> 'a"
        and b :: "nat \<Rightarrow> 'a"
        and c :: "nat \<Rightarrow> 'a"
     sorry
      (* using that Cauchy_add by auto  *)
    show "Cauchy (\<lambda>n. (a n::'a) + (b n + c n)) \<and> Vanishes (\<lambda>n. a n + b n + c n - (a n + (b n + c n)))"
      if "Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. (a n::'a) - a n)"
        and "Cauchy b \<and> Cauchy b \<and> Vanishes (\<lambda>n. (b n::'a) - b n)"
        and "Cauchy c \<and> Cauchy c \<and> Vanishes (\<lambda>n. (c n::'a) - c n)"
      for a :: "nat \<Rightarrow> 'a"
        and b :: "nat \<Rightarrow> 'a"
        and c :: "nat \<Rightarrow> 'a"
      using that apply auto
     sorry
      (* using Cauchy_add by auto *)
  qed
  show "(a::'a completion) + b = b + a"
    for a :: "'a completion"
      and b :: "'a completion"
    apply transfer unfolding completion_rel_def proof
    show "Cauchy (\<lambda>n. (a n::'a) + b n)"
      if "Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. (a n::'a) - a n)"
        and "Cauchy b \<and> Cauchy b \<and> Vanishes (\<lambda>n. (b n::'a) - b n)"
      for a :: "nat \<Rightarrow> 'a"
        and b :: "nat \<Rightarrow> 'a"
      using that
     sorry
      (* by (simp add: Cauchy_add)  *)
    show "Cauchy (\<lambda>n. (b n::'a) + a n) \<and> Vanishes (\<lambda>n. a n + b n - (b n + a n))"
      if "Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. (a n::'a) - a n)"
        and "Cauchy b \<and> Cauchy b \<and> Vanishes (\<lambda>n. (b n::'a) - b n)"
      for a :: "nat \<Rightarrow> 'a"
        and b :: "nat \<Rightarrow> 'a"
      using that apply auto
      using \<open>\<And>b a. \<lbrakk>Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. a n - a n); Cauchy b \<and> Cauchy b \<and> Vanishes (\<lambda>n. b n - b n)\<rbrakk> \<Longrightarrow> Cauchy (\<lambda>n. a n + b n)\<close> that(1) that(2) by blast 
  qed
  show "(0::'a completion) + a = a"
    for a :: "'a completion"
    apply transfer unfolding completion_rel_def proof
    show "Cauchy (\<lambda>n. (0::'a) + a n)"
      if "Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. (a n::'a) - a n)"
      for a :: "nat \<Rightarrow> 'a"
      using that by auto
    show "Cauchy a \<and> Vanishes (\<lambda>n. (0::'a) + a n - a n)"
      if "Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. (a n::'a) - a n)"
      for a :: "nat \<Rightarrow> 'a"
      using that by auto
  qed
  show "- (a::'a completion) + a = 0"
    for a :: "'a completion"
    apply transfer apply auto
    by (simp add: Completion.zero_completion.rsp) 
  show "(a::'a completion) - b = a + - b"
    for a :: "'a completion"
      and b :: "'a completion"
    apply transfer apply auto unfolding completion_rel_def apply auto
     sorry
    (* by (simp add: Cauchy_minus) *)

  show "a *\<^sub>R ((x::'a completion) + y) = a *\<^sub>R x + a *\<^sub>R y"
    for a :: real
      and x :: "'a completion"
      and y :: "'a completion"
     sorry
(*     apply transfer unfolding completion_rel_def apply auto
      apply (simp add: Cauchy_add Cauchy_scaleR)
     apply (simp add: Cauchy_add Cauchy_scaleR)
    unfolding Vanishes_def apply auto proof
    show "\<forall>\<^sub>F n in sequentially. dist (a *\<^sub>R (x n + y n) - (a *\<^sub>R x n + a *\<^sub>R y n)) (0::'a) < e"
      if "Cauchy (y::nat \<Rightarrow> 'a)"
        and "Cauchy (x::nat \<Rightarrow> 'a)"
        and "(0::real) < e"
      for a :: real
        and x :: "nat \<Rightarrow> 'a"
        and y :: "nat \<Rightarrow> 'a"
        and e :: real
    proof-
      have \<open>a *\<^sub>R (x n + y n) = (a *\<^sub>R x n + a *\<^sub>R y n)\<close>
        for n
        by (simp add: pth_6)
      have \<open>a *\<^sub>R (x n + y n) - (a *\<^sub>R x n + a *\<^sub>R y n) = 0\<close>
        for n
        by (simp add: \<open>\<And>n. a *\<^sub>R (x n + y n) = a *\<^sub>R x n + a *\<^sub>R y n\<close>)
      hence \<open>dist (a *\<^sub>R (x n + y n) - (a *\<^sub>R x n + a *\<^sub>R y n)) (0::'a) = 0\<close>
        for n
        by simp
      thus ?thesis
        by (simp add: that(3)) 
    qed
  qed *)

  show "(a + b) *\<^sub>R (x::'a completion) = a *\<^sub>R x + b *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a completion"
     sorry
(*     apply transfer unfolding completion_rel_def apply auto
      apply (simp add: Cauchy_scaleR)
     apply (simp add: Cauchy_add Cauchy_scaleR)
    unfolding Vanishes_def proof
    show "\<forall>\<^sub>F n in sequentially. dist ((a + b) *\<^sub>R x n - (a *\<^sub>R x n + b *\<^sub>R x n)) (0::'a) < e"
      if "Cauchy (x::nat \<Rightarrow> 'a)"
        and "(\<lambda>n. 0::'a) \<longlonglongrightarrow> 0"
        and "(0::real) < e"
      for a :: real
        and b :: real
        and x :: "nat \<Rightarrow> 'a"
        and e :: real
    proof-
      have \<open>(a + b) *\<^sub>R x n = (a *\<^sub>R x n + b *\<^sub>R x n)\<close>
        for n
        by (simp add: scaleR_add_left)
      hence \<open>(a + b) *\<^sub>R x n - (a *\<^sub>R x n + b *\<^sub>R x n) = 0\<close>
        for n
        by simp
      hence \<open>dist ((a + b) *\<^sub>R x n - (a *\<^sub>R x n + b *\<^sub>R x n)) (0::'a) = 0\<close>
        for n
        by simp
      thus ?thesis
        by (simp add: that(3)) 
    qed
  qed *)

  show "a *\<^sub>R b *\<^sub>R (x::'a completion) = (a * b) *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a completion"
    apply transfer apply auto unfolding completion_rel_def apply auto
    using bounded_linear.Cauchy bounded_linear_scaleR_right by blast

  show "1 *\<^sub>R (x::'a completion) = x"
    for x :: "'a completion"
    apply transfer by auto

  show "sgn (x::'a completion) = inverse (norm x) *\<^sub>R x"
    for x :: "'a completion"
    apply transfer unfolding completion_rel_def apply auto
    using bounded_linear.Cauchy bounded_linear_scaleR_right by blast

  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a completion) y < e})"
    by (simp add: Completion.uniformity_completion_def)    

  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a completion) = x \<longrightarrow> y \<in> U)"
    for U :: "'a completion set"
    by (simp add: Completion.open_completion_def)

  show "(norm (x::'a completion) = 0) = (x = 0)"
    for x :: "'a completion"
    apply transfer apply auto unfolding completion_rel_def Vanishes_def apply auto
      apply (metis completion_rel_def zero_completion.rsp)
     sorry
(*      apply (metis Cauchy_convergent_norm convergent_eq_Cauchy limI tendsto_norm_zero_iff)
    by (simp add: limI tendsto_norm_zero) *)

  show "norm ((x::'a completion) + y) \<le> norm x + norm y"
    for x :: "'a completion"
      and y :: "'a completion"
    apply transfer unfolding completion_rel_def apply auto
  proof-
    fix x y :: \<open>nat \<Rightarrow> 'a\<close>
    assume \<open>Cauchy x\<close> and \<open>Cauchy y\<close> and \<open>Vanishes (\<lambda>n. 0)\<close>
    from \<open>Cauchy x\<close>
    have \<open>Cauchy (\<lambda> n. norm (x n))\<close>
     sorry
      (* by (simp add: Cauchy_convergent_norm) *)
    hence \<open>convergent (\<lambda> n. norm (x n))\<close>
      by (simp add: real_Cauchy_convergent)
    from \<open>Cauchy y\<close>
    have \<open>Cauchy (\<lambda> n. norm (y n))\<close>
     sorry
      (* by (simp add: Cauchy_convergent_norm) *)
    hence \<open>convergent (\<lambda> n. norm (y n))\<close>
      by (simp add: real_Cauchy_convergent)
    have \<open>convergent (\<lambda> n. norm (x n) + norm (y n))\<close>
      by (simp add: \<open>convergent (\<lambda>n. norm (x n))\<close> \<open>convergent (\<lambda>n. norm (y n))\<close> convergent_add)
    have \<open>Cauchy (\<lambda> n. (x n + y n))\<close>
      using \<open>Cauchy x\<close> \<open>Cauchy y\<close>  
     sorry
      (* by (simp add: Cauchy_add) *)
    hence \<open>Cauchy (\<lambda> n. norm (x n + y n))\<close>
     sorry
      (* by (simp add: Cauchy_convergent_norm) *)
    hence \<open>convergent (\<lambda> n. norm (x n + y n))\<close>
      by (simp add: Cauchy_convergent)
    have \<open>norm (x n + y n) \<le> norm (x n) + norm (y n)\<close>
      for n
      by (simp add: norm_triangle_ineq)
    hence \<open>lim (\<lambda> n. norm (x n + y n)) \<le> lim (\<lambda> n. norm (x n) + norm (y n))\<close>
     sorry
(*       using \<open>convergent (\<lambda> n. norm (x n + y n))\<close> \<open>convergent (\<lambda> n. norm (x n) + norm (y n))\<close> lim_leq
      by auto *)
    moreover have \<open>lim (\<lambda> n. norm (x n) + norm (y n)) = lim (\<lambda> n. norm (x n)) + lim (\<lambda> n. norm (y n))\<close>
     sorry
      (* using \<open>convergent (\<lambda> n. norm (x n))\<close>  \<open>convergent (\<lambda> n. norm (y n))\<close> lim_add *)
      (* by blast *)
    ultimately show  \<open>lim (\<lambda>n. norm (x n + y n))
           \<le> lim (\<lambda>n. norm (x n)) + lim (\<lambda>n. norm (y n))\<close>
      by simp
  qed

  show "norm (a *\<^sub>R (x::'a completion)) = \<bar>a\<bar> * norm x"
    for a :: real
      and x :: "'a completion"
    apply transfer unfolding completion_rel_def apply auto
  proof-
    fix a::real and x::\<open>nat \<Rightarrow> 'a\<close>
    assume \<open>Cauchy x\<close> and \<open>Vanishes (\<lambda>n. 0)\<close>
    hence \<open>convergent (\<lambda> n. norm (x n))\<close>
     sorry
      (* using Cauchy_convergent_iff Cauchy_convergent_norm by blast *)
    moreover have \<open>norm (a *\<^sub>R x n) = \<bar>a\<bar> * norm (x n)\<close>
      for n
      by simp
    ultimately have \<open>lim (\<lambda>n. norm (a *\<^sub>R x n)) =  lim (\<lambda>n. \<bar>a\<bar> * norm (x n))\<close>
      by simp
    also have \<open>lim (\<lambda>n. \<bar>a\<bar> * norm (x n)) = \<bar>a\<bar> * lim (\<lambda>n. norm (x n))\<close>
      using  \<open>convergent (\<lambda> n. norm (x n))\<close>
     sorry
(*         lim_scaleR[where r = "\<bar>a\<bar>" and x = "\<lambda> n. norm (x n)"] 
      by auto
 *)
  finally have  \<open>lim (\<lambda>n. norm (a *\<^sub>R x n)) = \<bar>a\<bar> * lim (\<lambda>n. norm (x n))\<close>
      by blast
    thus \<open>lim (\<lambda>n. \<bar>a\<bar> * norm (x n)) = \<bar>a\<bar> * lim (\<lambda>n. norm (x n))\<close>
      by simp
  qed
qed
end


instantiation completion :: (real_normed_vector) banach
begin
instance
proof
  show "convergent (X::nat \<Rightarrow> 'a completion)"
    if "Cauchy (X::nat \<Rightarrow> 'a completion)"
    for X :: "nat \<Rightarrow> 'a completion"
  proof-
    have \<open>(\<lambda> i. inverse (real (Suc i))) \<longlonglongrightarrow> 0\<close>
      using LIMSEQ_inverse_real_of_nat by auto
    hence \<open>\<forall> e > 0. \<exists> H. \<forall> i \<ge> H. dist (inverse (real (Suc i))) 0 < e\<close>
      using Real_Vector_Spaces.metric_LIMSEQ_D by blast
    hence \<open>\<forall> e > 0. \<exists> H. \<forall> i \<ge> H. norm (inverse (real (Suc i))) < e\<close>
      by (simp add: dist_norm)
    hence \<open>\<forall> e > 0. \<exists> H. \<forall> i \<ge> H. inverse (real (Suc i)) < e\<close>
      by auto
    hence \<open>\<exists> H. \<forall> e > 0. \<forall> i \<ge> H e. inverse (real (Suc i)) < e\<close>
      by metis
    then obtain H where \<open>\<forall> e > 0. \<forall> i \<ge> H e. inverse (real (Suc i)) < e\<close>
      by blast

    have \<open>\<forall> e > 0. \<exists> R. \<forall> i \<ge> R. \<forall> j \<ge> R. lim (\<lambda> m. norm (rep_completion (X i) m - rep_completion (X j) m)) < e\<close>
      using \<open>Cauchy X\<close>
      unfolding Cauchy_def dist_completion_def
      by auto
    hence \<open>\<exists> R. \<forall> e > 0. \<forall> i \<ge> R e. \<forall> j \<ge> R e. lim (\<lambda> m. norm (rep_completion (X i) m - rep_completion (X j) m)) < e\<close>
      by metis
    then obtain R where \<open>\<forall> e > 0. \<forall> i \<ge> R e. \<forall> j \<ge> R e. lim (\<lambda> m. norm (rep_completion (X i) m - rep_completion (X j) m)) < e\<close>
      by blast

    have \<open>Cauchy (rep_completion (X i))\<close>
      for i
      by (metis Quotient3_completion Quotient3_rel_rep completion_rel_def)      
    hence \<open>\<exists> T. \<forall> m \<ge> T. \<forall> n \<ge> T. norm (rep_completion (X i) m - rep_completion (X i) n) < inverse (of_nat (Suc i))\<close>
      for i
      unfolding Cauchy_def
      by (simp add: dist_norm)
    hence \<open>\<forall> i. \<exists> T. \<forall> m \<ge> T. norm (rep_completion (X i) m - rep_completion (X i) T) < inverse (of_nat (Suc i))\<close>
      by blast
    hence \<open>\<exists> T. \<forall> i. \<forall> m \<ge> T i. norm (rep_completion (X i) m - rep_completion (X i) (T i)) < inverse (of_nat (Suc i))\<close>
      by metis
    then obtain T where \<open>\<forall> i. \<forall> m \<ge> T i. norm (rep_completion (X i) m - rep_completion (X i) (T i)) < inverse (of_nat (Suc i))\<close>
      by blast
    define l where \<open>l i = rep_completion (X i) (T i)\<close> for i
    from \<open>\<forall> i. \<forall> m \<ge> T i. norm (rep_completion (X i) m - rep_completion (X i) (T i)) < inverse (of_nat (Suc i))\<close>
    have \<open>\<forall> i. \<forall> m \<ge> T i. norm (rep_completion (X i) m - l i) < inverse (of_nat (Suc i))\<close>
      unfolding l_def by blast
    have \<open>convergent (\<lambda> m. norm ( rep_completion (X i) m - rep_completion (X j) m ))\<close>
      for i j
    proof-
      have \<open>Cauchy (rep_completion (X i))\<close>
        by (simp add: \<open>\<And>i. Cauchy (rep_completion (X i))\<close>)
      moreover have \<open>Cauchy (rep_completion (X j))\<close>
        by (simp add: \<open>\<And>i. Cauchy (rep_completion (X i))\<close>)
      ultimately have \<open>Cauchy (\<lambda> m. rep_completion (X i) m - rep_completion (X j) m)\<close>
     sorry
        (* using Cauchy_minus by blast *)
      hence \<open>Cauchy (\<lambda> m. norm (rep_completion (X i) m - rep_completion (X j) m) )\<close>
     sorry
        (* by (simp add: Cauchy_convergent_norm) *)
      thus ?thesis
        by (simp add: real_Cauchy_convergent) 
    qed

    have \<open>convergent (\<lambda> m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)))\<close>
      for i j
    proof-
      define a where \<open>a m = norm ( rep_completion (X i) m - rep_completion (X j) m )\<close> for m
      have \<open>convergent a\<close>
        using \<open>\<And> i j. convergent (\<lambda> m. norm ( rep_completion (X i) m - rep_completion (X j) m ))\<close>
        unfolding a_def by auto
      hence \<open>convergent (\<lambda> m.  a (m + (T i + T j)))\<close>
        using Limits.convergent_ignore_initial_segment
        by blast
      moreover have \<open>m + (T i + T j) = m + T i + T j\<close>
        for m
        by simp
      ultimately have \<open>convergent (\<lambda> m.  a (m + T i + T j))\<close>
        by simp
      thus \<open>convergent (\<lambda> m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)))\<close>
        unfolding a_def by simp
    qed

    have \<open>Cauchy l\<close>
    proof-
      have \<open>(l i - l j) =
              (l i - rep_completion (X i) m)
           +  (rep_completion (X i) m - rep_completion (X j) m)
           +  (rep_completion (X j) m - l j)\<close>
        for i j m
        by simp
      have \<open>norm (l i - l j) =
         norm ( (l i - rep_completion (X i) m)
           +  (rep_completion (X i) m - rep_completion (X j) m)
           +  (rep_completion (X j) m - l j) )\<close>
        for i j m
        by simp
      hence \<open>norm (l i - l j) \<le>
             norm (l i - rep_completion (X i) m)
           + norm (rep_completion (X i) m - rep_completion (X j) m)
           + norm (rep_completion (X j) m - l j)\<close>
        for i j m
        by (smt norm_triangle_ineq)
      moreover have \<open>m \<ge> T i \<Longrightarrow> norm (l i - rep_completion (X i) m) \<le> inverse (of_nat (Suc i))\<close>
        for i m
        using \<open>\<forall> i. \<forall> m \<ge> T i. norm (rep_completion (X i) m - l i) < inverse (of_nat (Suc i))\<close>
        by (smt norm_minus_commute)
      moreover have \<open>m \<ge> T j \<Longrightarrow> norm (rep_completion (X j) m - l j) \<le> inverse (of_nat (Suc j))\<close>
        for j m
        using \<open>\<forall> i. \<forall> m \<ge> T i. norm (rep_completion (X i) m - l i) < inverse (of_nat (Suc i))\<close>
        by fastforce
      ultimately have \<open>m \<ge> T i \<Longrightarrow> m \<ge> T j \<Longrightarrow> norm (l i - l j) \<le>
             inverse (of_nat (Suc i))
           + norm (rep_completion (X i) m - rep_completion (X j) m)
           + inverse (of_nat (Suc j))\<close>
        for i j m
        by smt
      hence \<open>norm (l i - l j) \<le>
             inverse (of_nat (Suc i))
           + norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j))
           + inverse (of_nat (Suc j))\<close>
        for i j m
        by fastforce
      moreover have \<open>convergent ( \<lambda> m.
             inverse (of_nat (Suc i))
           + norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j))
           + inverse (of_nat (Suc j)) )\<close>
        for i j
        by (simp add: convergent_add_const_right_iff \<open>\<And>j i. convergent (\<lambda>m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)))\<close> convergent_add_const_iff)  
      ultimately have \<open>norm (l i - l j) \<le> lim ( \<lambda> m.
             inverse (of_nat (Suc i))
           + norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j))
           + inverse (of_nat (Suc j)) )\<close>
        for i j
        sorry
(*         using lim_ge
        by simp *)
      moreover have \<open>lim ( \<lambda> m.
             inverse (of_nat (Suc i))
           + norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j))
           + inverse (of_nat (Suc j)) )
          = inverse (of_nat (Suc i)) 
        + lim ( \<lambda> m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)) )
        + inverse (of_nat (Suc j))\<close>
        for i j
      proof-
        have \<open>lim ( \<lambda> m.
           norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j))
           + inverse (of_nat (Suc j)) )
          = lim ( \<lambda> m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)) ) 
            + inverse (of_nat (Suc j))\<close>
     sorry
          (* using lim_add_const_right[where c = "inverse (of_nat (Suc j))" and x = "(\<lambda> m.
           norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)))"] *)
          (* by (simp add: \<open>\<And>j i. convergent (\<lambda>m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)))\<close>)  *)
        have \<open>convergent ( \<lambda> m.
           norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j))
           + inverse (of_nat (Suc j)) )\<close>
          using \<open>\<And>j i. convergent (\<lambda>m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)))\<close>
          by (simp add: convergent_add_const_right_iff)
        hence \<open>lim ( \<lambda> m. inverse (of_nat (Suc i)) + (
           norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j))
           + inverse (of_nat (Suc j)) ) ) =  inverse (of_nat (Suc i)) + lim ( \<lambda> m.
           norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j))
           + inverse (of_nat (Suc j)) )\<close>
     sorry
          (* using lim_add_const_left by auto *)
        also have \<open>\<dots> = inverse (of_nat (Suc i)) + lim ( \<lambda> m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)) ) 
            + inverse (of_nat (Suc j))\<close>
          using \<open>lim ( \<lambda> m.
           norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j))
           + inverse (of_nat (Suc j)) )
          = lim ( \<lambda> m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)) ) 
            + inverse (of_nat (Suc j))\<close>
          by simp
        finally have \<open>lim ( \<lambda> m. inverse (of_nat (Suc i)) + (
           norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j))
           + inverse (of_nat (Suc j)) ) ) = inverse (of_nat (Suc i)) + lim ( \<lambda> m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)) ) 
            + inverse (of_nat (Suc j))\<close>
          by blast
        moreover have \<open>( \<lambda> m. inverse (of_nat (Suc i)) + (
           norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j))
           + inverse (of_nat (Suc j)) ) )
          = ( \<lambda> m. inverse (of_nat (Suc i)) 
             + norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j))
             + inverse (of_nat (Suc j)) )\<close>
          by auto
        ultimately show ?thesis by simp
      qed
      ultimately have \<open>norm (l i - l j) \<le> inverse (of_nat (Suc i)) 
        + lim ( \<lambda> m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)) )
        + inverse (of_nat (Suc j))\<close>
        for i j
        by simp
      moreover have \<open>e > 0 \<Longrightarrow> i \<ge> R e \<Longrightarrow> j \<ge> R e \<Longrightarrow>
             lim ( \<lambda> m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)) ) < e\<close>
        for i j e
      proof-
        assume \<open>e > 0\<close> and \<open>i \<ge> R e\<close> and \<open>j \<ge> R e\<close>
        have \<open>e > 0 \<Longrightarrow> i \<ge> R e \<Longrightarrow> j \<ge> R e \<Longrightarrow>
             lim ( \<lambda> m. norm (rep_completion (X i) m - rep_completion (X j) m) ) < e\<close>
          using \<open>\<forall>e>0. \<forall>i\<ge>R e. \<forall>j\<ge>R e. lim (\<lambda>m. norm (rep_completion (X i) m - rep_completion (X j) m)) < e\<close> by auto
        moreover have \<open>lim ( \<lambda> m. norm (rep_completion (X i) m - rep_completion (X j) m) )
              = lim ( \<lambda> m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)) )\<close>
        proof-
          have \<open>lim ( \<lambda> m. norm (rep_completion (X i) m - rep_completion (X j) m) )
              = lim (\<lambda> n. ( \<lambda> m. norm (rep_completion (X i) m - rep_completion (X j) m) ) (n + (T i + T j)) )\<close>
            using \<open>convergent ( \<lambda> m. norm (rep_completion (X i) m - rep_completion (X j) m) )\<close>
            sorry
            (* by auto *)
          moreover have \<open>n + (T i + T j) = n + T i + T j\<close>
            for n
            by auto
          ultimately show ?thesis by auto
        qed
        ultimately have \<open>e > 0 \<Longrightarrow> i \<ge> R e \<Longrightarrow> j \<ge> R e \<Longrightarrow>
             lim ( \<lambda> m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)) ) < e\<close>
        proof-
          assume \<open>e > 0\<close> and \<open>i \<ge> R e\<close> and \<open>j \<ge> R e\<close>
          hence \<open>lim ( \<lambda> m. norm (rep_completion (X i) m - rep_completion (X j) m) ) < e\<close>
            by (simp add: \<open>\<lbrakk>0 < e; R e \<le> i; R e \<le> j\<rbrakk> \<Longrightarrow> lim (\<lambda>m. norm (rep_completion (X i) m - rep_completion (X j) m)) < e\<close>)
          thus ?thesis 
            using \<open>lim ( \<lambda> m. norm (rep_completion (X i) m - rep_completion (X j) m) )
              = lim ( \<lambda> m. norm (rep_completion (X i) (m + T i + T j) - rep_completion (X j) (m + T i + T j)) )\<close>
            by simp
        qed
        thus ?thesis using \<open>e > 0\<close> \<open>i \<ge> R e\<close> \<open>j \<ge> R e\<close> by blast
      qed
      ultimately have \<open>e > 0 \<Longrightarrow> i \<ge> R e \<Longrightarrow> j \<ge> R e \<Longrightarrow>
          norm (l i - l j) \<le> inverse (real (Suc i)) + e + inverse (real (Suc j))\<close>
        for i j e
        by smt
      moreover have \<open>e > 0 \<Longrightarrow> i \<ge> H e \<Longrightarrow> inverse (real (Suc i)) < e\<close>
        for e i
        using \<open>\<forall>e>0. \<forall>i\<ge>H e. inverse (real (Suc i)) < e\<close> by blast
      ultimately have \<open>e > 0 \<Longrightarrow> i \<ge> R e \<Longrightarrow> j \<ge> R e \<Longrightarrow> i \<ge> H e \<Longrightarrow> j \<ge> H e \<Longrightarrow>
          norm (l i - l j) <  e + e + e\<close>
        for i j e
        by smt
      hence \<open>e > 0 \<Longrightarrow> \<exists> M. \<forall> i \<ge> M. \<forall> j \<ge> M. norm (l i - l j) < e + e + e\<close>
        for e
        by (metis (no_types, opaque_lifting) add.assoc le_add_same_cancel2 le_iff_add zero_le)
      hence \<open>e > 0 \<Longrightarrow> \<exists> M. \<forall> i \<ge> M. \<forall> j \<ge> M. norm (l i - l j) < 3*e\<close>
        for e
        by simp
      hence \<open>e > 0 \<Longrightarrow> \<exists> M. \<forall> i \<ge> M. \<forall> j \<ge> M. norm (l i - l j) < e\<close>
        for e
      proof-
        assume \<open>e > 0\<close>
        hence \<open>e/3 > 0\<close>
          by simp
        hence \<open>\<exists> M. \<forall> i \<ge> M. \<forall> j \<ge> M. norm (l i - l j) < 3*(e/3)\<close>
          using \<open>\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>i\<ge>M. \<forall>j\<ge>M. norm (l i - l j) < 3 * e\<close> by blast
        thus ?thesis by simp            
      qed
      thus ?thesis
        unfolding Cauchy_def 
        by (simp add: dist_norm) 
    qed
    hence \<open>completion_rel l l\<close>
      unfolding completion_rel_def
      apply auto
      unfolding Vanishes_def
      by simp
    hence \<open>\<exists> L. L = abs_completion l\<close>
      using Abs_completion_inverse by blast
    then obtain L where \<open>L = abs_completion l\<close>
      by blast
    have \<open>X \<longlonglongrightarrow> L\<close>
    proof-
      have \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> i \<ge> N. dist (X i) L \<le> e\<close>
        for e
      proof-
        assume \<open>e > 0\<close>
        hence \<open>e/2 > 0\<close>
          by simp
        hence \<open>e/4 > 0\<close>
          by simp
        have \<open>completion_rel l l\<close>
          unfolding completion_rel_def
          apply auto
          using \<open>Cauchy l\<close>
           apply auto
          unfolding Vanishes_def
          by auto
        hence \<open>completion_rel (rep_completion (abs_completion l))  l\<close>
          by (simp add: Quotient3_completion rep_abs_rsp_left)
        hence \<open>(\<lambda> n. (rep_completion (abs_completion l)) n - l n ) \<longlonglongrightarrow> 0\<close>
          unfolding completion_rel_def Vanishes_def by blast
        have \<open>\<exists>N. \<forall>i\<ge>N. lim (\<lambda>n. norm (rep_completion (X i) n -
             rep_completion (abs_completion l) n)) \<le> e\<close>
        proof-
          have \<open>\<exists>N. \<forall>i\<ge>N. lim (\<lambda>n. norm (rep_completion (X i) n - l n)) \<le> e/2\<close>
          proof-
            have \<open>\<exists> W. \<forall> i \<ge> W. \<forall> n \<ge> W. norm (l i - l n) < e/4\<close>
              using \<open>Cauchy l\<close> Cauchy_iff \<open>0 < e\<close> linordered_field_class.divide_pos_pos zero_less_numeral by blast
            then obtain W where \<open>\<forall> i \<ge> W. \<forall> n \<ge> W. norm (l i - l n) < e/4\<close>
              by blast
            have \<open>\<exists> N. \<forall> n \<ge> N.  inverse (of_nat (Suc n)) < e/4\<close>
              using \<open>0 < e / 4\<close> \<open>\<forall>e>0. \<exists>H. \<forall>i\<ge>H. inverse (real (Suc i)) < e\<close> 
              by blast
            then obtain N where \<open>\<forall> n \<ge> N. inverse (of_nat (Suc n)) < e/4\<close>
              by blast
            hence \<open>i\<ge>N \<Longrightarrow> i \<ge> W \<Longrightarrow> n \<ge> T i \<Longrightarrow> n \<ge> W \<Longrightarrow>  norm (rep_completion (X i) n - l n) \<le> e/2\<close>
              for i n
            proof-
              assume \<open>i\<ge>N\<close> and \<open>i\<ge>W\<close> and \<open>n \<ge> T i\<close> and \<open>n \<ge> W\<close>
              have \<open>norm (rep_completion (X i) n - l n) \<le> e/2\<close>
              proof-
                have \<open>norm (rep_completion (X i) n - l n) \<le> norm (rep_completion (X i) n - l i) + norm (l i - l n)\<close>
                proof-
                  have \<open>(rep_completion (X i) n - l n) = (rep_completion (X i) n - l i) + (l i - l n)\<close>
                    by simp
                  thus ?thesis
                    by (metis norm_triangle_ineq)
                qed
                moreover have \<open>norm (rep_completion (X i) n - l i) \<le> e/4\<close>
                proof-
                  have \<open>norm (rep_completion (X i) n - l i) < inverse (of_nat (Suc i))\<close>
                    using \<open>\<forall> i. \<forall> m \<ge> T i. norm (rep_completion (X i) m - l i) < inverse (of_nat (Suc i))\<close> 
                      \<open>n \<ge> T i\<close>
                    by blast
                  moreover have \<open>inverse (of_nat (Suc i)) \<le> e/4\<close>
                    using \<open>N \<le> i\<close> \<open>\<forall>n\<ge>N. inverse (real (Suc n)) < e / 4\<close> by auto
                  ultimately show ?thesis by auto
                qed
                moreover have \<open>norm (l i - l n) \<le> e/4\<close>
                  using \<open>\<forall> i \<ge> W. \<forall> n \<ge> W. norm (l i - l n) < e/4\<close>
                    \<open>i \<ge> W\<close> \<open>n \<ge> W\<close>
                  by fastforce                  
                ultimately have \<open>norm (rep_completion (X i) n - l n) \<le> e/4 + e/4\<close>
                  by simp
                thus ?thesis
                  by simp
              qed
              thus ?thesis by blast
            qed
            have \<open>i\<ge>N \<Longrightarrow> i\<ge>W \<Longrightarrow> lim (\<lambda>n. norm (rep_completion (X i) n - l n)) \<le> e/2\<close>
              for i
            proof-
              assume \<open>i\<ge>N\<close> and \<open>i \<ge> W\<close>
              hence \<open>\<forall> n. n \<ge> T i \<and> n \<ge> W \<longrightarrow> norm (rep_completion (X i) n - l n) \<le> e/2\<close>
                using \<open>\<And>n i. \<lbrakk>N \<le> i; W \<le> i; T i \<le> n; W \<le> n\<rbrakk> \<Longrightarrow> norm (rep_completion (X i) n - l n) \<le> e / 2\<close> by auto
              hence \<open>\<forall> n \<ge> (max (T i) W).  norm (rep_completion (X i) n - l n) \<le> e/2\<close>
                by simp                
              moreover have \<open>convergent (\<lambda> n. norm (rep_completion (X i) n - l n))\<close>
                sorry
                (* by (simp add: Cauchy_convergent Cauchy_convergent_norm Cauchy_minus \<open>Cauchy l\<close> \<open>\<And>i. Cauchy (rep_completion (X i))\<close>) *)
              ultimately show \<open>lim (\<lambda>n. norm (rep_completion (X i) n - l n)) \<le> e/2\<close>
                sorry
            qed
            thus ?thesis
              by (meson add_leE)  
          qed
          then obtain N where \<open>\<forall>i\<ge>N. lim (\<lambda>n. norm (rep_completion (X i) n - l n)) \<le> e/2\<close>
            by blast
          have \<open>\<exists> M. \<forall> n\<ge>M. norm ((\<lambda> n. (rep_completion (abs_completion l)) n - l n ) n) < e/2\<close>
            using \<open>(\<lambda> n. (rep_completion (abs_completion l)) n - l n ) \<longlonglongrightarrow> 0\<close>
            unfolding LIMSEQ_def 
            using \<open>e/2 > 0\<close> 
            by (metis dist_0_norm dist_commute) 
          then obtain M where \<open>\<forall> n\<ge>M. norm ((\<lambda> n. (rep_completion (abs_completion l)) n - l n ) n) < e/2\<close>
            by blast
          have \<open>i\<ge>N  \<Longrightarrow> lim (\<lambda>n. norm (rep_completion (X i) n - rep_completion (abs_completion l) n)) \<le> e\<close>
            for i
          proof-
            assume \<open>i\<ge>N\<close>
            hence \<open>lim (\<lambda>n. norm (rep_completion (X i) n - l n)) \<le> e/2\<close>
              using \<open>\<forall>i\<ge>N. lim (\<lambda>n. norm (rep_completion (X i) n - l n)) \<le> e/2\<close>
              by blast
            have \<open>lim (\<lambda>n. norm (rep_completion (X i) n - rep_completion (abs_completion l) n))
              = lim (\<lambda>n. norm ( (rep_completion (X i) n - l n) + (l n - rep_completion (abs_completion l) n) ))\<close>
              by simp
            also have \<open>lim (\<lambda>n. norm ( (rep_completion (X i) n - l n) + (l n - rep_completion (abs_completion l) n) ))
              \<le> lim (\<lambda>n. norm ( (rep_completion (X i) n - l n) ) + norm ( (l n - rep_completion (abs_completion l) n) ))\<close>
            proof-
              have  \<open> norm ( (rep_completion (X i) n - l n) + (l n - rep_completion (abs_completion l) n) )
              \<le>  norm ( (rep_completion (X i) n - l n) ) + norm ( (l n - rep_completion (abs_completion l) n) )\<close>
                for n
                using norm_triangle_ineq by blast
              moreover have \<open>convergent (\<lambda> n. norm ( (rep_completion (X i) n - l n) + (l n - rep_completion (abs_completion l) n) ) )\<close>
              proof-
                have \<open>(\<lambda>n. norm (rep_completion (X i) n - rep_completion (abs_completion l) n))
                  = (\<lambda> n. norm ( (rep_completion (X i) n - l n) + (l n - rep_completion (abs_completion l) n) ) )\<close>
                  by simp
                moreover have \<open>convergent (\<lambda>n. norm (rep_completion (X i) n - rep_completion (abs_completion l) n))\<close>
     sorry
                  (* by (metis Cauchy_convergent Cauchy_convergent_norm Cauchy_minus \<open>\<And>i. Cauchy (rep_completion (X i))\<close> \<open>completion_rel (rep_completion (abs_completion l)) l\<close> completion_rel_def)                   *)
                ultimately show ?thesis by simp
              qed
              moreover have \<open>convergent (\<lambda> n. norm ( (rep_completion (X i) n - l n) ) + norm ( (l n - rep_completion (abs_completion l) n) ) )\<close>
              proof-
                have \<open>convergent (\<lambda> n. norm ( (rep_completion (X i) n - l n) ) )\<close>
     sorry
                  (* by (simp add: Cauchy_convergent_norm Cauchy_minus \<open>Cauchy l\<close> \<open>\<And>i. Cauchy (rep_completion (X i))\<close> real_Cauchy_convergent) *)
                moreover have \<open>convergent (\<lambda> n. norm ( (l n - rep_completion (abs_completion l) n) ) )\<close>
     sorry
                  (* by (metis Cauchy_convergent Cauchy_convergent_norm Cauchy_minus \<open>completion_rel (rep_completion (abs_completion l)) l\<close> completion_rel_def)                   *)
                ultimately show ?thesis
                  by (simp add: convergent_add) 
              qed
              ultimately show ?thesis
     sorry
                (* by (simp add: lim_leq)  *)
            qed
            finally have \<open>lim (\<lambda>n. norm (rep_completion (X i) n - rep_completion (abs_completion l) n))
              \<le> lim (\<lambda>n. norm (rep_completion (X i) n - l n) +
              norm (l n - rep_completion (abs_completion l) n))\<close>
              by blast
            moreover have \<open>lim (\<lambda>n. norm ( (rep_completion (X i) n - l n) ) + norm ( (l n - rep_completion (abs_completion l) n) )) \<le> e\<close>
            proof-
              have \<open>convergent (\<lambda> n. norm ( (rep_completion (X i) n - l n) ) )\<close>
     sorry
                (* by (simp add: Cauchy_convergent_norm Cauchy_minus \<open>Cauchy l\<close> \<open>\<And>i. Cauchy (rep_completion (X i))\<close> real_Cauchy_convergent) *)
              moreover have \<open>convergent (\<lambda> n. norm ( (l n - rep_completion (abs_completion l) n) ) )\<close>
     sorry
                (* by (metis Cauchy_convergent Cauchy_convergent_norm Cauchy_minus \<open>completion_rel (rep_completion (abs_completion l)) l\<close> completion_rel_def)                   *)
              ultimately have \<open>lim (\<lambda>n. norm ( (rep_completion (X i) n - l n) ) + norm ( (l n - rep_completion (abs_completion l) n) ))
            = lim (\<lambda>n. norm ( (rep_completion (X i) n - l n) ) )
              + lim (\<lambda>n. norm ( (l n - rep_completion (abs_completion l) n) ))\<close>
     sorry
                (* by (simp add: lim_add) *)
              moreover have \<open>lim (\<lambda>n. norm ( (rep_completion (X i) n - l n) ) ) \<le> e/2\<close>
                using \<open>lim (\<lambda>n. norm (rep_completion (X i) n - l n)) \<le> e / 2\<close> by auto
              moreover have \<open>lim (\<lambda>n. norm ( (l n - rep_completion (abs_completion l) n) )) \<le> e/2\<close>
              proof-
                have \<open>convergent (\<lambda>n. norm (rep_completion (abs_completion l) n - l n))\<close>
    
                  using \<open>(\<lambda>n. rep_completion (abs_completion l) n - l n) \<longlonglongrightarrow> 0\<close> convergent_def convergent_norm by blast
                moreover have \<open>\<forall> n\<ge>M. norm ((\<lambda> n. (rep_completion (abs_completion l)) n - l n ) n) \<le> e/2\<close>
                  using \<open>\<forall> n\<ge>M. norm ((\<lambda> n. (rep_completion (abs_completion l)) n - l n ) n) < e/2\<close>
                  by auto
                ultimately have \<open>lim (\<lambda>n. norm ( (rep_completion (abs_completion l) n - l n) )) \<le> e/2\<close>
                  apply auto 
                  using \<open>(\<lambda>n. rep_completion (abs_completion l) n - l n) \<longlonglongrightarrow> 0\<close> dual_order.trans limI tendsto_norm_zero by fastforce
                moreover have \<open>lim (\<lambda>n. norm ( (rep_completion (abs_completion l) n - l n) ))
                    = lim (\<lambda>n. norm ( l n - (rep_completion (abs_completion l) n) ))\<close>
                proof-
                  have \<open>(\<lambda>n. norm ( (rep_completion (abs_completion l) n - l n) ))
                    = (\<lambda>n. norm ( l n - (rep_completion (abs_completion l) n) ))\<close>
                  proof-
                    have \<open>norm ( (rep_completion (abs_completion l) n - l n) )
                    = norm ( l n - (rep_completion (abs_completion l) n) )\<close>
                      for n
                    proof-
                      have \<open> ( (rep_completion (abs_completion l) n - l n) )
                    = - ( l n - (rep_completion (abs_completion l) n) )\<close>
                        by simp
                      thus ?thesis
                        using norm_minus_commute by blast 
                    qed
                    thus ?thesis by blast
                  qed
                  thus ?thesis by simp
                qed
                ultimately show ?thesis by simp
              qed
              ultimately have \<open>lim (\<lambda>n. norm ( (rep_completion (X i) n - l n) ) + norm ( (l n - rep_completion (abs_completion l) n) )) \<le> e/2 + e/2\<close>
                by auto
              thus \<open>lim (\<lambda>n. norm ( (rep_completion (X i) n - l n) ) + norm ( (l n - rep_completion (abs_completion l) n) )) \<le> e\<close>
                by simp
            qed
            ultimately show \<open>lim (\<lambda>n. norm (rep_completion (X i) n - rep_completion (abs_completion l) n)) \<le> e\<close>
              by simp
          qed
          thus ?thesis
            by (meson dual_order.trans le_cases) 
        qed
        thus \<open>\<exists> N. \<forall> i \<ge> N. dist (X i) L \<le> e\<close>
          unfolding dist_completion_def
          using \<open>L = abs_completion l\<close>
          by auto
      qed
      hence \<open>0 < e \<Longrightarrow> \<exists>N. \<forall>i\<ge>N. dist (X i) L < e\<close>
        for e
      proof-
        assume \<open>e > 0\<close>
        hence \<open>e/2 > 0\<close>
          by simp
        hence \<open>\<exists>N. \<forall>i\<ge>N. dist (X i) L \<le> e/2\<close>
          using \<open>\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>i\<ge>N. dist (X i) L \<le> e\<close> by blast
        moreover have \<open>e/2 < e\<close>
          using \<open>e/2 > 0\<close> by auto
        ultimately show ?thesis
          by fastforce 
      qed
      thus ?thesis
        by (simp add: metric_LIMSEQ_I)
    qed
    thus ?thesis unfolding convergent_def by blast
  qed
qed
end

instantiation completion :: (complex_normed_vector) cbanach
begin
lift_definition scaleC_completion :: \<open>complex \<Rightarrow> 'a completion \<Rightarrow> 'a completion\<close>
  is \<open>\<lambda> r x. (\<lambda> n. r *\<^sub>C (x n))\<close>
  unfolding completion_rel_def proof
  show "Cauchy (\<lambda>n. r *\<^sub>C (f1 n::'a))"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
    for r :: complex
      and f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy f1\<close>
      using that by blast
    thus ?thesis 
      using bounded_clinear.Cauchy[OF bounded_clinear_scaleC_right] by blast
  qed
  show "Cauchy (\<lambda>n. r *\<^sub>C (f2 n::'a)) \<and> Vanishes (\<lambda>n. r *\<^sub>C f1 n - r *\<^sub>C f2 n)"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
    for r :: complex
      and f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy (\<lambda>n. r *\<^sub>C (f2 n))\<close>
    proof-
      have \<open>Cauchy f2\<close>
        using that by blast
      thus ?thesis 
        using bounded_clinear.Cauchy[OF bounded_clinear_scaleC_right] by blast
    qed
    moreover have \<open>Vanishes (\<lambda>n. r *\<^sub>C f1 n - r *\<^sub>C f2 n)\<close>
    proof-
      have \<open>Vanishes (\<lambda>n. (f1 n) - (f2 n))\<close>
        using that by blast
      hence \<open>(\<lambda>n. (f1 n) - (f2 n)) \<longlonglongrightarrow> 0\<close>
        unfolding Vanishes_def by blast
      moreover have \<open>(\<lambda>n. r) \<longlonglongrightarrow> r\<close>
        by simp
      ultimately have \<open>(\<lambda>n. r *\<^sub>C (f1 n - f2 n)) \<longlonglongrightarrow> r *\<^sub>C 0\<close>
        using isCont_scaleC isCont_tendsto_compose 
        sorry
      moreover have \<open>r *\<^sub>C (f1 n - f2 n) = r *\<^sub>C f1 n - r *\<^sub>C f2 n\<close>
        for n
        by (simp add: complex_vector.scale_right_diff_distrib)
      ultimately show ?thesis unfolding Vanishes_def
        by auto 
    qed
    ultimately show ?thesis by blast
  qed
qed     


instance 
proof
  show "((*\<^sub>R) r::'a completion \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
    unfolding scaleC_completion_def scaleR_completion_def
    apply auto
    by (simp add: scaleR_scaleC)
  show "a *\<^sub>C ((x::'a completion) + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "'a completion"
      and y :: "'a completion"
     sorry

(*     apply transfer unfolding completion_rel_def apply auto
      apply (simp add: Cauchy_add Cauchy_scaleC)
     apply (simp add: Cauchy_add Cauchy_scaleC)
    unfolding Vanishes_def apply auto proof
    show "\<forall>\<^sub>F n in sequentially. dist (a *\<^sub>C (x n + y n) - (a *\<^sub>C x n + a *\<^sub>C y n)) (0::'a) < e"
      if "Cauchy (y::nat \<Rightarrow> 'a)"
        and "Cauchy (x::nat \<Rightarrow> 'a)"
        and "(0::real) < e"
      for a :: complex
        and x :: "nat \<Rightarrow> 'a"
        and y :: "nat \<Rightarrow> 'a"
        and e :: real
    proof-
      have \<open>a *\<^sub>C (x n + y n) = (a *\<^sub>C x n + a *\<^sub>C y n)\<close>
        for n
        by (simp add: scaleC_add_right)        
      have \<open>a *\<^sub>C (x n + y n) - (a *\<^sub>C x n + a *\<^sub>C y n) = 0\<close>
        for n
        by (simp add: \<open>\<And>n. a *\<^sub>C (x n + y n) = a *\<^sub>C x n + a *\<^sub>C y n\<close>)
      hence \<open>dist (a *\<^sub>C (x n + y n) - (a *\<^sub>C x n + a *\<^sub>C y n)) (0::'a) = 0\<close>
        for n
        by simp
      thus ?thesis
        by (simp add: that(3)) 
    qed
  qed *)


  show "(a + b) *\<^sub>C (x::'a completion) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a completion"
     sorry
(*     apply transfer unfolding completion_rel_def apply auto
      apply (simp add: Cauchy_scaleC)
     apply (simp add: Cauchy_add Cauchy_scaleC)
    unfolding Vanishes_def proof
    show "\<forall>\<^sub>F n in sequentially. dist ((a + b) *\<^sub>C x n - (a *\<^sub>C x n + b *\<^sub>C x n)) (0::'a) < e"
      if "Cauchy (x::nat \<Rightarrow> 'a)"
        and "(\<lambda>n. 0::'a) \<longlonglongrightarrow> 0"
        and "(0::real) < e"
      for a :: complex
        and b :: complex
        and x :: "nat \<Rightarrow> 'a"
        and e :: real
    proof-
      have \<open>(a + b) *\<^sub>C x n = (a *\<^sub>C x n + b *\<^sub>C x n)\<close>
        for n
        by (simp add: scaleC_add_left)
      hence \<open>(a + b) *\<^sub>C x n - (a *\<^sub>C x n + b *\<^sub>C x n) = 0\<close>
        for n
        by simp
      hence \<open>dist ((a + b) *\<^sub>C x n - (a *\<^sub>C x n + b *\<^sub>C x n)) (0::'a) = 0\<close>
        for n
        by simp
      thus ?thesis
        by (simp add: that(3)) 
    qed
  qed *)

  show "a *\<^sub>C b *\<^sub>C (x::'a completion) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a completion"
    apply transfer apply auto unfolding completion_rel_def apply auto
    using bounded_clinear.Cauchy[OF bounded_clinear_scaleC_right] by blast

  show "1 *\<^sub>C (x::'a completion) = x"
    for x :: "'a completion"
    apply transfer by auto 

  show "norm (a *\<^sub>C (x::'a completion)) = cmod a * norm x"
    for a :: complex
      and x :: "'a completion"
    apply transfer unfolding completion_rel_def apply auto
  proof-
    fix a::complex and x::\<open>nat \<Rightarrow> 'a\<close>
    assume \<open>Cauchy x\<close> and \<open>Vanishes (\<lambda>n. 0)\<close>
    hence \<open>convergent (\<lambda> n. norm (x n))\<close>
     sorry
      (* using Cauchy_convergent_iff Cauchy_convergent_norm by blast *)
    moreover have \<open>norm (a *\<^sub>C x n) = (cmod a) * norm (x n)\<close>
      for n
      by simp
    ultimately have \<open>lim (\<lambda>n. norm (a *\<^sub>C x n)) =  lim (\<lambda>n. (cmod a) * norm (x n))\<close>
      by simp
    also have \<open>lim (\<lambda>n. (cmod a) * norm (x n)) = (cmod a) * lim (\<lambda>n. norm (x n))\<close>
      using  \<open>convergent (\<lambda> n. norm (x n))\<close>
     sorry
(*       using lim_scaleR[where r = "(cmod a)" and x = "(\<lambda>n. norm (x n))"]
      by simp *)
    finally have  \<open>lim (\<lambda>n. norm (a *\<^sub>C x n)) = (cmod a) * lim (\<lambda>n. norm (x n))\<close>
      by blast
    thus \<open>lim (\<lambda>n. (cmod a) * norm (x n)) = (cmod a) * lim (\<lambda>n. norm (x n))\<close>
      by simp
  qed
qed

end

instantiation completion :: (complex_inner) chilbert_space
begin
lift_definition cinner_completion :: \<open>'a completion \<Rightarrow> 'a completion \<Rightarrow> complex\<close>
  is \<open>\<lambda> x y. lim (\<lambda> n. x n \<bullet>\<^sub>C y n)\<close>
proof-
  fix f1 f2 f3 f4::\<open>nat \<Rightarrow> 'a::complex_inner\<close>
  assume \<open>completion_rel f1 f2\<close> and \<open>completion_rel f3 f4\<close>
  have \<open>Cauchy f1\<close>
    using \<open>completion_rel f1 f2\<close> unfolding completion_rel_def by blast
  have \<open>Cauchy f2\<close>
    using \<open>completion_rel f1 f2\<close> unfolding completion_rel_def by blast
  have \<open>Cauchy f3\<close>
    using \<open>completion_rel f3 f4\<close> unfolding completion_rel_def by blast
  have \<open>Cauchy f4\<close>
    using \<open>completion_rel f3 f4\<close> unfolding completion_rel_def by blast
  have \<open>lim (\<lambda>n. f1 n \<bullet>\<^sub>C f3 n) = lim (\<lambda>n. f2 n \<bullet>\<^sub>C f3 n)\<close>
  proof-
    have \<open>Cauchy f3\<close>
      using \<open>completion_rel f3 f4\<close> unfolding completion_rel_def by blast
    hence \<open>bounded (range f3)\<close>
      by (simp add: Elementary_Metric_Spaces.cauchy_imp_bounded)
    hence \<open>\<exists> M. \<forall> n. norm (f3 n) \<le> M\<close>
      by (simp add: bounded_iff)
    then obtain M where \<open>\<forall> n. norm (f3 n) \<le> M\<close>
      by blast
    hence \<open>M \<ge> 0\<close>
      using dual_order.trans norm_imp_pos_and_ge by blast        
    have \<open>norm ((f1 n - f2 n) \<bullet>\<^sub>C f3 n) \<le> norm (f1 n - f2 n) * norm (f3 n)\<close> for n
      by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)
    hence \<open>norm ((f1 n - f2 n) \<bullet>\<^sub>C f3 n) \<le> norm (f1 n - f2 n) * M\<close> for n
      using \<open>\<forall> n. norm (f3 n) \<le> M\<close>
      by (meson dual_order.trans mult_left_mono norm_ge_zero)
    moreover have \<open>(\<lambda> n. norm (f1 n - f2 n) * M) \<longlonglongrightarrow> 0\<close>
    proof-
      have \<open>(\<lambda> n. f1 n - f2 n) \<longlonglongrightarrow> 0\<close>
        using \<open>completion_rel f1 f2\<close> unfolding completion_rel_def Vanishes_def by blast
      hence \<open>(\<lambda> n. norm (f1 n - f2 n)) \<longlonglongrightarrow> 0\<close>
        by (simp add: tendsto_norm_zero)
      thus ?thesis
        by (simp add: tendsto_mult_left_zero) 
    qed
    ultimately have \<open>(\<lambda> n. (f1 n - f2 n) \<bullet>\<^sub>C f3 n) \<longlonglongrightarrow> 0\<close>
      by (metis (no_types, lifting) Lim_null_comparison eventually_sequentiallyI) 
    hence \<open>lim (\<lambda> n. (f1 n - f2 n) \<bullet>\<^sub>C f3 n) = 0\<close>
      by (simp add: limI)
    have \<open>lim (\<lambda> n. (f1 n \<bullet>\<^sub>C f3 n) - (f2 n \<bullet>\<^sub>C f3 n)) = 0\<close>
    proof-
      have \<open>(f1 n - f2 n) \<bullet>\<^sub>C f3 n = (f1 n \<bullet>\<^sub>C f3 n) - (f2 n \<bullet>\<^sub>C f3 n)\<close>
        for n
        by (simp add: cinner_diff_left)
      thus ?thesis 
        using \<open>lim (\<lambda> n. ((f1 n - f2 n) \<bullet>\<^sub>C f3 n)) = 0\<close> by simp
    qed
    moreover have \<open>convergent (\<lambda> n. (f1 n \<bullet>\<^sub>C f3 n))\<close>
      using Cauchy_cinner_Cauchy \<open>Cauchy f1\<close> \<open>Cauchy f3\<close> complex_Cauchy_convergent by blast
    moreover have \<open>convergent (\<lambda> n. (f2 n \<bullet>\<^sub>C f3 n))\<close>
      by (simp add: Cauchy_cinner_Cauchy \<open>Cauchy f2\<close> \<open>Cauchy f3\<close> complex_Cauchy_convergent)
    ultimately have \<open>lim (\<lambda> n. (f1 n \<bullet>\<^sub>C f3 n)) - lim (\<lambda> n. (f2 n \<bullet>\<^sub>C f3 n)) = 0\<close>
    proof -
      have "\<And>c. \<not> (\<lambda>n. (f1 n \<bullet>\<^sub>C f3 n)) \<longlonglongrightarrow> c \<or> (\<lambda>n. (f1 n \<bullet>\<^sub>C f3 n) - (f2 n \<bullet>\<^sub>C f3 n)) \<longlonglongrightarrow> c - lim (\<lambda>n. (f2 n \<bullet>\<^sub>C f3 n))"
        using \<open>convergent (\<lambda>n. (f2 n \<bullet>\<^sub>C f3 n))\<close> convergent_LIMSEQ_iff tendsto_diff by blast
      thus ?thesis
        by (metis (no_types) LIMSEQ_unique \<open>convergent (\<lambda>n. (f1 n \<bullet>\<^sub>C f3 n))\<close> \<open>lim (\<lambda>n. (f1 n \<bullet>\<^sub>C f3 n) - (f2 n \<bullet>\<^sub>C f3 n)) = 0\<close> convergentI convergent_LIMSEQ_iff)
    qed
    thus ?thesis by simp
  qed
  also have \<open>\<dots>= lim (\<lambda>n. (f2 n \<bullet>\<^sub>C f4 n))\<close>
  proof-
    have \<open>Cauchy f2\<close>
      using \<open>completion_rel f1 f2\<close> unfolding completion_rel_def by blast
    hence \<open>bounded (range f2)\<close>
      by (simp add: Elementary_Metric_Spaces.cauchy_imp_bounded)
    hence \<open>\<exists> M. \<forall> n. norm (f2 n) \<le> M\<close>
      by (simp add: bounded_iff)
    then obtain M where \<open>\<forall> n. norm (f2 n) \<le> M\<close>
      by blast
    hence \<open>M \<ge> 0\<close>
      using dual_order.trans norm_imp_pos_and_ge by blast        
    have \<open>norm ((f1 n - f2 n) \<bullet>\<^sub>C f3 n) \<le> norm (f1 n - f2 n) * norm (f3 n)\<close> for n
      by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)
    hence \<open>norm (f2 n \<bullet>\<^sub>C (f3 n - f4 n)) \<le> M * norm (f3 n - f4 n)\<close> for n
      using \<open>\<forall> n. norm (f2 n) \<le> M\<close>
      by (meson complex_inner_class.Cauchy_Schwarz_ineq2 dual_order.trans mult_right_mono norm_ge_zero)
    moreover have \<open>(\<lambda> n. M * norm (f3 n - f4 n)) \<longlonglongrightarrow> 0\<close>
    proof-
      have \<open>(\<lambda> n. f3 n - f4 n) \<longlonglongrightarrow> 0\<close>
        using \<open>completion_rel f3 f4\<close> unfolding completion_rel_def Vanishes_def by blast
      hence \<open>(\<lambda> n. norm (f3 n - f4 n)) \<longlonglongrightarrow> 0\<close>
        by (simp add: tendsto_norm_zero)
      thus ?thesis
        by (simp add: tendsto_mult_right_zero) 
    qed
    ultimately have \<open>(\<lambda> n. (f2 n \<bullet>\<^sub>C (f3 n - f4 n))) \<longlonglongrightarrow> 0\<close>
      by (metis (no_types, lifting) Lim_null_comparison eventually_sequentiallyI) 
    hence \<open>lim (\<lambda> n. (f2 n \<bullet>\<^sub>C (f3 n - f4 n))) = 0\<close>
      by (simp add: limI)
    have \<open>lim (\<lambda> n. (f2 n \<bullet>\<^sub>C f3 n) - (f2 n \<bullet>\<^sub>C f4 n)) = 0\<close>
    proof-
      have \<open>(f2 n \<bullet>\<^sub>C (f3 n - f4 n)) = (f2 n \<bullet>\<^sub>C f3 n) - (f2 n \<bullet>\<^sub>C f4 n)\<close>
        for n
        by (simp add: cinner_diff_right)
      thus ?thesis 
        using \<open>lim (\<lambda> n. (f2 n \<bullet>\<^sub>C (f3 n - f4 n))) = 0\<close> by simp
    qed
    have \<open>convergent (\<lambda> n. (f2 n \<bullet>\<^sub>C f3 n))\<close>
      by (simp add: Cauchy_cinner_Cauchy \<open>Cauchy f2\<close> \<open>Cauchy f3\<close> complex_Cauchy_convergent)
    moreover have \<open>convergent (\<lambda> n. (f2 n \<bullet>\<^sub>C f4 n))\<close>
      by (simp add: Cauchy_cinner_Cauchy \<open>Cauchy f2\<close> \<open>Cauchy f4\<close> complex_Cauchy_convergent)
    ultimately have \<open>lim ( \<lambda> m. (\<lambda> n. (f2 n \<bullet>\<^sub>C f3 n)) m - (\<lambda> n. (f2 n \<bullet>\<^sub>C f4 n)) m)
      = lim (\<lambda> n. (f2 n \<bullet>\<^sub>C f3 n)) - lim (\<lambda> n. (f2 n \<bullet>\<^sub>C f4 n))\<close>
    proof -
      have "(\<lambda>n. (f2 n \<bullet>\<^sub>C f3 n)) \<longlonglongrightarrow> lim (\<lambda>n. (f2 n \<bullet>\<^sub>C f4 n))"
        by (metis (no_types) Lim_transform \<open>convergent (\<lambda>n. (f2 n \<bullet>\<^sub>C f3 n))\<close> \<open>convergent (\<lambda>n. (f2 n \<bullet>\<^sub>C f4 n))\<close> \<open>lim (\<lambda>n. (f2 n \<bullet>\<^sub>C f3 n) - (f2 n \<bullet>\<^sub>C f4 n)) = 0\<close> convergent_LIMSEQ_iff convergent_diff)
      thus ?thesis
        using \<open>lim (\<lambda>n. (f2 n \<bullet>\<^sub>C f3 n) - (f2 n \<bullet>\<^sub>C f4 n)) = 0\<close> limI by auto
    qed
    hence \<open>lim (\<lambda> n. (f2 n \<bullet>\<^sub>C f3 n)) - lim (\<lambda> n. (f2 n \<bullet>\<^sub>C f4 n)) = 0\<close>
      using \<open>lim (\<lambda>n. (f2 n \<bullet>\<^sub>C f3 n) - (f2 n \<bullet>\<^sub>C f4 n)) = 0\<close> by auto      
    thus ?thesis by simp
  qed

  finally show \<open>lim (\<lambda>n. (f1 n \<bullet>\<^sub>C f3 n)) = lim (\<lambda>n. (f2 n \<bullet>\<^sub>C f4 n))\<close>
    by blast
qed

instance
proof
  fix x y z :: "'a completion"
  fix r :: complex
  show "(x::'a completion) \<bullet>\<^sub>C y = cnj (y \<bullet>\<^sub>C x)"
    apply transfer
    unfolding completion_rel_def
    apply auto unfolding Vanishes_def apply auto
  proof-
    fix x y :: \<open>nat \<Rightarrow> 'a\<close>
    assume \<open>Cauchy y\<close> and \<open>Cauchy x\<close>
    have \<open>(x n \<bullet>\<^sub>C y n) = cnj (y n \<bullet>\<^sub>C x n)\<close>
      for n
      by simp
    hence \<open>(\<lambda> n. (x n \<bullet>\<^sub>C y n)) = (\<lambda> n. cnj (y n \<bullet>\<^sub>C x n))\<close>
      by blast
    hence \<open>lim (\<lambda> n. (x n \<bullet>\<^sub>C y n)) = lim (\<lambda> n. cnj (y n \<bullet>\<^sub>C x n))\<close>
      by simp
    moreover have \<open>lim (\<lambda> n. cnj (y n \<bullet>\<^sub>C x n)) = cnj (lim (\<lambda> n. (y n \<bullet>\<^sub>C x n)))\<close>
    proof-
      have \<open>convergent (\<lambda> n. (y n \<bullet>\<^sub>C x n))\<close>
        using \<open>Cauchy y\<close> and \<open>Cauchy x\<close>
        using Cauchy_cinner_Cauchy Cauchy_convergent_iff by blast
      hence \<open>\<exists> l. (\<lambda> n. (y n \<bullet>\<^sub>C x n)) \<longlonglongrightarrow> l\<close>
        by (simp add: convergentD)
      then obtain l where \<open>(\<lambda> n. (y n \<bullet>\<^sub>C x n)) \<longlonglongrightarrow> l\<close> by blast
      hence  \<open>(\<lambda> n. cnj (y n \<bullet>\<^sub>C x n)) \<longlonglongrightarrow> cnj l\<close>
        using lim_cnj by force
      thus ?thesis
        using \<open>(\<lambda>n. (y n \<bullet>\<^sub>C x n)) \<longlonglongrightarrow> l\<close> limI by blast 
    qed
    ultimately show \<open>lim (\<lambda>n. (x n \<bullet>\<^sub>C y n)) = cnj (lim (\<lambda>n. (y n \<bullet>\<^sub>C x n)))\<close>
      by simp
  qed
  show "((x + y) \<bullet>\<^sub>C z) = (x \<bullet>\<^sub>C z) + (y \<bullet>\<^sub>C z)"
    apply transfer
    unfolding completion_rel_def
    apply auto unfolding Vanishes_def apply auto
  proof-
    fix x y z :: \<open>nat \<Rightarrow> 'a\<close>
    assume \<open>Cauchy y\<close> and \<open>Cauchy z\<close> and \<open>Cauchy x\<close> 
    have \<open>((x n + y n) \<bullet>\<^sub>C z n) = (x n \<bullet>\<^sub>C z n) + (y n \<bullet>\<^sub>C z n)\<close>
      for n
      by (simp add: cinner_add_left)
    have \<open>convergent (\<lambda>n. (x n \<bullet>\<^sub>C z n))\<close>
      using \<open>Cauchy x\<close> \<open>Cauchy z\<close>
      by (simp add: Cauchy_cinner_Cauchy complex_Cauchy_convergent)
    moreover have \<open>convergent  (\<lambda>n. (y n \<bullet>\<^sub>C z n))\<close>
      using \<open>Cauchy y\<close> \<open>Cauchy z\<close>
      by (simp add: Cauchy_cinner_Cauchy complex_Cauchy_convergent)
    ultimately have \<open>lim (\<lambda>n. (\<lambda>i. (x i \<bullet>\<^sub>C z i)) n + (\<lambda>i. (y i \<bullet>\<^sub>C z i)) n) = lim (\<lambda>n. (x n \<bullet>\<^sub>C z n)) + lim (\<lambda>n. (y n \<bullet>\<^sub>C z n))\<close>
     sorry
      (* using lim_add by auto *)
    moreover have \<open>(\<lambda>i. (x i \<bullet>\<^sub>C z i)) n + (\<lambda>i. (y i \<bullet>\<^sub>C z i)) n = ((x n + y n) \<bullet>\<^sub>C z n)\<close>
      for n
      using \<open>((x n + y n) \<bullet>\<^sub>C z n) = (x n \<bullet>\<^sub>C z n) + (y n \<bullet>\<^sub>C z n)\<close> by simp
    ultimately show \<open>lim (\<lambda>n. ((x n + y n) \<bullet>\<^sub>C z n)) = lim (\<lambda>n. (x n \<bullet>\<^sub>C z n)) + lim (\<lambda>n. (y n \<bullet>\<^sub>C z n))\<close>
      by auto
  qed
  show "((r *\<^sub>C x) \<bullet>\<^sub>C y) = cnj r * (x \<bullet>\<^sub>C y)"
    apply transfer
    unfolding completion_rel_def
    apply auto unfolding Vanishes_def apply auto
  proof-
    fix x y :: \<open>nat \<Rightarrow> 'a\<close> and r::complex
    assume \<open>Cauchy y\<close> and \<open>Cauchy x\<close>
    hence \<open>convergent (\<lambda>n. (x n \<bullet>\<^sub>C y n))\<close>
      by (simp add: Cauchy_cinner_Cauchy complex_Cauchy_convergent)
    thus \<open>lim (\<lambda>n. cnj r * (x n \<bullet>\<^sub>C y n)) = cnj r * lim (\<lambda>n. (x n \<bullet>\<^sub>C y n))\<close>
     sorry
(*       using lim_scaleC[where r = "cnj r" and x = "(\<lambda>n. (x n \<bullet>\<^sub>C y n))"]
      by simp
 *)
qed

  show "0 \<le> (x \<bullet>\<^sub>C x)"
(*     apply transfer
    unfolding completion_rel_def
    apply auto unfolding Vanishes_def apply auto *)
  proof (transfer, unfold completion_rel_def Vanishes_def)
    fix x::\<open>nat \<Rightarrow> 'a\<close>
    assume \<open>Cauchy x \<and> Cauchy x \<and> (\<lambda>n. x n - x n) \<longlonglongrightarrow> 0\<close>
    then have \<open>Cauchy x\<close> by simp
    have \<open>0 \<le> (x n \<bullet>\<^sub>C x n)\<close> for n
      by (meson cinner_ge_zero)
    have \<open>(x n \<bullet>\<^sub>C x n) \<in> \<real>\<close> for n
      by (simp add: cinner_real)
    hence \<open>(x n \<bullet>\<^sub>C x n) = Re (x n \<bullet>\<^sub>C x n)\<close>
      for n by simp
    have  \<open>convergent (\<lambda>n. (x n \<bullet>\<^sub>C x n))\<close>
      using \<open>Cauchy x\<close>
      using Cauchy_cinner_Cauchy Cauchy_convergent by blast
    have \<open>\<forall> n \<ge> 0. 0 \<le> Re (x n \<bullet>\<^sub>C x n)\<close>
      by (metis \<open>\<And>n. (x n \<bullet>\<^sub>C x n) = complex_of_real (Re (x n \<bullet>\<^sub>C x n))\<close> cinner_ge_zero complex_of_real_nn_iff)      
    moreover have \<open>convergent (\<lambda>n. Re (x n \<bullet>\<^sub>C x n))\<close>
      by (simp add: Cauchy_Re \<open>convergent (\<lambda>n. (x n \<bullet>\<^sub>C x n))\<close> convergent_Cauchy real_Cauchy_convergent)
    ultimately have \<open>0 \<le> lim (\<lambda>n. Re (x n \<bullet>\<^sub>C x n))\<close>
      using Lim_bounded2[where N = "0" and f = "(\<lambda>n. Re ((x n \<bullet>\<^sub>C x n)))" and C = "0"]
      using convergent_LIMSEQ_iff by blast
    have \<open>lim (\<lambda>n. (x n \<bullet>\<^sub>C x n)) = complex_of_real (lim (\<lambda>n. Re (x n \<bullet>\<^sub>C x n)))\<close>
    proof-
      have \<open>(\<lambda>n. (x n \<bullet>\<^sub>C x n)) = (\<lambda>n. complex_of_real (Re (x n \<bullet>\<^sub>C x n)))\<close>
        using \<open>\<And>n. (x n \<bullet>\<^sub>C x n) = complex_of_real (Re (x n \<bullet>\<^sub>C x n))\<close> by auto        
      moreover have \<open>(lim (\<lambda>n. complex_of_real (Re (x n \<bullet>\<^sub>C x n)))) = complex_of_real (lim (\<lambda>n. Re (x n \<bullet>\<^sub>C x n)))\<close>
        using tendsto_of_real[where g = "(\<lambda> n. Re (x n \<bullet>\<^sub>C x n))"]
        sorry
      ultimately show ?thesis by simp
    qed
    then show \<open>0 \<le> lim (\<lambda>n. (x n \<bullet>\<^sub>C x n))\<close>
      by (simp add: \<open>0 \<le> lim (\<lambda>n. Re (x n \<bullet>\<^sub>C x n))\<close>)
  qed

  show "((x \<bullet>\<^sub>C x) = 0) \<longleftrightarrow> (x = 0)"
    apply transfer unfolding completion_rel_def
    apply auto unfolding Vanishes_def apply auto
    using convergent_Cauchy convergent_const apply auto[1]
  proof
    show "\<forall>\<^sub>F n in sequentially. dist (x n) (0::'a) < e"
      if "Cauchy (x::nat \<Rightarrow> 'a)"
        and "lim (\<lambda>n. (x n::'a) \<bullet>\<^sub>C x n) = 0"
        and "(0::real) < e"
      for x :: "nat \<Rightarrow> 'a"
        and e :: real
    proof-
      have \<open>(\<lambda>n. (x n \<bullet>\<^sub>C x n)) \<longlonglongrightarrow> 0\<close>
        using that(2)
        by (metis Cauchy_cinner_Cauchy convergent_eq_Cauchy limI that(1))
      hence \<open>\<forall>\<^sub>F n in sequentially. dist ((x n \<bullet>\<^sub>C x n)) 0 < e^2\<close>
        using tendstoD that(3) by fastforce      
      hence \<open>\<forall>\<^sub>F n in sequentially. (norm ((x n \<bullet>\<^sub>C x n) - 0)) < e^2\<close>
        using dist_norm
        by auto 
      hence \<open>\<forall>\<^sub>F n in sequentially. (norm (x n \<bullet>\<^sub>C x n)) < e^2\<close>
        by simp
      hence \<open>\<forall>\<^sub>F n in sequentially. sqrt (norm (x n \<bullet>\<^sub>C x n)) < e\<close>
        using eventually_elim2 real_less_lsqrt that(3) by force
      hence \<open>\<forall>\<^sub>F n in sequentially. norm (x n)  < e\<close>
        by (metis (mono_tags, lifting) eventually_mono norm_eq_sqrt_cinner)      
      thus ?thesis using dist_norm
        by (simp add: \<open>\<forall>\<^sub>F n in sequentially. norm (x n) < e\<close>) 
    qed
    show "lim (\<lambda>n. (x n::'a) \<bullet>\<^sub>C x n) = 0"
      if "Cauchy (x::nat \<Rightarrow> 'a)"
        and "Cauchy (\<lambda>n. 0::'a)"
        and "x \<longlonglongrightarrow> (0::'a)"
      for x :: "nat \<Rightarrow> 'a"
      using tendsto_cinner limI that(3) by fastforce
  qed
  show "norm x = sqrt (norm (x \<bullet>\<^sub>C x))"
    apply transfer unfolding completion_rel_def
    apply auto unfolding Vanishes_def apply auto
  proof-
    fix x :: \<open>nat \<Rightarrow> 'a\<close>
    assume \<open>Cauchy x\<close>
    have \<open>lim (\<lambda>n. sqrt ( norm (x n \<bullet>\<^sub>C x n) )) = sqrt ( lim (\<lambda>n.  norm (x n \<bullet>\<^sub>C x n) ) )\<close>
      using tendsto_real_sqrt[where f = \<open>(\<lambda>n.  norm (x n \<bullet>\<^sub>C x n) )\<close>]
      sorry
    moreover have \<open>lim (\<lambda>n.  norm (x n \<bullet>\<^sub>C x n) ) = norm (lim (\<lambda>n. (x n \<bullet>\<^sub>C x n) ))\<close>
      using tendsto_norm[where f = "(\<lambda>n. (x n \<bullet>\<^sub>C x n) )"]
      using Cauchy_cinner_Cauchy \<open>Cauchy x\<close> complex_Cauchy_convergent 
      sorry
    ultimately have \<open>lim (\<lambda>n. sqrt ( norm (x n \<bullet>\<^sub>C x n) )) = sqrt (norm (lim (\<lambda>n. (x n \<bullet>\<^sub>C x n))))\<close>
      by simp
    moreover have \<open>norm (x n) =  sqrt ( norm (x n \<bullet>\<^sub>C x n) )\<close>
      for n
      using norm_eq_sqrt_cinner by auto     
    ultimately show \<open>lim (\<lambda>n. norm (x n)) = sqrt (norm (lim (\<lambda>n. (x n \<bullet>\<^sub>C x n))))\<close>
      by simp
  qed
qed
end

lift_definition inclusion_completion :: \<open>'a::real_normed_vector \<Rightarrow> 'a completion\<close>
  is "\<lambda> x. (\<lambda> n. x)"
  unfolding completion_rel_def
  apply auto unfolding Cauchy_def apply auto
  unfolding Vanishes_def by auto

lemma inclusion_completion_inj:
  assumes \<open>inclusion_completion x = inclusion_completion y\<close>
  shows \<open>x = y\<close>
  using assms apply transfer unfolding completion_rel_def
  apply auto 
proof-
  fix x y :: \<open>'a::real_normed_vector\<close>
  assume \<open>Cauchy (\<lambda>n. x)\<close> and \<open>Cauchy (\<lambda>n. y)\<close> 
    and \<open>Vanishes (\<lambda>n. x - y)\<close> 
  from  \<open>Vanishes (\<lambda>n. x - y)\<close>
  have \<open>(\<lambda>n. x - y) \<longlonglongrightarrow> 0\<close>
    unfolding Vanishes_def
    by blast
  hence \<open>\<forall> e > 0. dist (x - y) 0 < e\<close>
    by (simp add: LIMSEQ_const_iff)
  hence \<open>\<forall> e > 0. norm ((x - y) - 0) < e\<close>
    using dist_norm
    by simp
  hence \<open>\<forall> e > 0. norm (x - y) < e\<close>
    by simp
  hence \<open>x - y = 0\<close>
    using zero_less_norm_iff by blast
  show \<open>x = y\<close>
    by (simp add: \<open>x - y = 0\<close> eq_iff_diff_eq_0)
qed

definition proj_completion :: \<open>('a::real_normed_vector) completion \<Rightarrow> 'a option\<close>
  where "proj_completion f = (if (\<exists> x. f = inclusion_completion x) 
    then Some (SOME x. f = inclusion_completion x) 
    else None )"

lemma proj_inclusion_completion:
  \<open>proj_completion (inclusion_completion x) = Some x\<close>
  unfolding proj_completion_def
  apply auto using inclusion_completion_inj
  by blast 

lemma proj_inclusion_completion_none:
  \<open>x \<notin> range inclusion_completion \<Longrightarrow> proj_completion x = None\<close>
  unfolding proj_completion_def
  by auto

lemma inclusion_completion_add:
  \<open>inclusion_completion (x + y) = inclusion_completion x + inclusion_completion y\<close>
  apply transfer
  unfolding completion_rel_def Vanishes_def apply auto
  unfolding Cauchy_def by auto

lemma inclusion_completion_add_general:
  \<open>inclusion_completion (\<Sum>i\<in>I. x i) = (\<Sum>i\<in>I. inclusion_completion (x i))\<close>
  by (metis additive.intro additive.sum inclusion_completion_add)


lemma inclusion_completion_scaleC:
  \<open>inclusion_completion (c *\<^sub>C x) = c *\<^sub>C (inclusion_completion x)\<close>
  apply transfer
  unfolding completion_rel_def Vanishes_def apply auto
  unfolding Cauchy_def by auto

lemma inclusion_completion_norm:
  \<open>norm (inclusion_completion x) = norm x\<close>
  apply transfer
  unfolding completion_rel_def Vanishes_def by auto

lemma inclusion_completion_cinner:
  \<open>inclusion_completion x \<bullet>\<^sub>C inclusion_completion y = x \<bullet>\<^sub>C y\<close>
  apply transfer
  unfolding completion_rel_def Vanishes_def by auto


lemma completion_map_Cauchy:
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector\<close> and x :: \<open>'a completion\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>Cauchy (\<lambda> n. f (rep_completion x n))\<close>
proof-
  have \<open>Cauchy (rep_completion x)\<close>
    by (simp add: Cauchy_rep_completion)    
  thus ?thesis
    by (simp add: bounded_clinear.Cauchy assms)
qed

(* TODO: This could be more generally defined as mapping a continuous function
   to a continuous function (if 'a,'b are metric spaces).

   The fact that it maps a bounded linear function to a bounded linear function
   would then be a simple corollary. *)
lift_definition completion_map' :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun
 \<Rightarrow> ('a completion \<Rightarrow> 'b completion)\<close>
  is \<open>\<lambda> f x. (\<lambda> n. f (rep_completion x n))\<close>
  using completion_map_Cauchy 
  unfolding completion_rel_def apply auto unfolding Vanishes_def 
  by auto


lemma compeltion_map_well_defined:
  assumes \<open>completion_rel x y\<close> and \<open>bounded_clinear f\<close>
  shows \<open>completion_rel (\<lambda> n. f (x n)) (\<lambda> n. f (y n))\<close>
  using assms unfolding completion_rel_def apply auto 
    apply (simp add: bounded_clinear.Cauchy)
   apply (simp add: bounded_clinear.Cauchy)
  unfolding Vanishes_def
proof-
  assume \<open>bounded_clinear f\<close> and \<open>Cauchy x\<close> and \<open>Cauchy y\<close> and \<open>(\<lambda>n. x n - y n) \<longlonglongrightarrow> 0\<close>
  have \<open>isCont f 0\<close>
    using \<open>bounded_clinear f\<close>
    by (simp add: clinear_continuous_at)    
  moreover have \<open>f 0 = 0\<close>
    using \<open>bounded_clinear f\<close> complex_vector.linear_0
    unfolding bounded_clinear_def
    by blast
  ultimately have  \<open>(\<lambda>n. f (x n - y n)) \<longlonglongrightarrow> 0\<close>
    using  \<open>(\<lambda>n. x n - y n) \<longlonglongrightarrow> 0\<close> isCont_tendsto_compose 
    by fastforce 
  moreover have \<open>f (x n - y n) = f (x n) - f (y n)\<close>
    for n
    using \<open>bounded_clinear f\<close> unfolding bounded_clinear_def clinear_def
    using assms(2) bounded_clinear_def complex_vector.linear_diff 
    by blast 
  ultimately show \<open>(\<lambda>n. f (x n) - f (y n)) \<longlonglongrightarrow> 0\<close>
    by simp
qed


lift_definition completion_map :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun
 \<Rightarrow> ('a completion, 'b completion) cblinfun\<close>
  is completion_map'
proof
  fix F :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  fix b b1 b2 :: "'a completion"
  fix r :: complex
  show "completion_map' F (b1 + b2) = completion_map' F b1 + completion_map' F b2"
  proof transfer
    fix F::\<open>'a\<Rightarrow>'b\<close> and b1 b2::\<open>'a completion\<close>
    assume \<open>bounded_clinear F\<close>
    have \<open>completion_rel (rep_completion b1) (rep_completion b1)\<close>
      using Quotient_completion Quotient_rep_reflp by fastforce
    moreover have \<open>completion_rel (rep_completion b2) (rep_completion b2)\<close>
      using Quotient_completion Quotient_rep_reflp by fastforce        
    ultimately have \<open>completion_rel (\<lambda>n. rep_completion b1 n + rep_completion b2 n) (\<lambda>n. rep_completion b1 n + rep_completion b2 n)\<close>
      unfolding completion_rel_def apply auto
     sorry
      (* by (simp add: Cauchy_add) *)
    hence \<open>completion_rel (\<lambda>n.  (rep_completion (b1 + b2) n))
        (\<lambda>n. (rep_completion b1 n) +  (rep_completion b2 n))\<close>
      unfolding plus_completion_def apply auto
      by (simp add: Quotient3_completion rep_abs_rsp_left) 
    hence \<open>completion_rel (\<lambda>n. F (rep_completion (b1 + b2) n))
        (\<lambda>n. F ( (rep_completion b1 n) +  (rep_completion b2 n) ))\<close>
      using \<open>bounded_clinear F\<close> compeltion_map_well_defined 
      by blast
    moreover have \<open>F ( (rep_completion b1 n) +  (rep_completion b2 n) )
          = F (rep_completion b1 n) + F (rep_completion b2 n)\<close>
      for n
      using  \<open>bounded_clinear F\<close> unfolding bounded_clinear_def clinear_def
      using \<open>bounded_clinear F\<close> bounded_clinear_def complex_vector.linear_add 
      by blast 
    ultimately show \<open>completion_rel (\<lambda>n. F (rep_completion (b1 + b2) n))
        (\<lambda>n. F (rep_completion b1 n) + F (rep_completion b2 n))\<close>
      by simp
  qed
  show "completion_map' F (r *\<^sub>C b) = r *\<^sub>C completion_map' F b"
  proof transfer
    fix F::\<open>'a\<Rightarrow>'b\<close> and b::\<open>'a completion\<close> and r::complex
    assume \<open>bounded_clinear F\<close>
    have \<open>completion_rel (rep_completion b) (rep_completion b)\<close>
      using Quotient_completion Quotient_rep_reflp by fastforce
    hence \<open>completion_rel (\<lambda>n. r *\<^sub>C (rep_completion b) n) (\<lambda>n. r *\<^sub>C (rep_completion b) n)\<close>
      unfolding completion_rel_def apply auto
      using bounded_clinear.Cauchy[OF bounded_clinear_scaleC_right] by blast
    hence \<open>completion_rel (\<lambda>n.  (rep_completion (r *\<^sub>C b) n))
        (\<lambda>n. r *\<^sub>C (rep_completion b n))\<close>
      unfolding scaleC_completion_def apply auto
      by (simp add: Quotient3_completion rep_abs_rsp_left)
    hence \<open>completion_rel (\<lambda>n. F (rep_completion (r *\<^sub>C b) n))
        (\<lambda>n. F (r *\<^sub>C (rep_completion b n)))\<close>
      using \<open>bounded_clinear F\<close> compeltion_map_well_defined 
      by blast
    moreover have \<open>F ( r *\<^sub>C (rep_completion b n) )
          = r *\<^sub>C (F (rep_completion b n)) \<close>
      for n
      using  \<open>bounded_clinear F\<close> unfolding bounded_clinear_def clinear_def
      by (simp add: clinear_def complex_vector.linear_scale)        
    ultimately show \<open>completion_rel (\<lambda>n. F (rep_completion (r *\<^sub>C b) n))
        (\<lambda>n. r *\<^sub>C F ( (rep_completion b n)))\<close>
      by simp
  qed

  show "\<exists>K. \<forall>x. norm (completion_map' F (x::'a completion)::'b completion) \<le> norm x * K"
  proof-
    interpret bounded_clinear \<open>cblinfun_apply F\<close>
      using cblinfun_apply by auto      
    have \<open>\<exists> K. \<forall> x. norm ((cblinfun_apply F) x) \<le> norm x * K \<and> K > 0\<close>
      using pos_bounded by blast
    then obtain K where \<open>\<forall> x. norm ((cblinfun_apply F) x) \<le> norm x * K\<close> and \<open>K > 0\<close>
      by blast
    have \<open>Cauchy (rep_completion x)\<close>
      for x::\<open>'a completion\<close>
      using Rep_completion
      by (simp add: Cauchy_rep_completion) 
    hence \<open>Cauchy (\<lambda>n. norm (rep_completion x n))\<close>
      for x::\<open>'a completion\<close>
     sorry
      (* by (simp add: Cauchy_convergent_norm) *)
    have f1: \<open>completion_rel (\<lambda>n. cblinfun_apply F (rep_completion x n)) (\<lambda>n. cblinfun_apply F (rep_completion x n))\<close>
      for x
      unfolding completion_rel_def apply (auto simp: Vanishes_def)
      by (simp add: bounded_clinear_axioms completion_map_Cauchy)
    hence \<open>norm (abs_completion (\<lambda>n. cblinfun_apply F (rep_completion x n)))
          = lim (\<lambda>n. norm (cblinfun_apply F (rep_completion x n)) )\<close>
      for x
      unfolding norm_completion_def apply auto
      by (metis (no_types) norm_completion.abs_eq norm_completion.rep_eq)
    also have \<open>lim (\<lambda>n. norm (cblinfun_apply F (rep_completion x n)) )
             \<le> lim (\<lambda>n. norm (rep_completion x n) * K )\<close>
      for x
    proof-
      have \<open>norm (cblinfun_apply F (rep_completion x n))
          \<le> norm (rep_completion x n) * K\<close>
        for n
        by (simp add: \<open>\<forall>x. norm (cblinfun_apply F x) \<le> norm x * K\<close>)
      moreover have \<open>convergent (\<lambda>n. norm (rep_completion x n) * K)\<close>
        by (metis (no_types) Cauchy_convergent \<open>0 < K\<close> \<open>\<And>x. Cauchy (\<lambda>n. norm (rep_completion x n))\<close> convergent_mult_const_right_iff less_numeral_extra(3))
      moreover have \<open>convergent (\<lambda>n. norm (cblinfun_apply F (rep_completion x n)) )\<close>
     sorry
        (* by (metis Cauchy_convergent Cauchy_convergent_norm completion_rel_def f1) *)
      ultimately show ?thesis
     sorry
        (* by (simp add: lim_leq)  *)
    qed
    also have \<open>lim (\<lambda>n. norm (rep_completion x n) * K ) = lim (\<lambda>n. norm (rep_completion x n)) * K\<close>
      for x::\<open>'a completion\<close>
    proof-
      have \<open>convergent (\<lambda>n. norm (rep_completion x n))\<close>
        using \<open>\<And>x. Cauchy (\<lambda>n. norm (rep_completion x n))\<close> real_Cauchy_convergent 
        by auto
      hence  \<open>lim (\<lambda>n. complex_of_real K *
              complex_of_real (norm (rep_completion x n))) =
    complex_of_real K *
    lim (\<lambda>y. complex_of_real (norm (rep_completion x y)))\<close>
     sorry
(*         using lim_scaleC[where x = "(\<lambda>n. norm (rep_completion x n))" and r = "K"]
        by (simp add: convergent_of_real)         *)
      hence  \<open>lim (\<lambda>n.  K *\<^sub>C (norm (rep_completion x n))) =
                 K *\<^sub>C lim (\<lambda>y.  (norm (rep_completion x y)))\<close>
        (* by (simp add: \<open>convergent (\<lambda>n. norm (rep_completion x n))\<close> lim_complex_of_real) *)
        sorry
        moreover have \<open>lim (\<lambda>n.  K *\<^sub>C (norm (rep_completion x n))) = lim (\<lambda>n. (norm (rep_completion x n)) * K)\<close>
      proof-     
        have \<open>K *\<^sub>C (norm (rep_completion x n)) = (norm (rep_completion x n)) * K\<close>
          for n
          by auto
        hence \<open>K *\<^sub>C (norm (rep_completion x n)) - (norm (rep_completion x n)) * K  = 0\<close>
          for n
          by simp
        hence \<open>(\<lambda> n. K *\<^sub>C (norm (rep_completion x n)) - (norm (rep_completion x n)) * K ) = (\<lambda> _. 0)\<close>
          by simp
        hence \<open>(\<lambda> n. K *\<^sub>C (norm (rep_completion x n)) - (norm (rep_completion x n)) * K ) \<longlonglongrightarrow> 0\<close>
          by simp
        hence \<open>lim (\<lambda> n. K *\<^sub>C (norm (rep_completion x n)) - (norm (rep_completion x n)) * K ) = 0\<close>
          by simp
        moreover have  \<open>lim (\<lambda> n. K *\<^sub>C (norm (rep_completion x n)) - (norm (rep_completion x n)) * K ) = 
          lim (\<lambda> n. K *\<^sub>C (norm (rep_completion x n))) - lim (\<lambda> n. (norm (rep_completion x n)) * K )\<close>
        proof-
          have \<open>convergent (\<lambda> n. (norm (rep_completion x n)))\<close>
            by (simp add: \<open>convergent (\<lambda>n. norm (rep_completion x n))\<close>)

          hence \<open>convergent (\<lambda> n. K *\<^sub>C (norm (rep_completion x n)))\<close>
            using Cauchy_convergent convergent_Cauchy convergent_of_real 
            sorry
          moreover have \<open>convergent (\<lambda> n. (norm (rep_completion x n)) * K )\<close>
            using \<open>convergent (\<lambda> n. (norm (rep_completion x n)))\<close>
          proof -
            have "convergent (\<lambda>n. norm (rep_completion x n) * K) \<or> 0 = K"
              using \<open>convergent (\<lambda>n. norm (rep_completion x n))\<close> convergent_mult_const_right_iff by fastforce
            moreover
            { assume "\<not> (\<lambda>n. complex_of_real K *\<^sub>C complex_of_real (norm (rep_completion x n))) \<longlonglongrightarrow> 0"
              hence "complex_of_real K \<noteq> 0"
                by auto }
            moreover
            { assume "(\<lambda>n. complex_of_real K *\<^sub>C complex_of_real (norm (rep_completion x n))) \<longlonglongrightarrow> 0 \<and> \<not> (\<lambda>n. norm (rep_completion x n) * K) \<longlonglongrightarrow> K"
              moreover
              { assume "\<exists>c f. ((\<lambda>n. complex_of_real K *\<^sub>C complex_of_real (norm (rep_completion x n))) \<longlongrightarrow> c) f \<and> ((\<lambda>n. complex_of_real K *\<^sub>C complex_of_real (norm (rep_completion x n)) - complex_of_real (norm (rep_completion x n) * K)) \<longlongrightarrow> 0) f \<and> \<not> ((\<lambda>n. complex_of_real (norm (rep_completion x n) * K)) \<longlongrightarrow> c) f"
                hence "complex_of_real K \<noteq> 0"
                  by fastforce }
              ultimately have "complex_of_real K \<noteq> 0"
                by fastforce }
            ultimately show ?thesis
              using convergent_def of_real_0 by blast
          qed

          ultimately show ?thesis
     sorry
(*             using convergent_of_real lim_complex_of_real lim_minus 
            by fastforce  *)
        qed
        thus ?thesis
          by auto 
      qed
      moreover have \<open>K *\<^sub>C lim (\<lambda>y.  (norm (rep_completion x y)))
           = lim (\<lambda>y.  (norm (rep_completion x y))) * K\<close>
        by auto
      ultimately have \<open>complex_of_real (lim (\<lambda>n. norm (rep_completion x n) * K)) =
        complex_of_real (lim (\<lambda>n. norm (rep_completion x n)) * K)\<close>
        by simp
      thus ?thesis
        using of_real_eq_iff by blast 
    qed
    hence \<open>\<forall>x. norm (abs_completion (\<lambda>n. cblinfun_apply F (rep_completion x n))) \<le> norm x * K\<close>
      unfolding norm_completion_def
      apply auto
      using \<open>\<forall> x. norm ((cblinfun_apply F) x) \<le> norm x * K\<close>
      by (metis calculation norm_completion.rep_eq)      
    thus ?thesis
      unfolding completion_map'_def
      by auto
  qed
qed

lemma inclusion_completion_isometry:
  \<open>dist (inclusion_completion x) (inclusion_completion y) = dist x y\<close>
  using dist_norm[where x = "x" and y = "y"]  
  apply transfer
  by simp 

lemma inclusion_completion_continuous:
  \<open>isCont inclusion_completion (a::'a::complex_inner)\<close>
proof-
  have \<open>isCont (map_fun id abs_completion (\<lambda>x n. x)) a\<close>
    unfolding isCont_def apply auto unfolding LIM_def
    apply auto using inclusion_completion_isometry
    by (metis inclusion_completion.abs_eq)        
  thus ?thesis
    unfolding inclusion_completion_def apply transfer 
    by blast
qed


end
