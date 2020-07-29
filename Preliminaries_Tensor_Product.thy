(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Preliminaries_Tensor_Product
  imports
    "Bounded_Operators.Preliminaries"

begin

lemma big_sum_reordering_fst:
  fixes  S :: \<open>('a \<times> 'b) set\<close>
  assumes \<open>finite S\<close>
  shows \<open>(\<Sum>z\<in>S. f z) = (\<Sum>u\<in>fst ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>S}. f (u, v)))\<close>
proof-
  define g where \<open>g z = (if z \<in> S then f z else 0)\<close>
    for z
  have \<open>(\<Sum>z\<in>S. f z) = (\<Sum>z\<in>S. g z)\<close>
    unfolding g_def
    by auto
  also have \<open>\<dots>  = (\<Sum>z\<in>((fst ` S) \<times> (snd ` S)). g z)\<close>
  proof-
    have \<open>S \<subseteq> ((fst ` S) \<times> (snd ` S))\<close>
      by (simp add: subset_fst_snd)
    thus ?thesis unfolding g_def
      by (smt DiffD2 assms finite_SigmaI finite_imageI sum.mono_neutral_right)
        (* > 1s *)
  qed
  also have \<open>\<dots>  = (\<Sum>u\<in>(fst ` S). (\<Sum>v\<in>(snd ` S). g (u,v)))\<close>
    by (simp add: sum.cartesian_product)
  also have \<open>\<dots>  = (\<Sum>u\<in>(fst ` S). (\<Sum>v\<in>{v|v. (u,v)\<in>S}.  f (u, v)) )\<close>
  proof-
    have \<open>u \<in> fst ` S \<Longrightarrow> (\<Sum>v\<in>(snd ` S). g (u,v)) = (\<Sum>v\<in>{v|v. (u,v)\<in>S}.  f (u, v))\<close>
      for u
    proof-
      have \<open>{v|v. (u,v)\<in>S} \<subseteq> (snd ` S)\<close>
        using image_iff by fastforce
      hence \<open>(\<Sum>v\<in>(snd ` S). g (u,v)) = (\<Sum>v\<in>{v|v. (u,v)\<in>S}. g (u,v))
             + (\<Sum>v\<in>(snd ` S)-{v|v. (u,v)\<in>S}. g (u,v))\<close>
        by (simp add: add.commute assms sum.subset_diff)
      moreover have \<open>(\<Sum>v\<in>(snd ` S)-{v|v. (u,v)\<in>S}. g (u,v)) = 0\<close>
        by (simp add: g_def)        
      moreover have \<open>(\<Sum>v\<in>{v|v. (u,v)\<in>S}. g (u,v)) = (\<Sum>v\<in>{v|v. (u,v)\<in>S}. f (u,v))\<close>
        unfolding g_def
        by auto
      ultimately show ?thesis by auto
    qed
    thus ?thesis
      by auto 
  qed
  finally show ?thesis by blast
qed

lemma swap_set_fst:
  \<open>fst ` (prod.swap ` S) = snd ` S\<close>
  unfolding prod.swap_def apply auto
  apply (simp add: rev_image_eqI)
  by (metis (no_types, lifting) fst_conv image_cong image_eqI pair_in_swap_image prod.swap_def)

lemma swap_set_snd:
  \<open>snd ` (prod.swap ` S) = fst ` S\<close>
  unfolding prod.swap_def apply auto
  apply (simp add: rev_image_eqI)
  using image_iff by fastforce

lemma big_sum_reordering_snd:
  fixes  S :: \<open>('a \<times> 'b) set\<close>
  assumes \<open>finite S\<close>
  shows \<open>(\<Sum>z\<in>S. f z) = (\<Sum>v\<in>snd ` S. (\<Sum>u\<in>{u|u. (u,v)\<in>S}. f (u, v)))\<close>
proof-
  have \<open>prod.swap \<circ> (prod.swap::('a \<times> 'b \<Rightarrow> 'b \<times> 'a)) = id\<close>
    by simp    
  hence \<open>(\<Sum>z\<in>S. f z) = (\<Sum>z\<in>prod.swap ` (prod.swap ` S). f z)\<close>
    by (simp add: \<open>prod.swap \<circ> prod.swap = id\<close> image_comp)
  also have \<open>\<dots> = (\<Sum>z\<in>(prod.swap ` S). (f \<circ> prod.swap) z)\<close>
  proof-
    have \<open>inj prod.swap\<close>
      by simp      
    show ?thesis
      by (meson \<open>inj prod.swap\<close> inj_def inj_on_def sum.reindex)    
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>fst ` (prod.swap ` S). (\<Sum>v\<in>{v|v. (u,v)\<in>(prod.swap ` S)}. (f \<circ> prod.swap) (u,v)))\<close>
  proof-
    have \<open>finite (prod.swap ` S)\<close>
      using \<open>finite S\<close> by simp
    thus ?thesis
      using big_sum_reordering_fst[where S = "prod.swap ` S" and f = "f \<circ> prod.swap"]
      by blast
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>(prod.swap ` S)}. (f \<circ> prod.swap) (u,v)))\<close>
  proof-
    have \<open>fst ` (prod.swap ` S) = snd ` S\<close>
      by (simp add: swap_set_fst) 
    thus ?thesis by simp
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>(prod.swap ` S)}. f (v,u) ))\<close>
  proof-
    have \<open>prod.swap (u, v) = (v, u)\<close>
      for u::'a and v::'b
      unfolding prod.swap_def by auto
    hence \<open>(f \<circ> prod.swap) (u, v) = f (v, u)\<close>
      for v::'a and u::'b
      by simp
    thus ?thesis by simp      
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (v,u)\<in>S}. f (v,u) ))\<close>
  proof-
    have \<open>(u,v)\<in>(prod.swap ` S) \<longleftrightarrow> (v,u)\<in>S\<close>
      for u v
      by simp
    thus ?thesis by simp
  qed
  finally show ?thesis by blast
qed

(* TODO move somewhere appropriate *)
lemma (in vector_space) span_finite_basis_exists:
  assumes "finite A"
  shows "\<exists>B. finite B \<and> independent B \<and> span B = span A \<and> card B = dim A"
proof -
  obtain B where BT1: "B \<subseteq> span A" 
    and BT2: "span A \<subseteq> span B"
    and indep: "independent B"  
    and card: "card B = dim (span A)"
    using basis_exists[where V="span A"]
    by metis
  have "finite B"
    using assms indep BT1 by (rule independent_span_bound[THEN conjunct1])
  moreover from BT1 BT2 have BT: "span B = span A"
    using span_mono span_span by blast
  moreover from card have "card B = dim (span A)"
    by auto
  moreover note indep
  ultimately show ?thesis
    by auto
qed


end