(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Miscellany results on Nonstandard Analysis.

*)

theory NSA_Miscellany
  imports 
    "HOL-Analysis.Elementary_Metric_Spaces"
    "HOL-Analysis.Operator_Norm"
    Ordered_Fields
    Unobtrusive_NSA
begin

lemma nsbounded_existencial:
  \<open>(\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite) \<longleftrightarrow> (\<exists>x. ((*f2* dist) x) ` (*s* S) \<subseteq> HFinite)\<close>
  for S::\<open>('a::metric_space) set\<close>
proof
  show "\<exists>x. (*f2* dist) x ` (*s* S) \<subseteq> HFinite"
    if "\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite"
    using that image_subset_iff  by fastforce
  show "\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite"
    if "\<exists>x. (*f2* dist) x ` (*s* S) \<subseteq> HFinite"
  proof-
    obtain z where \<open>(*f2* dist) z ` (*s* S) \<subseteq> HFinite\<close>
      using \<open>\<exists>x. (*f2* dist) x ` (*s* S) \<subseteq> HFinite\<close> by blast
    have \<open>x\<in>*s* S \<Longrightarrow> y\<in>*s* S \<Longrightarrow> (*f2* dist) x y \<in> HFinite\<close>
      for x y
    proof-
      assume \<open>x\<in>*s* S\<close> and \<open>y\<in>*s* S\<close>
      have \<open>(*f2* dist) x y \<le> (*f2* dist) x z + (*f2* dist) z y\<close>
      proof-
        have \<open>\<forall> xx yy zz. dist xx yy \<le> dist xx zz + dist zz yy\<close>
          by (simp add: dist_triangle)
        hence \<open>\<forall> xx yy zz. (*f2* dist) xx yy \<le> (*f2* dist) xx zz + (*f2* dist) zz yy\<close>
          by StarDef.transfer
        thus ?thesis by blast 
      qed
      moreover have \<open>(*f2* dist) x z + (*f2* dist) z y \<in> HFinite\<close>
      proof-
        have  \<open>(*f2* dist) x z \<in> HFinite\<close>
        proof-
          have  \<open>(*f2* dist) z x \<in> HFinite\<close>
            using \<open>(*f2* dist) z ` (*s* S) \<subseteq> HFinite\<close> \<open>x\<in>*s* S \<close> 
            by blast
          moreover have \<open>(*f2* dist) z x = (*f2* dist) x z\<close>
          proof-
            have \<open>\<forall> zz xx. dist zz xx = dist xx zz\<close>
              using dist_commute by blast
            hence \<open>\<forall> zz xx. (*f2* dist) zz xx = (*f2* dist) xx zz\<close>
              by StarDef.transfer
            thus ?thesis by blast
          qed
          ultimately show ?thesis by simp
        qed
        moreover have  \<open>(*f2* dist) z y \<in> HFinite\<close>
          using \<open>(*f2* dist) z ` (*s* S) \<subseteq> HFinite\<close> \<open>y\<in>*s* S \<close> 
          by blast
        ultimately show ?thesis
          by (simp add: HFinite_add) 
      qed
      moreover have \<open>0 \<le> (*f2* dist) x y\<close>
      proof-
        have \<open>\<forall> xx yy. 0 \<le> dist xx yy\<close>
          by simp
        hence \<open>\<forall> xx yy. 0 \<le> (*f2* dist) xx yy\<close>
          by StarDef.transfer
        show ?thesis
          by (simp add: \<open>\<forall>xx yy. 0 \<le> (*f2* dist) xx yy\<close>) 
      qed
      ultimately show ?thesis
        using HFinite_bounded by blast  
    qed
    thus ?thesis by blast
  qed
qed

lemma nsbounded_I:
  \<open>\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite \<Longrightarrow> \<exists>x. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close>
   by blast

lemma nsbounded_D:
  \<open>\<exists>x. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite \<Longrightarrow> \<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close>
  by (meson image_subsetI nsbounded_existencial)
  
lemma bounded_nsbounded:
  fixes S :: \<open>('a::metric_space) set\<close>
  assumes \<open>bounded S\<close>
  shows \<open>\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close>
proof-
  from  \<open>bounded S\<close>
  have \<open>\<exists> M. \<exists> u. \<forall> v \<in> S. dist u v < M\<close>
    by (meson bounded_def gt_ex le_less_trans)
  then obtain M where \<open>\<exists> u. \<forall> v \<in> S. dist u v < M\<close>
    by blast
  have \<open>\<exists> u. \<forall> v \<in> *s* S. (*f2* dist) u v < hypreal_of_real M\<close>
    using \<open>\<exists> u. \<forall> v \<in> S. dist u v < M\<close> by StarDef.transfer
  have \<open>\<exists> u. \<forall> v \<in> *s* S. (*f2* dist) u v \<in> HFinite\<close>
  proof-
    obtain u where \<open>\<forall> v \<in> *s* S. (*f2* dist) u v < hypreal_of_real M\<close>
      using  \<open>\<exists> u. \<forall> v \<in> *s* S. (*f2* dist) u v < hypreal_of_real M\<close>
      by blast
    have \<open>v \<in> *s* S \<Longrightarrow> (*f2* dist) u v \<in> HFinite\<close>
      for v
    proof-
      assume \<open>v \<in> *s* S\<close>
      hence \<open>(*f2* dist) u v < hypreal_of_real M\<close>
        using  \<open>\<forall> v \<in> *s* S. (*f2* dist) u v < hypreal_of_real M\<close>
        by blast
      moreover have \<open>hnorm ((*f2* dist) u v) = (*f2* dist) u v\<close>
      proof-
        have \<open>\<forall> uu vv. norm (dist uu vv) =  dist uu vv\<close>
          by simp         
        hence \<open>\<forall> uu vv. hnorm ((*f2* dist) uu vv) =  (*f2* dist) uu vv\<close>
          by StarDef.transfer
        thus ?thesis by blast
      qed
      ultimately show \<open>(*f2* dist) u v \<in> HFinite\<close>
        by (metis HInfiniteD HInfinite_HFinite_disj SReal_hypreal_of_real order.asym) 
    qed
    thus ?thesis
      by blast 
  qed    
  thus ?thesis
    by (simp add: nsbounded_D) 
qed

(* TODO: move? *)
lemma hypreal_of_hypnat_hypnat_of_nat_hypreal_of_nat:
  \<open>hypreal_of_hypnat (hypnat_of_nat n) = hypreal_of_nat n\<close>
proof-
  have \<open>(*f* of_nat) (star_of n) = (plus 1 ^^ n) (0::hypreal)\<close>
  proof(induction n)
    case 0
    then show ?case
      by (metis funpow_0 of_nat_0 star_zero_def starfun_eq) 
  next
    case (Suc n)
    then show ?case
      by (metis of_nat_def star_of_nat_def starfun_star_of) 
  qed
  thus ?thesis
    by (simp add: of_hypnat_def)  
qed

lemma nsbounded_bounded:
  fixes S :: \<open>('a::metric_space) set\<close>
  assumes \<open>\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close>
  shows \<open>bounded S\<close>
proof-
  have \<open>\<exists>x e. \<forall>y\<in>S. dist x y \<le> e\<close> 
  proof-
    from \<open>\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close>
    obtain x where \<open>\<forall> y \<in> *s* S. (*f2* dist) x y \<in> HFinite\<close>
      by blast
    have \<open>\<exists> M. \<forall> y \<in> *s* S. (*f2* dist) x y < M\<close>
    proof(rule classical)
      assume \<open>\<not>(\<exists> M. \<forall> y \<in> *s* S. (*f2* dist) x y < M)\<close>
      hence \<open>\<forall> M. \<exists> y \<in> *s* S. (*f2* dist) x y \<ge> M\<close>
        using leI by blast
      hence \<open>\<exists> y \<in> *s* S. (*f2* dist) x y \<ge> hypreal_of_hypnat whn\<close>
        by blast
      then obtain y where \<open>y \<in> *s* S\<close> and \<open>(*f2* dist) x y \<ge> hypreal_of_hypnat whn\<close>
        by blast
      have \<open>(*f2* dist) x y \<notin> HFinite\<close>
      proof(rule classical)
        assume \<open>\<not>((*f2* dist) x y \<notin> HFinite)\<close>
        hence \<open>(*f2* dist) x y \<in> HFinite\<close>
          by blast
        hence \<open>\<exists> r \<in> \<real>. hnorm ((*f2* dist) x y) < r\<close>
          using HFinite_def by blast
        moreover have \<open>hnorm ((*f2* dist) x y) = (*f2* dist) x y\<close>
        proof-
          have \<open>\<forall> xx. \<forall> yy. norm ( dist xx yy) = dist xx yy\<close>
            by simp
          hence \<open>\<forall> xx. \<forall> yy. hnorm ((*f2* dist) xx yy) = (*f2* dist) xx yy\<close>
            by StarDef.transfer
          thus ?thesis
            by blast 
        qed
        ultimately have \<open>\<exists> r \<in> \<real>. (*f2* dist) x y < r\<close>
          by simp
        hence \<open>\<exists> r \<in> \<real>. hypreal_of_hypnat whn < r\<close>
          using \<open>(*f2* dist) x y \<ge> hypreal_of_hypnat whn\<close>
            order.not_eq_order_implies_strict by fastforce
        then obtain r where \<open>r \<in> \<real>\<close> and \<open>hypreal_of_hypnat whn < r\<close>
          by blast
        have \<open>\<exists> n::nat. r < hypreal_of_nat n\<close>
        proof-
          from \<open>r \<in> \<real>\<close>
          have \<open>\<exists> s. r = hypreal_of_real s\<close>
            by (simp add: SReal_iff)
          then obtain s where \<open>r = hypreal_of_real s\<close>
            by blast
          have \<open>\<exists> n::nat. s < n\<close>
            by (simp add: reals_Archimedean2)
          then obtain n::nat where \<open>s < n\<close>
            by blast
          from \<open>s < n\<close>
          have \<open>hypreal_of_real s < hypreal_of_nat n\<close>
            by StarDef.transfer
          thus ?thesis using \<open>r = hypreal_of_real s\<close> by blast
        qed
        then obtain n where \<open>r < hypreal_of_nat n\<close>
          by blast
        from \<open>hypreal_of_hypnat whn < r\<close>  \<open>r < hypreal_of_nat n\<close>
        have \<open>hypreal_of_hypnat whn < hypreal_of_nat n\<close>
          by simp
        moreover have \<open>hypreal_of_nat n < hypreal_of_hypnat whn\<close>
        proof-
          have  \<open>hypnat_of_nat n < whn\<close>
            by simp
          hence  \<open>hypreal_of_hypnat (hypnat_of_nat n) < hypreal_of_hypnat whn\<close>
            by simp
          moreover have \<open>hypreal_of_hypnat (hypnat_of_nat n) = hypreal_of_nat n\<close>
            using hypreal_of_hypnat_hypnat_of_nat_hypreal_of_nat by blast
          ultimately show ?thesis by simp
        qed
        ultimately have \<open>hypreal_of_hypnat whn < hypreal_of_hypnat whn\<close>
          by simp
        thus ?thesis by blast
      qed
      thus ?thesis
        using \<open>\<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close> \<open>y \<in> *s* S\<close> by auto 
    qed
    hence \<open>\<exists> x. \<exists>M. \<forall>y\<in>*s* S. (*f2* dist) x y < M\<close>
      by blast
    hence \<open>\<exists> x. \<exists>M. \<forall>y\<in>*s* S. (*f2* dist) x y \<le> M\<close>
      using le_less by blast
    thus ?thesis by StarDef.transfer 
  qed
  thus ?thesis using bounded_def by blast
qed

proposition bounded_nsbounded_iff:
  \<open>bounded S \<longleftrightarrow> (\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite)\<close>
  using bounded_nsbounded nsbounded_bounded by blast


lemma ex_approx:
  fixes f::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
    and S::\<open>'a set\<close> and l::'b
  assumes \<open>\<forall>e>0. \<exists> x\<in>S. norm (f x - l) < e\<close>
  shows \<open>\<exists> x\<in>*s* S. (*f* f) x \<approx> star_of l\<close>
proof-
  have \<open>\<forall>e>0. \<exists> x. x\<in>S \<and> norm (f x - l) < e\<close>
    using \<open>\<forall>e>0. \<exists> x\<in>S. norm (f x - l) < e\<close>
    by blast
  hence \<open>\<exists> x. \<forall>e>0. x e \<in> S \<and> norm (f (x e) - l) < e\<close>
    by metis
  then obtain x where \<open>\<forall>e>0. x e \<in> S\<close> and \<open>\<forall>e>0. norm (f (x e) - l) < e\<close>
    by blast
  from \<open>\<forall>e>0. x e \<in> S\<close> 
  have \<open>\<forall>e>0. (*f* x) e \<in> *s* S\<close>
    by StarDef.transfer
  hence \<open>(*f* x) epsilon \<in> *s* S\<close>
    by (simp add: hypreal_epsilon_gt_zero)
  from  \<open>\<forall>e>0. norm (f (x e) - l) < e\<close>
  have  \<open>\<forall>e>0. hnorm ((*f* f) ((*f* x) e) - (star_of l)) < e\<close>
    by StarDef.transfer
  hence  \<open>hnorm ((*f* f) ((*f* x) epsilon) - (star_of l)) < epsilon\<close>
    by (simp add: hypreal_epsilon_gt_zero)
  hence  \<open>(*f* f) ((*f* x) epsilon) \<approx> (star_of l)\<close>
    by (metis Infinitesimal_epsilon add_diff_cancel_left' bex_Infinitesimal_iff2 diff_add_cancel hnorm_less_Infinitesimal)
  thus ?thesis using \<open>(*f* x) epsilon \<in> *s* S\<close> by blast
qed


lemma inv_hSuc_Infinite_Infinitesimal:
  \<open>N\<in>HNatInfinite \<Longrightarrow> inverse (hypreal_of_hypnat (hSuc N)) \<in> Infinitesimal\<close>
proof-
  assume \<open>N\<in>HNatInfinite\<close>
  have \<open>\<forall> n. n < Suc n\<close>
    by auto
  hence \<open>\<forall> n. n < hSuc n\<close>
    by StarDef.transfer
  hence \<open>N < hSuc N\<close>
    by blast
  hence \<open>hSuc N \<in> HNatInfinite\<close>
    using \<open>N\<in>HNatInfinite\<close> HNatInfinite_upward_closed dual_order.strict_implies_order by blast
  thus ?thesis
    by simp
qed

definition starfun3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a star \<Rightarrow> 'b star \<Rightarrow> 'c star \<Rightarrow> 'd star"  (\<open>*f3* _\<close> [80] 80)
  where "starfun3 f \<equiv> \<lambda>x y z. star_of f \<star> x \<star> y \<star> z"
declare starfun3_def [StarDef.transfer_unfold]

section \<open>Closure\<close>

lemma nsclosure_I:
\<open>r \<in> closure A \<Longrightarrow> \<exists> a \<in> *s* A. star_of r \<approx> a\<close>
proof-
  assume \<open>r \<in> closure A\<close>
  hence \<open>\<exists> s::nat\<Rightarrow>_. (\<forall> n. s n \<in> A) \<and> s \<longlonglongrightarrow> r\<close>
    by (simp add: closure_sequential)
  then obtain s::\<open>nat\<Rightarrow>_\<close> where \<open>\<forall> n. s n \<in> A\<close> and \<open>s \<longlonglongrightarrow> r\<close>     
    by blast
  from  \<open>\<forall> n. s n \<in> A\<close>
  have \<open>\<forall> n. (*f* s) n \<in> *s* A\<close>
    by StarDef.transfer
  obtain N where \<open>N \<in> HNatInfinite\<close>
    using HNatInfinite_whn by blast
  have \<open>(*f* s) N \<in> *s* A\<close>    
    using \<open>\<forall> n. (*f* s) n \<in> *s* A\<close> by blast
  moreover have \<open>(*f* s) N \<approx> star_of r\<close>    
    using \<open>s \<longlonglongrightarrow> r\<close>
    by (simp add: LIMSEQ_NSLIMSEQ NSLIMSEQ_D \<open>N \<in> HNatInfinite\<close>)   
  ultimately show ?thesis
    using approx_reorient by blast 
qed

lemma nsclosure_D:
\<open>\<exists> a \<in> *s* A. star_of r \<approx> a \<Longrightarrow> r \<in> closure A\<close>
proof-
  assume \<open>\<exists> a \<in> *s* A. star_of r \<approx> a\<close>
  hence \<open>\<exists> a \<in> *s* A. hnorm (star_of r - a) \<in> Infinitesimal\<close>
    using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by auto
  hence \<open>\<exists> a \<in> *s* A. \<forall> e\<in>Reals. e > 0 \<longrightarrow> hnorm (star_of r - a) <  e\<close>
    using Infinitesimal_less_SReal2 by blast
  hence \<open>\<forall> e\<in>Reals. e > 0 \<longrightarrow> (\<exists> a \<in> *s* A. hnorm (star_of r - a) <  e)\<close>
    by blast
  hence \<open>hypreal_of_real ( (\<lambda>n. inverse (real (Suc n))) n ) > 0
   \<longrightarrow> (\<exists> a \<in> *s* A. hnorm (star_of r - a)
           < hypreal_of_real ( (\<lambda>n. inverse (real (Suc n))) n ) )\<close>
    for n::nat    
    by auto
  hence \<open>\<exists> a \<in> *s* A. hnorm (star_of r - a)
           < hypreal_of_real ( (\<lambda>n. inverse (real (Suc n))) n )\<close>
    for n::nat
    by (meson InfinitesimalD2 \<open>\<exists>a\<in>*s* A. star_of r \<approx> a\<close> bex_Infinitesimal_iff nice_ordered_field_class.inverse_positive_iff_positive of_nat_0_less_iff zero_less_Suc)    
   hence \<open>\<exists> a \<in>  A. norm (r - a)
           <  ( (\<lambda>n. inverse (real (Suc n))) n )\<close>
    for n::nat
   proof-
     have \<open>\<exists> a \<in> *s* A. hnorm (star_of r - a)
           < hypreal_of_real ( (\<lambda>n. inverse (real (Suc n))) n )\<close>
       using \<open>\<And>n. \<exists>a\<in>*s* A. hnorm (star_of r - a) < hypreal_of_real (inverse (real (Suc n)))\<close> by auto
     thus ?thesis
       by StarDef.transfer
   qed
   hence \<open>\<forall> n. \<exists> a \<in>  A. norm (r - a)
           <  ( (\<lambda>n. inverse (real (Suc n))) n )\<close>
     by blast
   hence \<open>\<exists> s. \<forall> n. s n \<in> A \<and> norm (r - s n)  <  (\<lambda>n. inverse (real (Suc n))) n\<close>
     by metis
   then obtain s where \<open>\<forall> n. s n \<in> A\<close> 
     and \<open>\<forall> n. norm (r - s n)  <  (\<lambda>n. inverse (real (Suc n))) n\<close> 
     by blast
   from \<open>\<forall> n. norm (r - s n)  <  (\<lambda>n. inverse (real (Suc n))) n\<close>
   have \<open>\<forall> n. hnorm (star_of r - (*f* s) n)  <  (*f* (\<lambda>n. inverse (real (Suc n)))) n\<close>
     by StarDef.transfer
   have \<open>N\<in>HNatInfinite \<Longrightarrow> (*f* s) N \<approx> star_of r\<close>
     for N
   proof-
     assume  \<open>N \<in> HNatInfinite\<close>
     have \<open>hnorm (star_of r - (*f* s) N)  <  (*f* (\<lambda>n. inverse (real (Suc n)))) N\<close>
       using \<open>\<forall> n. hnorm (star_of r - (*f* s) n)  <  (*f* (\<lambda>n. inverse (real (Suc n)))) n\<close>
         \<open>N \<in> HNatInfinite\<close>
       by blast
     moreover have \<open> (*f* (\<lambda>n. inverse (real (Suc n)))) N \<in> Infinitesimal\<close>
       using  \<open>N \<in> HNatInfinite\<close>
       by (metis (full_types) hSuc_def inv_hSuc_Infinite_Infinitesimal of_hypnat_def starfun_inverse2 starfun_o2)
     ultimately have \<open>hnorm (star_of r - (*f* s) N) \<in> Infinitesimal\<close>
       using Infinitesimal_hnorm_iff hnorm_less_Infinitesimal by blast
     thus \<open>(*f* s) N \<approx> star_of r\<close>
       by (meson Infinitesimal_hnorm_iff approx_sym bex_Infinitesimal_iff)
   qed
   hence \<open>s \<longlonglongrightarrow> r\<close>
     using NSLIMSEQ_I NSLIMSEQ_LIMSEQ by metis     
   thus ?thesis
     using \<open>\<forall> n. s n \<in> A\<close> closure_sequential by blast     
qed

text \<open>Theorem 10.1.1 (3) of [goldblatt2012lectures]\<close>
lemma nsclosure_iff:
\<open>r \<in> closure A \<longleftrightarrow> (\<exists> a \<in> *s* A. star_of r \<approx> a)\<close>
  using nsclosure_D nsclosure_I by blast


end
