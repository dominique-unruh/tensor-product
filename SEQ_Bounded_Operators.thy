(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Main results: 
- banach_steinhaus: Banach-Steinhaus theorem.
- completeness_real_bounded: Completeness of the metric space of (real) bounded operators.

*)

theory SEQ_Bounded_Operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL-Analysis.Infinite_Set_Sum"
    Operator_Norm_Plus
    "HOL-Nonstandard_Analysis.Nonstandard_Analysis"

begin

section \<open>Several kinds of Convergence\<close>

definition strong_convergence:: 
  \<open>(nat \<Rightarrow> ('a::real_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  where \<open>strong_convergence f l = (\<forall> x. ( \<lambda> n. norm (f n x - l x) ) \<longlonglongrightarrow> 0 )\<close>

abbreviation strong_convergence_abbr:: 
  \<open>(nat \<Rightarrow> ('a::real_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  (\<open>((_)/ \<midarrow>strong\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>strong\<rightarrow> l \<equiv> ( strong_convergence f l )\<close>

definition onorm_convergence::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  where \<open>onorm_convergence f l = ( ( \<lambda> n. onorm (\<lambda> x. f n x - l x) ) \<longlonglongrightarrow> 0 )\<close>

abbreviation onorm_convergence_abbr::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>  (\<open>((_)/ \<midarrow>onorm\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>onorm\<rightarrow> l \<equiv> ( onorm_convergence f l )\<close>

definition ustrong_convergence:: 
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close> where 
  \<open>ustrong_convergence f l = ( \<forall> e > 0. \<exists> N. \<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e )\<close>

abbreviation ustrong_convergence_abbr::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>  (\<open>((_)/ \<midarrow>ustrong\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>ustrong\<rightarrow> l \<equiv> ( ustrong_convergence f l )\<close>

definition uCauchy::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)) \<Rightarrow> bool\<close>
  where \<open>uCauchy f = (\<forall> e > 0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall> x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e)\<close>

section \<open>External analogs\<close>

subsection \<open>nsustrong_convergence\<close>

text \<open>See theorem 7.12.2 of [goldblatt2012lectures]\<close>
definition nsustrong_convergence :: "(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector))
   \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  ("((_)/ \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (_))" [60, 60] 60) where
  \<comment> \<open>Nonstandard definition of uniform convergence of sequence on the unit sphere\<close>
  "f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l \<longleftrightarrow> 
( \<forall>N\<in>HNatInfinite. \<forall> x::'a star. hnorm x = 1 \<longrightarrow> (*f2* f) N x \<approx> (*f* l) x )"

 lemma nsustrong_convergence_I: 
  \<open>( \<And>N. \<And> x. N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 \<Longrightarrow> (*f2* f) N x  \<approx> (*f* l) x )
   \<Longrightarrow> f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l\<close> 
  by (simp add: nsustrong_convergence_def) 

lemma nsustrong_convergence_D: 
  \<open>f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l \<Longrightarrow> N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 
  \<Longrightarrow> (*f2* f) N x \<approx> (*f* l) x\<close>
  by (simp add: nsustrong_convergence_def)

lemma nsustrong_convergence_const:
  fixes k :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
  assumes \<open>\<And> n::nat. f n = k\<close>
  shows \<open>f\<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S k\<close>
proof-
  have \<open>\<forall> n. \<forall> x::'a. norm x = 1 \<longrightarrow> f n x = k x\<close>
    using  \<open>\<And> n::nat. f n = k\<close> by auto
  hence \<open>\<forall> n. \<forall> x::'a star. hnorm x = 1 \<longrightarrow> (*f2* f) n x = (*f* k) x\<close>
    by transfer
  thus ?thesis using nsustrong_convergence_def
    by (simp add: nsustrong_convergence_def) 
qed

lemma nsustrong_convergence_add: "X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. X n t + Y n t)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. a t + b t)"
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> and \<open>Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b\<close> and \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsustrong_convergence_D by blast 
  moreover have \<open>(*f2* Y) N x \<approx> (*f* b) x\<close>
    using \<open>Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsustrong_convergence_D by blast 
  ultimately have \<open>(*f2* X) N x + (*f2* Y) N x \<approx> (*f* a) x + (*f* b) x\<close>
    by (simp add: approx_add)
  moreover have \<open>(*f2* X) N x + (*f2* Y) N x = (*f2* (\<lambda>n t. X n t + Y n t)) N x\<close>
  proof-
    have \<open>\<forall> NN. \<forall> xx. X NN xx + Y NN xx = (\<lambda>n t. X n t + Y n t) NN xx\<close>
      by auto
    hence \<open>\<forall> NNN. \<forall> xxx. (*f2* X) NNN xxx + (*f2* Y) NNN xxx = (*f2* (\<lambda>n t. X n t + Y n t)) NNN xxx\<close>
      apply transfer
      by auto
    thus ?thesis
      by simp  
  qed
  moreover have \<open>(*f* a) x + (*f* b) x = (*f* (\<lambda>t. a t + b t)) x\<close>
    by simp
  ultimately show \<open>(*f2* (\<lambda>n t. X n t + Y n t)) N x \<approx> (*f* (\<lambda>t. a t + b t)) x\<close>
    by smt
qed

lemma nsustrong_convergence_add_const: "f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. f n t + b)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. a t + b)"
  by (simp only: nsustrong_convergence_add nsustrong_convergence_const)

lemma bounded_linear_HFinite:
  \<open>bounded_linear a \<Longrightarrow> hnorm x = 1 \<Longrightarrow> ((*f* a) x) \<in> HFinite\<close>
  unfolding HFinite_def
  apply auto
proof-
  assume \<open>bounded_linear a\<close> and \<open>hnorm x = 1\<close>
  have \<open>\<And> t. norm t = 1 \<Longrightarrow> norm (a t) \<le> onorm a\<close>
    using \<open>bounded_linear a\<close> by (metis mult_cancel_left2 onorm)      
  hence  \<open>\<And> t. norm t = 1 \<Longrightarrow> norm (a t) < onorm a + 1\<close>
    by fastforce      
  hence  \<open>\<And> t. hnorm t = 1 \<Longrightarrow> hnorm ((*f* a) t) < star_of (onorm a + 1)\<close>
    by transfer
  hence  \<open>hnorm ((*f* a) x) < star_of (onorm a + 1)\<close>
    using \<open>hnorm x = 1\<close>
    by auto
  thus \<open>\<exists>xa\<in>\<real>. hnorm ((*f* a) x) < xa\<close> by auto
qed

lemma nsustrong_convergence_mult: "X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b
 \<Longrightarrow> bounded_linear a \<Longrightarrow> bounded_linear b 
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. X n t * Y n t)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. a t * b t)"
  for a b :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> and \<open>Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
    and \<open>bounded_linear a\<close> and \<open>bounded_linear b\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsustrong_convergence_D by blast 
  moreover have \<open>(*f2* Y) N x \<approx> (*f* b) x\<close>
    using \<open>Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsustrong_convergence_D by blast 
  moreover have \<open>((*f* a) x) \<in> HFinite\<close>
    using \<open>bounded_linear a\<close> \<open>hnorm x = 1\<close>
    by (simp add: bounded_linear_HFinite) 
  moreover have \<open>((*f* b) x) \<in> HFinite\<close>
    using \<open>bounded_linear b\<close> \<open>hnorm x = 1\<close>
    by (simp add: bounded_linear_HFinite)
  ultimately have \<open>(*f2* X) N x * (*f2* Y) N x \<approx> (*f* a) x * (*f* b) x\<close>
    using approx_mult_HFinite by auto
  moreover have \<open>(*f2* X) N x * (*f2* Y) N x = (*f2* (\<lambda>n t. X n t * Y n t)) N x\<close>
  proof-
    have \<open>\<forall> NN. \<forall> xx. X NN xx * Y NN xx = (\<lambda>n t. X n t * Y n t) NN xx\<close>
      by auto
    hence \<open>\<forall> NNN. \<forall> xxx. (*f2* X) NNN xxx * (*f2* Y) NNN xxx = (*f2* (\<lambda>n t. X n t * Y n t)) NNN xxx\<close>
      apply transfer
      by auto
    thus ?thesis
      by simp  
  qed
  moreover have \<open>(*f* a) x * (*f* b) x = (*f* (\<lambda>t. a t * b t)) x\<close>
    by simp
  ultimately show \<open>(*f2* (\<lambda>n t. X n t * Y n t)) N x \<approx> (*f* (\<lambda>t. a t * b t)) x\<close>
    by smt
qed

lemma nsustrong_convergence_minus: "X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. - X n t)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. - a t)"
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  from \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> and \<open>hnorm x = 1\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    by (simp add: \<open>N \<in> HNatInfinite\<close> nsustrong_convergence_D)
  hence \<open>-(*f2* X) N x \<approx> -(*f* a) x\<close>
    by simp
  moreover have \<open>-(*f2* X) N x \<approx> (*f2* (\<lambda>n t. - X n t)) N x\<close>
  proof-
    have \<open>\<forall> NN. \<forall> xx. -( X) NN xx = ( (\<lambda>n t. - X n t)) NN xx\<close>
      by blast
    hence \<open>\<forall> NN. \<forall> xx. -(*f2* X) NN xx = (*f2* (\<lambda>n t. - X n t)) NN xx\<close>
      by transfer
    thus ?thesis by simp
  qed
  moreover have \<open>-(*f* a) x \<approx> (*f* (\<lambda>t. - a t)) x\<close>
    by simp
  ultimately show \<open>(*f2* (\<lambda>n t. - X n t)) N x \<approx> (*f* (\<lambda>t. - a t)) x\<close>
    using approx_trans3 by blast 
qed

lemma nsustrong_convergence_minus_cancel: "(\<lambda>n. (\<lambda> t. - X n t)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. - a t)
 \<Longrightarrow> X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a"
  by (drule nsustrong_convergence_minus) simp

lemma nsustrong_convergence_diff: "X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. X n t - Y n t)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. a t - b t)"
  using nsustrong_convergence_add [of X a "- Y" "- b"]
  by (simp add: nsustrong_convergence_minus fun_Compl_def)

lemma nsustrong_convergence_diff_const: "f  \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. f n t - b)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. a t - b)"
  by (simp add: nsustrong_convergence_diff nsustrong_convergence_const)


lemma nsustrong_convergence_inverse: "X  \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> 
 bounded_linear a \<Longrightarrow> \<exists> e > 0. \<forall> t. norm t = 1 \<longrightarrow> norm (a t) > e
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. inverse (X n t) )) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. inverse (a t))"
  for a :: "'a::real_normed_vector \<Rightarrow>'b::real_normed_div_algebra"
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> and \<open>N \<in> HNatInfinite\<close>
    and \<open>hnorm x = 1\<close> and \<open>\<exists> e > 0. \<forall> t. norm t = 1 \<longrightarrow> norm (a t) > e\<close> and \<open>bounded_linear a\<close>
  from \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsustrong_convergence_def by blast
  moreover have \<open>inverse ((*f2* X) N x) \<approx> (*f2* (\<lambda>n t. inverse (X n t))) N x\<close>
  proof-                            
    have \<open>\<forall> NN. \<forall> xx. inverse ( X NN xx) = ( (\<lambda>n t. inverse (X n t))) NN xx\<close>
      by blast
    hence \<open>\<forall> NN. \<forall> xx. inverse ((*f2* X) NN xx) = (*f2* (\<lambda>n t. inverse (X n t))) NN xx\<close>
      by transfer
    thus ?thesis
      by simp 
  qed
  moreover have \<open>inverse ((*f* a) x) \<approx> (*f* (\<lambda>t. inverse (a t))) x\<close>
  proof-
    have \<open>\<forall> xx. inverse (a xx) = (\<lambda>t. inverse (a t)) xx\<close>
      by simp
    hence \<open>\<forall> xx. inverse ((*f* a) xx) = (*f* (\<lambda>t. inverse (a t))) xx\<close>
      by transfer
    thus ?thesis by simp
  qed
  moreover have \<open>(*f* a) x \<in> HFinite - Infinitesimal\<close>
  proof
    show "(*f* a) x \<in> HFinite"
      using \<open>bounded_linear a\<close> \<open>hnorm x = 1\<close> bounded_linear_HFinite by auto
    show "(*f* a) x \<notin> Infinitesimal"
    proof
      show False
        if "(*f* a) x \<in> Infinitesimal"
      proof-
        from \<open>\<exists> e > 0. \<forall> t. norm t = 1 \<longrightarrow> norm (a t) > e\<close>
        obtain e::real where \<open>e > 0\<close> and \<open>\<forall> t. norm t = 1 \<longrightarrow> norm (a t) > e\<close>
          by blast
        from \<open>\<forall> t. norm t = 1 \<longrightarrow> norm (a t) > e\<close>
        have \<open>\<forall> t. hnorm t = 1 \<longrightarrow> hnorm ((*f* a) t) > star_of e\<close>
          by transfer
        hence  \<open>hnorm ((*f* a) x) > star_of e\<close>
          using \<open>hnorm x = 1\<close> by blast       
        thus ?thesis using \<open>e > 0\<close>
        proof -
          have "\<not> e \<le> 0"
            using \<open>0 < e\<close> by linarith
          thus ?thesis
            by (meson Infinitesimal_hnorm_iff \<open>hypreal_of_real e < hnorm ((*f* a) x)\<close> hypreal_of_real_less_Infinitesimal_le_zero star_of_le_0 that)
        qed 
      qed
    qed
  qed
  ultimately show \<open>(*f2* (\<lambda>n t. inverse (X n t))) N x \<approx> (*f* (\<lambda>t. inverse (a t))) x\<close>
    by (meson approx_inverse approx_sym approx_trans2)    
qed

lemma nsustrong_convergence_norm: \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S  a \<Longrightarrow> (\<lambda>n. (\<lambda> t. norm (X n t)))
 \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S  (\<lambda> t. norm (a t))\<close>
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S  a\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using  \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S  a\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
     nsustrong_convergence_D by blast
  moreover have  \<open>hnorm ((*f2* X) N x) \<approx> (*f2* (\<lambda>n t. norm (X n t))) N x\<close>
  proof-
    have \<open>\<forall> NN. \<forall> xx. norm ( X NN xx) = ( (\<lambda>n t. norm (X n t))) NN xx\<close>
      by blast
    hence \<open>\<forall> NN. \<forall> xx. hnorm ( (*f2* X) NN xx) = (*f2* (\<lambda>n t. norm (X n t))) NN xx\<close>
      by transfer
    thus ?thesis by simp
  qed
  moreover have \<open>hnorm ((*f* a) x) \<approx> (*f* (\<lambda>t. norm (a t))) x\<close>
  proof-
    have \<open>\<forall> xx. norm (a xx) = (\<lambda>t. norm (a t)) xx\<close>
      by blast
    hence \<open>\<forall> xx. hnorm ((*f* a) xx) = (*f* (\<lambda>t. norm (a t))) xx\<close>
      by transfer
    thus ?thesis by simp
  qed
  ultimately show \<open>(*f2* (\<lambda>n t. norm (X n t))) N x \<approx> (*f* (\<lambda>t. norm (a t))) x\<close>
    by (meson approx_hnorm approx_sym approx_trans2)    
qed

(* TODO: move to real_normed_vector? *)
lemma linear_ball_zero:
  \<open>linear f \<Longrightarrow>  \<forall> x. norm x = 1 \<longrightarrow> f x = 0 \<Longrightarrow> f = (\<lambda> _. 0)\<close>
proof
  show "f u = 0"
    if "linear f"
      and "\<forall>x. norm x = 1 \<longrightarrow> f x = 0"
    for u :: 'a
  proof(cases \<open>u = 0\<close>)
    case True
    thus ?thesis
      by (simp add: linear_0 that(1))
  next
    case False
    have \<open>norm ( (inverse (norm u)) *\<^sub>R u ) = 1\<close>
      by (simp add: False)
    hence \<open>f ( (inverse (norm u)) *\<^sub>R u ) = 0\<close>
      by (simp add: that(2))
    moreover have \<open>f ( (inverse (norm u)) *\<^sub>R u ) = (inverse (norm u)) *\<^sub>R (f  u)\<close>
      using \<open>linear f\<close> unfolding linear_def
      by (simp add: Real_Vector_Spaces.linear_def linear_scale) 
    ultimately have \<open>(inverse (norm u)) *\<^sub>R (f  u) = 0\<close>
      by simp
    moreover have \<open>(inverse (norm u)) \<noteq> 0\<close>
      using \<open>norm (u /\<^sub>R norm u) = 1\<close> by auto
    ultimately show ?thesis by simp
  qed
qed

(* TODO: move to real_normed_vector? *)
lemma linear_ball_uniq:
  \<open>linear f \<Longrightarrow> linear g \<Longrightarrow> \<forall> x. norm x = 1 \<longrightarrow> f x = g x \<Longrightarrow> f = g\<close>
proof
  show "f x = g x"
    if "linear f"
      and "linear g"
      and "\<forall>x. norm x = 1 \<longrightarrow> f x = g x"
    for x :: 'a
  proof-
    have "\<forall>x. norm x = 1 \<longrightarrow> (\<lambda> t. f t - g t) x = 0"
      by (simp add: that(3))
    moreover have \<open>linear (\<lambda> t. f t - g t)\<close>
      using \<open>linear f\<close> \<open>linear g\<close>
      by (simp add: linear_compose_sub) 
    ultimately have \<open>(\<lambda> t. f t - g t) = (\<lambda> _. 0)\<close>
      using linear_ball_zero by smt
    thus ?thesis
      by (meson eq_iff_diff_eq_0) 
  qed
qed

lemma nsustrong_convergence_unique: "X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b
 \<Longrightarrow> linear a  \<Longrightarrow> linear b \<Longrightarrow> a = b"
proof-
  assume \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> and \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b\<close> and \<open>linear a\<close> and \<open>linear b\<close>
  have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow>(*f2* X) N x \<approx> (*f* a) x\<close>
    using \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close>
    by (simp add: nsustrong_convergence_D)
  moreover have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow> (*f2* X) N x \<approx> (*f* b) x\<close>
    using \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b\<close>
    by (simp add: nsustrong_convergence_D)
  ultimately have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow> (*f* a) x \<approx> (*f* b) x\<close>
    by (simp add: approx_monad_iff)
  hence \<open>\<forall> x. hnorm x = 1 \<longrightarrow> (*f* a) x \<approx> (*f* b) x\<close>
    by (meson NSLIMSEQ_def NSLIMSEQ_unique zero_neq_one)
  have \<open>norm t = 1 \<Longrightarrow> a t = b t\<close>
    for t
  proof-
    assume \<open>norm t = 1\<close>
    hence \<open>hnorm (star_of t) = 1\<close>
      by (metis star_of_norm star_one_def)
    hence \<open>(*f* a) (star_of t) \<approx> (*f* b) (star_of t)\<close>
      using \<open>\<forall>x. hnorm x = 1 \<longrightarrow> (*f* a) x \<approx> (*f* b) x\<close> by blast
    thus ?thesis
      by simp 
  qed
  thus ?thesis using linear_ball_uniq  \<open>linear a\<close>  \<open>linear b\<close>
    by blast
qed

lemma nsustrong_convergence_iff:
  fixes l::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
  shows "((\<lambda>n. f (Suc n)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l) \<longleftrightarrow> (f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l)"
proof
  assume *: "f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l"
  show "(\<lambda>n. f(Suc n)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l"
  proof (rule nsustrong_convergence_I)
    fix N and x::'a
    assume "N \<in> HNatInfinite" and \<open>norm x = 1\<close>
    hence "(*f* (\<lambda> n. f n x)) (N + 1) \<approx> star_of (l x)"
      by (simp add: HNatInfinite_add nsustrong_convergence_D *)
    moreover have \<open>(*f* (\<lambda>k. f (Suc k) x)) N = (*f* (\<lambda> n. f n x)) (N + 1)\<close>
    proof-   
      define g where \<open>g n = f n x\<close> for n
      have \<open>( *f* (\<lambda>n. g (Suc n))) N = ( *f* g) (N + (1::hypnat))\<close>
        using starfun_shift_one
        by (simp add: starfun_shift_one)
      thus ?thesis unfolding g_def
        by simp  
    qed
    ultimately show \<open>(*f* (\<lambda>k. f (Suc k) x)) N \<approx> star_of (l x)\<close> by simp
  qed
next
  assume *: "(\<lambda>n. f(Suc n)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l"
  show  "f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l"
  proof (rule nsustrong_convergence_I)
    fix N and x::'a
    assume "N \<in> HNatInfinite" and \<open>norm x = 1\<close>
    hence "(*f* (\<lambda>n. (f (Suc n) x))) (N - 1) \<approx> star_of (l x)"
      using * HNatInfinite_diff nsustrong_convergence_D by fastforce
    moreover have \<open>(*f* (\<lambda>n. (f (Suc n) x))) (N - 1) = (*f* (\<lambda>k. f k x)) N\<close>
    proof-
      define g where \<open>g n = f n x\<close> for n
      have \<open>( *f* (\<lambda>n. g (Suc n))) (N-1) = ( *f* g) ((N-1) + (1::hypnat))\<close>
        using starfun_shift_one
        by (simp add: starfun_shift_one)
      moreover have \<open>( *f* (\<lambda>n. g (Suc n))) (N-1) = (*f* (\<lambda>n. (f (Suc n) x))) (N - 1)\<close>
        unfolding g_def
        by simp 
      moreover have \<open>( *f* g) ((N-1) + (1::hypnat)) =  (*f* (\<lambda>k. f k x)) N\<close>
        unfolding g_def
        by (simp add: \<open>N \<in> HNatInfinite\<close> one_le_HNatInfinite) 
      ultimately show ?thesis
        by simp   
    qed
    ultimately show "(*f* (\<lambda>k. f k x)) N \<approx> star_of (l x)"
      by simp
  qed
qed

lemma ustrong_convergence_nsustrong_convergence:
  fixes l::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
  assumes \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
  shows \<open>f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l\<close>
proof (rule nsustrong_convergence_I)
  fix N and x::'a
  assume \<open>N \<in> HNatInfinite\<close> and \<open>norm x = 1\<close>
  have \<open>(*f* (\<lambda>k. f k x)) N - star_of (l x) \<in> Infinitesimal\<close>
  proof (rule InfinitesimalI2)
    fix r :: real
    assume \<open>0 < r\<close>
    have \<open>\<exists> no. \<forall> n \<ge> no. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < r\<close>
      using \<open>f \<midarrow>ustrong\<rightarrow> l\<close>  \<open>0 < r\<close> ustrong_convergence_def by auto 
    then obtain no where \<open>\<forall> n \<ge> no. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> no. \<forall> x. norm x = 1
       \<longrightarrow> norm ( (\<lambda> k. f k x) n - (l x)) <  r\<close>
      by blast
    hence \<open>\<forall> n \<ge> no. norm ( (\<lambda> k. f k x) n - (l x)) <  r\<close>
      using \<open>norm x = 1\<close> by blast
    hence \<open>\<forall> n \<ge> star_of no. hnorm ((*f* (\<lambda>k. f k x)) n - star_of (l x))
         < hypreal_of_real r\<close>
      by transfer
    thus \<open>hnorm ((*f* (\<lambda>k. f k x)) N - star_of (l x))
         < hypreal_of_real r\<close>
      using star_of_le_HNatInfinite
      by (simp add: \<open>N \<in> HNatInfinite\<close>) 
  qed
  thus \<open>(*f* (\<lambda>k. f k x)) N \<approx> star_of (l x)\<close>
    by (simp only: approx_def)
qed

lemma ustrong_convergence_I: \<open>(\<And>r. 0 < r \<Longrightarrow>
\<exists> no. \<forall> n \<ge> no. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < r) \<Longrightarrow> f \<midarrow>ustrong\<rightarrow> l\<close>
  for l :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  by (simp add: ustrong_convergence_def)

lemma nsustrong_convergence_ustrong_convergence:
  fixes l::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
  assumes \<open>f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l\<close>
  shows \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
  apply (rule ustrong_convergence_I)
proof
  fix r :: real
  assume \<open>r > (0::real)\<close>
  from \<open>f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l\<close>
  have \<open>\<forall>n\<in>HNatInfinite. \<forall>x. norm x = 1 \<longrightarrow> (*f* (\<lambda>k. f k x)) n \<approx> star_of (l x)\<close>
    unfolding nsustrong_convergence_def by blast
  hence \<open>\<forall>n\<in>HNatInfinite.
       \<forall>x. norm x = 1 \<longrightarrow> hnorm ( (*f* (\<lambda>k. f k x)) n - star_of (l x) ) < star_of r\<close>
    by (simp add: InfinitesimalD2 Infinitesimal_approx_minus \<open>0 < r\<close>)
  have \<open>\<exists> no. \<forall>n \<ge> no.
       \<forall>x. norm x = 1 \<longrightarrow> hnorm ( (*f* (\<lambda>k. f k x)) n - star_of (l x) ) < star_of r\<close>
  proof-
    have \<open>n \<ge> whn \<Longrightarrow>
       \<forall>x. norm x = 1 \<longrightarrow> hnorm ( (*f* (\<lambda>k. f k x)) n - star_of (l x) ) < star_of r\<close>
      for n
    proof-
      assume \<open>n \<ge> whn\<close>
      hence \<open>n \<in> HNatInfinite\<close>
        using HNatInfinite_upward_closed HNatInfinite_whn by blast
      hence \<open>\<forall>x. norm x = 1 \<longrightarrow> hnorm ( (*f* (\<lambda>k. f k x)) n - star_of (l x) ) < star_of r\<close>
        using  \<open>\<forall>n\<in>HNatInfinite.
       \<forall>x. norm x = 1 \<longrightarrow> hnorm ( (*f* (\<lambda>k. f k x)) n - star_of (l x) ) < star_of r\<close> by blast
      thus ?thesis by blast
    qed
    thus ?thesis by blast
  qed
  hence \<open>\<exists> no. \<forall>n \<ge> no.
       \<forall>x. norm x = 1 \<longrightarrow> norm ( (\<lambda>k. f k x) n - (l x) ) < r\<close>
        

  show \<open>\<forall>n\<ge>no r. \<forall>x. norm x = 1 \<longrightarrow> norm (f n x - l x) < r\<close>
    sorry
qed



subsection \<open>nsuCauchy\<close>

definition nsuCauchy::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)) \<Rightarrow> bool\<close>
  where \<open>nsuCauchy f \<longleftrightarrow> ( \<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. \<forall> x::'a. norm x = 1 \<longrightarrow>
 (*f* (\<lambda> k. f k x)) N \<approx> (*f* (\<lambda> k. f k x)) M )\<close>                                                                 


section \<open>Properties of sequences of bounded operators\<close>

(* TODO: move? *)
fun rec::\<open>'a \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a\<close> where
  "rec x0 \<Phi> 0 = x0" 
|  "rec x0 \<Phi> (Suc n) = \<Phi> n (rec x0 \<Phi> n)"

(* TODO: move? *)
lemma sum_mono:
  fixes a :: \<open>nat \<Rightarrow> real\<close>
  assumes \<open>\<And> n. a n \<ge> 0\<close>
  shows  \<open>p \<ge> 0 \<Longrightarrow> \<forall> n. sum a {0..n + p} \<ge> sum a {0..n}\<close>
proof(induction p)
  case 0
  thus ?case
    by simp 
next
  case (Suc p)
  thus ?case
    by (smt Suc_neq_Zero add_Suc_right assms le_SucE sum.atLeast0_atMost_Suc) 
qed

(* TODO: move? *)
lemma sum_comp:
  fixes a :: \<open>nat \<Rightarrow> real\<close>
  assumes \<open>p \<ge> 0\<close>
  shows  \<open>\<forall> n. sum a {Suc n..n + p} = sum a {0.. n + p} - sum a {0..n}\<close>
proof(induction p)
  case 0
  thus ?case 
    by simp
next
  case (Suc p)
  thus ?case 
    using add.commute add_nonneg_nonneg le_add1 le_add_same_cancel2 by auto
qed

(* TODO: nonstandard *)
lemma non_Cauchy_unbounded:
  fixes a ::\<open>nat \<Rightarrow> real\<close> and e::real
  assumes  \<open>\<And> n. a n \<ge> 0\<close> and \<open>e > 0\<close> and
    \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
  shows \<open>(\<lambda> n. (sum a  {0..n}) ) \<longlonglongrightarrow> \<infinity>\<close>
proof-
  have \<open>incseq (\<lambda> n. (sum a  {..<n}))\<close>
    using \<open>\<And> n. a n \<ge> 0\<close> using Extended_Real.incseq_sumI 
    by auto
  hence \<open>incseq (\<lambda> n. (sum a  {..< Suc n}))\<close>
    by (meson incseq_Suc_iff)
  hence \<open>incseq (\<lambda> n. (sum a  {0..n}))\<close>
    by (metis (mono_tags, lifting) sum_mono assms(1) incseq_def le_add_same_cancel1 le_iff_add)
  hence \<open>incseq (\<lambda> n. (sum a  {0..n})::ereal)\<close>
    using incseq_ereal by blast
  hence \<open>(\<lambda> n. (sum a  {0..n})::ereal) \<longlonglongrightarrow> Sup (range (\<lambda> n. (sum a  {0..n})::ereal))\<close>
    using LIMSEQ_SUP by auto
  moreover have \<open>Sup ((range (\<lambda> n. (sum a  {0..n})))::ereal set) = \<infinity>\<close>
  proof-
    define S where \<open>S = ((range (\<lambda> n. (sum a  {0..n})))::ereal set)\<close>
    have \<open>\<exists> s \<in> S.  k*e \<le> s\<close>
      for k::nat
    proof(induction k)
      case 0
      from \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
      obtain m n where \<open>m \<ge> 0\<close> and \<open>n \<ge> 0\<close> and \<open>m > n\<close>
        and \<open>sum a {Suc n..m} \<ge> e\<close>
        by blast
      from \<open>sum a {Suc n..m} \<ge> e\<close>
      have \<open>sum a {Suc n..m} > 0\<close>
        using \<open>e > 0\<close>
        by linarith
      moreover have \<open>sum a {0..n} \<ge> 0\<close>
        by (simp add: assms(1) sum_nonneg)
      moreover have \<open>sum a {0..n} + sum a {Suc n..m} = sum a {0..m}\<close>
      proof-
        have \<open>finite {0..n}\<close>
          by simp
        moreover have \<open>finite {Suc n..m}\<close>
          by simp
        moreover have \<open>{0..n} \<union> {Suc n..m} = {0..m}\<close>
        proof-
          have \<open>n < Suc n\<close>
            by simp
          thus ?thesis using Set_Interval.ivl_disj_un(7)
            using \<open>n < m\<close> by auto
        qed
        moreover have \<open>{0..n} \<inter> {Suc n..m} = {}\<close>
          by simp
        ultimately show ?thesis
          by (metis sum.union_disjoint) 
      qed
      ultimately have \<open>sum a {0..m} > 0\<close>
        by linarith
      moreover have \<open>ereal (sum a {0..m}) \<in> S\<close>
        unfolding S_def
        by blast
      ultimately have \<open>\<exists> s \<in> S. 0 \<le> s\<close>
        using ereal_less_eq(5) by fastforce    
      thus ?case
        by (simp add: zero_ereal_def)  
    next
      case (Suc k)
      assume \<open>\<exists>s\<in>S. ereal (real k * e) \<le> s\<close>
      then obtain s where \<open>s \<in> S\<close> 
        and \<open> ereal (real k * e) \<le> s\<close>
        by blast
      have \<open>\<exists> N. s = ereal (sum a {0..N})\<close>
        using \<open>s \<in> S\<close>
        unfolding S_def by blast
      then obtain N where \<open>s = ereal (sum a {0..N})\<close>
        by blast
      from \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
      obtain m n where \<open>m \<ge> Suc N\<close> and \<open>n \<ge> Suc N\<close> and \<open>m > n\<close>
        and \<open>sum a {Suc n..m} \<ge> e\<close>
        by blast
      have \<open>sum a {Suc N..m} \<ge> e\<close>
      proof-
        have \<open>sum a {Suc N..m} = sum a {Suc N..n} + sum a {Suc n..m}\<close>
        proof-
          have \<open>finite {Suc N..n}\<close>
            by simp
          moreover have \<open>finite {Suc n..m}\<close>
            by simp
          moreover have \<open>{Suc N..n} \<union> {Suc n..m} = {Suc N..m}\<close>
            using Set_Interval.ivl_disj_un
            by (smt \<open>Suc N \<le> n\<close> \<open>n < m\<close> atLeastSucAtMost_greaterThanAtMost less_imp_le_nat)
          moreover have \<open>{} = {Suc N..n} \<inter> {Suc n..m}\<close>
            by simp
          ultimately show ?thesis 
            by (metis sum.union_disjoint)
        qed
        moreover have \<open>sum a {Suc N..n} \<ge> 0\<close>
          using  \<open>\<And> n. a n \<ge> 0\<close>
          by (simp add: sum_nonneg) 
        ultimately show ?thesis
          using \<open>e \<le> sum a {Suc n..m}\<close> by linarith 
      qed
      moreover have \<open>sum a {0..N} + sum a {Suc N..m} =  sum a {0..m}\<close>
      proof-
        have \<open>finite {0..N}\<close>
          by simp
        have \<open>finite {Suc N..m}\<close>
          by simp
        moreover have \<open>{0..N} \<union> {Suc N..m} = {0..m}\<close>
        proof-
          have \<open>N < Suc N\<close>
            by simp
          thus ?thesis using Set_Interval.ivl_disj_un(7)
              \<open>Suc N \<le> m\<close> by auto            
        qed          
        moreover have \<open>{0..N} \<inter> {Suc N..m} = {}\<close>
          by simp
        ultimately show ?thesis 
          by (metis \<open>finite {0..N}\<close> sum.union_disjoint)
      qed
      ultimately have \<open>e + k * e \<le> sum a {0..m}\<close>
        using \<open>ereal (real k * e) \<le> s\<close> \<open>s = ereal (sum a {0..N})\<close> by auto
      moreover have \<open>e + k * e = (Suc k) * e\<close>
      proof-
        have \<open>e + k * e = (1 + k) * e\<close>
          by (simp add: semiring_normalization_rules(3))
        thus ?thesis by simp
      qed
      ultimately have \<open>(Suc k) * e \<le> sum a {0..m}\<close>
        by linarith
      hence \<open>ereal ((Suc k) * e) \<le> ereal (sum a {0..m})\<close>
        by auto
      moreover have \<open>ereal (sum a {0..m}) \<in> S\<close>
        unfolding S_def
        by blast
      ultimately show ?case
        by blast
    qed
    hence  \<open>\<exists> s \<in> S.  (real n) \<le> s\<close>
      for n::nat
      by (meson assms(2) ereal_le_le ex_less_of_nat_mult less_le_not_le)
    hence  \<open>Sup S = \<infinity>\<close>
      using Sup_le_iff Sup_subset_mono dual_order.strict_trans1 leD less_PInf_Ex_of_nat subsetI 
      by metis
    thus ?thesis using S_def 
      by blast
  qed
  ultimately show ?thesis 
    using PInfty_neq_ereal by auto 
qed

(* TODO: nonstandard *)
lemma sum_Cauchy_positive:
  fixes a ::\<open>nat \<Rightarrow> real\<close>
  assumes \<open>\<And> n. a n \<ge> 0\<close> 
    and \<open>\<exists> K. \<forall> n::nat. (sum a  {0..n}) \<le> K\<close>
  shows \<open>Cauchy (\<lambda> n. (sum a  {0..n}))\<close>
proof-
  have \<open>e>0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
    for e
  proof-
    assume \<open>e>0\<close>       
    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
    proof(rule classical)
      assume \<open>\<not>(\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e)\<close>
      hence \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> \<not>(sum a {Suc n..m} < e)\<close>
        by blast
      hence \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
        by fastforce
      hence \<open>(\<lambda> n. (sum a  {0..n}) ) \<longlonglongrightarrow> \<infinity>\<close>
        using non_Cauchy_unbounded \<open>0 < e\<close> assms(1) by blast
      from  \<open>\<exists> K. \<forall> n::nat. (sum a  {0..n}) \<le> K\<close>
      obtain K where  \<open>\<forall> n::nat. (sum a  {0..n}) \<le> K\<close>
        by blast
      from  \<open>(\<lambda> n. (sum a  {0..n}) ) \<longlonglongrightarrow> \<infinity>\<close>
      have \<open>\<forall>B. \<exists>N. \<forall>n\<ge>N. (\<lambda> n. (sum a  {0..n}) ) n \<ge> ereal B\<close>
        using Lim_PInfty by simp
      hence  \<open>\<exists> n::nat. (sum a  {0..n}) \<ge> K+1\<close>
        using ereal_less_eq(3) by blast        
      thus ?thesis using  \<open>\<forall> n::nat. (sum a  {0..n}) \<le> K\<close> by smt       
    qed
    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
    proof-        
      have \<open>m > n \<Longrightarrow> sum a {Suc n..m} = sum a {0..m} - sum a {0..n}\<close>
        for m n
        using sum_comp 
        by (metis less_imp_add_positive less_imp_le_nat)
      thus ?thesis using \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close> 
        by smt 
    qed
    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
    proof-
      from \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
      obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
        by blast
      moreover have \<open>m > n \<Longrightarrow> sum a {0..m} \<ge> sum a {0..n}\<close>
        for m n
        using \<open>\<And> n. a n \<ge> 0\<close> sum_mono 
        by (metis less_imp_add_positive less_imp_le_nat)
      ultimately show ?thesis 
        by auto
    qed
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m \<ge> n \<longrightarrow> \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
      by (metis \<open>0 < e\<close> abs_zero cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' less_irrefl_nat linorder_neqE_nat zero_less_diff)      
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
      by (metis abs_minus_commute nat_le_linear)
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
      by (simp add: dist_real_def)      
    thus ?thesis by blast
  qed
  thus ?thesis
    using Cauchy_altdef2 le_refl by fastforce 
qed

(* TODO: nonstandard *)
lemma convergent_series_Cauchy:
  fixes a::\<open>nat \<Rightarrow> real\<close> and \<phi>::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes \<open>\<exists> M. \<forall> n. (sum a {0..n}) \<le> M\<close>
    and \<open>\<And> n. dist (\<phi> (Suc n)) (\<phi> n) \<le> a n\<close>
  shows \<open>Cauchy \<phi>\<close>
proof-
  have \<open>e > 0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> dist (\<phi> m) (\<phi> n) < e\<close>
    for e
  proof-
    assume \<open>e > 0\<close>
    have \<open>dist (\<phi> (n+p+1)) (\<phi> n) \<le> sum a {n..n+p}\<close>
      for p n :: nat
    proof(induction p)
      case 0
      thus ?case
        by (simp add: assms(2))
    next
      case (Suc p)
      thus ?case
        by (smt Suc_eq_plus1 add_Suc_right assms(2) dist_self dist_triangle2 le_add1 sum.nat_ivl_Suc') 
    qed
    hence \<open>m > n \<Longrightarrow> dist (\<phi> m) (\<phi> n) \<le> sum a {n..m-1}\<close>
      for m n :: nat
      by (metis Suc_eq_plus1 Suc_le_D diff_Suc_1  gr0_implies_Suc less_eq_Suc_le less_imp_Suc_add zero_less_Suc)
    moreover have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {n..m-1} < e\<close>
    proof-
      have  \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
      proof-
        have \<open>\<And> k. a k \<ge> 0\<close>
          using \<open>\<And> n. dist (\<phi> (Suc n)) (\<phi> n) \<le> a n\<close>
            dual_order.trans zero_le_dist by blast
        hence \<open>Cauchy (\<lambda> k. sum a {0..k})\<close>
          using  \<open>\<exists> M. \<forall> n. (sum a {0..n}) \<le> M\<close>
            sum_Cauchy_positive by blast
        hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
          unfolding Cauchy_def
          using \<open>e > 0\<close>
          by blast
        hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> dist (sum a {0..m}) (sum a {0..n}) < e\<close>
          by blast
        have \<open>m > n \<Longrightarrow> dist (sum a {0..m}) (sum a {0..n}) = sum a {Suc n..m}\<close>
          for m n
        proof-
          assume \<open>m > n\<close>
          have \<open>dist (sum a {0..m}) (sum a {0..n}) 
            = \<bar>(sum a {0..m}) - (sum a {0..n})\<bar>\<close>
            using dist_real_def by blast
          moreover have \<open>(sum a {0..m}) - (sum a {0..n}) = sum a {Suc n..m}\<close>
          proof-
            have  \<open>(sum a {0..n}) + sum a {Suc n..m} = (sum a {0..m})\<close>
            proof-
              have \<open>finite {0..n}\<close>
                by simp
              moreover have \<open>finite {Suc n..m}\<close>
                by simp
              moreover have \<open>{0..n} \<union> {Suc n..m} = {0..m}\<close>
              proof-
                have \<open>n < Suc n\<close>
                  by simp
                thus ?thesis using  \<open>n < m\<close> by auto
              qed
              moreover have  \<open>{0..n} \<inter> {Suc n..m} = {}\<close>
                by simp
              ultimately show ?thesis
                by (metis sum.union_disjoint)
            qed
            thus ?thesis
              by linarith 
          qed
          ultimately show ?thesis
            by (simp add: \<open>\<And>k. 0 \<le> a k\<close> sum_nonneg) 
        qed
        thus ?thesis
          by (metis \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>) 
      qed  
      show ?thesis 
      proof-
        obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
          using \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. n < m \<longrightarrow> sum a {Suc n..m} < e\<close> by blast
        hence  \<open>\<forall>m. \<forall>n. Suc m \<ge> Suc M \<and> Suc n \<ge> Suc M \<and> Suc m > Suc n \<longrightarrow> sum a {Suc n..Suc m - 1} < e\<close>
          by simp
        hence  \<open>\<forall>m\<ge>1. \<forall>n\<ge>1. m \<ge> Suc M \<and> n \<ge> Suc M \<and> m > n \<longrightarrow> sum a {n..m - 1} < e\<close>
          by (metis Suc_le_D)
        thus ?thesis 
          by (meson add_leE)
      qed
    qed
    ultimately show ?thesis using \<open>e > 0\<close> by smt
  qed
  thus ?thesis
    using Cauchy_altdef2 by fastforce 
qed

(* TODO: delete *)
lemma LIMSEQ_realpow_inf: 
  fixes x :: real
  assumes \<open>x > 1\<close>
  shows  \<open>( \<lambda> n::nat. x^n) \<longlonglongrightarrow> \<infinity>\<close>
  using Limits.LIMSEQ_inverse_realpow_zero
  by (metis (mono_tags, lifting) Elementary_Topology.real_arch_pow Lim_PInfty assms le_ereal_le less_eq_ereal_def less_ereal.simps(1) power_increasing_iff) 

(* TODO: nonstandard *)
lemma LIMSEQ_scalarR: 
  fixes x :: \<open>nat \<Rightarrow> real\<close> and c :: real
  assumes \<open>x \<longlonglongrightarrow> \<infinity>\<close> and \<open>c > 0\<close>
  shows  \<open>( \<lambda> n::nat. c * (x n)) \<longlonglongrightarrow> \<infinity>\<close>
proof-
  have \<open>M \<ge> 0 \<Longrightarrow> \<exists> N. \<forall> n\<ge>N. c * x n \<ge> ereal M\<close>
    for M
  proof-
    assume \<open>M \<ge> 0\<close>
    hence \<open>(1/c) * M \<ge> 0\<close>
      using \<open>c > 0\<close>
      by auto
    from \<open>x \<longlonglongrightarrow> \<infinity>\<close>
    have \<open>\<exists> N. \<forall> n\<ge>N. x n \<ge> ereal ((1/c) * M)\<close>
      by (simp add: Lim_PInfty)
    hence \<open>\<exists> N. \<forall> n\<ge>N. c*(x n) \<ge> ereal M\<close>
      using \<open>c > 0\<close>
      by (simp add: mult.commute pos_divide_le_eq)
    thus ?thesis
      by blast 
  qed
  hence \<open>\<exists> N. \<forall> n\<ge>N. c * x n \<ge> ereal M\<close>
    for M
  proof(cases \<open>M \<ge> 0\<close>)
    case True
    thus ?thesis
      using \<open>\<And>M. 0 \<le> M \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. ereal M \<le> ereal (c * x n)\<close> by auto 
  next
    case False
    thus ?thesis
    proof -
      have "(0::real) \<le> 0"
        by auto
      then obtain nn :: "real \<Rightarrow> nat" where
        f1: "\<forall>n. \<not> nn 0 \<le> n \<or> ereal 0 \<le> ereal (c * x n)"
        by (meson \<open>\<And>M. 0 \<le> M \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. ereal M \<le> ereal (c * x n)\<close>)
      obtain nna :: "nat \<Rightarrow> nat" where
        "\<forall>x0. (\<exists>v1\<ge>x0. \<not> ereal M \<le> ereal (c * x v1)) = (x0 \<le> nna x0 \<and> \<not> ereal M \<le> ereal (c * x (nna x0)))"
        by moura
      moreover
      { assume "0 \<le> c * x (nna (nn 0))"
        hence "M + - 1 * (c * x (nna (nn 0))) \<le> 0"
          using False by linarith
        hence "\<exists>n. \<not> n \<le> nna n \<or> ereal M \<le> ereal (c * x (nna n))"
          by auto }
      ultimately show ?thesis
        using f1 ereal_less_eq(3) by blast
    qed 
  qed
  thus ?thesis 
    by (simp add: Lim_PInfty)
qed

(* TODO: move? *)
lemma PRElim_shift:
  fixes n::nat
  shows  \<open>\<forall> x::nat \<Rightarrow> 'a::real_normed_vector. \<forall> l::'a. ((\<lambda> k. x (n + k)) \<longlonglongrightarrow> l) \<longrightarrow> (x \<longlonglongrightarrow> l)\<close>
proof(induction n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have \<open>(\<lambda>k. x (Suc n + k)) \<longlonglongrightarrow> l \<Longrightarrow> x \<longlonglongrightarrow> l\<close>
    for x::"nat \<Rightarrow> 'a" and l::'a
  proof-
    assume \<open>(\<lambda>k. x (Suc n + k)) \<longlonglongrightarrow> l\<close>
    hence \<open>(\<lambda>k. x (n + Suc k)) \<longlonglongrightarrow> l\<close>
      by simp
    hence \<open>(\<lambda> t. (\<lambda>k. x (n + k)) (Suc t)) \<longlonglongrightarrow> l\<close>
      by simp
    hence \<open>(\<lambda> t. (\<lambda>k. x (n + k)) t) \<longlonglongrightarrow> l\<close>
      by (rule LIMSEQ_imp_Suc)
    hence \<open>(\<lambda>k. x (n + k)) \<longlonglongrightarrow> l\<close>
      by simp
    thus ?thesis 
      by (simp add: \<open>(\<lambda>k. x (n + k)) \<longlonglongrightarrow> l\<close> Suc.IH)
  qed
  thus ?case by blast
qed

(* TODO: delete *)
lemma lim_shift:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and l::'a and n::nat
  assumes \<open>(\<lambda> k. x (n + k)) \<longlonglongrightarrow> l\<close>
  shows \<open>x \<longlonglongrightarrow> l\<close>
  using assms  PRElim_shift by auto

lemma identity_telescopic:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and l::'a and n::nat
  assumes \<open>x \<longlonglongrightarrow> l\<close>
  shows \<open>(\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<longlonglongrightarrow> l - x n\<close>
proof-
  have \<open>sum (\<lambda> k. x (Suc k) - x k) {n..n+p} = x (Suc (n+p)) - x n\<close>
    for p
  proof(induction p)
    case 0
    thus ?case by simp
  next
    case (Suc p)
    thus ?case by simp
  qed
  moreover have \<open>(\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) (n + t)  = (\<lambda> p. sum (\<lambda> k. x (Suc k) - x k) {n..n+p}) t\<close>
    for t
    by blast
  moreover have \<open>(\<lambda> p. x (Suc (n + p)) - x n)\<longlonglongrightarrow> l - x n\<close>
  proof-
    from \<open>x \<longlonglongrightarrow> l\<close>
    have \<open>(\<lambda> p. x (p + Suc n)) \<longlonglongrightarrow> l\<close>
      by (rule LIMSEQ_ignore_initial_segment)
    hence \<open>(\<lambda> p. x (Suc n + p)) \<longlonglongrightarrow> l\<close>   
      by (simp add: add.commute)
    have \<open>(\<lambda> p. x (Suc (n + p))) \<longlonglongrightarrow> l\<close>
    proof-
      have \<open>Suc n + p = Suc (n + p)\<close>
        for p
        by simp
      thus ?thesis using \<open>(\<lambda> p. x (Suc n + p)) \<longlonglongrightarrow> l\<close> by simp 
    qed
    hence \<open>(\<lambda> t. (- (x n)) + (\<lambda> p.  x (Suc (n + p))) t ) \<longlonglongrightarrow> (- (x n))  + l\<close>
      using tendsto_add_const_iff 
      by metis 
    thus ?thesis by simp
  qed
  ultimately have  \<open>(\<lambda> p. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) (n + p)) \<longlonglongrightarrow> l - x n\<close>
    by simp
  hence  \<open>(\<lambda> p. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) p) \<longlonglongrightarrow> l - x n\<close>
    by (rule lim_shift)
  hence  \<open>(\<lambda> M. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) M) \<longlonglongrightarrow> l - x n\<close>
    by simp
  thus ?thesis by blast
qed


lemma bound_telescopic:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and l::'a and n::nat and K::real
  assumes \<open>x \<longlonglongrightarrow> l\<close> and \<open>\<And> k. (sum (\<lambda> t. norm (x (Suc t) - x t)) {n..k}) \<le> K\<close>
  shows \<open>norm (l - x n) \<le> K\<close>
proof-
  have \<open>(\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<longlonglongrightarrow> l - x n\<close>
    by (simp add: assms identity_telescopic)
  hence \<open>(\<lambda> N. norm (sum (\<lambda> k. x (Suc k) - x k) {n..N})) \<longlonglongrightarrow> norm (l - x n)\<close>
    using tendsto_norm by blast
  moreover have \<open>norm (sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<le> K\<close>
    for N
  proof-
    have \<open>norm (sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<le> sum (\<lambda> n. norm (x (Suc n) - x n)) {n..N}\<close>
      by (simp add: sum_norm_le)      
    also have \<open>... \<le> K \<close>
    proof-
      have \<open>sum (\<lambda> n. norm (x (Suc n) - x n)) {n..N}
               \<in> { (sum (\<lambda> n. norm (x (Suc n) - x n)) {n..K})|K::nat. True}\<close>
        by blast
      moreover have \<open>bdd_above { (sum (\<lambda> n. norm (x (Suc n) - x n)) {n..K})|K::nat. True}\<close>
        using  \<open>\<And> k. (sum (\<lambda> n. norm (x (Suc n) - x n)) {n..k}) \<le> K\<close>
        by fastforce        
      ultimately have  \<open>sum (\<lambda> n. norm (x (Suc n) - x n)) {n..N} \<le> K\<close>
        using  \<open>\<And> k. (sum (\<lambda> n. norm (x (Suc n) - x n)) {n..k}) \<le> K\<close>
        by blast
      thus ?thesis
        by (simp add: full_SetCompr_eq) 
    qed
    finally show ?thesis by blast
  qed
  ultimately show ?thesis
    using Lim_bounded by blast 
qed

text \<open>The proof of the following result was taken from [sokal2011really]\<close>

(* TODO: nonstandard *)
theorem banach_steinhaus:
  fixes f :: \<open>'c \<Rightarrow> ('a::{banach,perfect_space} \<Rightarrow> 'b::real_normed_vector)\<close>
  assumes \<open>\<And> n. bounded_linear (f n)\<close>
    and  \<open>\<And> x. \<exists> M. \<forall> n.  norm ((f n) x) \<le> M\<close>
  shows  \<open>\<exists> M. \<forall> n. onorm (f n) \<le> M\<close>
proof(rule classical)
  assume \<open>\<not>(\<exists> M. \<forall> k. onorm (f k) \<le> M)\<close>
  hence \<open>\<forall> M. \<exists> k. onorm (f k) > M\<close>
    using leI by blast
  hence \<open>\<forall> n. \<exists> k. onorm (f k) > 4^n\<close>
    by simp
  hence \<open>\<exists> k\<^sub>f. \<forall> n. onorm (f (k\<^sub>f n)) > 4^n\<close>
    by metis
  then obtain k\<^sub>f where \<open>\<forall> n. onorm (f (k\<^sub>f n)) > 4^n\<close> 
    by blast
  define g::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close> where \<open>g n = f (k\<^sub>f n)\<close>
    for n
  hence \<open>\<forall> n. onorm (g n) > 4^n\<close>
    using  \<open>\<forall> n. onorm (f (k\<^sub>f n)) > 4^n\<close>  by simp
  from \<open>\<And> n. bounded_linear (f n)\<close>
  have \<open>\<And> n. bounded_linear (g n)\<close>
    using g_def by simp
  have \<open>bounded_linear h \<Longrightarrow> 0 < onorm h \<Longrightarrow> r > 0
     \<Longrightarrow> \<exists> y. dist y x < r \<and> norm (h y) > (2/3) * r * onorm h\<close>
    for r and x and h::\<open>'a \<Rightarrow> 'b\<close>
  proof-
    assume \<open>bounded_linear h\<close>
    moreover assume \<open>r > 0\<close>
    ultimately have \<open>(onorm h) * r \<le> Sup {norm (h y) | y. dist y x < r}\<close>
      by (simp add: sokal_banach_steinhaus)
    assume \<open>0 < onorm h\<close>
    have \<open>(onorm h) * r * (2/3) < Sup {norm (h y) | y. dist y x < r}\<close>
    proof -
      have f1: "\<forall>r ra. (ra::real) * r = r * ra"
        by auto
      hence f2: "r * onorm h \<le> Sup {norm (h a) |a. dist a x < r}"
        by (metis \<open>onorm h * r \<le> Sup {norm (h y) |y. dist y x < r}\<close>)
      have "0 < r * onorm h"
        by (metis \<open>0 < onorm h\<close> \<open>0 < r\<close> linordered_semiring_strict_class.mult_pos_pos)
      hence "r * onorm h * (2 / 3) < Sup {norm (h a) |a. dist a x < r}"
        using f2 by linarith
      thus ?thesis
        using f1 by presburger
    qed 
    moreover have \<open>{norm (h y) | y. dist y x < r} \<noteq> {}\<close>
    proof-
      have \<open>\<exists> y::'a. dist y x < r\<close>
        using \<open>r > 0\<close>
        by (metis dist_self)
      hence \<open>{y | y. dist y x < r} \<noteq> {}\<close>
        by simp
      hence \<open>(\<lambda> y. norm ((g n) y)) ` {y | y. dist y x < r} \<noteq> {}\<close>
        for n
        by blast
      thus ?thesis by blast
    qed
    moreover have \<open>bdd_above {norm (h y) | y. dist y x < r}\<close>
    proof-
      have \<open>norm (h y) \<le> onorm h * norm y\<close>
        for y
        using \<open>bounded_linear h\<close>
        by (simp add: onorm)    
      moreover have \<open>norm y \<le> norm x + norm (y - x)\<close>
        for y
        by (simp add: norm_triangle_sub)        
      moreover have \<open>onorm h \<ge> 0\<close>
        by (simp add: \<open>bounded_linear h\<close> onorm_pos_le)
      ultimately have \<open>norm (h y) \<le> onorm h * (norm x + norm (y - x))\<close>
        for y
        by (smt ordered_comm_semiring_class.comm_mult_left_mono)
      hence \<open>norm (h y) \<le> onorm h * (norm x + dist y x)\<close>
        for y
        by (simp add: dist_norm)
      hence \<open>dist y x < r \<Longrightarrow> norm (h y) < onorm h * (norm x + r)\<close>
        for y
        by (smt \<open>0 < onorm h\<close> mult_left_le_imp_le)
      hence \<open>t \<in> {norm (h y) | y. dist y x < r} \<Longrightarrow> t \<le> onorm h * (norm x + r)\<close>
        for t
        by fastforce
      thus ?thesis by fastforce
    qed
    ultimately have \<open>\<exists> t \<in> {norm (h y) | y. dist y x < r}. 
                    (onorm h) * r * (2/3) < t\<close>
      using less_cSup_iff
      by smt
    hence \<open>\<exists> s \<in> {y | y. dist y x < r}. 
                    (onorm h) * r * (2/3) < norm (h s)\<close>
      by blast
    hence \<open>\<exists> y. dist y x < r \<and> 
                    (onorm h) * r * (2/3) < norm (h y)\<close>
      by blast
    hence \<open>\<exists> y. dist y x < r \<and> 
                   r * (2/3) * (onorm h) < norm (h y)\<close>
      by (metis mult.commute vector_space_over_itself.scale_scale)
    thus ?thesis by auto
  qed
  hence \<open>\<exists> y. dist y x < (1/3)^n \<and> norm ((g n) y) > (2/3) * (1/3)^n * onorm (g n)\<close>
    for n and x
  proof-
    have \<open>((1/3)::real)^n > 0\<close>
      by simp
    moreover have \<open>\<And> n. onorm (g n) > 0\<close>
      using  \<open>\<forall> n. onorm (g n) > (4::real)^n\<close>
      by (smt zero_less_power)                             
    ultimately show ?thesis using  \<open>\<And> n. bounded_linear (g n)\<close>
      using \<open>\<And>x r h. \<lbrakk>bounded_linear h; 0 < onorm h; 0 < r\<rbrakk> \<Longrightarrow> \<exists>y. dist y x < r \<and> 2 / 3 * r * onorm h < norm (h y)\<close> by auto
  qed
  hence \<open>\<forall> n. \<forall> x. \<exists> y. dist y x < (1/3)^n \<and> norm ((g n) y) > (2/3) * (1/3)^n * onorm (g n)\<close>
    by blast
  hence \<open>\<exists> \<Phi>. \<forall> n. \<forall> x. dist (\<Phi> n x) x < (1/3)^n \<and> norm ((g n) (\<Phi> n x)) > (2/3) * (1/3)^n * onorm (g n)\<close>
    by metis
  then obtain \<Phi>
    where \<open>\<forall> n. \<forall> x. dist (\<Phi> n x) x <
       (1/3)^n \<and> norm ((g n) (\<Phi> n x)) > (2/3) * (1/3)^n * onorm (g n)\<close>
    by blast
  define \<phi>::\<open>nat \<Rightarrow> 'a\<close> where \<open>\<phi> n = rec 0 \<Phi> n\<close>
    for n
  have \<open>\<phi> 0 = 0\<close>
    using \<phi>_def by simp
  have \<open>\<phi> (Suc n) = \<Phi> n (\<phi> n)\<close>
    for n
    using \<phi>_def by simp
  from \<open>\<forall> n. \<forall> x. dist (\<Phi> n x) x <
       (1/3)^n \<and> norm ((g n) (\<Phi> n x)) > (2/3) * (1/3)^n * onorm (g n)\<close>
  have \<open>dist (\<phi> (Suc n))  (\<phi> n) < (1/3)^n\<close>
    for n
    using \<open>\<And>n. \<phi> (Suc n) = \<Phi> n (\<phi> n)\<close> by auto
  have \<open>Cauchy \<phi>\<close>
  proof-
    have \<open>norm ((1/3)::real) < 1\<close>
      by simp      
    hence \<open>summable (\<lambda> k. ((1/3)::real)^k)\<close>
      using Series.summable_geometric_iff 
      by fastforce
    hence \<open>\<exists>s. (\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {..<n}) \<longlonglongrightarrow> s\<close>
      unfolding summable_def sums_def by blast
    hence \<open>\<exists>s. (\<lambda>m. (\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {..<n}) (Suc m)) \<longlonglongrightarrow> s\<close>
    proof-
      obtain s where \<open>(\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {..<n}) \<longlonglongrightarrow> s\<close>
        using  \<open>\<exists>s. (\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {..<n}) \<longlonglongrightarrow> s\<close> by blast
      hence  \<open>(\<lambda>m. (\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {..<n}) (Suc m)) \<longlonglongrightarrow> s\<close>
        by (rule LIMSEQ_Suc) 
      thus ?thesis by blast 
    qed
    hence \<open>\<exists>s. (\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {..n}) \<longlonglongrightarrow> s\<close>
      using \<open>summable (\<lambda> k::nat. ((1/3)::real)^k)\<close> summable_LIMSEQ' by blast 
    hence \<open>\<exists>s::real. (\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) \<longlonglongrightarrow> s\<close>
      unfolding atLeastAtMost_def 
      by auto
    then obtain s::real where \<open>(\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) \<longlonglongrightarrow> s\<close>
      by blast
    from  \<open>(\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) \<longlonglongrightarrow> s\<close>
    have \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> m \<ge> N. dist ((\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) m)  s < e\<close>
      for e::real
      by (meson LIMSEQ_iff_nz)
    moreover have \<open>(1::real) > 0\<close>
      by auto
    ultimately have \<open>\<exists> N. \<forall> m \<ge> N. dist ((\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) m)  s < (1::real)\<close>
      by auto
    then obtain N where \<open>\<forall> m \<ge> N. dist ((\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) m)  s < (1::real)\<close>
      by blast
    hence \<open>\<forall> m \<ge> N. \<bar> ((\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) m) - s \<bar> < (1::real)\<close>
      by (simp add: dist_real_def)
    hence \<open>\<forall> m \<ge> N. \<bar> ((\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) m) \<bar> < \<bar>s\<bar> + (1::real)\<close>
      by auto
    hence \<open>\<forall> m \<ge> N. ((\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) m) < \<bar>s\<bar> + (1::real)\<close>
      by auto
    hence \<open>\<forall> n \<ge> N. (sum (\<lambda> k. ((1/3)::real)^k) {0..n}) < \<bar>s\<bar> + (1::real)\<close>
      by auto
    hence \<open>\<forall> n \<ge> N. (sum (\<lambda> k. ((1/3)::real)^k) {0..n}) \<le> \<bar>s\<bar> + (1::real)\<close>
      by auto
    moreover have \<open>\<forall> n < N. (sum (\<lambda> k. ((1/3)::real)^k) {0..n}) \<le> (sum (\<lambda> k. ((1/3)::real)^k) {0..N})\<close>
    proof-
      have  \<open>\<forall> n. f n \<ge> 0 \<Longrightarrow> \<forall> n < N. sum f {0..n} \<le> sum f {0..N}\<close>
        for f :: \<open>nat \<Rightarrow> real\<close> and N::nat
      proof(induction N)
        case 0
        thus ?case
          by simp 
      next
        case (Suc N)
        assume \<open>\<forall> n. f n \<ge> 0\<close>
        moreover assume \<open>\<forall>n. 0 \<le> f n \<Longrightarrow> \<forall>n<N. sum f {0..n} \<le> sum f {0..N}\<close>
        ultimately have \<open>\<forall>n<N. sum f {0..n} \<le> sum f {0..N}\<close>
          by blast
        moreover have  \<open>sum f {0..N} \<le> sum f {0..Suc N}\<close>
        proof-
          have \<open>sum f {0..Suc N} = sum f {0..N} + f (Suc N)\<close>
            using sum.atLeast0_atMost_Suc by blast          
          thus ?thesis
            by (simp add: Suc.prems) 
        qed
        ultimately show ?case
          by (smt less_antisym)  
      qed
      thus ?thesis
        by auto
    qed
    ultimately have \<open>\<forall> n. (sum (\<lambda> k. ((1/3)::real)^k) {0..n})
         \<le> max (\<bar>s\<bar> + (1::real)) (sum (\<lambda> k. ((1/3)::real)^k) {0..N})\<close>
      by (smt diff_is_0_eq gr_zeroI zero_less_diff)
    hence \<open>\<exists> M. \<forall> n. (sum (\<lambda> k. ((1/3)::real)^k) {0..n}) \<le> M\<close>
      by blast
    thus ?thesis
      using convergent_series_Cauchy  \<open>\<And> n. dist (\<phi> (Suc n))  (\<phi> n) < (1/3)^n\<close>
      by smt
  qed
  hence \<open>\<exists> l. \<phi> \<longlonglongrightarrow> l\<close>
    by (simp add: convergent_eq_Cauchy)
  then obtain l where \<open>\<phi> \<longlonglongrightarrow> l\<close>
    by blast
  obtain M where \<open>\<forall> n.  norm ((f n) l) \<le> M\<close>
    using \<open>\<And> x. \<exists> M. \<forall> n.  norm ((f n) x) \<le> M\<close>
    by blast
  have \<open>(\<lambda> n. norm ((g n) l)) \<longlonglongrightarrow> \<infinity>\<close>    
  proof-
    have  \<open>norm ((\<phi> (Suc n)) - l) \<le> (1/2)*(1/3::real)^n\<close>
      for n
    proof-             
      define x where \<open>x = (\<lambda> n.  \<phi> (Suc n))\<close>
      have \<open>x \<longlonglongrightarrow> l\<close> 
        using x_def
        by (meson \<open>\<phi> \<longlonglongrightarrow> l\<close> le_imp_less_Suc pinf(8) tendsto_explicit)
      moreover have \<open>(sum (\<lambda> t. norm (x (Suc t) - x t)) {n..k}) \<le> (1/2)*(1/3::real)^n\<close>
        for k
      proof-
        have \<open>(sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..k}) \<le> (1/2)*(1/3::real)^n\<close>
        proof-
          from  \<open>\<And> n. dist (\<phi> (Suc n))  (\<phi> n) < (1/3)^n\<close>
          have  \<open>norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t)) < (1/3::real)^(Suc t)\<close>
            for t
            by (metis dist_norm)            
          hence \<open>(sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..n+p}) 
              \<le> (sum (\<lambda> t. (1/3::real)^(Suc t) ) {n..n+p})\<close> 
            for p::nat
          proof(induction p)
            case 0
            have \<open>norm (\<phi> (Suc (Suc n)) - \<phi> (Suc n)) < (1/3::real)^(Suc n)\<close>
              using \<open>\<And> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t)) < (1/3::real)^(Suc t)\<close>
              by blast
            hence \<open>(\<Sum>t = n..n. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) \<le> (\<Sum>t = n..n. (1 / 3) ^ Suc t)\<close>
              by simp
            thus ?case 
              by simp
          next
            case (Suc p)
            thus ?case
              by (smt add_Suc_right le_add1 sum.nat_ivl_Suc') 
          qed
          moreover have  \<open>(sum (\<lambda> t. (1/3::real)^(Suc t) ) {n..n+p}) \<le> (1/2)*(1/3::real)^n\<close> 
            for p::nat
          proof-
            have \<open>n \<le> n + p\<close>
              by auto
            hence \<open>(sum (\<lambda> t. (1/3::real)^(Suc t)) {n..n+p})  
                = (sum ((\<lambda> t. (1/3::real)^(Suc t))\<circ>((+) n)) {0..(n + p) - n})\<close> 
              by (rule Set_Interval.comm_monoid_add_class.sum.atLeastAtMost_shift_0)
            hence \<open>(sum (\<lambda> t. (1/3::real)^(Suc t)) {n..n+p})  
                = (sum (\<lambda> t. (1/3::real)^(Suc n+t)) {0..p})\<close> 
              by simp
            hence \<open>(sum (\<lambda> t. (1/3::real)^(Suc t)) {n..n+p})  
                = (sum (\<lambda> t. (1/3::real)^(Suc n)*(1/3::real)^t) {0..p})\<close>
              by (simp add: power_add) 
            hence \<open>(sum (\<lambda> t. (1/3::real)^(Suc t)) {n..n+p})  
                = (1/3::real)^(Suc n)*(sum (\<lambda> t. (1/3::real)^t) {0..p})\<close>
              by (simp add: sum_distrib_left)
            moreover have  \<open>(sum (\<lambda> t. (1/3::real)^t) {0..p}) \<le> (3/2::real)\<close>
            proof-
              have \<open>norm (1/3::real) < 1\<close>
                by simp
              hence \<open>(sum (\<lambda> t. (1/3::real)^t) {0..p}) = (1 - (1/3::real)^(Suc p))/(1 -  (1/3::real))\<close>
                using sum_gp0
                by (smt atMost_atLeast0 right_inverse_eq)
              also have \<open>... \<le> 1/(1 -  (1/3::real))\<close>
                by simp
              finally show ?thesis by simp
            qed
            ultimately have \<open>(sum (\<lambda> t. (1/3::real)^(Suc t) ) {n..n+p}) 
                  \<le> (1/3::real)^(Suc n)*(3/2)\<close>
              by (smt ordered_comm_semiring_class.comm_mult_left_mono zero_le_divide_1_iff zero_le_power)               
            thus ?thesis
              by simp 
          qed
          ultimately have \<open>(sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..n+p})
                           \<le> (1/2)*(1/3::real)^n\<close>
            for p::nat
            by smt
          hence \<open>m \<ge> n \<Longrightarrow> (sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..m})
                           \<le> (1/2)*(1/3::real)^n\<close>
            for m::nat
            using nat_le_iff_add by auto
          moreover have \<open>m < n \<Longrightarrow> (sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..m})
                           \<le> (1/2)*(1/3::real)^n\<close>
            for m::nat
            by simp
          ultimately have \<open>(sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..m})
                           \<le> (1/2)*(1/3::real)^n\<close>
            for m::nat
            by (metis (full_types) le_eq_less_or_eq less_or_eq_imp_le linorder_neqE_nat) 
          thus ?thesis by blast           
        qed
        thus ?thesis unfolding x_def by blast
      qed
      ultimately have \<open>norm (l - x n) \<le> (1/2)*(1/3::real)^n\<close>
        by (rule bound_telescopic )
      show ?thesis using x_def
        by (metis \<open>norm (l - x n) \<le> 1 / 2 * (1 / 3) ^ n\<close> norm_minus_commute) 
    qed
    have \<open>norm ((g n) l) \<ge> (1/6) * (1/3::real)^n * onorm (g n)\<close>
      for n
    proof-
      have \<open>norm ((g n) (\<phi> (Suc n))) = norm ( ((g n) l) + (g n) ((\<phi> (Suc n)) - l) )\<close>
      proof-
        have \<open>(g n) (\<phi> (Suc n)) = ((g n) l) + (g n) ((\<phi> (Suc n)) - l)\<close>
          using \<open>bounded_linear (g n)\<close>
          by (simp add: linear_simps(2)) 
        thus ?thesis by simp
      qed
      also have \<open>... \<le>  norm ((g n) l) + norm ((g n) ((\<phi> (Suc n)) - l))\<close>
        by (simp add: norm_triangle_ineq) 
      finally have \<open>norm ((g n) (\<phi> (Suc n))) \<le> norm ((g n) l) + norm ((g n) ((\<phi> (Suc n)) - l))\<close>
        by blast
      moreover have \<open>norm ((g n) ((\<phi> (Suc n)) - l)) \<le> onorm (g n) * norm ((\<phi> (Suc n)) - l)\<close>
      proof-
        have \<open>bounded_linear (g n)\<close>
          by (simp add: \<open>\<And>n. bounded_linear (g n)\<close>)          
        thus ?thesis using onorm by blast
      qed
      ultimately have \<open>norm ((g n) (\<phi> (Suc n))) \<le> norm ((g n) l) + onorm (g n) * norm ((\<phi> (Suc n)) - l)\<close>
        by simp
      also have \<open>... \<le>  norm ((g n) l) + onorm (g n) * ((1/2) * (1/3::real)^n) \<close>
      proof-
        have \<open>onorm (g n)  \<ge> 0\<close>
          by (simp add: \<open>\<And>n. bounded_linear (g n)\<close> onorm_pos_le)          
        hence \<open>onorm (g n) * norm ((\<phi> (Suc n)) - l) \<le> onorm (g n) * ((1/2) * (1/3::real)^n)\<close>
          using \<open>norm ((\<phi> (Suc n)) - l) \<le> (1/2)*(1/3::real)^n\<close>
          using mult_left_mono by blast
        thus ?thesis by simp
      qed
      finally have \<open>norm ((g n) (\<phi> (Suc n))) \<le> norm ((g n) l) + onorm (g n) * ((1/2) * (1/3::real)^n)\<close>
        by blast
      moreover have \<open>norm ((g n) (\<phi> (Suc n))) > (2/3) * (1/3)^n * onorm (g n)\<close>
      proof-
        from \<open>\<forall> n. \<forall> x. dist (\<Phi> n x) x <
         (1/3)^n \<and> norm ((g n) (\<Phi> n x)) > (2/3) * (1/3)^n * onorm (g n)\<close>
        have \<open>norm ((g n) (\<Phi> n x)) > (2/3) * (1/3)^n * onorm (g n)\<close>
          for x     
          by blast
        hence \<open>norm ((g n) (\<Phi> n (\<phi> n))) > (2/3) * (1/3)^n * onorm (g n)\<close>
          by blast
        thus ?thesis by (simp add: \<open>\<And>n. \<phi> (Suc n) = \<Phi> n (\<phi> n)\<close>)
      qed
      ultimately have \<open>(2/3) * (1/3)^n * onorm (g n) < norm ((g n) l) + onorm (g n) * ((1/2) * (1/3::real)^n)\<close>
        by simp
      hence \<open>(2/3) * (1/3)^n * onorm (g n) - onorm (g n) * ((1/2) * (1/3::real)^n)  < norm ((g n) l)\<close>
        by smt
      hence \<open>(2/3) * ((1/3)^n * onorm (g n)) - (1/2) * ((1/3::real)^n * onorm (g n))  < norm ((g n) l)\<close>
        by simp
      moreover have \<open>(2/3) * ((1/3)^n * onorm (g n)) - (1/2) * ((1/3::real)^n * onorm (g n))
          = (1/6) * (1/3)^n * onorm (g n)\<close>
        by simp
      ultimately have \<open>(1/6) * (1/3)^n * onorm (g n) < norm ((g n) l)\<close>
        by linarith
      thus ?thesis by simp
    qed
    moreover have \<open>(1/6) * (1/3::real)^n * onorm (g n) > (1/6) * (1/3::real)^n * 4^n\<close>
      for n
      using \<open>\<forall> n. onorm (g n) > 4^n\<close>
      by auto
    ultimately have \<open>norm ((g n) l) > (1/6) * (1/3::real)^n * 4^n\<close>
      for n
      by smt
    hence \<open>norm ((g n) l) > ereal((1/6) * (4/3::real)^n)\<close>
      for n
      by (simp add: power_divide) 
    moreover have \<open>(\<lambda> n::nat. ereal((1/6) * (4/3::real)^n) ) \<longlonglongrightarrow> \<infinity>\<close>
    proof-
      have \<open>norm (4/3::real) > 1\<close>
        by simp
      hence  \<open>(\<lambda> n::nat. ((4/3::real)^n)) \<longlonglongrightarrow> \<infinity>\<close>
        using LIMSEQ_realpow_inf by auto
      moreover have \<open>(1/6::real) > 0\<close>
        by simp
      ultimately have \<open>(\<lambda> n::nat. (1/6::real) * (4/3::real)^n ) \<longlonglongrightarrow> \<infinity>\<close>
        using LIMSEQ_scalarR
        by blast       
      thus ?thesis by blast
    qed
    ultimately show ?thesis using Lim_PInfty
    proof -
      obtain rr :: real where
        "\<forall>n. norm (g n l) \<le> rr"
        by (metis (no_types) \<open>\<And>thesis. (\<And>M. \<forall>n. norm (f n l) \<le> M \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>g \<equiv> \<lambda>n. f (k\<^sub>f n)\<close>)
      hence "\<forall>e. e \<le> ereal rr \<or> \<not> (\<lambda>n. ereal (1 / 6 * (4 / 3) ^ n)) \<longlonglongrightarrow> e"
        by (meson Lim_bounded \<open>\<And>n. ereal (1 / 6 * (4 / 3) ^ n) < ereal (norm (g n l))\<close> less_eq_ereal_def less_ereal_le)
      hence "\<infinity> \<le> ereal rr"
        using \<open>(\<lambda>n. ereal (1 / 6 * (4 / 3) ^ n)) \<longlonglongrightarrow> \<infinity>\<close> by blast
      thus ?thesis
        by simp
    qed 
  qed
  hence \<open>(\<lambda> n. norm ((f (k\<^sub>f n)) l)) \<longlonglongrightarrow> \<infinity>\<close>    
    using g_def by simp
  hence \<open>\<exists> N. norm ((f (k\<^sub>f N)) l) > M\<close>
    using Lim_bounded_PInfty2 \<open>\<forall>n. norm (f n l) \<le> M\<close> ereal_less_eq(3) by blast 
  then obtain N where \<open>norm ((f (k\<^sub>f N)) l) > M\<close>
    by blast
  have \<open>norm ((f (k\<^sub>f N)) l) \<le> M\<close>
    by (simp add: \<open>\<forall>n. norm (f n l) \<le> M\<close>)
  show ?thesis using  \<open>norm ((f (k\<^sub>f N)) l) > M\<close>  \<open>norm ((f (k\<^sub>f N)) l) \<le> M\<close>
    by linarith
qed

lemma strong_convergence_pointwise: 
  \<open>f \<midarrow>strong\<rightarrow> F \<Longrightarrow> (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
  for x
proof-
  assume  \<open>f \<midarrow>strong\<rightarrow> F\<close>
  hence  \<open>( \<lambda> n. norm ((f n) x - F x))  \<longlonglongrightarrow> 0\<close>
    unfolding strong_convergence_def
    by blast
  have \<open>( \<lambda> n. (F x) )  \<longlonglongrightarrow> F x\<close>
    by simp
  moreover have  \<open>( \<lambda> n. ( (f n) x - F x))  \<longlonglongrightarrow> 0\<close>
    using  \<open>( \<lambda> n. norm ((f n) x - F x) )  \<longlonglongrightarrow> 0\<close>
    by (simp add:  tendsto_norm_zero_iff)
  ultimately have  \<open>( \<lambda> n. (f n) x)  \<longlonglongrightarrow> F x\<close>
    by (rule Limits.Lim_transform)
  thus ?thesis by blast
qed

lemma linear_limit_linear:
  fixes f :: \<open>nat \<Rightarrow> ('a::real_vector \<Rightarrow> 'b::real_normed_vector)\<close>
    and F :: \<open>'a\<Rightarrow>'b\<close>
  assumes  \<open>\<And> n. linear (f n)\<close> 
    and  \<open>f \<midarrow>strong\<rightarrow> F\<close>
  shows \<open>linear F\<close> 
proof
  have \<open>\<And> x. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
    using  \<open>f \<midarrow>strong\<rightarrow> F\<close> by (rule strong_convergence_pointwise)
  show "F (x + y) = F x + F y"
    for x :: 'a
      and y :: 'a
  proof-
    have \<open>(\<lambda> n. (f n) (x + y)) \<longlonglongrightarrow> F (x + y)\<close>
      by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>(\<lambda> n. (f n) y) \<longlonglongrightarrow> F y\<close>
      by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>lim (\<lambda> n. (f n) (x + y)) = lim (\<lambda> n. (f n) x) + lim (\<lambda> n. (f n) y)\<close> 
    proof-
      have \<open>(f n) (x + y) = (f n) x + (f n) y\<close>
        for n
        using \<open>\<And> n.  linear (f n)\<close>
        unfolding linear_def
        using Real_Vector_Spaces.linear_iff assms(1) by auto
      hence \<open>lim (\<lambda> n. (f n) (x + y)) = lim (\<lambda> n. (f n) x + (f n) y)\<close>
        by simp
      moreover have \<open>lim (\<lambda> n. (f n) x + (f n) y) = lim (\<lambda> n. (f n) x) + lim (\<lambda> n. (f n) y)\<close>
      proof-
        have \<open>convergent (\<lambda> n. (f n) x)\<close> 
          using \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> convergentI by auto
        moreover have \<open>convergent (\<lambda> n. (f n) y)\<close> 
          using \<open>(\<lambda> n. (f n) y) \<longlonglongrightarrow> F y\<close> convergentI by auto            
        ultimately show ?thesis
        proof -
          have f1: "\<forall>a. F a = lim (\<lambda>n. f n a)"
            by (metis (full_types)  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close> limI)
          have "\<forall>f b ba fa. (lim (\<lambda>n. fa n + f n) = (b::'b) + ba \<or> \<not> f \<longlonglongrightarrow> ba) \<or> \<not> fa \<longlonglongrightarrow> b"
            by (metis (no_types) limI tendsto_add)
          thus ?thesis
            using f1  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close> by fastforce
        qed 
      qed
      ultimately show ?thesis
        by simp  
    qed
    ultimately show ?thesis
      by (metis limI) 
  qed
  show "F (r *\<^sub>R x) = r *\<^sub>R F x"
    for r :: real
      and x :: 'a
  proof-
    have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      by (simp add:  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>(\<lambda> n.  (f n) (r *\<^sub>R x)) \<longlonglongrightarrow> F (r *\<^sub>R x)\<close>
      by (simp add:  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>lim (\<lambda> n.  (f n) (r *\<^sub>R x)) = r *\<^sub>R lim (\<lambda> n. (f n) x)\<close>
    proof-
      have \<open>(f n) (r *\<^sub>R x) = r *\<^sub>R (f n) x\<close>
        for n
        using  \<open>\<And> n.  linear (f n)\<close>
        unfolding linear_def
        unfolding Modules.additive_def
        by (simp add: Real_Vector_Spaces.linear_def linear_scale)

      hence \<open>lim (\<lambda> n. (f n) (r *\<^sub>R x)) = lim (\<lambda> n. r *\<^sub>R (f n) x)\<close>
        by simp
      show ?thesis 
      proof-
        have \<open>convergent (\<lambda> n. (f n) x)\<close>
          using \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> convergentI by auto
        moreover have \<open>isCont (\<lambda> t::'b. r *\<^sub>R t) tt\<close>
          for tt
          by (simp add: bounded_linear_scaleR_right)
        ultimately have \<open>lim (\<lambda> n. r *\<^sub>R ((f n) x)) =  r *\<^sub>R lim (\<lambda> n. (f n) x)\<close>
          by (metis (mono_tags)  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close> isCont_tendsto_compose limI)
        thus ?thesis using  \<open>lim (\<lambda> n. (f n) (r *\<^sub>R x)) = lim (\<lambda> n. r *\<^sub>R (f n) x)\<close>
          by simp
      qed
    qed
    ultimately show ?thesis
      by (metis limI) 
  qed
qed

lemma bounded_linear_limit_bounded_linear:
  fixes f :: \<open>nat \<Rightarrow> ('a::{banach, perfect_space} \<Rightarrow> 'b::real_normed_vector)\<close>
    and F :: \<open>'a\<Rightarrow>'b\<close>
  assumes  \<open>\<And> n. bounded_linear (f n)\<close> and  \<open>f \<midarrow>strong\<rightarrow> F\<close> 
  shows \<open>bounded_linear F\<close> 
proof-
  have \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
    using \<open>f \<midarrow>strong\<rightarrow> F\<close> by (rule strong_convergence_pointwise)
  have \<open>linear F\<close>
    using assms(1) assms(2) bounded_linear.linear linear_limit_linear by blast
  moreover have \<open>bounded_linear_axioms F\<close>
  proof
    have "\<exists>K. \<forall> n. \<forall>x. norm ((f n) x) \<le> norm x * K"
    proof-
      have \<open>\<exists> M. \<forall> n. norm ((f n) x) \<le> M\<close>
        for x
      proof-
        have \<open>isCont (\<lambda> t::'b. norm t) y\<close>
          for y::'b
          using Limits.isCont_norm
          by simp
        hence \<open>(\<lambda> n. norm ((f n) x)) \<longlonglongrightarrow> (norm (F x))\<close>
          using \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
          by (simp add: tendsto_norm)
        thus ?thesis using Elementary_Metric_Spaces.convergent_imp_bounded
          by (metis UNIV_I \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> bounded_iff image_eqI)
      qed
      hence \<open>\<exists> M. \<forall> n. onorm (f n) \<le> M\<close>
      proof-
        have \<open>\<And> n. bounded_linear (f n)\<close>
          by (simp add: assms(1) bounded_linear.bounded_linear)           
        moreover have  \<open>\<And>x. \<exists>M. \<forall>n. norm (f n x) \<le> M\<close>
          by (simp add: \<open>\<And>x. \<exists>M. \<forall>n. norm (f n x) \<le> M\<close>)          
        ultimately show ?thesis 
          by (rule banach_steinhaus)
      qed
      then obtain M where \<open>\<forall> n. \<forall> x. onorm (f n) \<le> M\<close>
        by blast
      have \<open>\<forall> n. \<forall>x. norm ((f n) x) \<le> norm x * onorm (f n)\<close>
        using \<open>\<And> n. bounded_linear (f n)\<close>
        unfolding bounded_linear_def
        by (metis assms(1) mult.commute onorm)
      thus ?thesis using  \<open>\<forall> n. \<forall> x. onorm (f n) \<le> M\<close>
        by (metis (no_types, hide_lams) dual_order.trans norm_eq_zero order_refl real_mult_le_cancel_iff2 vector_space_over_itself.scale_zero_left zero_less_norm_iff)    
    qed
    thus "\<exists>K. \<forall>x. norm (F x) \<le> norm x * K"
      using  \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      by (metis Lim_bounded tendsto_norm) 
  qed
  ultimately show ?thesis unfolding bounded_linear_def by blast
qed

(* TODO: nonstandard *)
lemma onorm_tendsto:
  fixes f :: \<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close> and l :: \<open>'a \<Rightarrow> 'b\<close> 
    and e :: real
  assumes \<open>\<forall>n. bounded_linear (f n)\<close> and \<open>e > 0\<close>
    and \<open>bounded_linear l\<close> and \<open>f \<midarrow>onorm\<rightarrow> l\<close>
  shows \<open>\<forall>\<^sub>F n in sequentially. onorm (\<lambda>x. f n x - l x) < e\<close>
proof-
  from  \<open>f \<midarrow>onorm\<rightarrow> l\<close>
  have \<open>(\<lambda> n. onorm (\<lambda> x. f n x - l x)) \<longlonglongrightarrow> 0\<close>
    unfolding onorm_convergence_def
    by blast
  hence \<open>\<exists> N. \<forall> n \<ge> N. dist ((\<lambda> n. onorm (\<lambda>x. f n x - l x)) n) 0 < e\<close>
    using \<open>e > 0\<close>
    by (simp add: lim_sequentially) 
  hence \<open>\<exists> N. \<forall> n \<ge> N. \<bar> onorm (\<lambda>x. f n x - l x) \<bar> < e\<close>
    by simp
  have \<open>\<exists> N. \<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) < e\<close>
  proof-
    have \<open>bounded_linear t \<Longrightarrow> onorm t \<ge> 0\<close>
      for t::\<open>'a \<Rightarrow> 'b\<close>
      using onorm_pos_le by blast 
    thus ?thesis using  \<open>\<exists> N. \<forall> n \<ge> N. \<bar> onorm (\<lambda>x. f n x - l x) \<bar> < e\<close> by fastforce
  qed
  thus ?thesis
    by (simp add: eventually_at_top_linorder)
qed

(* TODO: nonstandard *)
lemma onorm_strong:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close> and l::\<open>'a \<Rightarrow> 'b\<close>
  assumes \<open>\<forall>n. bounded_linear (f n)\<close> and \<open>bounded_linear l\<close> and \<open>f \<midarrow>onorm\<rightarrow> l\<close>
  shows \<open>f \<midarrow>strong\<rightarrow> l\<close>
proof-
  have \<open>(\<lambda>n. norm (f n x - l x)) \<longlonglongrightarrow> 0\<close>
    for x
  proof-
    have \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N. dist (norm (f n x - l x)) 0 < e\<close>
      for e::real
    proof-
      assume \<open>e > 0\<close>
      have \<open>\<exists> N. \<forall> n \<ge> N. norm (f n x - l x) < e\<close>
      proof-
        have \<open>norm (f n x - l x) \<le> onorm (\<lambda> t. f n t - l t) * norm x\<close>
          for n::nat
          using assms(1) assms(2) bounded_linear_sub onorm by blast                          
        moreover have \<open>\<exists> N. \<forall> n \<ge> N. onorm (\<lambda> t. f n t - l t) * norm x < e\<close>
        proof(cases \<open>norm x = 0\<close>)
          case True
          thus ?thesis
            by (simp add: \<open>0 < e\<close>) 
        next
          case False
          hence \<open>norm x > 0\<close>
            by simp
          have \<open>\<exists> N. \<forall> n \<ge> N. onorm (\<lambda> t. f n t - l t) < e/norm x\<close>
          proof-
            from \<open>f \<midarrow>onorm\<rightarrow> l\<close>
            have \<open>(\<lambda> n. onorm (\<lambda> t. f n t - l t)) \<longlonglongrightarrow> 0\<close>
              unfolding onorm_convergence_def
              by blast
            moreover have \<open>e / norm x > 0\<close>
              using \<open>e > 0\<close> \<open>norm x > 0\<close> by simp
            ultimately have \<open>\<exists> N. \<forall> n\<ge>N. norm ((\<lambda> n. onorm (\<lambda> t. f n t - l t)) n ) < e / norm x\<close>
              by (simp add: LIMSEQ_iff) 
            then obtain N where \<open>\<forall> n\<ge>N. norm ((\<lambda> n. onorm (\<lambda> t. f n t - l t)) n ) < e / norm x\<close>
              by blast
            hence \<open>\<forall> n\<ge>N. norm ( onorm (\<lambda> t. f n t - l t ) ) < e / norm x\<close>
              by blast
            have \<open>\<forall> n\<ge>N.  onorm (\<lambda> t. f n t - l t ) < e / norm x\<close>
            proof-
              have \<open>onorm (\<lambda> t. f n t - l t ) \<ge> 0\<close>
                for n
                by (simp add: assms(1) assms(2) bounded_linear_sub onorm_pos_le)                
              thus ?thesis using  \<open>\<forall> n\<ge>N. norm ( onorm (\<lambda> t. f n t - l t ) ) < e / norm x\<close>
                by simp
            qed
            thus ?thesis by blast
          qed
          thus ?thesis using \<open>norm x > 0\<close>
          proof -
            { fix nn :: "nat \<Rightarrow> nat"
              have ff1: "\<forall>r ra. (ra::real) * r = r * ra \<or> ra = 0"
                by auto
              have "\<forall>r ra rb. (((rb::real) = 0 \<or> rb * ra < r) \<or> \<not> ra < r / rb) \<or> \<not> 0 < rb"
                by (metis (no_types) linordered_comm_semiring_strict_class.comm_mult_strict_left_mono nonzero_mult_div_cancel_left times_divide_eq_right)
              hence "\<exists>n. \<not> n \<le> nn n \<or> onorm (\<lambda>a. f (nn n) a - l a) * norm x < e"
                using ff1 by (metis (no_types) False \<open>0 < norm x\<close> \<open>\<exists>N. \<forall>n\<ge>N. onorm (\<lambda>t. f n t - l t) < e / norm x\<close>) }
            thus ?thesis
              by (metis (no_types))
          qed  
        qed
        ultimately show ?thesis by smt
      qed
      thus ?thesis
        by auto 
    qed
    thus ?thesis
      by (simp add: LIMSEQ_I) 
  qed
  thus ?thesis unfolding strong_convergence_def by blast
qed

(* TODO: nonstandard *)
lemma uniform_strong_onorm:
  fixes f::\<open>nat \<Rightarrow> ('a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::real_normed_vector)\<close> and l::\<open>'a \<Rightarrow> 'b\<close>
  assumes \<open>\<forall>n. bounded_linear (f n)\<close> and \<open>bounded_linear l\<close>
    and \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
  shows \<open>f \<midarrow>onorm\<rightarrow> l\<close> 
proof-
  have \<open>(\<lambda>n. onorm (\<lambda>x. f n x - l x)) \<longlonglongrightarrow> 0\<close>
  proof-
    have \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N.  onorm (\<lambda>x. f n x - l x) \<le> e\<close>
      for e
    proof-
      assume \<open>e > 0\<close>
      hence \<open>\<exists> N. \<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
        using \<open>f \<midarrow>ustrong\<rightarrow> l\<close> unfolding ustrong_convergence_def
        by blast
      then obtain N where \<open>\<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
        by blast
      have \<open>bounded_linear g \<Longrightarrow> \<exists> x. norm x = 1 \<and> onorm g \<le> norm (g x) + inverse (real (Suc m))\<close>
        for x::'a and g::\<open>'a \<Rightarrow> 'b\<close> and m :: nat
      proof-
        assume \<open>bounded_linear g\<close>
        hence \<open>onorm g = Sup {norm (g x) | x. norm x = 1}\<close>
          using onorm_sphere by blast
        have \<open>\<exists> t \<in> {norm (g x) | x. norm x = 1}. onorm g \<le>  t + inverse (real (Suc m))\<close>
        proof-
          have \<open>ereal (inverse (real (Suc m))) > 0\<close>
            by simp
          moreover have \<open>\<bar>Sup {ereal (norm (g x)) | x. norm x = 1}\<bar> \<noteq> \<infinity>\<close>
          proof-
            have \<open>\<exists> M::real. \<forall> x. norm x = 1 \<longrightarrow>  (norm (g x))  \<le> M\<close>
              by (metis \<open>bounded_linear g\<close>  bounded_linear.bounded)
            then obtain M::real where \<open>\<forall> x. norm x = 1 \<longrightarrow>  (norm (g x))  \<le> M\<close>
              by blast
            hence \<open>\<forall> x. norm x = 1 \<longrightarrow> ereal (norm (g x)) \<le> M\<close>
              by simp
            hence \<open>t \<in> {ereal (norm (g x)) | x. norm x = 1} \<Longrightarrow> t \<le> M\<close>
              for t
              by blast
            hence \<open>Sup {ereal (norm (g x)) | x. norm x = 1} \<le> M\<close>
              using Sup_least by blast
            moreover have \<open>Sup { ereal (norm (g x))  | x. norm x = 1} \<ge> 0\<close>
            proof-
              have \<open>t \<in> { ereal (norm (g x))  | x. norm x = 1} \<Longrightarrow> t \<ge> 0\<close>
                for t
                by auto                
              moreover have \<open>{ ereal (norm (g x))  | x. norm x = 1} \<noteq> {}\<close>
              proof-
                have \<open>\<exists> x::'a.  norm x = 1\<close>
                  using le_numeral_extra(1) vector_choose_size by blast
                thus ?thesis by blast
              qed
              ultimately show ?thesis
                by (meson less_eq_Sup) 
            qed
            ultimately have \<open>\<bar> Sup { ereal (norm (g x))  | x. norm x = 1} \<bar> \<le> M\<close>
              by simp
            thus ?thesis by auto
          qed
          moreover have \<open>{ereal(norm (g x)) | x. norm x = 1} \<noteq> {}\<close>
            by (metis Sup_empty bot.extremum_strict calculation(2) less_ereal.simps(1) lt_ex not_infty_ereal)
          ultimately have \<open>\<exists> t \<in> {ereal(norm (g x)) | x. norm x = 1}. Sup {ereal(norm (g x)) | x. norm x = 1}
               - ereal (inverse (real (Suc m))) < t\<close>
            by (rule Sup_ereal_close)
          hence \<open>\<exists> t \<in> {(norm (g x)) | x. norm x = 1}. Sup {ereal(norm (g x)) | x. norm x = 1}
               - (inverse (real (Suc m))) < t\<close>
            by auto
          then obtain t::real where \<open>t \<in> {(norm (g x)) | x. norm x = 1}\<close> 
            and \<open>Sup {ereal(norm (g x)) | x. norm x = 1}
               - (inverse (real (Suc m))) < t\<close>
            by blast
          have \<open>onorm g = Sup {ereal(norm (g x)) | x. norm x = 1}\<close>
            using \<open>onorm g = Sup {norm (g x) | x. norm x = 1}\<close>
            by simp
          also have \<open>...
                < t + (inverse (real (Suc m)))\<close>
            apply auto
            using \<open>Sup {ereal(norm (g x)) | x. norm x = 1}
               - (inverse (real (Suc m))) < t\<close>
          proof auto
            assume \<open>Sup {ereal (norm (g x)) |x. norm x = 1} - ereal (inverse (1 + real m))
                  < ereal t\<close>
            moreover have \<open>\<bar> ereal (inverse (1 + real m)) \<bar> \<noteq> \<infinity>\<close>
              by auto
            ultimately have \<open>Sup {ereal (norm (g x)) |x. norm x = 1}
                  < ereal t + ereal (inverse (1 + real m))\<close>
              using ereal_minus_less by simp               
            hence \<open>Sup {ereal (norm (g x)) |x. norm x = 1}
                  < t + (inverse (1 + real m))\<close>
              by simp
            moreover have \<open>Sup {ereal (norm (g x)) |x. norm x = 1} = 
                    Sup {(norm (g x)) |x. norm x = 1}\<close>
            proof-
              have \<open>{ereal (norm (g x)) |x. norm x = 1} = 
                    {(norm (g x)) |x. norm x = 1}\<close>
                by simp
              hence \<open>y \<in> {ereal (norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<in> {(norm (g x)) |x. norm x = 1}\<close>
                for y
                by simp
              moreover have \<open>{ (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>
                by (metis \<open>t \<in> {norm (g x) |x. norm x = 1}\<close> empty_iff)                
              moreover have \<open>bdd_above { (norm (g x)) |x. norm x = 1}\<close>
                by (metis (mono_tags, lifting)  \<open>bounded_linear g\<close> norm_set_bdd_above_eq1) 
              ultimately have \<open>y \<in> {ereal (norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<le> Sup {(norm (g x)) |x. norm x = 1}\<close>
                for y
                by (smt cSup_upper ereal_less_eq(3) mem_Collect_eq)
              from \<open>{ereal (norm (g x)) |x. norm x = 1} = 
                    {(norm (g x)) |x. norm x = 1}\<close>
              have \<open>y \<in> {(norm (g x)) |x. norm x = 1} \<Longrightarrow>
                   y \<in> {ereal (norm (g x)) |x. norm x = 1}\<close>
                for y
                by simp
              moreover have \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>
                by (metis \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>)                
              moreover have \<open>bdd_above {ereal (norm (g x)) |x. norm x = 1}\<close>
                by (metis (no_types, lifting) bdd_above_top) 
              ultimately have \<open>y \<in> {(norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                for y
                by (simp add: Sup_upper)
              from  \<open>\<And> y. y \<in> {ereal (norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<le> Sup {(norm (g x)) |x. norm x = 1}\<close>
              have \<open>Sup {ereal (norm (g x)) |x. norm x = 1} \<le>  Sup {(norm (g x)) |x. norm x = 1}\<close>
                using \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>
                by (meson cSup_least)
              have \<open>(Sup { (norm (g x)) |x. norm x = 1}) \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close> 
              proof-
                define X::\<open>ereal set\<close> where \<open>X = {norm (g x) |x. norm x = 1}\<close>
                define z::ereal where \<open>z = Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                have \<open>X \<noteq> {}\<close>
                  unfolding X_def
                  using \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close> by blast 
                moreover have \<open>\<And>x. x \<in> X \<Longrightarrow> x \<le> z\<close>
                  unfolding X_def z_def
                  by (simp add: Sup_upper)
                ultimately have \<open>Sup X \<le> z\<close>
                  by (rule cSup_least)
                hence \<open>Sup X \<le>  Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                  unfolding z_def 
                  by auto
                hence \<open>real_of_ereal (Sup {norm (g x) |x. norm x = 1}) \<le>  Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                  unfolding X_def 
                  by auto
                thus ?thesis
                  by (smt \<open>\<And>y. y \<in> {norm (g x) |x. norm x = 1} \<Longrightarrow> ereal y \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close> \<open>\<bar>Sup {ereal (norm (g x)) |x. norm x = 1}\<bar> \<noteq> \<infinity>\<close> \<open>{norm (g x) |x. norm x = 1} \<noteq> {}\<close> cSup_least ereal_le_real_iff) 
              qed
              show ?thesis 
                using \<open>(Sup {(norm (g x)) |x. norm x = 1}) \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                  \<open>Sup {ereal (norm (g x)) |x. norm x = 1} \<le>  Sup {(norm (g x)) |x. norm x = 1}\<close>
                by auto
            qed
            ultimately show \<open>Sup {norm (g x) |x. norm x = 1} < t + inverse (1 + real m)\<close>
              by simp
          qed
          finally have \<open>(onorm g) < t + (inverse (real (Suc m)))\<close>
            by blast
          thus ?thesis
            using \<open>t \<in> {norm (g x) |x. norm x = 1}\<close> by auto             
        qed
        thus ?thesis by auto
      qed
      hence \<open>\<exists> x. norm x = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) x) + inverse (real (Suc m))\<close>
        for n and m::nat
        using \<open>\<forall>n. bounded_linear (f n)\<close>
        by (simp add: assms(2) bounded_linear_sub)
      hence \<open>n \<ge> N \<Longrightarrow>  onorm (\<lambda> x. f n x - l x) \<le> e\<close>
        for n
      proof-
        assume \<open>n \<ge> N\<close>
        hence  \<open>\<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
          using \<open>\<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
          by blast
        have  \<open>\<forall> m. \<exists> x. norm x = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) x) + inverse (real (Suc m))\<close>
          using \<open>\<And> m. \<exists> x. norm x = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) x) + inverse (real (Suc m))\<close>
          by blast
        hence  \<open>\<exists> x. \<forall> m. norm (x m) = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) (x m)) + inverse (real (Suc m))\<close>
          using choice by simp  
        then obtain x where \<open>norm (x m) = 1\<close> 
          and \<open>onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) (x m)) + inverse (real (Suc m))\<close>
        for m::nat
          by blast          
        have \<open>\<forall> m. onorm (\<lambda> x. f n x - l x) < e + inverse (real (Suc m))\<close>
          using \<open>\<And> m. norm (x m) = 1\<close>  \<open>\<And> m. onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) (x m)) + inverse (real (Suc m)) \<close>
            \<open>\<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
          by smt
        have \<open>onorm (\<lambda> x. f n x - l x) \<le> e\<close>
        proof(rule classical)
          assume \<open>\<not>(onorm (\<lambda> x. f n x - l x) \<le> e)\<close>
          hence \<open>e < onorm (\<lambda> x. f n x - l x)\<close>
            by simp
          hence \<open>0 < onorm (\<lambda> x. f n x - l x) - e\<close>
            by simp
          hence \<open>\<exists> n0. inverse (real (Suc n0)) < onorm (\<lambda> x. f n x - l x) - e\<close>
            by (rule Archimedean_Field.reals_Archimedean)
          then obtain n0 where \<open>inverse (real (Suc n0)) < onorm (\<lambda> x. f n x - l x) - e\<close>
            by blast
          have \<open>\<forall> m. onorm (\<lambda> x. f n x - l x) - e < inverse (real (Suc m))\<close>
            by (smt \<open>\<forall>m. onorm (\<lambda>x. f n x - l x) < e + inverse (real (Suc m))\<close>)
          hence \<open>\<forall> m. inverse (real (Suc n0)) < inverse (real (Suc m))\<close>
            using  \<open>inverse (real (Suc n0)) < onorm (\<lambda> x. f n x - l x) - e\<close> by smt
          hence \<open>inverse (real (Suc n0)) < inverse (real (Suc n0))\<close>
            by blast
          thus ?thesis by blast
        qed
        thus ?thesis by blast 
      qed
      thus ?thesis by blast
    qed
    hence \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N. norm ( onorm (\<lambda>x. f n x - l x) ) \<le> e\<close>
      for e
    proof-
      assume \<open>e > 0\<close>
      hence \<open>\<exists> N. \<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) \<le> e\<close>
        using  \<open>\<And> e. e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N.  onorm (\<lambda>x. f n x - l x) \<le> e\<close>
        by blast
      then obtain N where \<open>\<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) \<le> e\<close>
        by blast
      have  \<open>\<forall> n \<ge> N. norm (onorm (\<lambda>x. f n x - l x)) \<le> e\<close>
      proof-
        have \<open>n \<ge> N \<Longrightarrow> norm (onorm (\<lambda>x. f n x - l x)) \<le> e\<close>
          for n
        proof-
          assume \<open>n \<ge> N\<close>
          hence \<open>onorm (\<lambda>x. f n x - l x) \<le> e\<close>
            using \<open>\<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) \<le> e\<close> by blast
          moreover have \<open>onorm (\<lambda>x. f n x - l x) \<ge> 0\<close>
            by (simp add: assms(1) assms(2) bounded_linear_sub onorm_pos_le)            
          ultimately show ?thesis by simp
        qed
        thus ?thesis by blast
      qed
      thus ?thesis by blast 
    qed
    have \<open>0 < e \<Longrightarrow>
      \<exists>N. \<forall>n\<ge>N. norm (onorm (\<lambda>x. f n x - l x)) < e\<close>
      for e::real
    proof-
      assume \<open>0 < e\<close>
      hence \<open>e/2 < e\<close>
        by simp
      have \<open>0 < e/2\<close>
        using \<open>0 < e\<close> by simp
      hence \<open>\<exists>N. \<forall>n\<ge>N. norm (onorm (\<lambda>x. f n x - l x)) \<le> e/2\<close>
        using \<open>\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. norm (onorm (\<lambda>x. f n x - l x)) \<le> e\<close> by blast
      thus ?thesis using \<open>e/2 < e\<close> by fastforce
    qed
    thus ?thesis by (simp add: LIMSEQ_I) 
  qed
  thus ?thesis unfolding onorm_convergence_def by blast
qed

(* TODO: nonstandard *)
lemma PREuCauchy_ustrong:
  fixes f :: \<open>nat \<Rightarrow> ('a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::banach)\<close>
  assumes \<open>uCauchy f\<close>
  shows \<open>\<exists> l::'a\<Rightarrow>'b. f \<midarrow>ustrong\<rightarrow> l\<close>
proof-
  have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
    using \<open>uCauchy f\<close> unfolding uCauchy_def by blast
  hence \<open>norm x = 1 \<Longrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (f m x - f n x) < e)\<close>
    for x
    by blast
  hence \<open>norm x = 1 \<Longrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m x) (f n x) < e)\<close>
    for x
    by (simp add: dist_norm)    
  hence \<open>norm x = 1 \<Longrightarrow> Cauchy (\<lambda> n. f n x)\<close>
    for x
    using Cauchy_def by blast
  hence \<open>norm x = 1 \<Longrightarrow> convergent (\<lambda> n. f n x)\<close>
    for x
    by (simp add: Cauchy_convergent_iff)
  hence \<open>norm x = 1 \<Longrightarrow> \<exists> l. (\<lambda> n. f n x) \<longlonglongrightarrow> l\<close>
    for x
    by (simp add: convergentD)
  hence \<open>\<forall> x. \<exists> l. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l\<close>
    by blast
  hence \<open>\<exists> l. \<forall> x. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
    by metis
  then obtain l where \<open>\<forall> x. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close> by blast
  have \<open>e > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. \<forall>x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
    for e::real
  proof-
    assume \<open>e > 0\<close>
    hence \<open>e/2 > 0\<close>
      by simp
    hence \<open>\<forall> x. norm x = 1 \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. dist (f n x) (l x) < e/2)\<close>
      using  \<open>\<forall> x. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
      by (meson LIMSEQ_iff_nz)

    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> dist (f m x)  (f n x) < e/2\<close>
      using  \<open>e/2 > 0\<close> \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
      by (metis dist_norm)
    then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> dist (f m x) (f n x) < e/2\<close>
      by blast
    have \<open>m \<ge> M \<Longrightarrow> \<forall>x. norm x = 1 \<longrightarrow> dist (f m x) (l x) < e\<close>
      for m
    proof-
      assume \<open>m \<ge> M\<close>
      have \<open>norm x = 1 \<Longrightarrow> dist (f m x) (l x) < e\<close>
        for x
      proof-
        assume \<open>norm x = 1\<close>
        have \<open>dist (f m x) (l x) \<le> dist (f m x) (f n x) + dist (l x) (f n x)\<close>
          for n
          by (simp add: dist_triangle2)
        moreover have \<open>n \<ge> M \<Longrightarrow> dist (f m x) (f n x) < e/2\<close>
          for n
          using \<open>M \<le> m\<close> \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> dist (f m x) (f n x) < e / 2\<close> \<open>norm x = 1\<close> by blast
        moreover have \<open>\<exists> N. \<forall> n \<ge> N. dist (l x) (f n x) < e/2\<close>
        proof-
          have \<open>\<exists> N. \<forall> n \<ge> N. dist (f n x) (l x) < e/2\<close>
            using \<open>e/2 > 0\<close> \<open>\<forall>x. norm x = 1 \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. dist (f n x) (l x) < e / 2)\<close> \<open>norm x = 1\<close> by auto 
          thus ?thesis
            by (simp add: dist_commute) 
        qed
        ultimately show ?thesis
          by (meson dist_triangle_half_l le_add1 le_add2) 
      qed
      thus ?thesis by blast
    qed
    thus ?thesis
      by (metis dist_norm) 
  qed
  thus ?thesis unfolding ustrong_convergence_def by blast
qed

(* TODO: nonstandard *)
lemma uCauchy_ustrong:
  fixes f :: \<open>nat \<Rightarrow> ('a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::banach)\<close>
  assumes  \<open>uCauchy f\<close> and \<open>\<And> n. bounded_linear (f n)\<close>
  shows \<open>\<exists> l::'a\<Rightarrow>'b. bounded_linear l \<and> f \<midarrow>ustrong\<rightarrow> l\<close>
proof-
  have \<open>\<exists> s::'a\<Rightarrow>'b. f \<midarrow>ustrong\<rightarrow> s\<close>
    by (simp add: PREuCauchy_ustrong assms(1))
  then obtain s where \<open>f \<midarrow>ustrong\<rightarrow> s\<close> by blast
  define l::\<open>'a \<Rightarrow> 'b\<close> where \<open>l x = (norm x) *\<^sub>R s ((inverse (norm x)) *\<^sub>R x)\<close>
    for x::'a
  have \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
    using l_def \<open>f \<midarrow>ustrong\<rightarrow> s\<close> 
    unfolding l_def
    unfolding ustrong_convergence_def
    by simp
  moreover have \<open>bounded_linear l\<close>
  proof-
    have \<open>(\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
      for x
    proof(cases \<open> x = 0\<close>)
      case True
      have \<open>(\<lambda> n. f n x) \<longlonglongrightarrow> 0\<close>
      proof-
        have \<open>f n x = (0::'b)\<close>
          for n
          using \<open>\<And> n. bounded_linear (f n)\<close>
          by (simp add: True linear_simps(3))
        moreover  have \<open>(\<lambda> n. (0::'b)) \<longlonglongrightarrow> 0\<close>
          by simp            
        ultimately show ?thesis by simp
      qed
      moreover have \<open>l x = 0\<close>
      proof-
        have \<open>norm x = 0\<close>
          using \<open>x = 0\<close> by simp
        thus ?thesis using l_def by simp
      qed
      ultimately show ?thesis by simp 
    next
      case False
      hence  \<open>norm x \<noteq> 0\<close> by simp
      thus ?thesis
      proof-
        have  \<open>(\<lambda> n. f n (x  /\<^sub>R norm x)) \<longlonglongrightarrow> s (x /\<^sub>R norm x)\<close>
        proof-
          have \<open>norm (x  /\<^sub>R norm x) = 1\<close>
            by (simp add: False)
          have \<open> \<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x. norm x = 1 \<longrightarrow> norm (f n x - s x) < e\<close>
            using \<open>f \<midarrow>ustrong\<rightarrow> s\<close>
            unfolding ustrong_convergence_def by blast
          hence \<open> \<forall>e>0. \<exists>N. \<forall>n\<ge>N. norm (f n (x  /\<^sub>R norm x) - s (x  /\<^sub>R norm x)) < e\<close>
            using  \<open>norm (x  /\<^sub>R norm x) = 1\<close> by fastforce
          thus ?thesis
            by (simp add: LIMSEQ_iff) 
        qed
        hence  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow>  (norm x) *\<^sub>R  s (x /\<^sub>R norm x)\<close>
          using bounded_linear.tendsto bounded_linear_scaleR_right by blast
        hence  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
          using l_def
          by simp
        have  \<open>(\<lambda> n.  f n x) \<longlonglongrightarrow> l x\<close>
        proof-
          have \<open>(norm x) *\<^sub>R f n (x /\<^sub>R norm x) = f n x\<close>
            for n
            using \<open>norm x \<noteq> 0\<close> \<open>\<And> n. bounded_linear (f n)\<close>
            unfolding bounded_linear_def linear_def
            by (simp add: assms(2) linear_simps(5)) 
          thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close> by simp
        qed
        thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
          by auto
      qed
    qed
    have \<open>linear l\<close>
    proof
      show "l (b1 + b2) = l b1 + l b2"
        for b1 :: 'a
          and b2 :: 'a
      proof-
        have \<open>(\<lambda> n. f n (b1 + b2)) \<longlonglongrightarrow> l (b1 + b2)\<close>
          using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
          by blast
        moreover have \<open>(\<lambda> n. f n (b1 + b2)) \<longlonglongrightarrow> l b1 + l b2\<close>
        proof-
          have \<open>(\<lambda> n. f n b1) \<longlonglongrightarrow> l b1\<close>
            using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
            by blast
          moreover have \<open>(\<lambda> n. f n b2) \<longlonglongrightarrow> l b2\<close>
            using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
            by blast
          ultimately have \<open>(\<lambda> n. f n b1 + f n b2) \<longlonglongrightarrow> l b1 + l b2\<close>
            by (simp add: tendsto_add) 
          moreover have \<open>(\<lambda> n. f n (b1 + b2)) = (\<lambda> n. f n b1 + f n b2)\<close>
          proof-
            have \<open>f n (b1 + b2) = f n b1 + f n b2\<close>
              for n
              using \<open>\<And> n. bounded_linear (f n)\<close>
              unfolding bounded_linear_def
              by (simp add: linear_add)
            thus ?thesis by blast
          qed
          ultimately show ?thesis by simp 
        qed
        ultimately show ?thesis
          using LIMSEQ_unique by blast            
      qed
      show "l (r *\<^sub>R b) = r *\<^sub>R l b"
        for r :: real
          and b :: 'a
      proof-
        have \<open>(\<lambda> n. f n (r *\<^sub>R b)) \<longlonglongrightarrow> l (r *\<^sub>R b)\<close>
          using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
          by blast
        moreover have \<open>(\<lambda> n. f n (r *\<^sub>R b)) \<longlonglongrightarrow>  r *\<^sub>R (l b)\<close>
        proof-
          have \<open>(\<lambda> n. f n b) \<longlonglongrightarrow> l b\<close>
            using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
            by blast
          hence \<open>(\<lambda> n. r *\<^sub>R (f n b)) \<longlonglongrightarrow> r *\<^sub>R (l b)\<close>
            using bounded_linear.tendsto bounded_linear_scaleR_right by blast
          moreover have \<open>(\<lambda> n. (f n (r *\<^sub>R b))) = (\<lambda> n. r *\<^sub>R (f n b))\<close>
          proof-
            have \<open>f n (r *\<^sub>R b) = r *\<^sub>R (f n b)\<close>
              for n
              using \<open>\<And> n. bounded_linear (f n)\<close>
              unfolding bounded_linear_def
              by (simp add: linear_scale)
            thus ?thesis by blast
          qed
          ultimately show ?thesis by simp 
        qed
        ultimately show ?thesis
          using LIMSEQ_unique by blast            
      qed
    qed
    moreover have \<open>bounded_linear_axioms l\<close>
    proof-
      have \<open>\<exists>K. \<forall>x. norm (l x) \<le> norm x * K\<close>
      proof(rule classical)
        assume \<open>\<not> (\<exists>K. \<forall>x. norm (l x) \<le> norm x * K)\<close>
        hence \<open>\<forall> K. \<exists> x. norm (l x) > norm x * K\<close>
          by smt
        hence \<open>\<forall> K. \<exists> x \<noteq> 0. norm (l x) > norm x * K\<close>
          using calculation linear_0 by force
        have \<open>\<forall> K. \<exists> x. norm x = 1 \<and> K < norm (l x)\<close>
        proof-
          have \<open>\<exists> x. norm x = 1 \<and> K < norm (l x)\<close>
            for K
          proof-
            have \<open>\<exists> x \<noteq> 0. norm (l x) > norm x * K\<close>
              using  \<open>\<forall> K. \<exists> x \<noteq> 0. norm (l x) > norm x * K\<close> by blast
            then obtain x where \<open>x \<noteq> 0\<close> and \<open>norm (l x) > norm x * K\<close>
              by blast
            have \<open>norm x > 0\<close> using \<open>x \<noteq> 0\<close> by simp
            hence  \<open>inverse (norm x) * norm (l x) > inverse (norm x) * (norm x) * K\<close>
              using  \<open>norm (l x) > norm x * K\<close>
              by (smt linordered_field_class.sign_simps(23) mult_left_le_imp_le positive_imp_inverse_positive) 
            moreover have \<open>(inverse (norm x)) * (norm x) = 1\<close>
              using \<open>norm x > 0\<close> by simp
            ultimately have \<open>(inverse (norm x)) * norm (l x) >  K\<close>
              by simp
            moreover have \<open>(inverse (norm x)) * norm (l x) = norm ((inverse (norm x)) *\<^sub>R (l x))\<close>
            proof-
              have \<open>(inverse (norm x)) > 0\<close>
                using \<open>norm x > 0\<close> 
                by simp
              thus ?thesis using norm_scaleR
                by simp 
            qed
            hence \<open> norm ((inverse (norm x)) *\<^sub>R (l x)) >  K\<close>
              using calculation by linarith
            hence \<open> norm (l ((inverse (norm x)) *\<^sub>R  x)) >  K\<close>
            proof-
              have \<open>(inverse (norm x)) *\<^sub>R (l x) = l ((inverse (norm x)) *\<^sub>R  x)\<close>
                by (simp add: \<open>linear l\<close> linear_scale)
              thus ?thesis
                using \<open>K < norm (l x /\<^sub>R norm x)\<close> by simp                 
            qed
            have \<open>norm ( (inverse (norm x)) *\<^sub>R  x ) = 1\<close>
              using \<open>norm x > 0\<close> by simp
            show ?thesis
              using \<open>K < norm (l (x /\<^sub>R norm x))\<close> \<open>norm (x /\<^sub>R norm x) = 1\<close> by blast 
          qed
          thus ?thesis by blast
        qed
        have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm (f m x - f n x) < e\<close>
          using \<open>uCauchy f\<close>
          unfolding uCauchy_def
          by blast
        hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm (f m x - f n x) < 1\<close>
          by auto
        then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm (f m x - f n x) < 1\<close>
          by blast
        hence \<open>\<forall>m\<ge>M. \<forall>x. 
            norm x = 1 \<longrightarrow> norm (f m x - f M x) < 1\<close>
          by blast
        have \<open>norm (f m x) \<le> norm (f M x) + norm (f m x - f M x)\<close>
          for m and x
          by (simp add: norm_triangle_sub) 
        hence \<open>norm (f m x) \<le> onorm (f M) * norm x + norm (f m x - f M x)\<close>
          for m and x
          using onorm
          by (smt assms(2)) 
        hence \<open>norm x = 1 \<Longrightarrow> norm (f m x) \<le> onorm (f M) + norm (f m x - f M x)\<close>
          for m and x
          by (metis mult_cancel_left2)
        hence \<open>m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm (f m x) < onorm (f M) + 1\<close>
          for m and x
          using  \<open>\<forall>m\<ge>M. \<forall>x. 
            norm x = 1 \<longrightarrow> norm (f m x - f M x) < 1\<close> 
          by smt
        have \<open>norm x = 1 \<Longrightarrow> (\<lambda> m. f m x) \<longlonglongrightarrow> l x\<close>
          for x
          by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> l x\<close>)
        hence \<open>norm x = 1 \<Longrightarrow> (\<lambda> m. norm (f m x)) \<longlonglongrightarrow> norm (l x)\<close>
          for x
          by (simp add: tendsto_norm)
        hence \<open>norm x = 1 \<Longrightarrow> norm (l x) \<le> onorm (f M) + 1\<close>
          for x
        proof-
          assume \<open>norm x = 1\<close>
          hence \<open>(\<lambda> m. norm (f m x)) \<longlonglongrightarrow> norm (l x)\<close>
            using  \<open>\<And> x. norm x = 1 \<Longrightarrow> (\<lambda> m. norm (f m x)) \<longlonglongrightarrow> norm (l x)\<close>
            by blast
          moreover have \<open>\<forall>  m \<ge> M. norm (f m x) \<le> onorm (f M) + 1\<close>
            using  \<open>\<And> m. \<And> x.  m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm (f m x) < onorm (f M) + 1\<close>
              \<open>norm x = 1\<close> by smt
          ultimately show ?thesis 
            by (rule Topological_Spaces.Lim_bounded)
        qed
        moreover have  \<open>\<exists> x. norm x = 1 \<and> onorm (f M) + 1 < norm (l x)\<close>
          by (simp add: \<open>\<forall>K. \<exists>x. norm x = 1 \<and> K < norm (l x)\<close>)
        ultimately show ?thesis
          by fastforce 
      qed
      thus ?thesis unfolding bounded_linear_axioms_def by blast
    qed
    ultimately show ?thesis unfolding bounded_linear_def by blast
  qed
  ultimately show ?thesis by blast
qed


(* TODO: nonstandard *)
lemma completeness_real_bounded:
  fixes f :: \<open>nat \<Rightarrow> ('a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::banach)\<close>
  assumes \<open>\<forall>n. bounded_linear (f n)\<close>
    and \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
  shows \<open>\<exists> l. bounded_linear l \<and> (\<lambda>n. onorm (\<lambda>x. f n x - l x)) \<longlonglongrightarrow> 0\<close>
proof-
  have \<open>uCauchy f\<close>
  proof-
    have  \<open>e > 0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall> x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
      for e::real
    proof-
      assume \<open>e > 0\<close>
      hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
        using \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
        by blast
      then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
        by blast
      have \<open>m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> \<forall> x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
        for m n::nat
      proof-
        assume \<open>m \<ge> M\<close>
        moreover assume \<open>n \<ge> M\<close>
        ultimately have \<open>onorm (\<lambda>x. f m x - f n x) < e\<close>
          by (simp add: \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>)
        moreover have \<open>norm x = 1 \<Longrightarrow>  norm (f m x - f n x) \<le> onorm (\<lambda>x. f m x - f n x)\<close>
          for x
        proof-
          assume \<open>norm x = 1\<close>
          moreover have \<open>norm (f m x - f n x) \<le> onorm (\<lambda>x. f m x - f n x) * norm x\<close>
            using assms(1) bounded_linear_sub onorm by blast          
          ultimately show ?thesis by simp
        qed
        ultimately show ?thesis by smt
      qed
      thus ?thesis by blast
    qed
    thus ?thesis
      by (simp add: uCauchy_def) 
  qed
  hence \<open>\<exists> l. bounded_linear l \<and> f \<midarrow>ustrong\<rightarrow> l\<close>
    using \<open>\<forall>n. bounded_linear (f n)\<close>
      uCauchy_ustrong
    by auto
  then obtain l where  \<open>bounded_linear l\<close> and \<open>f \<midarrow>ustrong\<rightarrow> l\<close> 
    by blast
  have \<open>(\<lambda>n. onorm (\<lambda>x. f n x - l x)) \<longlonglongrightarrow> 0\<close>
    using  \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
      \<open>bounded_linear l\<close> assms(1) onorm_convergence_def uniform_strong_onorm by blast
  thus ?thesis
    using \<open>bounded_linear l\<close> by auto  
qed



end
