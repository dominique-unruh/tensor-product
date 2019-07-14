(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Nonstandard analogs of Convergence_Operators.

*)

theory NSA_Convergence_Operators
  imports 
    Convergence_Operators
    "HOL-Nonstandard_Analysis.Nonstandard_Analysis"

begin

section \<open>nsustrong_convergence\<close>

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
    hence \<open>\<forall> NN. \<forall> xx. (*f2* X) NN xx * (*f2* Y) NN xx = (*f2* (\<lambda>n t. X n t * Y n t)) NN xx\<close>
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

lemma nsustrong_convergence_norm: \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S  a \<Longrightarrow>
 (\<lambda>n. (\<lambda> t. norm (X n t))) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. norm (a t))\<close>
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
  show "(\<lambda>n. f (Suc n)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l"
  proof (rule nsustrong_convergence_I)
    fix N and x::\<open>'a star\<close>
    assume "N \<in> HNatInfinite" and \<open>hnorm x = 1\<close>
    hence "(*f2* f) (N + 1) x \<approx> (*f* l) x"
      by (simp add: HNatInfinite_add nsustrong_convergence_D *)
    moreover have \<open>(*f2* (\<lambda> n. f (Suc n))) N x = (*f2* f) (N + 1) x\<close>
    proof-
      have \<open>\<forall> NN. \<forall> xx. (\<lambda> n. f (Suc n)) NN xx =  f (NN + 1) xx\<close>
        by simp
      hence \<open>\<forall> NN. \<forall> xx. (*f2* (\<lambda> n. f (Suc n))) NN xx =  (*f2* f) (NN + 1) xx\<close>
        by transfer
      thus ?thesis
        by simp 
    qed 
    ultimately show \<open>(*f2* (\<lambda>k. f (Suc k))) N x \<approx> (*f* l) x\<close> by simp
  qed
next
  assume *: "(\<lambda>n. f(Suc n)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l"
  show  "f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l"
  proof (rule nsustrong_convergence_I)
    fix N and x::\<open>'a star\<close>
    assume "N \<in> HNatInfinite" and \<open>hnorm x = 1\<close>
    hence "(*f2* (\<lambda>n. f (Suc n))) (N - 1) x \<approx> (*f* l) x"
      using * HNatInfinite_diff nsustrong_convergence_D by fastforce
    moreover have \<open>(*f2* (\<lambda>n. (f (Suc n) ))) (N - 1) x = (*f2* f) N x\<close>
    proof-
      have \<open>\<forall> NN. \<forall> xx.  NN \<ge> 1 \<longrightarrow> (\<lambda>n. (f (Suc n) )) (NN - 1) xx =  f NN xx\<close>
        by simp
      hence \<open>\<forall> NN. \<forall> xx.  NN \<ge> 1 \<longrightarrow> (*f2* (\<lambda>n. (f (Suc n)))) (NN - 1) xx =  (*f2* f) NN xx\<close>
        by transfer
      thus ?thesis
        using \<open>N \<in> HNatInfinite\<close> one_le_HNatInfinite by auto 
    qed
    ultimately show "(*f2* f) N x \<approx> (*f* l) x"
      by simp
  qed
qed

lemma ustrong_convergence_nsustrong_convergence:
  fixes l::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
  assumes \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
  shows \<open>f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l\<close>
proof (rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  have \<open>(*f2* f) N x - (*f* l) x \<in> Infinitesimal\<close>
  proof (rule InfinitesimalI2)
    fix r :: real
    assume \<open>0 < r\<close>
    have \<open>\<exists> no. \<forall> n \<ge> no. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < r\<close>
      using \<open>f \<midarrow>ustrong\<rightarrow> l\<close>  \<open>0 < r\<close> ustrong_convergence_def by auto 
    then obtain no where \<open>\<forall> n \<ge> no. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> no. \<forall> x. norm x = 1 \<longrightarrow> norm ( f n x - l x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> hypnat_of_nat no. \<forall> x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) n x - (*f* l) x) < hypreal_of_real r\<close>
      by transfer
    thus \<open>hnorm ((*f2* f) N x- (*f* l) x) < hypreal_of_real r\<close>
      using star_of_le_HNatInfinite \<open>N \<in> HNatInfinite\<close>
      by (simp add: \<open>hnorm x = 1\<close>)
  qed
  thus \<open>(*f2* f) N x \<approx>  (*f* l) x\<close>
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
proof (rule ustrong_convergence_I)
  fix r :: real
  assume \<open>r > (0::real)\<close>
  from \<open>f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l\<close>
  have \<open>\<forall>n\<in>HNatInfinite. 
  \<forall>x. hnorm x = 1 \<longrightarrow> (*f2* f) n x \<approx> (*f* l) x\<close>
    unfolding nsustrong_convergence_def by blast
  hence \<open>\<forall>n\<in>HNatInfinite.
       \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
    by (simp add: InfinitesimalD2 Infinitesimal_approx_minus \<open>0 < r\<close>)
  have \<open>\<exists> no. \<forall>n \<ge> no.
       \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
  proof-
    have \<open>n \<ge> whn \<Longrightarrow>
       \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
      for n
      using HNatInfinite_upward_closed HNatInfinite_whn \<open>\<forall>n\<in>HNatInfinite. \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ((*f2* f) n x - (*f* l) x) < hypreal_of_real r\<close> by blast     
    thus ?thesis by blast
  qed
  thus \<open>\<exists> no. \<forall>n \<ge> no. \<forall>x. norm x = 1 \<longrightarrow> norm ( f n x - l x ) < r\<close>
    by transfer
qed

proposition ustrong_convergence_ustrong_convergence_iff:
  \<open>f \<midarrow>ustrong\<rightarrow> L \<longleftrightarrow> f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S L\<close>
  using nsustrong_convergence_ustrong_convergence ustrong_convergence_nsustrong_convergence by blast

subsection \<open>nsuCauchy\<close>

definition uNSCauchy::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)) \<Rightarrow> bool\<close>
  where \<open>uNSCauchy f \<longleftrightarrow> ( \<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. 
    \<forall> x. hnorm x = 1 \<longrightarrow> (*f2* f) N x \<approx> (*f2* f) M x )\<close> 

lemma Cauchy_uNSCauchy:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close>
  assumes \<open>uCauchy f\<close>
  shows \<open>uNSCauchy f\<close>
proof-
  from \<open>uCauchy f\<close>
  have \<open>\<forall>e>0. \<exists>K. \<forall>m\<ge>K. \<forall>n\<ge>K.
     \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
    unfolding uCauchy_def
    by blast
  hence \<open>N\<in>HNatInfinite \<Longrightarrow> M\<in>HNatInfinite \<Longrightarrow> hnorm x = 1 \<Longrightarrow> (*f2* f) N x \<approx> (*f2* f) M x\<close>
    for N M x
  proof-
    assume \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close> and \<open>hnorm x = 1\<close>
    have \<open>e \<in> \<real> \<Longrightarrow>  e > 0 \<Longrightarrow> hnorm ((*f2* f) N x - (*f2* f) M x) < e\<close>
      for e
    proof-
      assume \<open>e \<in> \<real>\<close> and \<open>e > 0\<close>
      have \<open>\<exists> d. e = hypreal_of_real d\<close>
        using  \<open>e \<in> \<real>\<close>
        by (simp add: SReal_iff)
      then obtain d where \<open>e = hypreal_of_real d\<close>
        by blast
      have \<open>d > 0\<close> using \<open>e = hypreal_of_real d\<close> \<open>e > 0\<close>
        by simp
      have \<open>\<exists>K. \<forall>m\<ge>K. \<forall>n\<ge>K. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < d\<close>
        by (simp add: \<open>0 < d\<close> \<open>\<forall>e>0. \<exists>K. \<forall>m\<ge>K. \<forall>n\<ge>K. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>)
      then obtain K::nat where \<open>\<forall>m\<ge>K. \<forall>n\<ge>K. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < d\<close>
        by blast
      hence \<open>\<forall>m \<ge> hypnat_of_nat K. \<forall>n \<ge> hypnat_of_nat K. 
          \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ((*f2* f) m x - (*f2* f) n x) < hypreal_of_real d\<close>
        by transfer
      hence \<open>\<forall>m \<ge> hypnat_of_nat K. \<forall>n \<ge> hypnat_of_nat K. 
          \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ((*f2* f) m x - (*f2* f) n x) < e\<close>
        using  \<open>e = hypreal_of_real d\<close> by blast
      hence \<open>\<forall>x. hnorm x = 1 \<longrightarrow> hnorm ((*f2* f) N x - (*f2* f) M x) < e\<close>
        using \<open>N\<in>HNatInfinite\<close> \<open>M\<in>HNatInfinite\<close>
        by (simp add: star_of_le_HNatInfinite) 
      thus ?thesis using \<open>hnorm x = 1\<close> by blast
    qed
    thus ?thesis
      using InfinitesimalI bex_Infinitesimal_iff by auto 
  qed
  thus ?thesis
    by (simp add: uNSCauchy_def) 
qed

lemma uNSCauchy_Cauchy:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close>
  assumes \<open>uNSCauchy f\<close>
  shows \<open>uCauchy f\<close>
proof-
  have \<open>e>0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
    for e
  proof-
    assume \<open>e>0\<close>
    have \<open>\<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. 
      \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) N x - (*f2* f) M x ) \<in> Infinitesimal\<close>
      using Infinitesimal_approx_minus Infinitesimal_hnorm_iff assms uNSCauchy_def by blast
    hence \<open>\<forall>e\<in>\<real>. e > 0 \<longrightarrow> ( \<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. 
      \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) N x - (*f2* f) M x ) < e )\<close>
      by (simp add: Infinitesimal_less_SReal2)
    hence \<open>\<forall>e\<in>\<real>. e > 0 \<longrightarrow> ( \<forall>N \<ge> whn. \<forall> M \<ge> whn. 
      \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) N x - (*f2* f) M x ) < e )\<close>
      using HNatInfinite_upward_closed HNatInfinite_whn by blast
    hence \<open>\<forall>e\<in>\<real>. e > 0 \<longrightarrow> ( \<exists> K. \<forall>N \<ge> K. \<forall> M \<ge> K. 
      \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) N x - (*f2* f) M x ) < e )\<close>
      by blast
    hence \<open>\<exists> K. \<forall>N \<ge> K. \<forall> M \<ge> K. 
      \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) N x - (*f2* f) M x ) < hypreal_of_real e\<close>
      by (simp add: \<open>0 < e\<close>)
    thus \<open>\<exists> K. \<forall>N \<ge> K. \<forall> M \<ge> K. 
      \<forall>x. norm x = 1 \<longrightarrow> norm ( f N x - f M x ) < e\<close>
      by transfer
  qed
  thus ?thesis unfolding uCauchy_def by blast
qed

proposition Cauchy_uNSCauchy_iff:
  \<open>uCauchy f \<longleftrightarrow> uNSCauchy f\<close>
  using Cauchy_uNSCauchy uNSCauchy_Cauchy by auto


end