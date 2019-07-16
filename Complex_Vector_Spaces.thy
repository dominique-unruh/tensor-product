(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee
*)


theory Complex_Vector_Spaces
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL-Analysis.Elementary_Topology"
    Ordered_Complex 
    "HOL-Analysis.Operator_Norm"
    Unobtrusive_NSA
begin

bundle notation_norm begin
notation norm ("\<parallel>_\<parallel>")
end

subsection \<open>Complex vector spaces\<close>

class scaleC = scaleR +
  fixes scaleC :: "complex \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "*\<^sub>C" 75)
  assumes scaleR_scaleC: "scaleR r = scaleC (complex_of_real r)"
begin

abbreviation divideC :: "'a \<Rightarrow> complex \<Rightarrow> 'a"  (infixl "'/\<^sub>C" 70)
  where "x /\<^sub>C c \<equiv> scaleC (inverse c) x"

lemma scaleC_real: assumes "r\<in>\<real>" shows "r *\<^sub>C x = Re r *\<^sub>R x"
  unfolding scaleR_scaleC using assms by simp

end

class complex_vector = scaleC + ab_group_add +
  assumes scaleC_add_right: "a *\<^sub>C (x + y) = (a *\<^sub>C x) + (a *\<^sub>C y)"
    and scaleC_add_left: "(a + b) *\<^sub>C x = (a *\<^sub>C x) + (b *\<^sub>C x)"
    and scaleC_scaleC[simp]: "a *\<^sub>C (b *\<^sub>C x) =  (a * b) *\<^sub>C x"
    and scaleC_one[simp]: "1 *\<^sub>C x = x"

interpretation complex_vector: vector_space "scaleC :: complex \<Rightarrow> 'a \<Rightarrow> 'a::complex_vector"
  apply unfold_locales
     apply (rule scaleC_add_right)
    apply (rule scaleC_add_left)
   apply (rule scaleC_scaleC)
  by (rule scaleC_one)

subclass (in complex_vector) real_vector
  by (standard, simp_all add: scaleR_scaleC scaleC_add_right scaleC_add_left)

text \<open>Recover original theorem names\<close>

lemmas scaleC_left_commute = complex_vector.scale_left_commute
lemmas scaleC_zero_left = complex_vector.scale_zero_left
lemmas scaleC_minus_left = complex_vector.scale_minus_left
lemmas scaleC_diff_left = complex_vector.scale_left_diff_distrib
lemmas scaleC_sum_left = complex_vector.scale_sum_left
lemmas scaleC_zero_right = complex_vector.scale_zero_right
lemmas scaleC_minus_right = complex_vector.scale_minus_right
lemmas scaleC_diff_right = complex_vector.scale_right_diff_distrib
lemmas scaleC_sum_right = complex_vector.scale_sum_right
lemmas scaleC_eq_0_iff = complex_vector.scale_eq_0_iff
lemmas scaleC_left_imp_eq = complex_vector.scale_left_imp_eq
lemmas scaleC_right_imp_eq = complex_vector.scale_right_imp_eq
lemmas scaleC_cancel_left = complex_vector.scale_cancel_left
lemmas scaleC_cancel_right = complex_vector.scale_cancel_right

lemma scaleC_minus1_left [simp]: "scaleC (-1) x = - x"
  for x :: "'a::complex_vector"
  using scaleC_minus_left [of 1 x] by simp

lemma scaleC_2:
  fixes x :: "'a::complex_vector"
  shows "scaleC 2 x = x + x"
  unfolding one_add_one [symmetric] scaleC_add_left by simp

lemma scaleC_half_double [simp]:
  fixes a :: "'a::complex_vector"
  shows "(1 / 2) *\<^sub>C (a + a) = a"
proof -
  have "\<And>r. r *\<^sub>C (a + a) = (r * 2) *\<^sub>C a"
    by (metis scaleC_2 scaleC_scaleC)
  thus ?thesis
    by simp
qed

class complex_algebra = complex_vector + ring +
  assumes mult_scaleC_left [simp]: "scaleC a x * y = scaleC a (x * y)"
    and mult_scaleC_right [simp]: "x * scaleC a y = scaleC a (x * y)"

subclass (in complex_algebra) real_algebra
  by (standard, simp_all add: scaleR_scaleC)

class complex_algebra_1 = complex_algebra + ring_1

subclass (in complex_algebra_1) real_algebra_1 ..

class complex_div_algebra = complex_algebra_1 + division_ring

subclass (in complex_div_algebra) real_div_algebra ..

class complex_field = complex_div_algebra + field

subclass (in complex_field) real_field ..

instantiation complex :: scaleC
begin
definition complex_scaleC_def [simp]: "scaleC = (*)"
instance 
  apply intro_classes
  apply (rule ext)
  by (simp add: scaleR_conv_of_real)
end

instantiation complex :: complex_field
begin
instance
  apply intro_classes
  by (simp_all add: algebra_simps scaleR_scaleC)
end

interpretation scaleC_left: additive "(\<lambda>a. scaleC a x :: 'a::complex_vector)"
  by standard (rule scaleC_add_left)

interpretation scaleC_right: additive "(\<lambda>x. scaleC a x :: 'a::complex_vector)"
  by standard (rule scaleC_add_right)

lemma nonzero_inverse_scaleC_distrib:
  "a \<noteq> 0 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> inverse (scaleC a x) = scaleC (inverse a) (inverse x)"
  for x :: "'a::complex_div_algebra"
  by (rule inverse_unique) simp

lemma inverse_scaleC_distrib: "inverse (scaleC a x) = scaleC (inverse a) (inverse x)"
  for x :: "'a::{complex_div_algebra,division_ring}"
  apply (cases "a = 0")
   apply simp
  apply (cases "x = 0")
   apply simp
  by (erule (1) nonzero_inverse_scaleC_distrib)


lemma sum_constant_scaleC: "(\<Sum>x\<in>A. y) = of_nat (card A) *\<^sub>C y"
  for y :: "'a::complex_vector"
  by (induct A rule: infinite_finite_induct) (simp_all add: algebra_simps)

lemma [vector_add_divide_simps]:
  "v + (b / z) *\<^sub>C w = (if z = 0 then v else (z *\<^sub>C v + b *\<^sub>C w) /\<^sub>C z)"
  "a *\<^sub>C v + (b / z) *\<^sub>C w = (if z = 0 then a *\<^sub>C v else ((a * z) *\<^sub>C v + b *\<^sub>C w) /\<^sub>C z)"
  "(a / z) *\<^sub>C v + w = (if z = 0 then w else (a *\<^sub>C v + z *\<^sub>C w) /\<^sub>C z)"
  "(a / z) *\<^sub>C v + b *\<^sub>C w = (if z = 0 then b *\<^sub>C w else (a *\<^sub>C v + (b * z) *\<^sub>C w) /\<^sub>C z)"
  "v - (b / z) *\<^sub>C w = (if z = 0 then v else (z *\<^sub>C v - b *\<^sub>C w) /\<^sub>C z)"
  "a *\<^sub>C v - (b / z) *\<^sub>C w = (if z = 0 then a *\<^sub>C v else ((a * z) *\<^sub>C v - b *\<^sub>C w) /\<^sub>C z)"
  "(a / z) *\<^sub>C v - w = (if z = 0 then -w else (a *\<^sub>C v - z *\<^sub>C w) /\<^sub>C z)"
  "(a / z) *\<^sub>C v - b *\<^sub>C w = (if z = 0 then -b *\<^sub>C w else (a *\<^sub>C v - (b * z) *\<^sub>C w) /\<^sub>C z)"
  for v :: "'a :: complex_vector"
  by (simp_all add: divide_inverse_commute scaleC_add_right complex_vector.scale_right_diff_distrib)



lemma eq_vector_fraction_iff [vector_add_divide_simps]:
  fixes x :: "'a :: complex_vector"
  shows "(x = (u / v) *\<^sub>C a) \<longleftrightarrow> (if v=0 then x = 0 else v *\<^sub>C x = u *\<^sub>C a)"
  by auto (metis (no_types) divide_eq_1_iff divide_inverse_commute scaleC_one scaleC_scaleC)

lemma vector_fraction_eq_iff [vector_add_divide_simps]:
  fixes x :: "'a :: complex_vector"
  shows "((u / v) *\<^sub>C a = x) \<longleftrightarrow> (if v=0 then x = 0 else u *\<^sub>C a = v *\<^sub>C x)"
  by (metis eq_vector_fraction_iff)

lemma complex_vector_affinity_eq:
  fixes x :: "'a :: complex_vector"
  assumes m0: "m \<noteq> 0"
  shows "m *\<^sub>C x + c = y \<longleftrightarrow> x = inverse m *\<^sub>C y - (inverse m *\<^sub>C c)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  hence "m *\<^sub>C x = y - c" by (simp add: field_simps)
  hence "inverse m *\<^sub>C (m *\<^sub>C x) = inverse m *\<^sub>C (y - c)" by simp
  thus "x = inverse m *\<^sub>C y - (inverse m *\<^sub>C c)"
    using m0
    by (simp add: complex_vector.scale_right_diff_distrib)
next
  assume ?rhs
  with m0 show "m *\<^sub>C x + c = y"
    by (simp add: complex_vector.scale_right_diff_distrib)
qed

lemma complex_vector_eq_affinity: "m \<noteq> 0 \<Longrightarrow> y = m *\<^sub>C x + c \<longleftrightarrow> inverse m *\<^sub>C y - (inverse m *\<^sub>C c) = x"
  for x :: "'a::complex_vector"
  using complex_vector_affinity_eq[where m=m and x=x and y=y and c=c]
  by metis

lemma scaleC_eq_iff [simp]: "b + u *\<^sub>C a = a + u *\<^sub>C b \<longleftrightarrow> a = b \<or> u = 1"
  for a :: "'a::complex_vector"
proof (cases "u = 1")
  case True
  thus ?thesis by auto
next
  case False
  have "a = b" if "b + u *\<^sub>C a = a + u *\<^sub>C b"
  proof -
    from that have "(u - 1) *\<^sub>C a = (u - 1) *\<^sub>C b"
      by (simp add: algebra_simps)
    with False show ?thesis
      by auto
  qed
  thus ?thesis by auto
qed

lemma scaleC_collapse [simp]: "(1 - u) *\<^sub>C a + u *\<^sub>C a = a"
  for a :: "'a::complex_vector"
  by (simp add: algebra_simps)


subsection \<open>Embedding of the Complex Numbers into any \<open>complex_algebra_1\<close>: \<open>of_complex\<close>\<close>

definition of_complex :: "complex \<Rightarrow> 'a::complex_algebra_1"
  where "of_complex c = scaleC c 1"

lemma scaleC_conv_of_complex: "scaleC r x = of_complex r * x"
  by (simp add: of_complex_def)

lemma of_complex_0 [simp]: "of_complex 0 = 0"
  by (simp add: of_complex_def)

lemma of_complex_1 [simp]: "of_complex 1 = 1"
  by (simp add: of_complex_def)

lemma of_complex_add [simp]: "of_complex (x + y) = of_complex x + of_complex y"
  by (simp add: of_complex_def scaleC_add_left)

lemma of_complex_minus [simp]: "of_complex (- x) = - of_complex x"
  by (simp add: of_complex_def)

lemma of_complex_diff [simp]: "of_complex (x - y) = of_complex x - of_complex y"
  by (simp add: of_complex_def scaleC_diff_left)

lemma of_complex_mult [simp]: "of_complex (x * y) = of_complex x * of_complex y"
  by (simp add: of_complex_def mult.commute)

lemma of_complex_sum[simp]: "of_complex (sum f s) = (\<Sum>x\<in>s. of_complex (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma of_complex_prod[simp]: "of_complex (prod f s) = (\<Prod>x\<in>s. of_complex (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma nonzero_of_complex_inverse:
  "x \<noteq> 0 \<Longrightarrow> of_complex (inverse x) = inverse (of_complex x :: 'a::complex_div_algebra)"
  by (simp add: of_complex_def nonzero_inverse_scaleC_distrib)

lemma of_complex_inverse [simp]:
  "of_complex (inverse x) = inverse (of_complex x :: 'a::{complex_div_algebra,division_ring})"
  by (simp add: of_complex_def inverse_scaleC_distrib)

lemma nonzero_of_complex_divide:
  "y \<noteq> 0 \<Longrightarrow> of_complex (x / y) = (of_complex x / of_complex y :: 'a::complex_field)"
  by (simp add: divide_inverse nonzero_of_complex_inverse)

lemma of_complex_divide [simp]:
  "of_complex (x / y) = (of_complex x / of_complex y :: 'a::complex_div_algebra)"
  by (simp add: divide_inverse)

lemma of_complex_power [simp]:
  "of_complex (x ^ n) = (of_complex x :: 'a::{complex_algebra_1}) ^ n"
  by (induct n) simp_all

lemma of_complex_eq_iff [simp]: "of_complex x = of_complex y \<longleftrightarrow> x = y"
  by (simp add: of_complex_def)

lemma inj_of_complex: "inj of_complex"
  by (auto intro: injI)

lemmas of_complex_eq_0_iff [simp] = of_complex_eq_iff [of _ 0, simplified]
lemmas of_complex_eq_1_iff [simp] = of_complex_eq_iff [of _ 1, simplified]

lemma of_complex_eq_id [simp]: "of_complex = (id :: complex \<Rightarrow> complex)"
  by (rule ext) (simp add: of_complex_def)

text \<open>Collapse nested embeddings.\<close>
lemma of_complex_of_nat_eq [simp]: "of_complex (of_nat n) = of_nat n"
  by (induct n) auto

lemma of_complex_of_real_eq [simp]: "of_complex (of_real n) = of_real n"
  unfolding of_complex_def of_real_def unfolding scaleR_scaleC by simp

lemma of_complex_of_int_eq [simp]: "of_complex (of_int z) = of_int z"
  by (cases z rule: int_diff_cases) simp

lemma of_complex_numeral [simp]: "of_complex (numeral w) = numeral w"
  using of_complex_of_int_eq [of "numeral w"] by simp

lemma of_complex_neg_numeral [simp]: "of_complex (- numeral w) = - numeral w"
  using of_complex_of_int_eq [of "- numeral w"] by simp

text \<open>Every complex algebra has characteristic zero.\<close>
instance complex_algebra_1 < ring_char_0 ..

lemma fraction_scaleC_times [simp]:
  fixes a :: "'a::complex_algebra_1"
  shows "(numeral u / numeral v) *\<^sub>C (numeral w * a) = (numeral u * numeral w / numeral v) *\<^sub>C a"
  by (metis (no_types, lifting) of_complex_numeral scaleC_conv_of_complex scaleC_scaleC times_divide_eq_left)

lemma inverse_scaleC_times [simp]:
  fixes a :: "'a::complex_algebra_1"
  shows "(1 / numeral v) *\<^sub>C (numeral w * a) = (numeral w / numeral v) *\<^sub>C a"
  by (metis divide_inverse_commute inverse_eq_divide of_complex_numeral scaleC_conv_of_complex scaleC_scaleC)

lemma scaleC_times [simp]:
  fixes a :: "'a::complex_algebra_1"
  shows "(numeral u) *\<^sub>C (numeral w * a) = (numeral u * numeral w) *\<^sub>C a"
  by (simp add: scaleC_conv_of_complex)

instance complex_field < field_char_0 ..

subsection \<open>The Set of Complex Numbers\<close>

definition Complexs :: "'a::complex_algebra_1 set"  ("\<complex>")
  where "\<complex> = range of_complex"

lemma Complexs_of_complex [simp]: "of_complex r \<in> \<complex>"
  by (simp add: Complexs_def)

lemma Complexs_of_real [simp]: "of_real r \<in> \<complex>"
  unfolding Complexs_def of_real_def of_complex_def 
  apply (subst scaleR_scaleC) by simp

lemma Reals_in_Complexs: "\<real> \<subseteq> \<complex>"
  unfolding Reals_def by auto

lemma Complexs_of_int [simp]: "of_int z \<in> \<complex>"
  by (subst of_complex_of_int_eq [symmetric], rule Complexs_of_complex)

lemma Complexs_of_nat [simp]: "of_nat n \<in> \<complex>"
  by (subst of_complex_of_nat_eq [symmetric], rule Complexs_of_complex)

lemma Complexs_numeral [simp]: "numeral w \<in> \<complex>"
  by (subst of_complex_numeral [symmetric], rule Complexs_of_complex)

lemma Complexs_0 [simp]: "0 \<in> \<complex>"
  apply (unfold Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_0 [symmetric])

lemma Complexs_1 [simp]: "1 \<in> \<complex>"
  apply (unfold Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_1 [symmetric])


lemma Complexs_add [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a + b \<in> \<complex>"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_add [symmetric])


lemma Complexs_minus [simp]: "a \<in> \<complex> \<Longrightarrow> - a \<in> \<complex>"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_minus [symmetric])


lemma Complexs_diff [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a - b \<in> \<complex>"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_diff [symmetric])


lemma Complexs_mult [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a * b \<in> \<complex>"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_mult [symmetric])


lemma nonzero_Complexs_inverse: "a \<in> \<complex> \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> inverse a \<in> \<complex>"
  for a :: "'a::complex_div_algebra"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (erule nonzero_of_complex_inverse [symmetric])


lemma Complexs_inverse: "a \<in> \<complex> \<Longrightarrow> inverse a \<in> \<complex>"
  for a :: "'a::{complex_div_algebra,division_ring}"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_inverse [symmetric])


lemma Complexs_inverse_iff [simp]: "inverse x \<in> \<complex> \<longleftrightarrow> x \<in> \<complex>"
  for x :: "'a::{complex_div_algebra,division_ring}"
  by (metis Complexs_inverse inverse_inverse_eq)

lemma nonzero_Complexs_divide: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a / b \<in> \<complex>"
  for a b :: "'a::complex_field"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (erule nonzero_of_complex_divide [symmetric])


lemma Complexs_divide [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a / b \<in> \<complex>"
  for a b :: "'a::{complex_field,field}"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_divide [symmetric])


lemma Complexs_power [simp]: "a \<in> \<complex> \<Longrightarrow> a ^ n \<in> \<complex>"
  for a :: "'a::complex_algebra_1"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_power [symmetric])


lemma Complexs_cases [cases set: Complexs]:
  assumes "q \<in> \<complex>"
  obtains (of_complex) r where "q = of_complex r"
  unfolding Complexs_def
proof -
  from \<open>q \<in> \<complex>\<close> have "q \<in> range of_complex" unfolding Complexs_def .
  then obtain r where "q = of_complex r" ..
  thus thesis ..
qed

lemma sum_in_Complexs [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<complex>) \<Longrightarrow> sum f s \<in> \<complex>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  thus ?case by (metis Complexs_0 sum.infinite)
qed simp_all

lemma prod_in_Complexs [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<complex>) \<Longrightarrow> prod f s \<in> \<complex>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  thus ?case by (metis Complexs_1 prod.infinite)
qed simp_all

lemma Complexs_induct [case_names of_complex, induct set: Complexs]:
  "q \<in> \<complex> \<Longrightarrow> (\<And>r. P (of_complex r)) \<Longrightarrow> P q"
  by (rule Complexs_cases) auto


subsection \<open>Ordered complex vector spaces\<close>

class ordered_complex_vector = complex_vector + ordered_ab_group_add +
  assumes scaleC_left_mono: "x \<le> y \<Longrightarrow> 0 \<le> a \<Longrightarrow> a *\<^sub>C x \<le> a *\<^sub>C y"
    and scaleC_right_mono: "a \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>C x \<le> b *\<^sub>C x"
begin

subclass ordered_real_vector
  apply standard unfolding scaleR_scaleC 
   apply (rule scaleC_left_mono) apply auto[2] 
  apply (rule scaleC_right_mono) by auto

lemma scaleC_mono: "a \<le> b \<Longrightarrow> x \<le> y \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>C x \<le> b *\<^sub>C y"
  apply (erule scaleC_right_mono [THEN order_trans])
   apply assumption
  apply (erule scaleC_left_mono)
  by assumption


lemma scaleC_mono': "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> c \<Longrightarrow> a *\<^sub>C c \<le> b *\<^sub>C d"
  by (rule scaleC_mono) (auto intro: order.trans)

lemma pos_le_divideRI:
  assumes "0 < c"
    and "c *\<^sub>C a \<le> b"
  shows "a \<le> b /\<^sub>C c"
proof -
  have "a = inverse c *\<^sub>C c *\<^sub>C a" using assms(1) by auto
  also have "\<dots> \<le> inverse c *\<^sub>C b"
    apply (rule scaleC_left_mono) using assms by auto
  finally show ?thesis by simp
qed

lemma pos_le_divideR_eq:
  assumes "0 < c"
  shows "a \<le> b /\<^sub>C c \<longleftrightarrow> c *\<^sub>C a \<le> b"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "0 \<noteq> c"
    using assms by blast
  thus ?thesis
    using assms local.pos_le_divideRI local.scaleC_left_mono preorder_class.less_imp_le by fastforce
qed

lemma scaleC_image_atLeastAtMost: "c > 0 \<Longrightarrow> scaleC c ` {x..y} = {c *\<^sub>C x..c *\<^sub>C y}"
  apply (auto intro!: scaleC_left_mono)
  apply (rule_tac x = "inverse c *\<^sub>C xa" in image_eqI)
  by (simp_all add: pos_le_divideR_eq[symmetric])

end

lemma neg_le_divideR_eq:
  fixes a :: "'a :: ordered_complex_vector"
  assumes "c < 0"
  shows "a \<le> b /\<^sub>C c \<longleftrightarrow> b \<le> c *\<^sub>C a"
  using pos_le_divideR_eq [of "-c" a "-b"] assms by simp

lemma scaleC_nonneg_nonneg: "0 \<le> a \<Longrightarrow> 0 \<le> x \<Longrightarrow> 0 \<le> a *\<^sub>C x"
  for x :: "'a::ordered_complex_vector"
  using scaleC_left_mono [of 0 x a] by simp

lemma scaleC_nonneg_nonpos: "0 \<le> a \<Longrightarrow> x \<le> 0 \<Longrightarrow> a *\<^sub>C x \<le> 0"
  for x :: "'a::ordered_complex_vector"
  using scaleC_left_mono [of x 0 a] by simp

lemma scaleC_nonpos_nonneg: "a \<le> 0 \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>C x \<le> 0"
  for x :: "'a::ordered_complex_vector"
  using scaleC_right_mono [of a 0 x] by simp

lemma split_scaleC_neg_le: "(0 \<le> a \<and> x \<le> 0) \<or> (a \<le> 0 \<and> 0 \<le> x) \<Longrightarrow> a *\<^sub>C x \<le> 0"
  for x :: "'a::ordered_complex_vector"
  by (auto simp add: scaleC_nonneg_nonpos scaleC_nonpos_nonneg)

lemma le_add_iff1: "a *\<^sub>C e + c \<le> b *\<^sub>C e + d \<longleftrightarrow> (a - b) *\<^sub>C e + c \<le> d"
  for c d e :: "'a::ordered_complex_vector"
  by (simp add: algebra_simps)

lemma le_add_iff2: "a *\<^sub>C e + c \<le> b *\<^sub>C e + d \<longleftrightarrow> c \<le> (b - a) *\<^sub>C e + d"
  for c d e :: "'a::ordered_complex_vector"
  by (simp add: algebra_simps)

lemma scaleC_left_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> c *\<^sub>C a \<le> c *\<^sub>C b"
  for a b :: "'a::ordered_complex_vector"
  apply (drule scaleC_left_mono [of _ _ "- c"])
  by simp_all


lemma scaleC_right_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> a *\<^sub>C c \<le> b *\<^sub>C c"
  for c :: "'a::ordered_complex_vector"
  apply (drule scaleC_right_mono [of _ _ "- c"])
  by simp_all


lemma scaleC_nonpos_nonpos: "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> 0 \<le> a *\<^sub>C b"
  for b :: "'a::ordered_complex_vector"
  using scaleC_right_mono_neg [of a 0 b] by simp

lemma split_scaleC_pos_le: "(0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0) \<Longrightarrow> 0 \<le> a *\<^sub>C b"
  for b :: "'a::ordered_complex_vector"
  by (auto simp add: scaleC_nonneg_nonneg scaleC_nonpos_nonpos)

lemma reals_zero_comparable_iff:
  "(x::complex)\<in>\<real> \<longleftrightarrow> x \<le> 0 \<or> x \<ge> 0"
  unfolding complex_is_Real_iff less_eq_complex_def
  by auto

lemma reals_zero_comparable:
  fixes x::complex
  assumes "x\<in>\<real>"
  shows "x \<le> 0 \<or> x \<ge> 0"
  using assms unfolding reals_zero_comparable_iff by assumption

lemma zero_le_scaleC_iff:
  fixes b :: "'a::ordered_complex_vector"
  assumes "a \<in> \<real>"
  shows "0 \<le> a *\<^sub>C b \<longleftrightarrow> 0 < a \<and> 0 \<le> b \<or> a < 0 \<and> b \<le> 0 \<or> a = 0"
    (is "?lhs = ?rhs")
proof (cases "a = 0")
  case True
  thus ?thesis by simp
next
  case False
  show ?thesis
  proof
    assume ?lhs
    from \<open>a \<noteq> 0\<close> consider "a > 0" | "a < 0"
      using reals_zero_comparable[OF assms] by auto
    thus ?rhs
    proof cases
      case 1
      with \<open>?lhs\<close> have "inverse a *\<^sub>C 0 \<le> inverse a *\<^sub>C (a *\<^sub>C b)"
        by (intro scaleC_mono) auto
      with 1 show ?thesis
        by simp
    next
      case 2
      with \<open>?lhs\<close> have "- inverse a *\<^sub>C 0 \<le> - inverse a *\<^sub>C (a *\<^sub>C b)"
        by (intro scaleC_mono) auto
      with 2 show ?thesis
        by simp
    qed
  next
    assume ?rhs
    thus ?lhs
      using reals_zero_comparable[OF assms]
      by (auto simp: not_le \<open>a \<noteq> 0\<close> intro!: split_scaleC_pos_le )
  qed
qed

lemma scaleC_le_0_iff: 
  fixes b::"'a::ordered_complex_vector"
  assumes "a \<in> \<real>"
  shows "a *\<^sub>C b \<le> 0 \<longleftrightarrow> 0 < a \<and> b \<le> 0 \<or> a < 0 \<and> 0 \<le> b \<or> a = 0"
  apply (insert zero_le_scaleC_iff [of "-a" b]) 
  using reals_zero_comparable[OF assms]
  using assms by auto

lemma scaleC_le_cancel_left: 
  fixes b :: "'a::ordered_complex_vector"
  assumes "c \<in> \<real>"
  shows "c *\<^sub>C a \<le> c *\<^sub>C b \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  using assms apply cases apply (simp add: scaleR_scaleC[symmetric] less_complex_def)
  by (rule scaleR_le_cancel_left)

lemma scaleC_le_cancel_left_pos: "0 < c \<Longrightarrow> c *\<^sub>C a \<le> c *\<^sub>C b \<longleftrightarrow> a \<le> b"
  for b :: "'a::ordered_complex_vector"
  by (meson dual_order.strict_implies_order reals_zero_comparable_iff scaleC_le_cancel_left scaleC_left_mono)

lemma scaleC_le_cancel_left_neg: "c < 0 \<Longrightarrow> c *\<^sub>C a \<le> c *\<^sub>C b \<longleftrightarrow> b \<le> a"
  for b :: "'a::ordered_complex_vector"
  by (meson dual_order.strict_implies_order reals_zero_comparable_iff scaleC_le_cancel_left scaleC_left_mono_neg)

lemma scaleC_left_le_one_le: "0 \<le> x \<Longrightarrow> a \<le> 1 \<Longrightarrow> a *\<^sub>C x \<le> x"
  for x :: "'a::ordered_complex_vector" and a :: complex
  using scaleC_right_mono[of a 1 x] by simp

subsection \<open>Complex normed vector spaces\<close>

class complex_normed_vector = complex_vector + sgn_div_norm + dist_norm + uniformity_dist + open_uniformity +
  real_normed_vector + 
  assumes norm_scaleC [simp]: "norm (a *\<^sub>C x) = (cmod a) * norm x"

class complex_normed_algebra = complex_algebra + complex_normed_vector + real_normed_algebra

class complex_normed_algebra_1 = complex_algebra_1 + complex_normed_algebra + real_normed_algebra_1

lemma (in complex_normed_algebra_1) scaleC_power [simp]: "(scaleC x y) ^ n = scaleC (x^n) (y^n)"
  by (induct n) (simp_all add: mult_ac)

class complex_normed_div_algebra = complex_div_algebra + complex_normed_vector + real_normed_div_algebra

class complex_normed_field = complex_field + complex_normed_div_algebra + real_normed_field

instance complex_normed_div_algebra < complex_normed_algebra_1 ..

lemma dist_scaleC [simp]: "dist (x *\<^sub>C a) (y *\<^sub>C a) = cmod (x - y) * norm a"
  for a :: "'a::complex_normed_vector"
  by (metis dist_norm norm_scaleC scaleC_left.diff)

lemma norm_of_complex [simp]: "norm (of_complex r :: 'a::complex_normed_algebra_1) = cmod r"
  by (simp add: of_complex_def)

lemma norm_of_complex_add1 [simp]: "norm (of_complex x + 1 :: 'a :: complex_normed_div_algebra) = cmod (x + 1)"
  by (metis norm_of_complex of_complex_1 of_complex_add)

lemma norm_of_complex_addn [simp]:
  "norm (of_complex x + numeral b :: 'a :: complex_normed_div_algebra) = cmod (x + numeral b)"
  by (metis norm_of_complex of_complex_add of_complex_numeral)

lemma norm_of_complex_diff [simp]:
  "norm (of_complex b - of_complex a :: 'a::complex_normed_algebra_1) \<le> cmod (b - a)"
  by (metis norm_of_complex of_complex_diff order_refl)


subsection \<open>Class instances for complex numbers\<close>

instantiation complex :: complex_normed_field
begin

instance
  apply intro_classes 
  by (simp add: norm_mult)

end

lemma dist_of_complex [simp]: "dist (of_complex x :: 'a) (of_complex y) = dist x y"
  for a :: "'a::complex_normed_div_algebra"
  by (metis dist_norm norm_of_complex of_complex_diff)

declare [[code abort: "open :: complex set \<Rightarrow> bool"]]

subsection \<open>Sign function\<close>

lemma sgn_scaleC: "sgn (scaleC r x) = scaleC (sgn r) (sgn x)"
  for x :: "'a::complex_normed_vector"
  by (simp add: scaleR_scaleC sgn_div_norm ac_simps)

lemma sgn_of_complex: "sgn (of_complex r :: 'a::complex_normed_algebra_1) = of_complex (sgn r)"
  unfolding of_complex_def by (simp only: sgn_scaleC sgn_one)

lemma complex_sgn_eq: "sgn x = x / \<bar>x\<bar>"
  for x :: complex
  by (simp add: abs_complex_def scaleR_scaleC sgn_div_norm divide_inverse)

subsection \<open>Bounded Linear and Bilinear Operators\<close>
locale clinear = additive f for f :: "'a::complex_vector \<Rightarrow> 'b::complex_vector" +
  assumes scaleC: "f (r *\<^sub>C x) = r  *\<^sub>C (f x)"

sublocale clinear \<subseteq> linear
  apply (rule linearI)
   apply (rule add)
  unfolding scaleR_scaleC by (rule scaleC)

lemma clinear_imp_scaleC:
  assumes "clinear D"
  obtains d where "D = (\<lambda>x. x *\<^sub>C d)"
  by (metis assms clinear.scaleC mult.commute mult.left_neutral complex_scaleC_def)

corollary complex_clinearD:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "clinear f" obtains c where "f = (*) c"
  by (rule clinear_imp_scaleC [OF assms]) (force simp: scaleC_conv_of_complex)

lemma clinear_times_of_complex: "clinear (\<lambda>x. a * of_complex x)"
  apply (simp add: clinear_def additive_def clinear_axioms_def)
  by (metis distrib_left mult_scaleC_right scaleC_conv_of_complex)

lemma clinearI:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c x. f (c *\<^sub>C x) = c *\<^sub>C f x"
  shows "clinear f"
  by standard (rule assms)+

locale bounded_clinear = clinear f for f :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" +
  assumes bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
begin

sublocale bounded_linear
  apply standard by (fact bounded) 

lemma bounded_linear: "bounded_linear f"
  by (fact bounded_linear)

lemma clinear: "clinear f"
  by (fact local.clinear_axioms)

end

lemma clinear_times: "clinear (\<lambda>x. c * x)"
  for c :: "'a::complex_algebra"
  by (auto simp: clinearI distrib_left)

lemma bounded_clinear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (scaleC r x) = scaleC r (f x)"
    and "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_clinear f"
  by standard (blast intro: assms)+

locale csemilinear = additive f for f :: "'a::complex_vector \<Rightarrow> 'b::complex_vector" +
  assumes scaleC: "f (scaleC r x) = scaleC (cnj r) (f x)"

sublocale csemilinear \<subseteq> linear
  apply (rule linearI)
   apply (rule add)
  unfolding scaleR_scaleC by (subst scaleC, simp)

lemma csemilinear_imp_scaleC:
  assumes "csemilinear D"
  obtains d where "D = (\<lambda>x. cnj (x *\<^sub>C d))"
proof (atomize_elim, rule exI[of _ "cnj (D 1)"], rule ext)
  fix x
  have "cnj (x *\<^sub>C cnj (D 1)) = cnj x *\<^sub>C D 1" by simp
  also have "\<dots> = D (x *\<^sub>C 1)" by (rule csemilinear.scaleC[OF assms, symmetric])
  also have "\<dots> = D x" by simp
  finally show "D x = cnj (x *\<^sub>C cnj (D 1))" by simp
qed

corollary complex_csemilinearD:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "csemilinear f" obtains c where "f = (\<lambda>x. cnj (c * x))"
  by (rule csemilinear_imp_scaleC [OF assms]) (force simp: scaleC_conv_of_complex)

lemma csemilinear_times_of_complex: "csemilinear (\<lambda>x. cnj (a * of_complex x))"
  apply (simp add: csemilinear_def additive_def csemilinear_axioms_def)
  by (metis distrib_left)

lemma csemilinearI:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c x. f (c *\<^sub>C x) = cnj c *\<^sub>C f x"
  shows "csemilinear f"
  by standard (rule assms)+

locale bounded_csemilinear = csemilinear f for f :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" +
  assumes bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
begin

sublocale bounded_linear
  apply standard by (fact bounded) 

lemma bounded_linear: "bounded_linear f"
  by (fact bounded_linear)

lemma csemilinear: "csemilinear f"
  by (fact csemilinear_axioms)

end

lemma bounded_csemilinear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (scaleC r x) = scaleC (cnj r) (f x)"
    and "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_csemilinear f"
  by standard (blast intro: assms)+

lemma cnj_bounded_csemilinear[simp]: "bounded_csemilinear cnj"
  apply (rule bounded_csemilinear_intro[where K=1]) by auto

lemma bounded_csemilinear_compose1:
  assumes "bounded_csemilinear f"
    and "bounded_csemilinear g"
  shows "bounded_clinear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_csemilinear f by fact
  interpret g: bounded_csemilinear g by fact
  show ?thesis
  proof unfold_locales
    show "f (g (x + y)) = f (g x) + f (g y)" for x y
      by (simp only: f.add g.add)
    show "f (g (scaleC r x)) = scaleC r (f (g x))" for r x
      by (simp only: f.scaleC g.scaleC complex_cnj_cnj)
    from f.pos_bounded obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf"
      by blast
    from g.pos_bounded obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg"
      by blast
    show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    proof (intro exI allI)
      fix x
      have "norm (f (g x)) \<le> norm (g x) * Kf"
        using f .
      also have "\<dots> \<le> (norm x * Kg) * Kf"
        using g Kf [THEN order_less_imp_le] by (rule mult_right_mono)
      also have "(norm x * Kg) * Kf = norm x * (Kg * Kf)"
        by (rule mult.assoc)
      finally show "norm (f (g x)) \<le> norm x * (Kg * Kf)" .
    qed
  qed
qed

lemma bounded_csemilinear_compose2:
  assumes "bounded_csemilinear f"
    and "bounded_clinear g"
  shows "bounded_csemilinear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_csemilinear f by fact
  interpret g: bounded_clinear g by fact
  show ?thesis
  proof unfold_locales
    show "f (g (x + y)) = f (g x) + f (g y)" for x y
      by (simp only: f.add g.add)
    show "f (g (scaleC r x)) = scaleC (cnj r) (f (g x))" for r x
      by (simp only: f.scaleC g.scaleC)
    from f.pos_bounded obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf"
      by blast
    from g.pos_bounded obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg"
      by blast
    show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    proof (intro exI allI)
      fix x
      have "norm (f (g x)) \<le> norm (g x) * Kf"
        using f .
      also have "\<dots> \<le> (norm x * Kg) * Kf"
        using g Kf [THEN order_less_imp_le] by (rule mult_right_mono)
      also have "(norm x * Kg) * Kf = norm x * (Kg * Kf)"
        by (rule mult.assoc)
      finally show "norm (f (g x)) \<le> norm x * (Kg * Kf)" .
    qed
  qed
qed

lemma bounded_csemilinear_compose3:
  assumes "bounded_clinear f"
    and "bounded_csemilinear g"
  shows "bounded_csemilinear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_clinear f by fact
  interpret g: bounded_csemilinear g by fact
  show ?thesis
  proof unfold_locales
    show "f (g (x + y)) = f (g x) + f (g y)" for x y
      by (simp only: f.add g.add)
    show "f (g (scaleC r x)) = scaleC (cnj r) (f (g x))" for r x
      by (simp only: f.scaleC g.scaleC)
    from f.pos_bounded obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf"
      by blast
    from g.pos_bounded obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg"
      by blast
    show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    proof (intro exI allI)
      fix x
      have "norm (f (g x)) \<le> norm (g x) * Kf"
        using f .
      also have "\<dots> \<le> (norm x * Kg) * Kf"
        using g Kf [THEN order_less_imp_le] by (rule mult_right_mono)
      also have "(norm x * Kg) * Kf = norm x * (Kg * Kf)"
        by (rule mult.assoc)
      finally show "norm (f (g x)) \<le> norm x * (Kg * Kf)" .
    qed
  qed
qed

locale bounded_cbilinear =
  fixes prod :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector"
    (infixl "**" 70)
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
    and add_right: "prod a (b + b') = prod a b + prod a b'"
    and scaleC_left: "prod (r *\<^sub>C a) b = scaleC r (prod a b)"
    and scaleC_right: "prod a (r *\<^sub>C b) = scaleC r (prod a b)"
    and bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
begin

sublocale bounded_bilinear
  apply standard
  unfolding scaleR_scaleC
      apply (fact add_left)
     apply (fact add_right)
    apply (fact scaleC_left)
   apply (fact scaleC_right)
  by (fact bounded)

lemma bounded_bilinear: "bounded_bilinear prod"
  by (fact bounded_bilinear_axioms)

lemma bounded_clinear_left: "bounded_clinear (\<lambda>a. prod a b)"
  apply (insert bounded)
  apply safe
  apply (rule_tac K="norm b * K" in bounded_clinear_intro)
    apply (rule add_left)
   apply (rule scaleC_left)
  by (simp add: ac_simps)


lemma bounded_clinear_right: "bounded_clinear (\<lambda>b. prod a b)"
  apply (insert bounded)
  apply safe
  apply (rule_tac K="norm a * K" in bounded_clinear_intro)
    apply (rule add_right)
   apply (rule scaleC_right)
  by (simp add: ac_simps)


lemma flip: "bounded_cbilinear (\<lambda>x y. prod y x)"
  apply standard
      apply (rule add_right)
     apply (rule add_left)
    apply (rule scaleC_right)
   apply (rule scaleC_left)
  apply (subst mult.commute)
  apply (insert bounded)
  by blast


lemma comp1:
  assumes "bounded_clinear g"
  shows "bounded_cbilinear (\<lambda>x. prod (g x))"
proof unfold_locales
  interpret g: bounded_clinear g by fact
  write prod (infixl "**" 70)
  show "\<And>a a' b. g (a + a') ** b = g a ** b + g a' ** b"
    "\<And>a b b'. g a ** (b + b') = g a ** b + g a ** b'"
    "\<And>r a b. g (r *\<^sub>C a) ** b = r *\<^sub>C (g a ** b)"
    "\<And>a r b. g a ** (r *\<^sub>C b) = r *\<^sub>C (g a ** b)"
    by (auto simp: g.add add_left add_right g.scaleC scaleC_left scaleC_right)
  from g.nonneg_bounded nonneg_bounded obtain K L
    where nn: "0 \<le> K" "0 \<le> L"
      and K: "\<And>x. norm (g x) \<le> norm x * K"
      and L: "\<And>a b. norm (a ** b) \<le> norm a * norm b * L"
    by auto
  have "norm (g a ** b) \<le> norm a * K * norm b * L" for a b
    by (auto intro!:  order_trans[OF K] order_trans[OF L] mult_mono simp: nn)
  thus "\<exists>K. \<forall>a b. norm (g a ** b) \<le> norm a * norm b * K"
    by (auto intro!: exI[where x="K * L"] simp: ac_simps)
qed

lemma comp: "bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_cbilinear (\<lambda>x y. prod (f x) (g y))"
  by (rule bounded_cbilinear.flip[OF bounded_cbilinear.comp1[OF bounded_cbilinear.flip[OF comp1]]])

end

lemma bounded_clinear_ident[simp]: "bounded_clinear (\<lambda>x. x)"
  by standard (auto intro!: exI[of _ 1])

lemma bounded_clinear_zero[simp]: "bounded_clinear (\<lambda>x. 0)"
  by standard (auto intro!: exI[of _ 1])

lemma bounded_clinear_add:
  assumes "bounded_clinear f"
    and "bounded_clinear g"
  shows "bounded_clinear (\<lambda>x. f x + g x)"
proof -
  interpret f: bounded_clinear f by fact
  interpret g: bounded_clinear g by fact
  show ?thesis
  proof
    from f.bounded obtain Kf where Kf: "norm (f x) \<le> norm x * Kf" for x
      by blast
    from g.bounded obtain Kg where Kg: "norm (g x) \<le> norm x * Kg" for x
      by blast
    show "\<exists>K. \<forall>x. norm (f x + g x) \<le> norm x * K"
      using add_mono[OF Kf Kg]
      by (intro exI[of _ "Kf + Kg"]) (auto simp: field_simps intro: norm_triangle_ineq order_trans)
  qed (simp_all add: f.add g.add f.scaleC g.scaleC scaleC_add_right)
qed

lemma bounded_clinear_minus:
  assumes "bounded_clinear f"
  shows "bounded_clinear (\<lambda>x. - f x)"
proof -
  interpret f: bounded_clinear f by fact
  show ?thesis
    apply unfold_locales
      apply (simp add: f.add)
     apply (simp add: f.scaleC)
    by (simp add: f.bounded)
qed

lemma bounded_clinear_sub: "bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_clinear (\<lambda>x. f x - g x)"
  using bounded_clinear_add[of f "\<lambda>x. - g x"] bounded_clinear_minus[of g]
  by (auto simp add: algebra_simps)

lemma bounded_clinear_sum:
  fixes f :: "'i \<Rightarrow> 'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector"
  shows "(\<And>i. i \<in> I \<Longrightarrow> bounded_clinear (f i)) \<Longrightarrow> bounded_clinear (\<lambda>x. \<Sum>i\<in>I. f i x)"
  by (induct I rule: infinite_finite_induct) (auto intro!: bounded_clinear_add)

lemma bounded_clinear_compose:
  assumes "bounded_clinear f"
    and "bounded_clinear g"
  shows "bounded_clinear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_clinear f by fact
  interpret g: bounded_clinear g by fact
  show ?thesis
  proof unfold_locales
    show "f (g (x + y)) = f (g x) + f (g y)" for x y
      by (simp only: f.add g.add)
    show "f (g (scaleC r x)) = scaleC r (f (g x))" for r x
      by (simp only: f.scaleC g.scaleC)
    from f.pos_bounded obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf"
      by blast
    from g.pos_bounded obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg"
      by blast
    show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    proof (intro exI allI)
      fix x
      have "norm (f (g x)) \<le> norm (g x) * Kf"
        using f .
      also have "\<dots> \<le> (norm x * Kg) * Kf"
        using g Kf [THEN order_less_imp_le] by (rule mult_right_mono)
      also have "(norm x * Kg) * Kf = norm x * (Kg * Kf)"
        by (rule mult.assoc)
      finally show "norm (f (g x)) \<le> norm x * (Kg * Kf)" .
    qed
  qed
qed

lemma bounded_cbilinear_mult: "bounded_cbilinear ((*) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a::complex_normed_algebra)"
  apply (rule bounded_cbilinear.intro)
      apply (rule distrib_right)
     apply (rule distrib_left)
    apply (rule mult_scaleC_left)
   apply (rule mult_scaleC_right)
  apply (rule_tac x="1" in exI)
  by (simp add: norm_mult_ineq)


lemma bounded_clinear_mult_left: "bounded_clinear (\<lambda>x::'a::complex_normed_algebra. x * y)"
  using bounded_cbilinear_mult
  by (rule bounded_cbilinear.bounded_clinear_left)

lemma bounded_clinear_mult_right: "bounded_clinear (\<lambda>y::'a::complex_normed_algebra. x * y)"
  using bounded_cbilinear_mult
  by (rule bounded_cbilinear.bounded_clinear_right)

lemmas bounded_clinear_mult_const =
  bounded_clinear_mult_left [THEN bounded_clinear_compose]

lemmas bounded_clinear_const_mult =
  bounded_clinear_mult_right [THEN bounded_clinear_compose]

lemma bounded_clinear_divide: "bounded_clinear (\<lambda>x. x / y)"
  for y :: "'a::complex_normed_field"
  unfolding divide_inverse by (rule bounded_clinear_mult_left)

lemma bounded_cbilinear_scaleC: "bounded_cbilinear scaleC"
  apply (rule bounded_cbilinear.intro)
      apply (rule scaleC_add_left)
     apply (rule scaleC_add_right)
    apply simp
   apply (rule scaleC_left_commute)
  apply (rule_tac x="1" in exI)
  by simp


lemma bounded_clinear_scaleC_left: "bounded_clinear (\<lambda>r. scaleC r x)"
  using bounded_cbilinear_scaleC
  by (rule bounded_cbilinear.bounded_clinear_left)

lemma bounded_clinear_scaleC_right: "bounded_clinear (\<lambda>x. scaleC r x)"
  using bounded_cbilinear_scaleC
  by (rule bounded_cbilinear.bounded_clinear_right)

lemmas bounded_clinear_scaleC_const =
  bounded_clinear_scaleC_left[THEN bounded_clinear_compose]

lemmas bounded_clinear_const_scaleC =
  bounded_clinear_scaleC_right[THEN bounded_clinear_compose]

lemma bounded_clinear_of_complex: "bounded_clinear (\<lambda>r. of_complex r)"
  unfolding of_complex_def by (rule bounded_clinear_scaleC_left)

lemma complex_bounded_clinear: "bounded_clinear f \<longleftrightarrow> (\<exists>c::complex. f = (\<lambda>x. x * c))"
  for f :: "complex \<Rightarrow> complex"
proof -
  {
    fix x
    assume "bounded_clinear f"
    then interpret bounded_clinear f .
    from scaleC[of x 1] have "f x = x * f 1"
      by simp
  }
  thus ?thesis
    by (auto intro: exI[of _ "f 1"] bounded_clinear_mult_left)
qed

lemma bij_clinear_imp_inv_clinear: "clinear f \<Longrightarrow> bij f \<Longrightarrow> clinear (inv f)"
  by (auto simp: clinear_def clinear_axioms_def additive_def bij_is_surj bij_is_inj surj_f_inv_f
      intro!:  Hilbert_Choice.inv_f_eq)

locale bounded_sesquilinear =
  fixes prod :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector"
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
    and add_right: "prod a (b + b') = prod a b + prod a b'"
    and scaleC_left: "prod (scaleC r a) b = scaleC (cnj r) (prod a b)"
    and scaleC_right: "prod a (scaleC r b) = scaleC r (prod a b)"
    and bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
begin

sublocale bounded_bilinear
  apply standard
  unfolding scaleR_scaleC
      apply (fact add_left)
     apply (fact add_right)
    apply (simp add: scaleC_left)
   apply (fact scaleC_right)
  by (fact bounded)

lemma bounded_bilinear: "bounded_bilinear prod" 
  by (fact bounded_bilinear_axioms)

lemma bounded_csemilinear_left: "bounded_csemilinear (\<lambda>a. prod a b)"
  apply (insert bounded)
  apply safe
  apply (rule_tac K="norm b * K" in bounded_csemilinear_intro)
    apply (rule add_left)
   apply (simp add: scaleC_left)
  by (simp add: ac_simps)

lemma bounded_clinear_right: "bounded_clinear (\<lambda>b. prod a b)"
  apply (insert bounded)
  apply safe
  apply (rule_tac K="norm a * K" in bounded_clinear_intro)
    apply (rule add_right)
   apply (rule scaleC_right)
  by (simp add: ac_simps)

lemma comp1:
  assumes "bounded_clinear g"
  shows "bounded_sesquilinear (\<lambda>x. prod (g x))"
proof unfold_locales
  interpret g: bounded_clinear g by fact
  write prod (infixl "**" 70)
  show "\<And>a a' b. g (a + a') ** b = g a ** b + g a' ** b"
    "\<And>a b b'. g a ** (b + b') = g a ** b + g a ** b'"
    "\<And>r a b. g (r *\<^sub>C a) ** b = cnj r *\<^sub>C (g a ** b)"
    "\<And>a r b. g a ** (r *\<^sub>C b) = r *\<^sub>C (g a ** b)"
    by (auto simp: g.add add_left add_right g.scaleC scaleC_left scaleC_right)
  from g.nonneg_bounded nonneg_bounded obtain K L
    where nn: "0 \<le> K" "0 \<le> L"
      and K: "\<And>x. norm (g x) \<le> norm x * K"
      and L: "\<And>a b. norm (a ** b) \<le> norm a * norm b * L"
    by auto
  have "norm (g a ** b) \<le> norm a * K * norm b * L" for a b
    by (auto intro!:  order_trans[OF K] order_trans[OF L] mult_mono simp: nn)
  thus "\<exists>K. \<forall>a b. norm (g a ** b) \<le> norm a * norm b * K"
    by (auto intro!: exI[where x="K * L"] simp: ac_simps)
qed

lemma comp2:
  assumes "bounded_clinear g"
  shows "bounded_sesquilinear (\<lambda>x y. prod x (g y))"
proof unfold_locales
  interpret g: bounded_clinear g by fact
  write prod (infixl "**" 70)
  show "\<And>a a' b. b ** g (a + a') = b ** g a + b ** g a'"
    "\<And>a b b'. (b + b') ** g a = b ** g a + b' ** g a"
    "\<And>r a b. b ** g (r *\<^sub>C a) = r *\<^sub>C (b ** g a)"
    "\<And>a r b. (r *\<^sub>C b) ** g a = cnj r *\<^sub>C (b ** g a)"
    by (auto simp: g.add add_left add_right g.scaleC scaleC_left scaleC_right)
  from g.nonneg_bounded nonneg_bounded obtain K L
    where nn: "0 \<le> K" "0 \<le> L"
      and K: "\<And>x. norm (g x) \<le> norm x * K"
      and L: "\<And>a b. norm (a ** b) \<le> norm a * norm b * L"
    by auto
  have "norm (b ** g a) \<le> norm b * (norm a * K) * L" for a b
    by (auto intro!:  order_trans[OF K] order_trans[OF L] mult_mono simp: nn)
  thus "\<exists>K. \<forall>a b. norm (a ** g b) \<le> norm a * norm b * K"
    by (auto intro!: exI[where x="K * L"] simp: ac_simps)
qed

lemma comp: "bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_sesquilinear (\<lambda>x y. prod (f x) (g y))" 
  using bounded_sesquilinear.comp2 comp1 by auto

end


instance complex_normed_algebra_1 \<subseteq> perfect_space ..

subsection \<open>Complete metric spaces\<close>

subsection \<open>Cauchy sequences\<close>

lemma cCauchy_iff2: "Cauchy X \<longleftrightarrow> (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. cmod (X m - X n) < inverse (real (Suc j))))"
  by (simp only: metric_Cauchy_iff2 dist_complex_def)

subsubsection \<open>Cauchy Sequences are Convergent\<close>

subsection \<open>The set of complex numbers is a complete metric space\<close>

class cbanach = complex_normed_vector + complete_space

subclass (in cbanach) banach ..

instance complex :: cbanach ..

lemmas sums_of_complex = bounded_linear.sums [OF bounded_clinear_of_complex[THEN bounded_clinear.bounded_linear]]
lemmas summable_of_complex = bounded_linear.summable [OF bounded_clinear_of_complex[THEN bounded_clinear.bounded_linear]]
lemmas suminf_of_complex = bounded_linear.suminf [OF bounded_clinear_of_complex[THEN bounded_clinear.bounded_linear]]

lemmas sums_scaleC_left = bounded_linear.sums[OF bounded_clinear_scaleC_left[THEN bounded_clinear.bounded_linear]]
lemmas summable_scaleC_left = bounded_linear.summable[OF bounded_clinear_scaleC_left[THEN bounded_clinear.bounded_linear]]
lemmas suminf_scaleC_left = bounded_linear.suminf[OF bounded_clinear_scaleC_left[THEN bounded_clinear.bounded_linear]]

lemmas sums_scaleC_right = bounded_linear.sums[OF bounded_clinear_scaleC_right[THEN bounded_clinear.bounded_linear]]
lemmas summable_scaleC_right = bounded_linear.summable[OF bounded_clinear_scaleC_right[THEN bounded_clinear.bounded_linear]]
lemmas suminf_scaleC_right = bounded_linear.suminf[OF bounded_clinear_scaleC_right[THEN bounded_clinear.bounded_linear]]


lemma clinear_linear:
  fixes f :: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector\<close>
  assumes \<open>clinear f\<close>
  shows \<open>linear f\<close>
proof
  show "f (b1 + b2) = f b1 + f b2"
    for b1 :: 'a
      and b2 :: 'a
    by (simp add: additive.add assms clinear.axioms(1))   
  show "f (r *\<^sub>R b) = r *\<^sub>R f b"
    for r :: real
      and b :: 'a
    using  \<open>clinear f\<close> scaleR_scaleC
    unfolding clinear_def clinear_axioms_def 
    by smt
qed


lemma clinear_add:
  \<open>clinear f \<Longrightarrow> clinear g \<Longrightarrow> clinear (\<lambda> x. f x + g x)\<close>
  by (smt ab_semigroup_add_class.add_ac(1) add.commute additive_def clinear.axioms(1) clinear.axioms(2) clinearI clinear_axioms_def scaleC_add_right)

lemma clinear_minus:
  \<open>clinear f \<Longrightarrow> clinear g \<Longrightarrow> clinear (\<lambda> x. f x - g x)\<close>
proof
  show "f (x + y) - g (x + y) = f x - g x + (f y - g y)"
    if "clinear f"
      and "clinear g"
    for x :: 'a
      and y :: 'a
    by (simp add: additive.add clinear.axioms(1) that(1) that(2)) 
  show "f (r *\<^sub>C x) - g (r *\<^sub>C x) = r *\<^sub>C (f x - g x)"
    if "clinear f"
      and "clinear g"
    for r :: complex
      and x :: 'a
    by (simp add: clinear.scaleC complex_vector.scale_right_diff_distrib that(1) that(2))
qed


lemma clinear_zero:
  fixes f :: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector\<close>
  shows \<open>clinear f \<Longrightarrow> f 0 = 0\<close>
proof-
  assume \<open>clinear f\<close>
  have \<open>(0::'a) + 0 = 0\<close>
    by simp
  hence \<open>f (0 + 0) = f 0\<close>
    by simp
  moreover have \<open>f 0 = f 0 + f 0\<close>
    using \<open>clinear f\<close> unfolding clinear_def
    by (metis additive.add calculation) 
  ultimately have \<open>f 0 + f 0 = f 0\<close>
    by simp
  thus ?thesis by simp
qed


definition scaleHC :: "complex star \<Rightarrow> 'a star \<Rightarrow> 'a::complex_normed_vector star"
  where [transfer_unfold]: "scaleHC = starfun2 scaleC"

instantiation star :: (scaleC) scaleC
begin
definition star_scaleC_def [transfer_unfold]: "scaleC r \<equiv> *f* (scaleC r)"
instance 
  apply intro_classes
  by (simp add: scaleR_scaleC star_scaleC_def star_scaleR_def)  
end

lemma hnorm_scaleC: "\<And>x::'a::complex_normed_vector star. 
hnorm (a *\<^sub>C x) = (hcmod (star_of a)) * hnorm x"
  by StarDef.transfer (rule norm_scaleC)

lemma Standard_scaleC [simp]: "x \<in> Standard \<Longrightarrow> scaleC r x \<in> Standard"
  by (simp add: star_scaleC_def)

lemma star_of_scaleC [simp]: "star_of (scaleC r x) = scaleC r (star_of x)"
  by StarDef.transfer (rule refl)

instance star :: (complex_vector) complex_vector
proof
  fix a b :: complex
  show "\<And>x y::'a star. scaleC a (x + y) = scaleC a x + scaleC a y"
    apply StarDef.transfer
    by (simp add: scaleC_add_right)
  show "\<And>x::'a star. scaleC (a + b) x = scaleC a x + scaleC b x"
    apply StarDef.transfer
    by (simp add: scaleC_add_left)
  show "\<And>x::'a star. scaleC a (scaleC b x) = scaleC (a * b) x"
    by StarDef.transfer (rule scaleC_scaleC)
  show "\<And>x::'a star. scaleC 1 x = x"
    by StarDef.transfer (rule scaleC_one)
qed

instance star :: (complex_algebra) complex_algebra
proof
  fix a :: complex
  show "\<And>x y::'a star. scaleC a x * y = scaleC a (x * y)"
    by StarDef.transfer (rule mult_scaleC_left)
  show "\<And>x y::'a star. x * scaleC a y = scaleC a (x * y)"
    by StarDef.transfer (rule mult_scaleC_right)
qed

instance star :: (complex_algebra_1) complex_algebra_1 ..

instance star :: (complex_div_algebra) complex_div_algebra ..

instance star :: (complex_field) complex_field ..

lemma isCont_scaleC:
  fixes l :: \<open>'a::complex_normed_vector\<close>
  shows \<open>isCont (\<lambda> v. scaleC a v) l\<close>
proof- (* Nonstandard proof *)
  have \<open>y \<approx> star_of l \<Longrightarrow> (*f* (*\<^sub>C) a) y \<approx> star_of (a *\<^sub>C l)\<close>
    for y         
  proof-
    assume \<open>y \<approx> star_of l\<close> 
    hence \<open>hnorm (y - star_of l) \<in> Infinitesimal\<close>
      using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by blast
    hence \<open>(star_of (cmod a)) * hnorm (y - star_of l) \<in> Infinitesimal\<close>
      using Infinitesimal_star_of_mult2 by blast      
    hence \<open>hnorm ( a *\<^sub>C (y - star_of l)) \<in> Infinitesimal\<close>
      by (simp add: hnorm_scaleC)
    moreover have \<open>a *\<^sub>C (y - star_of l) = a *\<^sub>C y -  a *\<^sub>C (star_of l)\<close>
      by (simp add: complex_vector.scale_right_diff_distrib)
    ultimately have \<open>hnorm ( a *\<^sub>C y -  a *\<^sub>C (star_of l)) \<in> Infinitesimal\<close>
      by auto
    hence \<open>(*f* (*\<^sub>C) a) y \<approx> star_of (a *\<^sub>C l)\<close>
      by (metis Infinitesimal_hnorm_iff bex_Infinitesimal_iff star_of_scaleC star_scaleC_def)      
    thus ?thesis by blast
  qed
  hence \<open>isNSCont (\<lambda> v. scaleC a v) l\<close>
    unfolding isNSCont_def
    by auto
  thus ?thesis
    by (simp add: isNSCont_isCont_iff) 
qed

(* Classical proof

proof-
  have \<open>x \<longlonglongrightarrow> l \<Longrightarrow> (\<lambda> n. (scaleC a) (x n))  \<longlonglongrightarrow> (scaleC a) l\<close>
    for x::\<open>nat \<Rightarrow> 'a\<close>
  proof(cases \<open>a = 0\<close>)
    case True
    assume \<open>x \<longlonglongrightarrow> l\<close>
    have \<open>(scaleC a) = (\<lambda> _::'a. (0::'a))\<close>
      using \<open>a = 0\<close> by auto
    thus ?thesis
      by simp 
  next
    case False
    hence \<open>a \<noteq> 0\<close>
      by blast
    assume \<open>x \<longlonglongrightarrow> l\<close>
    hence \<open>\<forall>e>0.\<exists>N.\<forall>n\<ge>N. norm (x n - l) < e\<close>
      using LIMSEQ_iff by blast
    hence \<open>\<forall>e>0.\<exists>N.\<forall>n\<ge>N. (cmod a) * norm (x n - l) < (cmod a) * e\<close>
      using \<open>a \<noteq> 0\<close> by auto
    hence \<open>\<forall>e>0.\<exists>N.\<forall>n\<ge>N.  norm ((scaleC a) (x n - l) ) < (cmod a) * e\<close>
      by simp
    hence \<open>\<forall>e>0.\<exists>N.\<forall>n\<ge>N.  norm ((scaleC a) (x n) - (scaleC a) l ) < (cmod a) * e\<close>
      by (simp add: complex_vector.scale_right_diff_distrib)
    hence \<open>\<forall>e>0.\<exists>N.\<forall>n\<ge>N.  norm ((scaleC a) (x n) - (scaleC a) l ) < (cmod a) * ((cmod (inverse a)) * e)\<close>
      using \<open>a \<noteq> 0\<close>
      by auto 
    moreover have \<open>(cmod a) * (cmod (inverse a)) = 1\<close>
      using \<open>a \<noteq> 0\<close>
      by (metis norm_mult norm_one right_inverse)      
    ultimately have \<open>\<forall>e>0.\<exists>N.\<forall>n\<ge>N.  norm ((scaleC a) (x n) - (scaleC a) l ) <  e\<close>
      by (simp add: ordered_field_class.sign_simps(5) ordered_field_class.sign_simps(6))
    thus ?thesis
      using LIMSEQ_iff by auto 
  qed
  thus ?thesis
    by (simp add: continuous_at_sequentiallyI) 
qed


*)

lemma closed_scaleC: 
  fixes S::\<open>'a::complex_normed_vector set\<close> and a :: complex
  assumes \<open>closed S\<close>
  shows \<open>closed (scaleC a ` S)\<close>
proof (cases \<open>S = {}\<close>)
  case True
  thus ?thesis
    by simp 
next
  case False
  hence \<open>S \<noteq> {}\<close> by blast
  show ?thesis
  proof(cases \<open>a = 0\<close>)
    case True
    have \<open>scaleC a ` S = {0}\<close>
      using \<open>a = 0\<close> \<open>S \<noteq> {}\<close> by auto 
    thus ?thesis using Topological_Spaces.t1_space_class.closed_singleton
      by simp
  next
    case False
    hence \<open>a \<noteq> 0\<close>
      by blast
    have \<open>\<forall>n. x n \<in> (scaleC a ` S) \<Longrightarrow> x \<longlonglongrightarrow> l \<Longrightarrow> l \<in> (scaleC a ` S)\<close>
      for x::\<open>nat \<Rightarrow> 'a\<close> and l::'a
    proof-
      assume \<open>\<forall>n. x n \<in> (scaleC a ` S)\<close>
      hence \<open>\<forall>n. \<exists>t. x n = scaleC a t\<close>
        by auto
      hence \<open>\<exists>t. \<forall>n. x n = scaleC a (t n)\<close>
        by metis
      then obtain t where \<open>x n = scaleC a (t n)\<close> and \<open>t n \<in> S\<close>
        for n
        using \<open>a \<noteq> 0\<close> \<open>\<forall>n. x n \<in> (*\<^sub>C) a ` S\<close> by fastforce      
      hence \<open>\<forall>n. t n = scaleC (inverse a) (x n)\<close>
        by (simp add: \<open>a \<noteq> 0\<close>)
      assume \<open>x \<longlonglongrightarrow> l\<close>
      moreover have \<open>isCont (\<lambda> v. scaleC (inverse a) v) l\<close>
        using isCont_scaleC by auto
      ultimately have \<open>((\<lambda> v. scaleC (inverse a) v) \<circ> x) \<longlonglongrightarrow> (\<lambda> v. scaleC (inverse a) v) l\<close>
        using Elementary_Topology.continuous_at_sequentially
        by auto
      moreover have \<open>(\<lambda> v. scaleC (inverse a) v) \<circ> x = t\<close>
      proof-
        have \<open>(\<lambda> v. scaleC (inverse a) v) \<circ> x = (\<lambda> n. scaleC (inverse a) (x n))\<close>
          by auto
        thus ?thesis using \<open>\<forall>n. t n = scaleC (inverse a) (x n)\<close>
          by auto
      qed
      ultimately have \<open>t \<longlonglongrightarrow> (\<lambda> v. scaleC (inverse a) v) l\<close>
        by simp
      hence \<open>t \<longlonglongrightarrow> (scaleC (inverse a) l)\<close>
        by simp      
      hence \<open>(scaleC (inverse a) l) \<in> S\<close>
        using \<open>closed S\<close> \<open>\<And>n. t n \<in> S\<close> closed_sequentially by auto      
      hence \<open>(scaleC a) (scaleC (inverse a) l) \<in> (scaleC a) ` S\<close>
        by blast
      moreover have \<open>(scaleC a) (scaleC (inverse a) l) = l\<close>
        by (simp add: \<open>a \<noteq> 0\<close>)
      ultimately show ?thesis by simp
    qed
    thus ?thesis using Elementary_Topology.closed_sequential_limits
      by blast
  qed

qed


lemma closure_scaleC: 
  fixes S::\<open>'a::complex_normed_vector set\<close>
  shows \<open>closure (scaleC a ` S) = scaleC a ` closure S\<close>
proof
  have \<open>closed (closure S)\<close>
    by simp
  show "closure ((*\<^sub>C) a ` S) \<subseteq> (*\<^sub>C) a ` closure S"
    by (simp add: closed_scaleC closure_minimal closure_subset image_mono)    
  show "(*\<^sub>C) a ` closure S \<subseteq> closure ((*\<^sub>C) a ` S)"
  proof
    show "x \<in> closure ((*\<^sub>C) a ` S)"
      if "x \<in> (*\<^sub>C) a ` closure S"
      for x :: 'a
    proof-
      obtain t where \<open>x = ((*\<^sub>C) a) t\<close> and \<open>t \<in> closure S\<close>
        using \<open>x \<in> (*\<^sub>C) a ` closure S\<close> by auto
      have \<open>\<exists>s. (\<forall>n. s n \<in> S) \<and> s \<longlonglongrightarrow> t\<close>
        using \<open>t \<in> closure S\<close> Elementary_Topology.closure_sequential
        by blast
      then obtain s where \<open>\<forall>n. s n \<in> S\<close> and \<open>s \<longlonglongrightarrow> t\<close>
        by blast
      have \<open>(\<forall> n. scaleC a (s n) \<in> ((*\<^sub>C) a ` S))\<close>
        using \<open>\<forall>n. s n \<in> S\<close> by blast
      moreover have \<open>(\<lambda> n. scaleC a (s n)) \<longlonglongrightarrow> x\<close>
      proof-
        have \<open>isCont (scaleC a) t\<close>
          using isCont_scaleC by blast
        thus ?thesis
          using  \<open>s \<longlonglongrightarrow> t\<close>  \<open>x = ((*\<^sub>C) a) t\<close>
          by (simp add: isCont_tendsto_compose)
      qed
      ultimately show ?thesis using Elementary_Topology.closure_sequential 
        by metis
    qed
  qed
qed

lemma onorm_scalarC:
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector\<close>
  assumes \<open>bounded_clinear f\<close>
  shows  \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (cmod r) * onorm f\<close>
proof-
  have \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (SUP x. norm ( (\<lambda> t. r *\<^sub>C (f t)) x) / norm x)\<close>
    by (simp add: onorm_def)
  hence \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (SUP x. (cmod r) * (norm (f x)) / norm x)\<close>
    by simp
  also have \<open>... = (cmod r) * (SUP x. (norm (f x)) / norm x)\<close>
  proof-
    have \<open>{(norm (f x)) / norm x | x. True} \<noteq> {}\<close>
      by blast      
    moreover have \<open>bdd_above {(norm (f x)) / norm x | x. True}\<close>
    proof-
      have \<open>(norm (f x)) / norm x \<le> onorm f\<close>
        for x
        using \<open>bounded_clinear f\<close>
        by (simp add: bounded_clinear.bounded_linear le_onorm)        
      thus ?thesis
        by fastforce 
    qed
    moreover have \<open>mono ((*) (cmod r))\<close>
      by (simp add: monoI ordered_comm_semiring_class.comm_mult_left_mono)      
    moreover have \<open>continuous (at_left (Sup {(norm (f x)) / norm x | x. True})) ((*) (cmod r))\<close>
    proof-
      have \<open>continuous_on UNIV ( (*) w ) \<close>
        for w::real
        by simp
      hence \<open>isCont ( ((*) (cmod r)) ) x\<close>
        for x
        by simp    
      thus ?thesis using Elementary_Topology.continuous_at_imp_continuous_within
        by blast  
    qed
    ultimately have \<open>Sup {((*) (cmod r)) ((norm (f x)) / norm x) | x. True}
         = ((*) (cmod r)) (Sup {(norm (f x)) / norm x | x. True})\<close>
      by (simp add: continuous_at_Sup_mono full_SetCompr_eq image_image)      
    hence  \<open>Sup {(cmod r) * ((norm (f x)) / norm x) | x. True}
         = (cmod r) * (Sup {(norm (f x)) / norm x | x. True})\<close>
      by blast
    moreover have \<open>Sup {(cmod r) * ((norm (f x)) / norm x) | x. True}
                = (SUP x. cmod r * norm (f x) / norm x)\<close>
      by (simp add: full_SetCompr_eq)            
    moreover have \<open>(Sup {(norm (f x)) / norm x | x. True})
                = (SUP x. norm (f x) / norm x)\<close>
      by (simp add: full_SetCompr_eq)      
    ultimately show ?thesis
      by simp 
  qed
  finally show ?thesis
    by (simp add: onorm_def) 
qed

lemma bounded_clinearDiff: \<open>clinear A \<Longrightarrow> clinear B \<Longrightarrow> clinear (A - B)\<close>
  by (smt add_diff_add additive.add clinear.axioms(1) clinear.axioms(2) clinearI clinear_axioms_def complex_vector.scale_right_diff_distrib minus_apply)

lemma scalarR_bounded_clinear:
  fixes c :: real
  assumes \<open>bounded_clinear f\<close>
  shows \<open>bounded_clinear (\<lambda> x. c *\<^sub>R f x )\<close>
proof-
  have  \<open>bounded_clinear (\<lambda> x. (complex_of_real c) *\<^sub>C f x )\<close>
    by (simp add: assms bounded_clinear_const_scaleC)
  thus ?thesis
    by (simp add: scaleR_scaleC) 
qed

lemma bounded_linear_bounded_clinear:
  \<open>bounded_linear A \<Longrightarrow> \<forall>c x. A (c *\<^sub>C x) = c *\<^sub>C A x \<Longrightarrow> bounded_clinear A\<close>
  proof
  show "A (x + y) = A x + A y"
    if "bounded_linear A"
    for x :: 'a
      and y :: 'a
    using that unfolding bounded_linear_def linear_def Vector_Spaces.linear_def 
      module_hom_def module_hom_axioms_def by blast
  show "A (r *\<^sub>C x) = r *\<^sub>C A x"
    if  "\<forall>c x. A (c *\<^sub>C x) = c *\<^sub>C A x"
    for r :: complex
      and x :: 'a
    using that by blast
  show "\<exists>K. \<forall>x. norm (A x) \<le> norm x * K"
    if "bounded_linear A"
    using that unfolding bounded_linear_def bounded_linear_axioms_def by blast
qed

end