theory HOLAnalysisVectorsMess
  imports Complex_Main "HOL-Analysis.Analysis"

begin

(* we'll try to define r^3 in terms of some stuff in HOL-Analysis *)

type_synonym pt = "(real, 3) vec"

(* "(real, 3) vec" is the Manuel Eberl-endorsed[1] way to define the vector space R^3.
   
   Hooray!

   [1]: https://stackoverflow.com/questions/43052941/convergence-and-vectors-theories *)

(* ... and it has the right cardinality *)
lemma "CARD(pt) = CARD(real) ^ 3"
  by simp

(* Can we add things? *)

lemma "(0 :: pt) + (p :: pt) = (p :: pt)"
  by simp

lemma "(p :: pt) - p = 0"
  by simp

(* I guess we can! Can we multiply points by scalars? *)
lemma "(a :: pt) + a = 2 * a"
  by simp

lemma "(a :: pt) + a = 2 *s a"
  by (smt add_diff_cancel minus_add_cancel vector_sadd_rdistrib vector_sneg_minus1)

lemma "(a :: pt) + a = 2 *\<^sub>R a"
  by (simp add: scaleR_2)

lemma "(a :: pt) + a = scaleR 2 a"
  by (simp add: scaleR_2)

(* Which of these is the right way to do things? Not sure, but definitely not the
   first one. On closer inspection, it's interpreting 2 as a pt! *)

lemma "(a :: pt) + a = (2 :: pt) * a" (*    2 is a point? Isabelle is happy :)    *)
  by simp

value "(2 :: real) * (a :: pt)" (*    2 is a real? Isabelle is sad :(    *)

(* By the way, turns out 2 is the vector where all its coordinates are 2.
   I'll spare you the details.*)

(* Can we say something about norms? This one is cribbed from HOL-Analysis.
   Presumably \<bar>a\<bar> means absolute value. *)
lemma "norm (scaleR a x) = \<bar>a\<bar> * norm x"
  by simp

(* Putting it all together to show something about the norm
   of a vector: *)
lemma double_norm:
  assumes "norm (i :: pt) = 1"
  shows "norm (i + i) = 2"
proof -
  have "(i :: pt) + i = scaleR 2 i" (* showed this earlier *)
    by (simp add: scaleR_2)
  then show ?thesis using assms by simp
qed




(* It would be nice to get the x, y, and z coordinates of a pt.
   
   Or does that just ensure we'll have to write the same logic
   three times to prove anything? Maybe we should never even
   think about individual coordinates.

   On the other hand, I've already written a lot of theorems
   that work with functions pt_x, pt_y, and pt_z. If we could
   redefine those, maybe we could reuse a bunch of stuff. *)

definition pt_x where "pt_x (p :: pt) = p $ 1"
definition pt_y where "pt_y (p :: pt) = p $ 2"
definition pt_z where "pt_z (p :: pt) = p $ 3"

(* "p $ n", a.k.a. vec_nth, gets the nth coordinate of p *)

(* What can we show about coordinates? *)

(* if two points are equal, they have equal x, y, and z coordinates *)
lemma pt_eq1: "(p :: pt) = (q :: pt) \<Longrightarrow> pt_x p = pt_x q \<and> pt_y p = pt_y q \<and> pt_z p = pt_z q"
  by simp

(* if two points have equal x, y, and z coordinates, they are equal *)
lemma pt_eq2: "pt_x (p :: pt) = pt_x (q :: pt) \<and> pt_y p = pt_y q \<and> pt_z p = pt_z q \<Longrightarrow> p = q"
  nitpick
  oops

(* Wait, what!?

   When we defined pt to be (real, 3) vec, that said that the indices are of
   type 3. What is type 3? *)

value "0 :: 3"
value "1 :: 3"
value "2 :: 3"
value "3 :: 3"
value "101 :: 3"

(* Looks like integers mod 3.

   Turns out, the counterexample nitpick found to pt_eq2 IS spurious
   (I think), but we have to show this: *)

lemma "(n :: 3) = 1 \<or> n = 2 \<or> n = 3"
  oops

(* Fortunately, this lemma is provided to us in the Cartesian_Space theory,
   under the subheading "Lemmas for working on \<open>real^1/2/3/4\<close>". It's
   called exhaust_3. *)

(* for convenience *)
lemma [simp]: "pt_x p = p $ 1" using pt_x_def by auto
lemma [simp]: "pt_y p = p $ 2" using pt_y_def by auto
lemma [simp]: "pt_z p = p $ 3" using pt_z_def by auto

lemma pt_eq2:
  assumes "pt_x (p :: pt) = pt_x (q :: pt)"
    and "pt_y p = pt_y q"
    and "pt_z p = pt_z q"
  shows "p = q"
proof -
  have "\<forall>(n :: 3). p $ n = q $ n"
  proof -
    fix n :: 3
    have "n = 1 \<or> n = 2 \<or> n = 3" using exhaust_3 by simp
    then show ?thesis using assms
      by (metis (mono_tags, lifting) exhaust_3 pt_x_def pt_y_def pt_z_def)
  qed
  then show ?thesis by (simp add: vec_eq_iff)
qed

(* Great! Now we have concise formulation of pt equality: *)
lemma pt_coord_eq: "(p :: pt) = (q :: pt) \<longleftrightarrow> pt_x p = pt_x q \<and> pt_y p = pt_y q \<and> pt_z p = pt_z q"
  using pt_eq1 pt_eq2 by auto

(* what can we say about the standard basis? *)

definition i :: pt where "i = axis 1 1"
definition j :: pt where "j = axis 2 1"
definition k :: pt where "k = axis 3 1"

lemma "norm i = 1"
  by (simp add: i_def)

lemma "pt_x ((i + j + k) :: pt) = 1"
  by (smt pt_x_def axis_nth cart_eq_inner_axis cross_basis(3) cross_basis(5) dot_cross_self(2)
      dot_cross_self(3) i_def j_def k_def vector_add_component)
(* That's an ugly one.  *)

(* Sum of i, j, k is 1 in every coordinate: *)
lemma "((i + j + k) :: pt) $ n = 1"
  (is "?s $ n = 1")
  oops

(* This is harder. Help it along with a lot of basic rules... *)
lemma [simp]: "i $ (1 :: 3) = 1" by (simp add: i_def)
lemma [simp]: "i $ (2 :: 3) = 0" by (simp add: cart_eq_inner_axis inner_axis_axis i_def)
lemma [simp]: "i $ (3 :: 3) = 0" by (simp add: cart_eq_inner_axis inner_axis_axis i_def)

lemma [simp]: "j $ (1 :: 3) = 0" by (simp add: cart_eq_inner_axis inner_axis_axis j_def)
lemma [simp]: "j $ (2 :: 3) = 1" by (simp add: cart_eq_inner_axis inner_axis_axis j_def)
lemma [simp]: "j $ (3 :: 3) = 0" by (simp add: cart_eq_inner_axis inner_axis_axis j_def)

lemma [simp]: "k $ (1 :: 3) = 0" by (simp add: cart_eq_inner_axis inner_axis_axis k_def)
lemma [simp]: "k $ (2 :: 3) = 0" by (simp add: cart_eq_inner_axis inner_axis_axis k_def)
lemma [simp]: "k $ (3 :: 3) = 1" by (simp add: cart_eq_inner_axis inner_axis_axis k_def)

(* now both lemmas are easier! *)
lemma "((i + j + k) :: pt) $ 1 = 1"
  by simp

lemma "((i + j + k) :: pt) $ n = 1"
  (is "?s $ n = 1")
proof -
  have ns: "n = 1 \<or> n = 2 \<or> n = 3" using exhaust_3 by simp
  show ?thesis using ns by auto
qed

(* Maybe adding so many rules to simp will bog it down later --
   I have no idea, since I haven't had time to prove anything
   else yet! *)

(* NOTE: pt_x, etc. are 1-indexed because that's how exhaust_3 does it *)





(* Now for the good stuff! cross product *)

definition scmult :: "pt \<Rightarrow> pt \<Rightarrow> bool" where
  "scmult P Q = (\<exists>s. s \<noteq> 0 \<and> P = scaleR s Q)"

lemma "scale_inv":
  assumes "r \<noteq> 0"
  shows "scaleR (1/r) (scaleR r x :: pt) = x"
  by (simp add: assms)

lemma "scale_flip":
  fixes a :: pt and b :: pt
  assumes "m \<noteq> 0"
    and "a = scaleR m b"
  shows "b = scaleR (1/m) a"
  by (simp add: assms)

lemma scmult_sym_help:
  fixes a :: pt fixes b :: pt
  assumes "(scmult a b)"
  shows "(scmult b a)"
proof-
  from assms obtain m where m: "a = scaleR m b \<and> m \<noteq> 0"
    using scmult_def by auto
  then have p1: "b = scaleR (1/m) a"
    using scale_flip assms by auto
  then show ?thesis
    using m scmult_def one_divide_eq_0_iff by blast
qed

lemma scmult_sym: "symp scmult"
  using scmult_sym_help by standard

lemma "scmult (scaleR 2 i) i"
proof -
  have "(2 :: real) \<noteq> 0" by simp
  then show ?thesis using scmult_def by blast
qed

lemma scmult_ref: "reflp scmult"
  using reflp_def scmult_def by force

lemma scmult_trans_help:
  fixes a :: pt fixes b :: pt fixes c :: pt
  assumes "(scmult a b)"
      and "(scmult b c)"
  shows "(scmult a c)"
proof-
  from assms obtain m1 where m1: "a = scaleR m1 b \<and> m1 \<noteq> 0"
    using scmult_def by auto
  from assms obtain m2 where m2: "b = scaleR m2 c \<and> m2 \<noteq> 0"
    using scmult_def by auto
  then have "m1 * m2 \<noteq> 0 \<and> a = scaleR (m1 * m2) c"
    using m1 m2 by simp
  then show ?thesis using scmult_def by blast
qed

lemma scmult_trans: "transp scmult"
  using transp_def scmult_trans_help by blast

lemma scmult_nz:
  assumes "scmult a b" and "a = 0 \<or> b = 0"
  shows "a = 0 \<and> b = 0"
proof -
  from assms obtain m where m: "a = scaleR m b \<and> m \<noteq> 0"
    using scmult_def by auto
  then show ?thesis using assms(2) scale_eq_0_iff by blast
qed

lemma "\<not>(scmult i j)"
  (* good enough for me *)
  by (smt axis_eq_0_iff cross_basis(1) cross_mult_left cross_refl cross_zero_right i_def j_def scmult_def)

definition construct_pt :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> pt" where
  "construct_pt a b c = (\<chi> i. if i = 1 then a
                             else if i = 2 then b
                             else if i = 3 then c
                             else -1)"
  (*by auto*)

lemma construct_pt_inv_x: "pt_x (construct_pt x y z) = x"
  using pt_x_def construct_pt_def by simp
lemma construct_pt_inv_y: "pt_y (construct_pt x y z) = y"
  using pt_z_def construct_pt_def by simp
lemma construct_pt_inv_z: "pt_z (construct_pt x y z) = z"
  using pt_y_def construct_pt_def by simp


lemma construct_pt_inv_1: "(construct_pt x y z) $ 1 = x"
  using pt_x_def construct_pt_def by simp
lemma construct_pt_inv_2: "(construct_pt x y z) $ 2 = y"
  using pt_z_def construct_pt_def by simp
lemma construct_pt_inv_3: "(construct_pt x y z) $ 3 = z"
  using pt_y_def construct_pt_def by simp

lemma scmult_constr_distr: "r *\<^sub>R construct_pt a b c = construct_pt (r * a) (r * b) (r * c)"
  (is "?LHS = ?RHS")
proof -
  have "?LHS $ q = r * ((construct_pt a b c) $ q)"
    using construct_pt_def scaleR_vec_def by auto
  have "... = ?RHS $ q"
    using exhaust_3 construct_pt_def scaleR_vec_def by auto
  then have "?LHS $ q = ?RHS $ q" by auto
  then have "\<forall>q. ?LHS $ q = ?RHS $ q" (* WHYYYYYY??? is this so hard *)
    using exhaust_3 by (smt construct_pt_inv_x construct_pt_inv_y construct_pt_inv_z pt_x_def pt_y_def pt_z_def real_scaleR_def vector_scaleR_component)
  then show ?thesis using vec_eq_iff by blast
qed

lemma sum_scale: "(\<Sum>(i :: real) \<in>UNIV. m * (f i)) = m * (\<Sum>(i :: real)\<in>UNIV. (f i))"
  (*by (metis sum.cong vector_space_over_itself.scale_sum_right)*)
  sorry

(*lemma scmult_nz:
  assumes "scmult a b"
  shows "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0"
proof -
  have "scmult a b \<Longrightarrow> a \<noteq> 0"
  proof -
    assume b0: "b = 0"
    from assms obtain m where m: "a = scaleR m b \<and> m \<noteq> 0"
      using scmult_def by auto
    have "a = 0"
      by (simp add: m b0)
    have "a \<noteq> 0"
    proof -
      
    qed
  qed
qed*)

lemma dot: "inner a b = (pt_x a) * (pt_x b)
                             + (pt_y a) * (pt_y b)
                             + (pt_z a) * (pt_z b)"
  (is "inner a b = ?dot_formula a b")
  by (simp add: inner_vec_def sum_3)

lemma scmult_inner:
  assumes "scmult a b"
    and "b \<noteq> 0"
  shows "inner a b \<noteq> 0"
proof -
  from assms obtain m where m: "a = scaleR m b \<and> m \<noteq> 0"
    using scmult_def by auto
  have r1: "pt_x a = m * pt_x b"
    by (simp add: m)
  have r2: "pt_y a = m * pt_y b"
    by (simp add: m)
  have r3: "pt_z a = m * pt_z b"
    by (simp add: m)

  have rep: "inner a b = pt_x a * pt_x b + pt_y a * pt_y b + pt_z a * pt_z b"
    using dot by simp
  then have "... = m * pt_x b * pt_x b + m * pt_y b * pt_y b + m * pt_z b * pt_z b"
    using rep r1 r2 r3 by simp
  then have "... = m * inner b b"
    using inner_vec_def sum_3 m rep by auto
  then show "inner a b \<noteq> 0"
    using assms m by simp
qed

  (*from assms obtain m where m: "a = scaleR m b \<and> m \<noteq> 0"
    using scmult_def by auto
  then have "inner a b = (\<Sum>i\<in>UNIV. (scaleR m b) $ i \<bullet> b $ i)" 
    using inner_vec_def by blast
  then have "... = (\<Sum>i\<in>UNIV. m * (b $ i) * (b $ i))"
    by simp
  let ?f = "\<lambda>i. (b $ i) * (b $ i)"
  have "(\<Sum>i\<in>UNIV. m * (?f i)) = m * (\<Sum>i\<in>UNIV. (?f i))"
    using sum_scale by (smt inner_real_def inner_sum_right sum_3)*)
  
(* try a proof with lemma "dot" *)

(* define dot product on pts*)
(*definition dot :: "pt \<Rightarrow> pt \<Rightarrow> real" where
  "dot a b = (pt_x a) * (pt_x b) + (pt_y a) * (pt_y b) + (pt_z a) * (pt_z b)"
*)

(*
lemma dot:
  fixes dot :: "pt \<Rightarrow> pt \<Rightarrow> real"
  assumes "dot = (\<lambda> a b. (pt_x a) * (pt_x b)
                           + (pt_y a) * (pt_y b)
                           + (pt_z a) * (pt_z b))"
  shows "inner = dot"
proof -
  have "dot = (\<lambda>x y. \<Sum>(i :: 3)\<in>UNIV. x $ i \<bullet> y $ i)"
    unfolding assms pt_x_def pt_y_def pt_z_def by (simp add: sum_3)
  then show ?thesis unfolding inner_vec_def by simp
qed*)

(*
proof -
  have "inner = ?dot_formula"
  proof -
    have "?dot_formula = (\<lambda>x y. \<Sum>(i :: 3)\<in>UNIV. x $ i \<bullet> y $ i)"
      unfolding pt_x_def pt_y_def pt_z_def by (simp add: sum_3)
    then show ?thesis unfolding inner_vec_def by simp
  qed
  then show ?thesis by metis
qed
*)

(*
(* inner_commute *)
lemma dot_sym: "(dot a b) = (dot b a)"
  by (simp add: dot_def)

(* inner_scaleR_left *)
lemma dot_homogeneous:
  fixes a :: pt and b :: pt
  fixes m :: real
  assumes m_nz: "m \<noteq> 0"
  shows "(dot (m *\<^sub>R a) b) = m * (dot a b)"
proof -
  have p1: "(dot (m *\<^sub>R a) b) = m * (pt_x a * pt_x b + pt_y a * pt_y b + pt_z a * pt_z b)" (* (m * pt_x a) * pt_x b + (m * pt_y a) + pt_y b + (m * pt_z a) + pt_z b*)
    unfolding dot_def
    apply simp
    by argo
  have p2: "... = m * (dot a b)"
    using dot_def by simp
  then show ?thesis using p1 p2 by auto
qed

(* inner_add_left *)
lemma dot_scalar: "dot (a + b) c = dot a c + dot b c"
  unfolding dot_def
  apply simp
  by argo
*)

(*
definition perp :: "pt \<Rightarrow> pt \<Rightarrow> bool" where
  "perp a b \<longleftrightarrow> a \<noteq> 0 \<and> b \<noteq> 0 \<and> inner a b = 0" *)

(* orthogonal_commute
lemma perp_sym: "symp perp"
  using perp_def by (simp add: inner_commute symp_def) *)

lemma scmult_preserves_orthog:
  assumes "orthogonal a1 b" and "scmult a1 a2"
  shows "orthogonal a2 b"
  using assms orthogonal_clauses scmult_def by auto

lemma orthog_scmult:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
  shows "orthogonal a b \<longrightarrow> \<not>(scmult a b)"
proof -
  have "scmult a b \<Longrightarrow> \<not>(orthogonal a b)"
  proof -
    assume a1: "scmult a b"
    then have "a \<noteq> 0 \<and> b \<noteq> 0" using scmult_nz assms by blast
    then have "inner a b \<noteq> 0" using scmult_inner a1 by auto
    then show "\<not>(orthogonal a b)" using orthogonal_def by auto
  qed
  then show ?thesis by auto
qed
(*
lemma perp_scmult: "perp a b \<longrightarrow> \<not>(scmult a b)"
proof -
  have "scmult a b \<Longrightarrow> \<not>(perp a b)"
  proof (cases "b = 0")
    case True
    then show ?thesis using perp_def by auto
  next
    case False
    assume a1: "scmult a b"
    assume a2: "b \<noteq> 0"
    then have "inner a b \<noteq> 0" using scmult_inner a1 a2 by auto
    then show "\<not>(perp a b)" using perp_def by auto
  qed
  then show ?thesis by auto
qed*)

(* also useful: norm_eq_sqrt_inner*)

definition cross_x :: "pt \<Rightarrow> pt \<Rightarrow> real" where
  "cross_x P Q = (pt_y P) * (pt_z Q) - (pt_z P) * (pt_y Q)"

definition cross_y :: "pt \<Rightarrow> pt \<Rightarrow> real" where
  "cross_y P Q = (pt_z P) * (pt_x Q) - (pt_x P) * (pt_z Q)"

definition cross_z :: "pt \<Rightarrow> pt \<Rightarrow> real" where
  "cross_z P Q = (pt_x P) * (pt_y Q) - (pt_y P) * (pt_x Q)"

definition cross :: "pt \<Rightarrow> pt \<Rightarrow> pt" where
  "cross P Q = (construct_pt (cross_x P Q) (cross_y P Q) (cross_z P Q))"

lemma cross_x_scale: "m * (cross_x A B) = cross_x (m *\<^sub>R A) B"
  using cross_x_def apply simp
  by argo

lemma cross_y_scale: "m * (cross_y A B) = cross_y (m *\<^sub>R A) B"
  using cross_y_def apply simp
  by argo

lemma cross_z_scale: "m * (cross_z A B) = cross_z (m *\<^sub>R A) B"
  using cross_z_def apply simp
  by argo

lemma cross_homog: "cross (m *\<^sub>R A) B = m *\<^sub>R (cross A B)"
proof -
  have p1: "m *\<^sub>R (cross A B) = construct_pt (m * cross_x A B)
     (m * cross_y A B) (m * cross_z A B)"
    using scmult_constr_distr cross_def by simp
  then have p2: "... = (construct_pt (cross_x (m *\<^sub>R A) B) (cross_y (m *\<^sub>R A) B) (cross_z (m *\<^sub>R A) B))"
    unfolding cross_def construct_pt_def
    using cross_x_scale cross_y_scale cross_z_scale by auto
  then have "... = cross (m *\<^sub>R A) B" using cross_def by simp
  then show ?thesis using p1 p2 by simp
qed
 

lemma cross_neg_sym: "cross A B = -1 *\<^sub>R (cross B A)"
proof -
  have x: "cross_x A B = -(cross_x B A)" using cross_x_def by simp
  have y: "cross_y A B = -(cross_y B A)" using cross_y_def by simp
  have z: "cross_z A B = -(cross_z B A)" using cross_z_def by simp

  (* I suspect there's some logic duplicated here with cross_homog *)
  have p1: "-1 *\<^sub>R (cross B A) = construct_pt (- cross_x B A)
     (- cross_y B A) (- cross_z B A)"
    using scmult_constr_distr cross_def by simp
  then have p2: "... = (construct_pt (cross_x A B) (cross_y A B) (cross_z A B))"
    unfolding cross_def construct_pt_def x y z by simp
  then have "... = cross A B" using cross_def by simp
  then show ?thesis using p1 p2 by simp
qed

(* corollary: *)
lemma cross_neg: "cross A B = cross (-1 *\<^sub>R B) A"
proof -
  have p1: "cross A B = -1 *\<^sub>R cross B A"
    using cross_neg_sym by blast
  then have p2: "... = cross (-1 *\<^sub>R B) A" using cross_homog
    by presburger (* WHY IS THIS SO @$(&*%^ HARD? *)
  then show ?thesis using p1 p2 by auto
qed

lemma cross_refl_zero: "cross A A = 0"
  unfolding cross_def cross_x_def cross_y_def cross_z_def
  apply (simp add: construct_pt_def zero_vec_def)
  using exhaust_3 by metis

lemma pt_zero_iff_coord: "A = 0 \<longleftrightarrow> pt_x A = 0 \<and> pt_y A = 0 \<and> pt_z A = 0"
  unfolding zero_vec_def
  using exhaust_3 pt_coord_eq by auto

lemma cross_zero_iff_scmult: "cross A B = 0 \<longleftrightarrow> scmult A B"
proof -
  have rtl: "scmult A B \<Longrightarrow> cross A B = 0"
  proof -
    assume "scmult A B"
    then obtain m where m: "m \<noteq> 0 \<and> A = scaleR m B"
      using scmult_def by blast
    then have "cross A B = cross (scaleR m B) B" by simp
    then have "cross A B = 0"
      using cross_homog cross_refl_zero by simp
    then show ?thesis by auto
  qed

  have ltr: "cross A B = 0 \<Longrightarrow> scmult A B"
  proof -
    assume "cross A B = 0"
    then have "cross_x A B = 0 \<and> cross_y A B = 0 \<and> cross_z A B = 0"
      using cross_def pt_zero_iff_coord
        construct_pt_inv_x construct_pt_inv_y construct_pt_inv_z by auto
    (* uuuuuugh *)
    then show ?thesis sorry
  qed

  from ltr rtl show ?thesis by auto
qed

lemma cross_scmult_sym: "scmult (cross A B) (cross B A)"
  using cross_neg_sym scmult_def by smt

(* unneeded proof for cross_scmult_sym:
proof (cases "scmult A B")
  case True
  have "(cross A B) = 0 \<and> (cross B A) = 0"
    using True cross_zero_iff_scmult scmult_sym_help by simp
  then show ?thesis using scmult_def by auto
next
  case False
  then show ?thesis
    unfolding cross_def
    unfolding cross_x_def cross_y_def cross_z_def
qed *)

lemma cross_sym_preserves_orthog:
  assumes "orthogonal (cross A B) C"
  shows "orthogonal (cross B A) C"
proof -
  have "scmult (cross A B) (cross B A)" using cross_scmult_sym by auto
  then show ?thesis using scmult_preserves_orthog assms by blast
qed

lemma not_scmult_nz: "\<not>(scmult A B) \<Longrightarrow> A \<noteq> 0 \<and> B \<noteq> 0"
  by (metis cross_homog cross_neg cross_zero_iff_scmult scale_eq_0_iff)

lemma cross_orthog1:
  assumes "\<not>(scmult A B)"
  shows "orthogonal A (cross A B)"
proof -
  have p0: "A \<bullet> (cross A B) = pt_x A * (cross_x A B) + pt_y A * (cross_y A B) + pt_z A * (cross_z A B)"
    unfolding cross_def construct_pt_def
    by (simp add: dot)
  then have p1: "... = pt_x A * pt_y A * pt_z B - pt_x A * pt_y A * pt_z B
                 + pt_y A * pt_z A * pt_x B - pt_y A * pt_z A * pt_x B
                 + pt_z A * pt_x A * pt_y B - pt_z A * pt_x A * pt_y B"
    unfolding cross_x_def cross_y_def cross_z_def by argo
  then have goal: "A \<bullet> (cross A B) = 0" using p0 p1 by simp
  have nz: "A \<noteq> 0 \<and> (cross A B) \<noteq> 0"
    using not_scmult_nz assms cross_zero_iff_scmult by auto
  show ?thesis using goal orthogonal_def by auto
qed

lemma cross_orthog2:
  assumes "\<not>scmult A B"
  shows "orthogonal B (cross A B) "
proof -
  have "\<not>scmult B A" using assms scmult_sym_help by blast
  then have "orthogonal B (cross B A)" using cross_orthog1 by auto
  then show ?thesis using cross_sym_preserves_orthog by (meson orthogonal_commute sympD)
qed











definition TT:: "pt \<Rightarrow> pt \<Rightarrow> pt \<Rightarrow> pt \<Rightarrow> pt" where
  "TT a b c p =  (p $ 1) *\<^sub>R a + (p $ 2) *\<^sub>R b + (p $ 3) *\<^sub>R c"

lemma cross_orthog_norm:
  assumes "orthogonal A B"
  shows "norm (cross A B) = norm A * norm B"
  unfolding cross_def
proof (cases "A = 0 \<and> B = 0")
  case True
  have "norm (cross A B) = 0" by (simp add: True cross_refl_zero)
  then have ?thesis using True by simp
next
  case False
  have "\<not>(scmult A B)" using assms False by (simp add: orthog_scmult)
  have "inner A A * inner B B = inner (cross A B) (cross A B)"
  proof -
    have "inner A A * inner B B = (A $ 1 * A $ 1 + A $ 2 * A $ 2 + A $ 3 * A $ 3) *
  (B $ 1 * B $ 1 + B $ 2 * B $ 2 + B $ 3 * B $ 3)"
      by (simp add: dot)
    have "inner (cross A B) (cross A B) =
  (A $ 2 * B $ 3 - A $ 3 * B $ 2) * (A $ 2 * B $ 3 - A $ 3 * B $ 2) +
  (A $ 3 * B $ 1 - A $ 1 * B $ 3) * (A $ 3 * B $ 1 - A $ 1 * B $ 3) +
  (A $ 1 * B $ 2 - A $ 2 * B $ 1) * (A $ 1 * B $ 2 - A $ 2 * B $ 1)"
      by (simp add: cross_def cross_x_def cross_y_def cross_z_def
          dot construct_pt_inv_1 construct_pt_inv_2 construct_pt_inv_3)
    have "... = (A $ 1 * A $ 1 + A $ 2 * A $ 2 + A $ 3 * A $ 3) *
  (B $ 1 * B $ 1 + B $ 2 * B $ 2 + B $ 3 * B $ 3)"
      oops
(* this is actually going to be maybe just as hard as showing
   uniqueness of cross-product, because it involves dealing with
   perpendicularity algebraically *)

(* start with A and B nice (unit vecs, perp) *)
lemma L6a_ijk: (* A,B nice; changing to ABC basis preserves dot prod. *)
  shows "inner (TT i j k v1) (TT i j k v2) = inner v1 v2"
  unfolding TT_def
  by (simp add: dot)

lemma L7:
  assumes "norm A = 1" and "norm B = 1"
    and "perp A B"
  shows "norm (cross A B) = 1"
proof -
  have "inner (cross A B) (cross A B) = 1"
    unfolding cross_def
    apply (simp add: dot)
    apply (simp add: construct_pt_inv_1 construct_pt_inv_2 construct_pt_inv_3)
    unfolding cross_x_def cross_y_def cross_z_def
    sorry
  show ?thesis sorry (* oops, can't do it on paper even *)
qed

lemma "A \<bullet> (B + C) = A \<bullet> B + A \<bullet> C"
  using cross3_simps by auto

(* is this enough? *)

(* start with A and B nice (unit vecs, perp) *)
lemma L6a: (* A,B nice; changing to ABC basis preserves dot prod. *)
  fixes A and B and U and V and C
  assumes "C = cross B A"
  (* stuff above will recur endlessly; stuff below will be reduced gradually *)
  assumes "norm A = 1"
  assumes "norm B = 1"
  assumes "perp A B"
  shows "inner (TT A B C v1) (TT A B C v2) = inner v1 v2"
  unfolding TT_def
  apply (simp add: dot)
proof -
  have "norm C = 1" using assms by (simp add: L7 orthogonal_clauses sympD)
  have "inner (TT A B C v1) (TT A B C v2) =
        (v1 $ 1 * A"
  show ?thesis
  