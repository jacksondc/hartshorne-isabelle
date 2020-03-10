theory Chapter4
  imports Chapter1 Complex_Main


begin
text \<open>
\spike
Soon to be filled in with some Hartshorne text. 

Key idea for this on 3/10: 

If you have a projective plane, defined by meets: points -> lines,
then you can define a NEW set of points:

type_equivalence ppoints = lines

and a new set of lines:

type_equivalence llines = points

in which you swap the role of "point" and "line". We already saw something like this in our 
work on the real projective plane, where I suggested that we could use the type "point" (3-coordinate
homogeneous vector) to represent a line (the "line" defined by "points in the plane orthogonal to the
given "normal" vector). 

With these two "new" types we can define a new "meets" function:

  fun dmeets :: "ppoint \<Rightarrow> lline \<Rightarrow> bool" where
    "dmeets P k = meets k P"

i.e., the "newpoint P" (which is really a line p) meets the "newline l" (which is really a point L)
exactly if L lies on p in our original projective plane. This new function, dmeets, (together with its
domain and codomain) constitutes a projective plane, called the "dual" of the original plane. 

To prove this, we have to (as usual) show the three axioms are true. 

\done\<close>


  locale projective_plane_plus =
    projective_plane meets
  for meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool" 
begin
    definition dmeets 
      where "dmeets P l  \<longleftrightarrow> ( meets l P)" 
(* Goal: to prove the theorem that "dmeets is a projective plane" *)

lemma dmeets_p1a:
  fixes P fixes Q
  assumes "P \<noteq> Q"
  shows "\<exists>l. dmeets P l \<and> dmeets Q l"
proof -
  obtain x where x: "meets x P \<and> meets x Q"
    using assms projective_plane.p2 projective_plane_axioms by fastforce
  have p1: "dmeets P x \<and> dmeets Q x"
    by (simp add: dmeets_def x)
  show ?thesis
    using p1 by blast
qed

lemma dunique_lines: 
  fixes B
  fixes l
  fixes m
  assumes diff:"P \<noteq> B"
  assumes "dmeets P l"
  assumes "dmeets B l"
  assumes "dmeets P m"
  assumes "dmeets B m"
  shows "l = m"
  using dmeets_def assms p1 by blast

lemma "dmeets_p1b": "P \<noteq> Q \<longrightarrow> (\<exists>!l. dmeets P l \<and> dmeets Q l)"
  using dmeets_p1a dunique_lines by blast

lemma "dmeets_p2": "\<forall>l m. l \<noteq> m \<longrightarrow> (\<exists>!P. dmeets P l \<and> dmeets P m)"
  by (simp add: dmeets_def p1)

lemma "dmeets_p3": "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> projective_plane_data.collinear dmeets P Q R"
proof -
  obtain l m n where lmn: "l \<noteq> m \<and> l \<noteq> n \<and> m \<noteq> n \<and> \<not> projective_plane_data.collinear meets l m n"
    using p3 by blast
  obtain P where P: "dmeets P l \<and> dmeets P m"
    using dmeets_p2 lmn by blast
  obtain Q where Q: "dmeets Q m \<and> dmeets Q n"
    using dmeets_p2 lmn by blast
  obtain R where R: "dmeets R n \<and> dmeets R l"
    using dmeets_p2 lmn by blast
  have PQ: "P \<noteq> Q"
    using P Q collinear_def dmeets_def lmn by blast
  have PR: "P \<noteq> R"
    using P R collinear_def dmeets_def lmn by blast
  have RQ: "R \<noteq> Q"
    using R Q collinear_def dmeets_def lmn by blast
  thus ?thesis
    by (smt P Q R dunique_lines lmn projective_plane_data.collinear_def)
qed

lemma "pmeets_p4_dual":
  shows "\<exists>l m n. l \<noteq> m \<and> l \<noteq> n \<and> m \<noteq> n \<and> meets P l \<and> meets P m \<and> meets P n"
proof -
  obtain w where w: "\<not> meets P w"
    by (metis (mono_tags, lifting) dmeets_def dmeets_p3 projective_plane_data.collinear_def)
  obtain X Y Z where xyz: "X \<noteq> Y \<and> X \<noteq> Z \<and> Y \<noteq> Z \<and> meets X w \<and> meets Y w \<and> meets Z w"
    using projective_plane.p4 projective_plane_axioms by blast
  obtain l where l: "meets X l \<and> meets P l"
    by (metis projective_plane.p1 projective_plane_axioms xyz)
  obtain m where m: "meets Y m \<and> meets P m"
    by (metis projective_plane.p1 projective_plane_axioms xyz)
  obtain n where n: "meets Z n \<and> meets P n"
    by (metis projective_plane.p1 projective_plane_axioms xyz)
  have p0: "meets P l \<and> meets P m \<and> meets P n"
    using l m n by simp
  have lm_ne: "l \<noteq> m"
    by (metis (no_types, lifting) w l m projective_plane_axioms projective_plane_def xyz)
  have mn_ne: "m \<noteq> n"
    by (metis (no_types, lifting) w m n projective_plane_axioms projective_plane_def xyz)
  have ln_ne: "l \<noteq> n"
    by (metis (no_types, lifting) w l n projective_plane_axioms projective_plane_def xyz)
  have lmn: "l \<noteq> m \<and> l \<noteq> n \<and> m \<noteq> n"
    using lm_ne ln_ne mn_ne by blast
  have p1: "l \<noteq> m \<and> l \<noteq> n \<and> m \<noteq> n \<and> meets P l \<and> meets P m \<and> meets P n"
    using lmn p0 by simp
  show ?thesis
    using p1 by auto
qed

lemma "pmeets_p4": "\<forall> l. \<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> dmeets P l \<and> dmeets Q l \<and> dmeets R l"
  using pmeets_p4_dual dmeets_def by simp

theorem "projective_plane dmeets"
  by (smt dmeets_p1b dmeets_p2 dmeets_p3 local.pmeets_p4 projective_plane_def)
end



