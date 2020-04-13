theory main imports ZF
begin
(* Main aim is to prove Recursion Theorem *)
(* 
then prove transfinite induction & recursion
then define Von Neumann hierarchy
then prove V=\<Union>(\<alpha>\<in>Ord).V\<alpha>
trying to rewrite everything without replacement
*)

(* Natural numbers are linearly ordered. *)

theorem zeroleq : \<open>\<forall>n\<in>nat. 0\<in>n\<or>0=n\<close>
proof(rule ballI)
  fix n
  assume H1:\<open>n\<in>nat\<close>
  show \<open>0\<in>n\<or>0=n\<close>          
  proof(rule nat_induct[of n])
    from H1 show \<open>n \<in> nat\<close> by assumption
  next
    show \<open>0 \<in> 0 \<or> 0 = 0\<close> by (rule disjI2, rule refl) 
  next
    fix x
    assume H2:\<open>x\<in>nat\<close>
    assume H3:\<open> 0 \<in> x \<or> 0 = x\<close>
    show \<open>0 \<in> succ(x) \<or> 0 = succ(x)\<close>
    proof(rule disjE[OF H3])
      assume H4:\<open>0\<in>x\<close>
      show \<open>0 \<in> succ(x) \<or> 0 = succ(x)\<close>
      proof(rule disjI1)
        show \<open>0 \<in> succ(x)\<close>
          by (rule succI2[OF H4])
      qed
    next
      assume H4:\<open>0=x\<close>
      show \<open>0 \<in> succ(x) \<or> 0 = succ(x)\<close>
      proof(rule disjI1)
        have q:\<open>x \<in> succ(x)\<close> by auto
        from q and H4 show \<open>0 \<in> succ(x)\<close> by auto
      qed
    qed
  qed
qed

theorem JH2_1ii : \<open>m\<in>succ(n) \<Longrightarrow> m\<in>n\<or>m=n\<close>
  by auto

theorem nat_induct_bound : 
  assumes H0:\<open>P(0)\<close>
  assumes H1:\<open>!!x. x\<in>nat \<Longrightarrow> P(x) \<Longrightarrow> P(succ(x))\<close>
  shows \<open>\<forall>n\<in>nat. P(n)\<close>
proof(rule ballI)
  fix n
  assume H2:\<open>n\<in>nat\<close>
  show \<open>P(n)\<close>
  proof(rule nat_induct[of n])
    from H2 show \<open>n\<in>nat\<close> by assumption
  next
    show \<open>P(0)\<close> by (rule H0)
  next
    fix x
    assume H3:\<open>x\<in>nat\<close>
    assume H4:\<open>P(x)\<close>
    show \<open>P(succ(x))\<close> by (rule H1[OF H3 H4])
  qed
qed

theorem nat_transitive:\<open>\<forall>n\<in>nat. \<forall>k. \<forall>m.  k \<in> m \<and> m \<in> n \<longrightarrow> k \<in> n\<close>
proof(rule nat_induct_bound)
  show \<open>\<forall>k. \<forall>m. k \<in> m \<and> m \<in> 0 \<longrightarrow> k \<in> 0\<close>
  proof(rule allI, rule allI, rule impI)
    fix k m
    assume H:\<open>k \<in> m \<and> m \<in> 0\<close>
    then have H:\<open>m \<in> 0\<close> by auto 
    then show \<open>k \<in> 0\<close> by auto
  qed
next
  fix n
  assume H0:\<open>n \<in> nat\<close>
  assume H1:\<open>\<forall>k.
            \<forall>m.
               k \<in> m \<and> m \<in> n \<longrightarrow>
               k \<in> n\<close>
  show \<open>\<forall>k. \<forall>m.
               k \<in> m \<and>
               m \<in> succ(n) \<longrightarrow>
               k \<in> succ(n)\<close>
  proof(rule allI, rule allI, rule impI)
    fix k m
(*    assume H2:\<open>k \<in> nat\<close>
    assume H3:\<open>m \<in> nat\<close>*)
    assume H4:\<open>k \<in> m \<and> m \<in> succ(n)\<close>
    hence H4':\<open>m \<in> succ(n)\<close> by (rule conjunct2)
    hence H4'':\<open>m\<in>n \<or> m=n\<close> by (rule succE, auto)
    from H4 have Q:\<open>k \<in> m\<close> by (rule conjunct1)
    have H1S:\<open>\<forall>m. k \<in> m \<and> m \<in> n \<longrightarrow> k \<in> n\<close>
      by (rule spec[OF H1])
    have H1S:\<open>k \<in> m \<and> m \<in> n \<longrightarrow> k \<in> n\<close> 
      by (rule spec[OF H1S])
    show \<open>k \<in> succ(n)\<close>
    proof(rule disjE[OF H4''])
      assume L:\<open>m\<in>n\<close>
      from Q and L have QL:\<open>k \<in> m \<and> m \<in> n\<close> by auto
      have G:\<open>k \<in> n\<close> by (rule mp [OF H1S QL])
      show \<open>k \<in> succ(n)\<close>
        by (rule succI2[OF G])
    next
      assume L:\<open>m=n\<close>
      from Q have F:\<open>k \<in> succ(m)\<close> by auto
      from L and Q show \<open>k \<in> succ(n)\<close> by auto
    qed
  qed
qed

theorem nat_xninx : \<open>\<forall>n\<in>nat. \<not>(n\<in>n)\<close>
proof(rule nat_induct_bound)
  show \<open>0\<notin>0\<close>
    by auto
next
  fix x
  assume H0:\<open>x\<in>nat\<close>
  assume H1:\<open>x\<notin>x\<close>
  show \<open>succ(x) \<notin> succ(x)\<close>
  proof(rule contrapos[OF H1])
    assume Q:\<open>succ(x) \<in> succ(x)\<close>
    have D:\<open>succ(x)\<in>x \<or> succ(x)=x\<close>
      by (rule JH2_1ii[OF Q])
    show \<open>x\<in>x\<close>
    proof(rule disjE[OF D])
      assume Y1:\<open>succ(x)\<in>x\<close>
      have U:\<open>x\<in>succ(x)\<close> by (rule succI1)
(*
      have T:\<open>\<forall>k\<in>nat. \<forall>m\<in>nat. k \<in> m \<and> m \<in> x \<longrightarrow> k \<in> x\<close> 
        by (rule bspec[OF nat_transitive H0])
      have T:\<open>\<forall>m\<in>nat. x \<in> m \<and> m \<in> x \<longrightarrow> x \<in> x\<close>
        by (rule bspec[OF T H0])
      have T:\<open>x \<in> succ(x) \<and> succ(x) \<in> x \<longrightarrow> x \<in> x\<close>
        by (rule bspec[OF T H0'])
*)
      have T:\<open>x \<in> succ(x) \<and> succ(x) \<in> x \<longrightarrow> x \<in> x\<close>
        by (rule spec[OF spec[OF bspec[OF nat_transitive H0]]])
      have R:\<open>x \<in> succ(x) \<and> succ(x) \<in> x\<close>
        by (rule conjI[OF U Y1])
      show \<open>x\<in>x\<close> 
        by (rule mp[OF T R])
    next
      assume Y1:\<open>succ(x)=x\<close>
      (*have U:\<open>x\<in>succ(x)\<close> by (rule succI1)
      from Y1 and U show \<open>x\<in>x\<close> 
        by auto
      from Y1 have Y1_r:\<open>x=succ(x)\<close> by (rule sym)*)
      show \<open>x\<in>x\<close> 
        by (rule subst[OF Y1], rule Q)
    qed
  qed
qed

theorem nat_asym : \<open>\<forall>n\<in>nat. \<forall>m. \<not>(n\<in>m \<and> m\<in>n)\<close>
proof(rule ballI, rule allI)
  fix n m
  assume H0:\<open>n \<in> nat\<close>
(*  assume H1:\<open>m \<in> nat\<close>*)
  have Q:\<open>\<not>(n\<in>n)\<close>
    by(rule bspec[OF nat_xninx H0])
  show \<open>\<not> (n \<in> m \<and> m \<in> n)\<close>
  proof(rule contrapos[OF Q])
    assume W:\<open>(n \<in> m \<and> m \<in> n)\<close>
    show \<open>n\<in>n\<close>
      by (rule mp[OF spec[OF spec[OF bspec[OF nat_transitive H0]]] W])
  qed
qed

theorem zerolesucc :\<open>\<forall>n\<in>nat. 0 \<in> succ(n)\<close>
proof(rule nat_induct_bound)
  show \<open>0\<in>1\<close>
    by auto
next
  fix x
  assume H0:\<open>x\<in>nat\<close>
  assume H1:\<open>0\<in>succ(x)\<close>
  show \<open>0\<in>succ(succ(x))\<close>
  proof
    assume J:\<open>0 \<notin> succ(x)\<close>
    show \<open>0 = succ(x)\<close>
      by(rule notE[OF J H1])
  qed
qed

theorem le_succ : \<open>\<forall>n\<in>nat. \<forall>m\<in>nat. m\<in>n \<longrightarrow> succ(m)\<in>succ(n)\<close>
proof(rule nat_induct_bound)
  show \<open>\<forall>m\<in>nat. m \<in> 0 \<longrightarrow> succ(m) \<in> 1\<close>
    by auto
next
  fix x
  assume H0:\<open>x\<in>nat\<close>
  assume H1:\<open>\<forall>m\<in>nat. m \<in> x \<longrightarrow> succ(m) \<in> succ(x)\<close>
  show \<open> \<forall>m\<in>nat. m \<in> succ(x) \<longrightarrow>
            succ(m) \<in> succ(succ(x))\<close>
  proof(rule ballI, rule impI)
    fix m
    assume HR0:\<open>m\<in>nat\<close>
    assume HR1:\<open>m\<in>succ(x)\<close>
    show \<open>succ(m) \<in> succ(succ(x))\<close>
    proof(rule succE[OF HR1])
      assume Q:\<open>m = x\<close>
      from Q show \<open>succ(m) \<in> succ(succ(x))\<close>
        by auto
    next
      assume Q:\<open>m \<in> x\<close>
      have Q:\<open>succ(m) \<in> succ(x)\<close>
        by (rule mp[OF bspec[OF H1 HR0] Q])
      from Q show \<open>succ(m) \<in> succ(succ(x))\<close>
        by (rule succI2)
    qed
  qed
qed

theorem nat_linord:\<open>\<forall>n\<in>nat. \<forall>m\<in>nat. m\<in>n\<or>m=n\<or>n\<in>m\<close>
proof(rule ballI)
  fix n
  assume H1:\<open>n\<in>nat\<close>
  show \<open>\<forall>m\<in>nat. m \<in> n \<or> m = n \<or> n \<in> m\<close>
  proof(rule nat_induct[of n])
    from H1 show \<open>n\<in>nat\<close> by assumption
  next
    show \<open>\<forall>m\<in>nat. m \<in> 0 \<or> m = 0 \<or> 0 \<in> m\<close>
    proof 
      fix m
      assume J:\<open>m\<in>nat\<close>
      show \<open> m \<in> 0 \<or> m = 0 \<or> 0 \<in> m\<close>
      proof(rule disjI2)
        have Q:\<open>0\<in>m\<or>0=m\<close> by (rule bspec[OF zeroleq J])
        show \<open>m = 0 \<or> 0 \<in> m\<close>
          by (rule disjE[OF Q], auto)
      qed
    qed
  next
    fix x
    assume K:\<open>x\<in>nat\<close>
    assume M:\<open>\<forall>m\<in>nat. m \<in> x \<or> m = x \<or> x \<in> m\<close>
    show \<open>\<forall>m\<in>nat.
            m \<in> succ(x) \<or>
            m = succ(x) \<or>
            succ(x) \<in> m\<close>
    proof(rule nat_induct_bound)
      show \<open>0 \<in> succ(x) \<or>  0 = succ(x) \<or> succ(x) \<in> 0\<close>
      proof(rule disjI1)
        show \<open>0 \<in> succ(x)\<close>
          by (rule bspec[OF zerolesucc K])
      qed
    next
      fix y
      assume H0:\<open>y \<in> nat\<close>
      assume H1:\<open>y \<in> succ(x) \<or> y = succ(x) \<or> succ(x) \<in> y\<close>
      show \<open>succ(y) \<in> succ(x) \<or>
            succ(y) = succ(x) \<or>
            succ(x) \<in> succ(y)\<close>
      proof(rule disjE[OF H1])
        assume W:\<open>y\<in>succ(x)\<close>
        show \<open>succ(y) \<in> succ(x) \<or>
              succ(y) = succ(x) \<or>
              succ(x) \<in> succ(y)\<close>
        proof(rule succE[OF W])
          assume G:\<open>y=x\<close>
          show \<open>succ(y) \<in> succ(x) \<or>
    succ(y) = succ(x) \<or>
    succ(x) \<in> succ(y)\<close>
            by (rule disjI2, rule disjI1, rule subst[OF G], rule refl)
        next
          assume G:\<open>y \<in> x\<close>
          have R:\<open>succ(y) \<in> succ(x)\<close>
            by (rule mp[OF bspec[OF bspec[OF le_succ K] H0] G])
          show \<open>succ(y) \<in> succ(x) \<or>
           succ(y) = succ(x) \<or>
           succ(x) \<in> succ(y)\<close>
            by(rule disjI1, rule R)
        qed
      next
        assume W:\<open>y = succ(x) \<or> succ(x) \<in> y\<close>
        show \<open>succ(y) \<in> succ(x) \<or>
              succ(y) = succ(x) \<or>
              succ(x) \<in> succ(y)\<close>
        proof(rule disjE[OF W])
          assume W:\<open>y=succ(x)\<close>
          show \<open>succ(y) \<in> succ(x) \<or>
              succ(y) = succ(x) \<or>
              succ(x) \<in> succ(y)\<close>
            by (rule disjI2, rule disjI2, rule subst[OF W], rule succI1)
        next
          assume W:\<open>succ(x)\<in>y\<close>
          show \<open>succ(y) \<in> succ(x) \<or>
              succ(y) = succ(x) \<or>
              succ(x) \<in> succ(y)\<close>
            by (rule disjI2, rule disjI2, rule succI2[OF W])
        qed
      qed
    qed
  qed
qed

theorem nat_elem_is_ss:\<open>\<forall>m\<in>nat. n\<in>m \<longrightarrow> n\<subseteq>m\<close>
  sorry (**)

theorem nat_ldfghj:\<open>\<forall>n\<in>nat. \<forall>m\<in>nat. n\<subseteq>m \<and> n\<noteq>m \<longrightarrow> n\<in>m\<close>
  sorry
(*
do it through ordinals.

*)

theorem nat_linord_ss:\<open>\<forall>n\<in>nat. \<forall>m\<in>nat. m\<subseteq>n\<or>n\<subseteq>m\<close>
  sorry

(* Union of compatible set of functions is a function. *)
definition compat :: \<open>[i,i]\<Rightarrow>o\<close>
  where "compat(f1,f2) == \<forall>x.\<forall>y1.\<forall>y2.\<langle>x,y1\<rangle> \<in> f1 \<and> \<langle>x,y2\<rangle> \<in> f2 \<longrightarrow> y1=y2"

(*\<in>(domain(f1)\<inter>domain(f2))*)

definition compatset :: \<open>i\<Rightarrow>o\<close>
  where "compatset(S) == \<forall>f1\<in>S.\<forall>f2\<in>S. compat(f1,f2)" 

theorem upairI1 : \<open>a \<in> {a, b}\<close>
proof
  assume \<open>a \<notin> {b}\<close>
  show \<open>a = a\<close> by (rule refl)
qed

theorem upairI2 : \<open>b \<in> {a, b}\<close>
proof
  assume H:\<open>b \<notin> {b}\<close>
  have Y:\<open>b \<in> {b}\<close> by (rule upair.singletonI)
  show \<open>b = a\<close> by (rule notE[OF H Y])
qed

theorem sinup : \<open>{x} \<in> \<langle>x, xa\<rangle>\<close>
proof (unfold Pair_def)
  show \<open>{x} \<in> {{x, x}, {x, xa}}\<close>
  proof (rule IFOL.subst)
    show \<open>{x} \<in> {{x},{x,xa}}\<close>
      by (rule upairI1)
  next
    show \<open>{{x}, {x, xa}} = {{x, x}, {x, xa}}\<close>
      by blast
  qed
qed

theorem compatsetunionfun : 
  fixes S
  assumes H0:\<open>compatset(S)\<close>
  shows \<open>function(\<Union>S)\<close>
proof(unfold function_def)
  from H0 have H0:\<open>\<forall>f1 \<in> S. \<forall>f2 \<in> S. compat(f1,f2)\<close> by (unfold compatset_def)
  show \<open> \<forall>x y1. \<langle>x, y1\<rangle> \<in> \<Union>S \<longrightarrow> 
          (\<forall>y2. \<langle>x, y2\<rangle> \<in> \<Union>S \<longrightarrow> y1 = y2)\<close>
  proof(rule allI, rule allI, rule impI, rule allI, rule impI)
    fix x y1 y2
    assume F1:\<open>\<langle>x, y1\<rangle> \<in> \<Union>S\<close>
    assume F2:\<open>\<langle>x, y2\<rangle> \<in> \<Union>S\<close> 
    show \<open>y1=y2\<close>
    proof(rule UnionE[OF F1], rule UnionE[OF F2])
      fix f1 f2
      assume J1:\<open>\<langle>x, y1\<rangle> \<in> f1\<close>
      assume J2:\<open>\<langle>x, y2\<rangle> \<in> f2\<close>
      assume K1:\<open>f1 \<in> S\<close>
      assume K2:\<open>f2 \<in> S\<close>
      have R:\<open>\<forall>f2 \<in> S. compat(f1,f2)\<close> by (rule bspec[OF H0 K1])
      have R:\<open>compat(f1,f2)\<close> by (rule bspec[OF R K2])
      from R have R:\<open>\<forall>x.
        \<forall>y1.\<forall>y2.\<langle>x,y1\<rangle> \<in> f1 \<and> \<langle>x,y2\<rangle> \<in> f2 \<longrightarrow> y1=y2\<close> by (unfold compat_def)
      find_theorems "_\<Longrightarrow>_\<in> domain(_)"
      have R:\<open>\<forall>y1.\<forall>y2.\<langle>x,y1\<rangle> \<in> f1 \<and> \<langle>x,y2\<rangle> \<in> f2 \<longrightarrow> y1=y2\<close> by (rule spec[OF R])
      have R:\<open>\<forall>y2.\<langle>x,y1\<rangle> \<in> f1 \<and> \<langle>x,y2\<rangle> \<in> f2 \<longrightarrow> y1=y2\<close> by (rule spec[OF R])
      have R:\<open>\<langle>x,y1\<rangle> \<in> f1 \<and> \<langle>x,y2\<rangle> \<in> f2 \<longrightarrow> y1=y2\<close> by (rule spec[OF R])
      from J1 and J2 have J:\<open>\<langle>x,y1\<rangle> \<in> f1 \<and> \<langle>x,y2\<rangle> \<in> f2\<close> by (rule conjI)
      show \<open>y1=y2\<close> by (rule mp[OF R J])
    qed
  qed
qed

(* Natural numbers are linearly ordered by \<in> *)


(* *. Recursion theorem *)
definition satpc :: \<open>[i,i,i] \<Rightarrow> o \<close>
  where \<open>satpc(t,\<alpha>,g) == \<forall>n \<in> \<alpha> . t`succ(n) = g ` <t`n, n>\<close>
                            
(* m-step computation based on a and g *)
definition partcomp :: \<open>[i,i,i,i,i]\<Rightarrow>o\<close>
  where \<open>partcomp(A,t,m,a,g) == (t:succ(m)\<rightarrow>A) \<and> (t`0=a) \<and> satpc(t,succ(m),g)\<close>

(* F *)
definition pcs :: \<open>[i,i,i]\<Rightarrow>i\<close>
  where \<open>pcs(A,a,g) == {t\<in>Pow(nat*A). \<exists>m. partcomp(A,t,m,a,g)}\<close>

lemma pcs_lem : \<open>compatset(pcs(A, a, g))\<close>
proof (unfold compatset_def)
  show \<open>\<forall>f1\<in>pcs(A, a, g). \<forall>f2\<in>pcs(A, a, g). compat(f1, f2)\<close>
  proof(rule ballI, rule ballI)
    fix f1 f2
    assume H1:\<open>f1 \<in> pcs(A, a, g)\<close>
    then have H1':\<open>f1 \<in> {t\<in>Pow(nat*A). \<exists>m. partcomp(A,t,m,a,g)}\<close> by (unfold pcs_def)
    (*(t:succ(m)\<rightarrow>A) \<and> (t`0=a) \<and> satpc(t,succ(m),g)*)
    assume H2:\<open>f2 \<in> pcs(A, a, g)\<close>
    then have H2':\<open>f2 \<in> {t\<in>Pow(nat*A). \<exists>m. partcomp(A,t,m,a,g)}\<close> by (unfold pcs_def)
    show \<open>compat(f1, f2)\<close>
    proof(unfold compat_def, rule allI, rule allI, rule allI, rule impI)
      fix x y1 y2
      assume P:\<open>\<langle>x, y1\<rangle> \<in> f1 \<and> \<langle>x, y2\<rangle> \<in> f2\<close>
      from P have P1:\<open>\<langle>x, y1\<rangle> \<in> f1\<close> by (rule conjunct1)
      from P have P2:\<open>\<langle>x, y2\<rangle> \<in> f2\<close> by (rule conjunct2)
      show \<open>y1 = y2\<close>
      proof(rule CollectE[OF H1'], rule CollectE[OF H2'])
        assume J0:\<open>f1 \<in> Pow(nat \<times> A)\<close>
        assume J1:\<open>f2 \<in> Pow(nat \<times> A)\<close>
        assume J2:\<open>\<exists>m. partcomp(A, f1, m, a, g)\<close>
        assume J3:\<open>\<exists>m. partcomp(A, f2, m, a, g)\<close>
        show \<open>y1 = y2\<close>
        proof(rule exE[OF J2], rule exE[OF J3])
          fix m1 m2
          assume K1:\<open>partcomp(A, f1, m1, a, g)\<close>
          hence K1:\<open>(f1:succ(m1)\<rightarrow>A) \<and> (f1`0=a) \<and> satpc(f1,succ(m1),g)\<close>
            by (unfold partcomp_def)
          assume K2:\<open>partcomp(A, f2, m2, a, g)\<close>
          hence K2':\<open>(f2:succ(m2)\<rightarrow>A) \<and> (f2`0=a) \<and> satpc(f2,succ(m2),g)\<close>
            by (unfold partcomp_def)
          show \<open>y1 = y2\<close>
(* x < succ(m1) & x < succ(m2)

*)
            sorry
        qed
      qed
    qed
  qed
qed
 (* apply (unfold pcs_def, unfold compatset_def)*)
theorem fuissu : \<open>f \<in> X -> Y \<Longrightarrow> f \<subseteq> X\<times>Y\<close>
proof
  fix w
  assume H1 : \<open>f \<in> X -> Y\<close>
  then have J1:\<open>f \<in> {q\<in>Pow(Sigma(X,\<lambda>_.Y)). X\<subseteq>domain(q) & function(q)}\<close>
    by (unfold Pi_def) 
  then have J2:\<open>f \<in> Pow(Sigma(X,\<lambda>_.Y))\<close>
    by auto
  then have J3:\<open>f \<subseteq> Sigma(X,\<lambda>_.Y)\<close>
    by auto
  assume H2 : \<open>w \<in> f\<close>
  from J3 and H2 have \<open>w\<in>Sigma(X,\<lambda>_.Y)\<close>
    by auto
  then have J4:\<open>w \<in> (\<Union>x\<in>X. (\<Union>y\<in>Y. {\<langle>x,y\<rangle>}))\<close>
    by auto
  show \<open>w \<in> X*Y\<close>
  proof (rule UN_E[OF J4])
    fix x
    assume V1:\<open>x \<in> X\<close>
    assume V2:\<open>w \<in> (\<Union>y\<in>Y. {\<langle>x, y\<rangle>})\<close>
    show \<open>w \<in> X \<times> Y\<close>
    proof (rule UN_E[OF V2])
      fix y
      assume V3:\<open>y \<in> Y\<close>
      assume V4:\<open>w \<in> {\<langle>x, y\<rangle>}\<close>
      then have V4:\<open>w = \<langle>x, y\<rangle>\<close>
        by auto
      have v5:\<open>\<langle>x, y\<rangle> \<in> Sigma(X,\<lambda>_.Y)\<close>
      proof(rule SigmaI)
        show \<open>x \<in> X\<close> by (rule V1)
      next
        show \<open>y \<in> Y\<close> by (rule V3)
      qed
      then have V5:\<open>\<langle>x, y\<rangle> \<in> X*Y\<close> 
        by auto
      from V4 and V5 show \<open>w \<in> X \<times> Y\<close> by auto
    qed
  qed
qed

theorem recuniq : 
  fixes f
  assumes H0:\<open>f \<in> nat -> A \<and> f ` 0 = a \<and> satpc(f, nat, g)\<close>
  fixes t
  assumes H1:\<open>t \<in> nat -> A \<and> t ` 0 = a \<and> satpc(t, nat, g)\<close>
  fixes x
  shows \<open>f=t\<close>
proof -
  from H0 have H02:\<open>\<forall>n \<in> nat. f`succ(n) = g ` <(f`n), n>\<close> by (unfold satpc_def, auto)
  from H0 have H01:\<open>f ` 0 = a\<close> by auto
  from H0 have H00:\<open>f \<in> nat -> A\<close> by auto
  from H1 have H12:\<open>\<forall>n \<in> nat. t`succ(n) = g ` <(t`n), n>\<close> by (unfold satpc_def, auto)
  from H1 have H11:\<open>t ` 0 = a\<close> by auto
  from H1 have H10:\<open>t \<in> nat -> A\<close> by auto
  show \<open>f=t\<close>
  proof (rule fun_extension[OF H00 H10])
    fix x
    assume K: \<open>x \<in> nat\<close>
    show \<open>(f ` x) = (t ` x)\<close>
(*
lemma nat_induct [case_names 0 succ, induct set: nat]:
    "[| n \<in> nat;  P(0);  !!x. [| x \<in> nat;  P(x) |] ==> P(succ(x)) |] ==> P(n)"
*)
(*    proof(induct x rule: nat_induct) *)
    proof(rule nat_induct[of x])
      show \<open>x \<in> nat\<close> by (rule K)
    next
      from H01 and H11 show \<open>f ` 0 = t ` 0\<close>
        by auto
    next
      fix x
      assume A:\<open>x\<in>nat\<close>
      assume B:\<open>f`x = t`x\<close>
      show \<open>f ` succ(x) = t ` succ(x)\<close>
      proof -
        from H02 and A have H02':\<open>f`succ(x) = g ` <(f`x), x>\<close> 
          by (rule bspec)
        from H12 and A have H12':\<open>t`succ(x) = g ` <(t`x), x>\<close> 
          by (rule bspec)
        from B and H12' have H12'':\<open>t`succ(x) = g ` <(f`x), x>\<close> by auto
        from H12'' and H02' show \<open>f ` succ(x) = t ` succ(x)\<close> by auto
      qed
    qed
  qed
qed
(*
context k_partial_order
begin
end
*)
locale rec_thm =
  fixes A a g
  assumes H1:\<open>a \<in> A\<close>
  assumes H2:\<open>g : ((A*nat)\<rightarrow>A)\<close>
begin

theorem trr: \<open>a\<in>A\<close>
  by (rule H1)

lemma l1 : \<open>\<Union>pcs(A, a, g) \<subseteq> nat \<times> A\<close>
proof
  fix x
  assume H:\<open>x \<in> \<Union>pcs(A, a, g)\<close>
  hence  H:\<open>x \<in> \<Union>{t\<in>Pow(nat*A). \<exists>m. partcomp(A,t,m,a,g)}\<close>
    by (unfold pcs_def)
  show \<open>x \<in> nat \<times> A\<close>
  proof(rule UnionE[OF H])
    fix B
    assume J1:\<open>x\<in>B\<close>
    assume J2:\<open>B \<in> {t \<in> Pow(nat \<times> A) .
            \<exists>m. partcomp(A, t, m, a, g)}\<close>
    hence J2:\<open>B \<in> Pow(nat \<times> A)\<close> by auto
    hence J2:\<open>B \<subseteq> nat \<times> A\<close> by auto
    from J1 and J2 show \<open>x \<in> nat \<times> A\<close>
      by auto
  qed
qed

lemma le1:
  assumes H:\<open>x\<in>1\<close>
  shows \<open>x=0\<close>
proof
  show \<open>x \<subseteq> 0\<close>
  proof
    fix z
    assume J:\<open>z\<in>x\<close>
    show \<open>z\<in>0\<close>
    proof(rule succE[OF H])
      assume J:\<open>x\<in>0\<close>
      show \<open>z\<in>0\<close>
        by (rule notE[OF not_mem_empty J])
    next
      assume K:\<open>x=0\<close>
      from J and K show \<open>z\<in>0\<close>
        by auto
    qed
  qed
next
  show \<open>0 \<subseteq> x\<close> by auto
qed

lemma lsinglfun : \<open>function({\<langle>0, a\<rangle>})\<close>
  sorry

lemma l2': \<open>0 \<in> domain(\<Union>pcs(A, a, g))\<close>
proof
  show \<open>\<langle>0, a\<rangle> \<in> \<Union>pcs(A, a, g)\<close>
  proof
    show \<open>\<langle>0, a\<rangle> \<in> {\<langle>0, a\<rangle>}\<close>
      by auto
  next
    show \<open>{\<langle>0, a\<rangle>} \<in> pcs(A, a, g)\<close>
    proof(unfold pcs_def)
      show \<open>{\<langle>0, a\<rangle>} \<in> {t \<in> Pow(nat \<times> A) . \<exists>m. partcomp(A, t, m, a, g)}\<close>
      proof
        show \<open>{\<langle>0, a\<rangle>} \<in> Pow(nat \<times> A)\<close>
        proof(rule PowI, rule equalities.singleton_subsetI)
          show \<open>\<langle>0, a\<rangle> \<in> nat \<times> A\<close>
          proof
            show \<open>0 \<in> nat\<close> by auto
          next
            show \<open>a \<in> A\<close> by (rule H1)
          qed
        qed
      next
        show \<open>\<exists>m. partcomp(A, {\<langle>0, a\<rangle>}, m, a, g)\<close>
        proof
          show \<open>partcomp(A, {\<langle>0, a\<rangle>}, 0, a, g)\<close>
          proof(unfold partcomp_def)
            show \<open>{\<langle>0, a\<rangle>} \<in> 1 -> A \<and> {\<langle>0, a\<rangle>} ` 0 = a \<and> satpc({\<langle>0, a\<rangle>}, 1, g)\<close>
            proof
              show \<open>{\<langle>0, a\<rangle>} \<in> 1 -> A\<close>
              proof (unfold Pi_def)
                show \<open>{\<langle>0, a\<rangle>} \<in> {f \<in> Pow(1 \<times> A) . 1 \<subseteq> domain(f) \<and> function(f)}\<close>
                proof
                  show \<open>{\<langle>0, a\<rangle>} \<in> Pow(1 \<times> A)\<close>
                  proof(rule PowI, rule equalities.singleton_subsetI)
                    show \<open>\<langle>0, a\<rangle> \<in> 1 \<times> A\<close>
                    proof
                      show \<open>0 \<in> 1\<close> by auto
                    next
                      show \<open>a \<in> A\<close> by (rule H1)
                    qed
                  qed
                next
                  show \<open>1 \<subseteq> domain({\<langle>0, a\<rangle>}) \<and> function({\<langle>0, a\<rangle>})\<close>
                  proof 
                    show \<open>1 \<subseteq> domain({\<langle>0, a\<rangle>})\<close>
                    proof
                      fix x
                      assume W:\<open>x\<in>1\<close>
                      from W have W:\<open>x=0\<close> by (rule le1)
                      have Y:\<open>0\<in>domain({\<langle>0, a\<rangle>})\<close>
                        sorry
                      from W and Y 
                      show \<open>x\<in>domain({\<langle>0, a\<rangle>})\<close>
                        by auto
                    qed
                  next
                    show \<open>function({\<langle>0, a\<rangle>})\<close>
                      by (rule lsinglfun)
                  qed
                qed
              qed
              show \<open>{\<langle>0, a\<rangle>} ` 0 = a \<and> satpc({\<langle>0, a\<rangle>}, 1, g)\<close>
              proof
                show \<open>{\<langle>0, a\<rangle>} ` 0 = a\<close>
                  sorry
              next
                show \<open>satpc({\<langle>0, a\<rangle>}, 1, g)\<close>
                  sorry
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma l2:\<open>nat \<subseteq> domain(\<Union>pcs(A, a, g))\<close>
proof
  fix x
  assume G:\<open>x\<in>nat\<close>
  show \<open>x \<in> domain(\<Union>pcs(A, a, g))\<close>
  proof(rule nat_induct[of x])
    show \<open>x\<in>nat\<close> by (rule G)
  next
    fix x
    assume Q1:\<open>x\<in>nat\<close>
    assume Q2:\<open>x\<in>domain(\<Union>pcs(A, a, g))\<close>
    show \<open>succ(x)\<in>domain(\<Union>pcs(A, a, g))\<close>
      sorry
  next
    show \<open>0 \<in> domain(\<Union>pcs(A, a, g))\<close>
      sorry
  qed
qed

lemma l3:\<open>function(\<Union>pcs(A, a, g))\<close>
  sorry

lemma l4 : \<open>(\<Union>pcs(A,a,g)) \<in> nat -> A\<close>
proof(unfold Pi_def)
  show \<open> \<Union>pcs(A, a, g) \<in> {f \<in> Pow(nat \<times> A) . nat \<subseteq> domain(f) \<and> function(f)}\<close>
  proof
    show \<open>\<Union>pcs(A, a, g) \<in> Pow(nat \<times> A)\<close>
    proof 
      show \<open>\<Union>pcs(A, a, g) \<subseteq> nat \<times> A\<close>
        by (rule l1)
    qed
  next 
    show \<open>nat \<subseteq> domain(\<Union>pcs(A, a, g)) \<and> function(\<Union>pcs(A, a, g))\<close>
    proof
      show \<open>nat \<subseteq> domain(\<Union>pcs(A, a, g))\<close>
        by (rule l2)
    next
      show \<open>function(\<Union>pcs(A, a, g))\<close>
        by (rule l3)
    qed
  qed
qed

lemma l5: \<open>(\<Union>pcs(A, a, g)) ` 0 = a\<close>
  sorry

lemma l6: \<open>satpc(\<Union>pcs(A, a, g), nat, g)\<close>
  sorry

(*
        have A1:\<open>\<Union>pcs(A,a,g)\<in>{f\<in>Pow(nat*A). nat\<subseteq>domain(f) & function(f)}\<close>
      proof 
        show \<open>\<Union>pcs(A, a, g) \<in> Pow(nat \<times> A)\<close>
        proof 
          show \<open>\<Union>pcs(A, a, g) \<subseteq> nat \<times> A\<close>
          proof(unfold pcs_def)
            show \<open> \<Union>{t \<in> Pow(nat \<times> A) . \<exists>m. partcomp (A, t, m, a, g)} \<subseteq> nat \<times> A\<close>
             (* by blast*)
              sorry
          qed
        qed
      next
        show \<open>nat \<subseteq> domain(\<Union>pcs(A, a, g)) \<and> function(\<Union>pcs(A, a, g))\<close>
        proof
          show \<open>nat \<subseteq> domain(\<Union>pcs(A, a, g))\<close>
          proof(unfold pcs_def)
            show \<open>nat \<subseteq> domain(\<Union>{t \<in> Pow(nat \<times> A) . \<exists>m. partcomp(A, t, m, a, g)})\<close>
              sorry (*by blast*)
          qed
        next
          have C : \<open>compatset(pcs(A, a, g))\<close> 
            by (rule pcs_lem)
          show \<open>function(\<Union>pcs(A, a, g))\<close>
            by (rule compatsetunionfun[OF C])
        qed
      qed
    next
      from A1 show \<open>\<Union>pcs(A,a,g) \<in> nat -> A\<close>
      proof(fold Pi_def)
        assume \<open>\<Union>pcs(A, a, g) \<in> nat -> A\<close>
        then show \<open>\<Union>pcs(A, a, g) \<in> nat -> A\<close>
          by assumption
      qed
    next
      show \<open>(\<Union>pcs(A, a, g)) ` 0 = a \<and> satpc(\<Union>pcs(A, a, g), nat, g)\<close>
      proof 
        show \<open>(\<Union>pcs(A, a, g)) ` 0 = a\<close>
          sorry
      next
        show \<open>satpc(\<Union>pcs(A, a, g), nat, g)\<close>
          sorry
      qed
    qed
  qed
*)

theorem recursion:
  shows \<open>\<exists>!f. ((f \<in> (nat\<rightarrow>A)) \<and> ((f`0) = a) \<and> satpc(f,nat,g))\<close>
proof 
  show \<open>\<exists>f. f \<in> nat -> A \<and> f ` 0 = a \<and> satpc(f, nat, g)\<close>
  proof 
    show \<open>(\<Union>pcs(A,a,g)) \<in> nat -> A \<and> (\<Union>pcs(A,a,g)) ` 0 = a \<and> satpc(\<Union>pcs(A,a,g), nat, g)\<close>
    proof
      show \<open>\<Union>pcs(A, a, g) \<in> nat -> A\<close>
        by (rule l4)
    next
      show \<open>(\<Union>pcs(A, a, g)) ` 0 = a \<and> satpc(\<Union>pcs(A, a, g), nat, g)\<close>
      proof 
        show \<open>(\<Union>pcs(A, a, g)) ` 0 = a\<close>
          by (rule l5)
      next
        show \<open>satpc(\<Union>pcs(A, a, g), nat, g)\<close>
          by (rule l6)
      qed
    qed
  qed
next
  show \<open>\<And>f y. f \<in> nat -> A \<and>
           f ` 0 = a \<and>
           satpc(f, nat, g) \<Longrightarrow>
           y \<in> nat -> A \<and>
           y ` 0 = a \<and>
           satpc(y, nat, g) \<Longrightarrow>
           f = y\<close>
    by (rule recuniq)
qed

end


theorem \<open>a\<in>A \<Longrightarrow> a\<in>A\<close>
proof (rule rec_thm.trr)
  show \<open>a \<in> A \<Longrightarrow> rec_thm(A,a,g)\<close>
  proof (unfold rec_thm_def)
    oops


definition fite :: "[i, o, i, i] \<Rightarrow> i" (\<open>from _ if _ then _ else _\<close>)
  where "fite(A, \<phi>, a, b) == \<Union>{x\<in>A.(\<phi>\<and>x=a)\<or>((\<not>\<phi>)\<and>x=b)}"

definition ite :: "[o, i, i] \<Rightarrow> i" (\<open>myif _ then _ else _\<close>)
  where "ite(\<phi>, a, b) == \<Union>{x\<in>{a,b}.(\<phi>\<and>x=a)\<or>((\<not>\<phi>)\<and>x=b)}"

theorem ite1 : \<open>\<phi> \<Longrightarrow> ((myif \<phi> then a else b) = a)\<close>
proof (unfold ite_def)
  assume H:\<open>\<phi>\<close>
  have P:\<open>{x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} = {a}\<close>
  proof 
    show \<open> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} \<subseteq> {a}\<close>
    proof
      fix x
      assume G:\<open>x \<in> {x \<in> {a, b} .  \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
      have U:\<open>\<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b\<close> by (rule CollectE[OF G])
      have T:\<open>x = a\<close>
      proof (rule disjE[OF U conjunct2])
        show \<open>\<phi> \<and> x = a \<Longrightarrow> \<phi> \<and> x = a\<close> by assumption
      next
        assume \<open>\<not>\<phi> \<and> x = b\<close>
        then have Y:\<open>\<not>\<phi>\<close> by (rule conjunct1)
        show \<open>x = a\<close> by (rule notE[OF Y H])
      qed
      have R:\<open>x\<in>{x}\<close> by (rule upair.singletonI)
      find_theorems "_\<in>{_}"
      show \<open>x\<in>{a}\<close>
      proof (rule subst)
        show \<open>x\<in>{x}\<close> by (rule upair.singletonI)
      next
        show \<open>{x} = {a}\<close> by (rule IFOL.subst_context[OF T])
      qed
    qed
  next
    show \<open>{a} \<subseteq> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
    proof (*(rule subsetI)... Which rule is used here? *)
      show\<open>a \<in> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} \<and>
      0 \<subseteq> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
      proof
        show \<open>0 \<subseteq> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
          by (rule empty_subsetI)
      next
        show \<open>a \<in> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
        proof 
          show \<open>a \<in> {a, b}\<close> by (rule upairI1)
        next
          show \<open>\<phi> \<and> a = a \<or> \<not> \<phi> \<and> a = b\<close>
          proof (rule disjI1)
            show \<open>\<phi> \<and> a = a\<close>
            proof
              show \<open>\<phi>\<close> by (rule H)
            next
              show \<open>a = a\<close> by (rule IFOL.refl)
            qed
          qed
        qed
      qed
    qed
  qed
  find_theorems "_\<Longrightarrow>a\<in>{a,b}"
  have P1:\<open>\<Union>{x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} = \<Union>{a}\<close>
    by (rule IFOL.subst_context[OF P])
  (*find_theorems "Lam [_]. _"*)
  have P2:\<open>\<Union>{a} = a\<close> by (rule equalities.Union_singleton)
  (*find_theorems "\<Union>{_}"*)
  (*find_theorems "_=_\<Longrightarrow>_=_ \<Longrightarrow>_"*)
  show \<open>\<Union>{x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} = a\<close>
    by (rule IFOL.trans[OF P1 P2])
qed

theorem ite2 : \<open>\<not>\<phi> \<Longrightarrow> ((myif \<phi> then a else b) = b)\<close>
proof (unfold ite_def)
  assume H:\<open>\<not>\<phi>\<close>
  have P:\<open>{x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} = {b}\<close>
  proof 
    show \<open> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} \<subseteq> {b}\<close>
    proof
      fix x
      assume G:\<open>x \<in> {x \<in> {a, b} .  \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
      have U:\<open>(\<phi> \<and> x = a) \<or> (\<not> \<phi> \<and> x = b)\<close> by (rule CollectE[OF G])

      have T:\<open>x = b\<close>
      proof (rule disjE[OF U conjunct2])
        assume \<open>\<not>\<phi> \<and> x = b\<close>
        then show \<open>x = b\<close> by (rule conjunct2)
      next
        assume \<open>\<phi> \<and> x = a\<close>
        then have Y:\<open>\<phi>\<close> by (rule conjunct1)
        have T1:\<open>x = b\<close> by (rule notE[OF H Y])
        show \<open>\<not>\<phi> \<and> x = b\<close> by (rule conjI[OF H T1])
      qed
      have R:\<open>x\<in>{x}\<close> by (rule upair.singletonI)
      find_theorems "_\<in>{_}"
      show \<open>x\<in>{b}\<close>
      proof (rule subst)
        show \<open>x\<in>{x}\<close> by (rule upair.singletonI)
      next
        show \<open>{x} = {b}\<close> by (rule IFOL.subst_context[OF T])
      qed
    qed
  next
    show \<open>{b} \<subseteq> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
    proof (*(rule subsetI)... Which rule is used here? *)
      show\<open>b \<in> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} \<and>
      0 \<subseteq> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
      proof
        show \<open>0 \<subseteq> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
          by (rule empty_subsetI)
      next
        show \<open>b \<in> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
        proof 
          show \<open>b \<in> {a, b}\<close> by (rule upairI2)
        next
          show \<open>(\<phi> \<and> b = a) \<or> (\<not> \<phi> \<and> b = b)\<close>
          proof (rule disjI2)
            show \<open>(\<not>\<phi>) \<and> b = b\<close>
            proof
              show \<open>\<not>\<phi>\<close> by (rule H)
            next
              show \<open>b = b\<close> by (rule IFOL.refl)
            qed
          qed
        qed
      qed
    qed
  qed
  have P1:\<open>\<Union>{x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} = \<Union>{b}\<close>
    by (rule IFOL.subst_context[OF P])
  have P2:\<open>\<Union>{b} = b\<close> by (rule equalities.Union_singleton)
  show \<open>\<Union>{x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} = b\<close>
    by (rule IFOL.trans[OF P1 P2])
qed

(* === This works but not used === *)
theorem lemma1 :
(*
\<open>\<forall> x . ((\<exists> y . \<langle>x, y\<rangle> \<in> f)
 \<longrightarrow> (\<exists> u. u \<in> f \<and> (\<exists> c. c \<in> u \<and> x \<in> c)))\<close>
*)
\<open>\<forall>x.(\<exists>y.\<langle>x, y\<rangle> \<in> f)\<longrightarrow>(\<exists>u\<in>f.\<exists>c\<in>u. x\<in>c)\<close>
proof
  fix x
  show \<open>(\<exists>y. \<langle>x, y\<rangle> \<in> f) \<longrightarrow> (\<exists>u\<in>f. \<exists>c\<in>u. x \<in> c)\<close>
  proof
    assume H1:\<open>\<exists>y. \<langle>x, y\<rangle> \<in> f\<close>
    show \<open>\<exists>u\<in>f. \<exists>c\<in>u. x \<in> c\<close>
    proof (rule exE[OF H1])
      fix xa
      assume H2:\<open>\<langle>x, xa\<rangle> \<in> f\<close>
      show \<open>\<exists>u\<in>f. \<exists>c\<in>u. x \<in> c\<close>
      proof
        show \<open>\<langle>x, xa\<rangle> \<in> f\<close> by (rule H2)
      next
        show \<open>\<exists>c\<in>\<langle>x, xa\<rangle>. x \<in> c\<close>
        proof 
          show \<open>{x} \<in> \<langle>x, xa\<rangle>\<close>
            by (rule sinup)
        next
          show \<open>x \<in> {x}\<close> 
            by (rule upair.singletonI)
        qed
      qed
    qed
  qed
qed

  find_theorems "_\<in>domain(_)"
theorem lemma2 : \<open>domain(f)\<subseteq>\<Union>\<Union>f\<close>
proof
  fix x
  assume H1:\<open>x\<in>domain(f)\<close>
  have H2:\<open>(\<exists>y. \<langle>x, y\<rangle> \<in> f)\<close>
    by (rule iffD1[OF equalities.domain_iff H1])
  show \<open>x\<in>\<Union>\<Union>f\<close>
  proof (rule exE[OF H2])
    fix xa
    assume H3:\<open>\<langle>x, xa\<rangle> \<in> f\<close>
    show \<open>x \<in> \<Union>\<Union>f\<close>
    proof
      show \<open>x \<in> {x}\<close> 
        by (rule upair.singletonI)
    next
      show \<open>{x} \<in> \<Union>f\<close>
      proof
        show \<open>\<langle>x, xa\<rangle> \<in> f\<close>
          by (rule H3)
      next
        show \<open>{x} \<in> \<langle>x, xa\<rangle>\<close>
          by (rule sinup)
      qed
    qed
  qed
qed

(* Maybe not be true!
theorem funext : 
  fixes A f1 f2
  assumes D1:\<open>dom(f1) = A\<close>
  assumes D2:\<open>dom(f2) = A\<close>
  assumes \<open>\<forall>x\<in>A. (f1`x=f2`x)\<close>
  shows \<open>f1 = f2\<close>
proof
*)

end