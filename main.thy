theory main imports ZF
begin
(* Main aim is to prove Recursion Theorem *)
(* 
then prove transfinite induction & recursion
then define Von Neumann hierarchy
then prove V=\<Union>(\<alpha>\<in>Ord).V\<alpha>
trying to rewrite everything without replacement
*)


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

theorem nat_Tr : \<open>\<forall>n\<in>nat. m\<in>n \<longrightarrow> m\<in>nat\<close>
proof(rule nat_induct_bound)
  show \<open>m \<in> 0 \<longrightarrow> m \<in> nat\<close> by auto
next
  fix x
  assume H0:\<open>x \<in> nat\<close>
  assume H1:\<open>m \<in> x \<longrightarrow> m \<in> nat\<close>
  show \<open>m \<in> succ(x) \<longrightarrow> m \<in> nat\<close>
  proof(rule impI)
    assume H2:\<open>m\<in>succ(x)\<close>
    show \<open>m \<in> nat\<close>
    proof(rule succE[OF H2])
      assume H3:\<open>m = x\<close>
      from H0 and H3 show \<open>m \<in> nat\<close>
        by auto
    next
      assume H4:\<open>m \<in> x\<close>
      show \<open>m \<in> nat\<close>
        by(rule mp[OF H1 H4])
    qed
  qed
qed

(* Natural numbers are linearly ordered. *)
theorem zeroleq : \<open>\<forall>n\<in>nat. 0\<in>n \<or> 0=n\<close>
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

theorem succ_le : \<open>\<forall>n\<in>nat. succ(m)\<in>succ(n) \<longrightarrow> m\<in>n\<close>
proof(rule nat_induct_bound)
  show \<open> succ(m) \<in> 1 \<longrightarrow> m \<in> 0\<close>
    by blast
next
  fix x
  assume H0:\<open>x \<in> nat\<close>
  assume H1:\<open>succ(m) \<in> succ(x) \<longrightarrow> m \<in> x\<close>
  show \<open> succ(m) \<in>
             succ(succ(x)) \<longrightarrow>
             m \<in> succ(x)\<close>
  proof(rule impI)
    assume J0:\<open>succ(m) \<in> succ(succ(x))\<close>
    show \<open>m \<in> succ(x)\<close>
    proof(rule succE[OF J0])
      assume R:\<open>succ(m) = succ(x)\<close>
      hence R:\<open>m=x\<close> by (rule upair.succ_inject)
      from R and succI1 show \<open>m \<in> succ(x)\<close> by auto
    next
      assume R:\<open>succ(m) \<in> succ(x)\<close>
      have R:\<open>m\<in>x\<close> by (rule mp[OF H1 R])
      then show \<open>m \<in> succ(x)\<close> by auto
    qed
  qed
qed

theorem succ_le2 : \<open>\<forall>n\<in>nat. \<forall>m. succ(m)\<in>succ(n) \<longrightarrow> m\<in>n\<close>
proof
  fix n
  assume H:\<open>n\<in>nat\<close>
  show \<open>\<forall>m. succ(m) \<in> succ(n) \<longrightarrow> m \<in> n\<close>
  proof
    fix m
    from succ_le and H show \<open>succ(m) \<in> succ(n) \<longrightarrow> m \<in> n\<close> by auto
  qed
qed

theorem le_succ : \<open>\<forall>n\<in>nat. m\<in>n \<longrightarrow> succ(m)\<in>succ(n)\<close>
proof(rule nat_induct_bound)
  show \<open>m \<in> 0 \<longrightarrow> succ(m) \<in> 1\<close>
    by auto
next
  fix x
  assume H0:\<open>x\<in>nat\<close>
  assume H1:\<open>m \<in> x \<longrightarrow> succ(m) \<in> succ(x)\<close>
  show \<open>m \<in> succ(x) \<longrightarrow>
            succ(m) \<in> succ(succ(x))\<close>
  proof(rule impI)
    assume HR1:\<open>m\<in>succ(x)\<close>
    show \<open>succ(m) \<in> succ(succ(x))\<close>
    proof(rule succE[OF HR1])
      assume Q:\<open>m = x\<close>
      from Q show \<open>succ(m) \<in> succ(succ(x))\<close>
        by auto
    next
      assume Q:\<open>m \<in> x\<close>
      have Q:\<open>succ(m) \<in> succ(x)\<close>
        by (rule mp[OF H1 Q])
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
            by (rule mp[OF bspec[OF le_succ K] G])
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

(* todo
theorem nat_elem_is_ss:\<open>\<forall>m\<in>nat. n\<in>m \<longrightarrow> n\<subseteq>m\<close>
proof(rule nat_induct_bound)
  sorry (**)

theorem nat_ldfghj:\<open>\<forall>n\<in>nat. \<forall>m\<in>nat. n\<subseteq>m \<and> n\<noteq>m \<longrightarrow> n\<in>m\<close>
  sorry
*)

(*
do it through ordinals.
*)
(*
theorem nat_linord_ss:\<open>\<forall>n\<in>nat. \<forall>m\<in>nat. m\<subseteq>n\<or>n\<subseteq>m\<close>
  sorry
*)
(* Union of compatible set of functions is a function. *)
definition compat :: \<open>[i,i]\<Rightarrow>o\<close>
  where "compat(f1,f2) == \<forall>x.\<forall>y1.\<forall>y2.\<langle>x,y1\<rangle> \<in> f1 \<and> \<langle>x,y2\<rangle> \<in> f2 \<longrightarrow> y1=y2"

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
  where \<open>partcomp(A,t,m,a,g) == (t:succ(m)\<rightarrow>A) \<and> (t`0=a) \<and> satpc(t,m,g)\<close>

(* F *)
definition pcs :: \<open>[i,i,i]\<Rightarrow>i\<close>
  where \<open>pcs(A,a,g) == {t\<in>Pow(nat*A). \<exists>m. partcomp(A,t,m,a,g)}\<close>

lemma pcs_ind : 
  assumes F1:\<open>m1\<in>nat\<close>
  assumes F2:\<open>m2\<in>nat\<close>
  assumes H1:\<open>(f1:succ(m1)\<rightarrow>A) \<and> (f1`0=a) \<and> satpc(f1,m1,g)\<close>
  assumes H2:\<open>(f2:succ(m2)\<rightarrow>A) \<and> (f2`0=a) \<and> satpc(f2,m2,g)\<close>
  shows \<open>\<forall>n\<in>nat. n\<in>succ(m1) \<and> n\<in>succ(m2) \<longrightarrow> f1`n = f2`n\<close>
proof(rule nat_induct_bound)
  from H1 and H2 show \<open>0\<in>succ(m1) \<and> 0\<in>succ(m2) \<longrightarrow> f1 ` 0 = f2 ` 0\<close> by auto
next
  fix x
  assume J0:\<open>x\<in>nat\<close>
  assume J1:\<open>x \<in> succ(m1) \<and> x \<in> succ(m2) \<longrightarrow> f1 ` x = f2 ` x\<close>
  from H1 have G1:\<open>\<forall>n \<in> m1 . f1`succ(n) = g ` <f1`n, n>\<close> 
    by (unfold satpc_def, auto)
  from H2 have G2:\<open>\<forall>n \<in> m2 . f2`succ(n) = g ` <f2`n, n>\<close> 
    by (unfold satpc_def, auto)
  show \<open>succ(x) \<in> succ(m1) \<and> succ(x) \<in> succ(m2) \<longrightarrow> 
        f1 ` succ(x) = f2 ` succ(x)\<close>
  proof
    assume K:\<open>succ(x) \<in> succ(m1) \<and> succ(x) \<in> succ(m2)\<close>
    from K have K1:\<open>succ(x) \<in> succ(m1)\<close> by auto
    from K have K2:\<open>succ(x) \<in> succ(m2)\<close> by auto
    have K1':\<open>x \<in> m1\<close> by (rule mp[OF bspec[OF succ_le F1] K1])
    have K2':\<open>x \<in> m2\<close> by (rule mp[OF bspec[OF succ_le F2] K2])
    have U1:\<open>x\<in>succ(m1)\<close> 
      by (rule Nat.succ_in_naturalD[OF K1 Nat.nat_succI[OF F1]])
    have U2:\<open>x\<in>succ(m2)\<close> 
      by (rule Nat.succ_in_naturalD[OF K2 Nat.nat_succI[OF F2]])
    have Y1:\<open>f1`succ(x) = g ` <f1`x, x>\<close>
      by (rule bspec[OF G1 K1'])
    have Y2:\<open>f2`succ(x) = g ` <f2`x, x>\<close>
      by (rule bspec[OF G2 K2'])
    have \<open>f1 ` x = f2 ` x\<close>
      by(rule mp[OF J1 conjI[OF U1 U2]])
    then have Y:\<open>g ` <f1`x, x> = g ` <f2`x, x>\<close> by auto
    from Y1 and Y2 and Y
    show \<open>f1 ` succ(x) = f2 ` succ(x)\<close>
      by auto
  qed
qed


lemma domainsubsetfunc : 
  assumes Q:\<open>f1\<subseteq>f2\<close>
  shows \<open>domain(f1)\<subseteq>domain(f2)\<close>
proof
  fix x
  assume H:\<open>x \<in> domain(f1)\<close>
  show \<open>x \<in> domain(f2)\<close>
  proof(rule domainE[OF H])
    fix y
    assume W:\<open>\<langle>x, y\<rangle> \<in> f1\<close>
    have \<open>\<langle>x, y\<rangle> \<in> f2\<close>
      by(rule subsetD[OF Q W])     
    then show \<open>x \<in> domain(f2)\<close>
      by(rule domainI)
  qed
qed

(*
lemma 
  assumes 1:\<open>q\<in>B\<close>
  shows \<open>domain(A\<times>B) = A\<close>
proof
  show \<open>domain(A \<times> B) \<subseteq> A\<close>
  proof(rule subsetI)
    show \<open> \<And>x. x \<in> domain(A \<times> B) \<Longrightarrow>
         x \<in> A\<close>
      by auto
  qed
next
show \<open>A \<subseteq> domain(A \<times> B)\<close>
proof
  show \<open>\<And>x. x \<in> A \<Longrightarrow>
         x \<in> domain(A \<times> B)\<close>
  proof(rule domainI,auto)
    show \<open>q\<in>A\<close> by (rule 1)
  sorry
*)

lemma natdomfunc:
  assumes 1:\<open>q\<in>A\<close>
  assumes J0:\<open>f1 \<in> Pow(nat \<times> A)\<close>
  assumes U:\<open>m1 \<in> domain(f1)\<close>
  shows \<open>m1\<in>nat\<close>
proof -
  from J0 have J0 : \<open>f1 \<subseteq> nat \<times> A\<close>
    by auto
  have J0:\<open>domain(f1) \<subseteq> domain(nat \<times> A)\<close>
    by(rule func.domain_mono[OF J0])
  have F:\<open>m1 \<in> domain(nat \<times> A)\<close>
    by(rule subsetD[OF J0 U])
  have R:\<open>domain(nat \<times> A) = nat\<close>
    by (rule equalities.domain_of_prod[OF 1])
  show \<open>m1 \<in> nat\<close>
    by(rule subst[OF R], rule F)
qed

(* lemma domain_of_fun: "f \<in> Pi(A,B) ==> domain(f)=A" *)
(*func.domain_type
lemma wertyu:
  assumes \<open>\<langle>x, y1\<rangle> \<in> f1\<close> 
  and \<open>(f1:succ(m1)\<rightarrow>A)\<close>
  shows \<open>x \<in> succ(m1)\<close>
proof (rule domain_of_fun[OF ])

lemma domain_of_fun: "f \<in> Pi(A,B) ==> domain(f)=A"
by (unfold Pi_def, blast)
*)

lemma pcs_lem :
  assumes 1:\<open>q\<in>A\<close>
  shows \<open>compatset(pcs(A, a, g))\<close>
proof (unfold compatset_def)
  show \<open>\<forall>f1\<in>pcs(A, a, g). \<forall>f2\<in>pcs(A, a, g). compat(f1, f2)\<close>
  proof(rule ballI, rule ballI)
    fix f1 f2
    assume H1:\<open>f1 \<in> pcs(A, a, g)\<close>
    then have H1':\<open>f1 \<in> {t\<in>Pow(nat*A). \<exists>m. partcomp(A,t,m,a,g)}\<close> by (unfold pcs_def)
    hence H1'A:\<open>f1 \<in> Pow(nat*A)\<close> by auto
    hence H1'A:\<open>f1 \<subseteq> (nat*A)\<close> by auto
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
          hence K1':\<open>(f1:succ(m1)\<rightarrow>A) \<and> (f1`0=a) \<and> satpc(f1,m1,g)\<close>
            by (unfold partcomp_def)
          assume K2:\<open>partcomp(A, f2, m2, a, g)\<close>
          hence K2':\<open>(f2:succ(m2)\<rightarrow>A) \<and> (f2`0=a) \<and> satpc(f2,m2,g)\<close>
            by (unfold partcomp_def)
          (*have \<open>\<forall>n\<in>nat. P(n)\<close>
 func.apply_equality: \<langle>?a, ?b\<rangle> \<in> ?f \<Longrightarrow> ?f \<in> Pi(?A, ?B) \<Longrightarrow> ?f ` ?a = ?b
*)
          from K1' have K1'A:\<open>(f1:succ(m1)\<rightarrow>A)\<close> by auto
          from K2' have K2'A:\<open>(f2:succ(m2)\<rightarrow>A)\<close> by auto
          from K1'A have K1'AD:\<open>domain(f1) = succ(m1)\<close> 
            by(rule domain_of_fun)
          from K2'A have K2'AD:\<open>domain(f2) = succ(m2)\<close> 
            by(rule domain_of_fun)

          have L1:\<open>f1`x=y1\<close>
            by (rule func.apply_equality[OF P1], rule K1'A)
          have L2:\<open>f2`x=y2\<close>
            by(rule func.apply_equality[OF P2], rule K2'A)
          have m1nat:\<open>m1\<in>nat\<close>
          proof(rule natdomfunc[OF 1 J0])
            show \<open>m1 \<in> domain(f1)\<close>
              by (rule ssubst[OF K1'AD], auto)
          qed
          have m2nat:\<open>m2\<in>nat\<close>
          proof(rule natdomfunc[OF 1 J1])
            show \<open>m2 \<in> domain(f2)\<close>
              by (rule ssubst[OF K2'AD], auto)
          qed
            (* P1:\<open>\<langle>x, y1\<rangle> \<in> f1\<close>
               H1'A:\<open>f1 \<subseteq> (nat*A)\<close>
            *)
          have G1:\<open>\<langle>x, y1\<rangle> \<in> (nat*A)\<close>
            by(rule subsetD[OF H1'A P1])
          have KK:\<open>x\<in>nat\<close>
            by(rule SigmaE[OF G1], auto)
(* x is in  the domain of f1  ---- succ(m1)
so we can have both  x \<in> ?m1.2 \<and> x \<in> ?m2.2 
how to prove that m1 \<in> nat ? from J0 !  f1 is a subset of nat \<times> A *)
          have W:\<open>f1`x=f2`x\<close>
          proof(rule mp[OF bspec[OF pcs_ind KK] ]) (*good!*)
            show \<open>m1 \<in> nat\<close>
              by (rule m1nat)
          next
            show \<open>m2 \<in> nat\<close>
              by (rule m2nat)
          next
            show \<open>f1 \<in> succ(m1) -> A \<and>
    f1 ` 0 = a \<and> satpc(f1, m1, g)\<close>
              by (rule K1')
          next
            show \<open>f2 \<in> succ(m2) -> A \<and>
    f2 ` 0 = a \<and> satpc(f2, m2, g)\<close>
              by (rule K2')
          next
            (*  P1:\<open>\<langle>x, y1\<rangle> \<in> f1\<close> 
              K1'A:\<open>(f1:succ(m1)\<rightarrow>A)\<close>
            *)
            have U1:\<open>x \<in> succ(m1)\<close>
              by (rule func.domain_type[OF P1 K1'A])
            have U2:\<open>x \<in> succ(m2)\<close>
              by (rule func.domain_type[OF P2 K2'A])
            show \<open>x \<in> succ(m1) \<and> x \<in> succ(m2)\<close>
              by (rule conjI[OF U1 U2])
          qed
          from L1 and W and L2
          show \<open>y1 = y2\<close> by auto
(*
  shows \<open>\<forall>n\<in>nat. n\<in>m1 \<and> n\<in>m2 \<longrightarrow> f1`n = f2`n\<close>
 x < succ(m1) & x < succ(m2)
x \<in> nat
nat_induct_bound :
  assumes H0:\<open>P(0)\<close>
  assumes H1:\<open>!!x. x\<in>nat \<Longrightarrow> P(x) \<Longrightarrow> P(succ(x))\<close>
  shows \<open>\<forall>n\<in>nat. P(n)\<close>
*)
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

locale rec_thm =
  fixes A a g
  assumes H1:\<open>a \<in> A\<close>
  assumes H2:\<open>g : ((A*nat)\<rightarrow>A)\<close>
begin

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
proof(unfold function_def)
  show \<open> \<forall>x y. \<langle>x, y\<rangle> \<in> {\<langle>0, a\<rangle>} \<longrightarrow>
          (\<forall>y'. \<langle>x, y'\<rangle> \<in> {\<langle>0, a\<rangle>} \<longrightarrow>
                y = y')\<close>
  proof(rule allI,rule allI,rule impI,rule allI,rule impI)
    fix x y y'
    assume H0:\<open>\<langle>x, y\<rangle> \<in> {\<langle>0, a\<rangle>}\<close>
    assume H1:\<open>\<langle>x, y'\<rangle> \<in> {\<langle>0, a\<rangle>}\<close>
    show \<open>y = y'\<close>
    proof(rule upair.singletonE[OF H0],rule upair.singletonE[OF H1])
      assume H0:\<open>\<langle>x, y\<rangle> = \<langle>0, a\<rangle>\<close>
      assume H1:\<open>\<langle>x, y'\<rangle> = \<langle>0, a\<rangle>\<close>
      from H0 and H1 have H:\<open>\<langle>x, y\<rangle> = \<langle>x, y'\<rangle>\<close> by auto
      then show \<open>y = y'\<close> by auto
    qed
  qed
qed

lemma singlsatpc:\<open>satpc({\<langle>0, a\<rangle>}, 0, g)\<close>
proof(unfold satpc_def)
  show \<open>\<forall>n\<in>0. {\<langle>0, a\<rangle>} ` succ(n) =
           g ` \<langle>{\<langle>0, a\<rangle>} ` n, n\<rangle>\<close>
    by auto
qed

lemma zainupcs : \<open>\<langle>0, a\<rangle> \<in> \<Union>pcs(A, a, g)\<close>
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
          show \<open>{\<langle>0, a\<rangle>} \<in> 1 -> A \<and> {\<langle>0, a\<rangle>} ` 0 = a \<and> satpc({\<langle>0, a\<rangle>}, 0, g)\<close>
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
                      by auto
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
            show \<open>{\<langle>0, a\<rangle>} ` 0 = a \<and> satpc({\<langle>0, a\<rangle>}, 0, g)\<close>
            proof
              show \<open>{\<langle>0, a\<rangle>} ` 0 = a\<close>
                by (rule func.singleton_apply)
            next
              show \<open>satpc({\<langle>0, a\<rangle>}, 0, g)\<close>
                by (rule singlsatpc)
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma l2': \<open>0 \<in> domain(\<Union>pcs(A, a, g))\<close>
proof
  show \<open>\<langle>0, a\<rangle> \<in> \<Union>pcs(A, a, g)\<close>
    by (rule zainupcs)
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
    proof(rule domainE[OF Q2])
      fix y
      assume W1:\<open>\<langle>x, y\<rangle> \<in> (\<Union>pcs(A, a, g))\<close>
      show \<open>succ(x)\<in>domain(\<Union>pcs(A, a, g))\<close>
      proof(rule UnionE[OF W1])
        fix t
        assume E1:\<open>\<langle>x, y\<rangle> \<in> t\<close>
        assume E2:\<open>t \<in> pcs(A, a, g)\<close>
        hence E2:\<open>t\<in>{t\<in>Pow(nat*A). \<exists>m. partcomp(A,t,m,a,g)}\<close> 
          by(unfold pcs_def)
        have E21:\<open>t\<in>Pow(nat*A)\<close>
          by(rule CollectD1[OF E2])
        have E22:\<open>\<exists>m. partcomp(A,t,m,a,g)\<close>
          by(rule CollectD2[OF E2])
        show \<open>succ(x)\<in>domain(\<Union>pcs(A, a, g))\<close>
        proof(rule exE[OF E22])
          fix m
          assume E22:\<open>partcomp(A,t,m,a,g)\<close>
          hence E22:\<open>((t:succ(m)\<rightarrow>A) \<and> (t`0=a)) \<and> satpc(t,m,g)\<close> 
            by(unfold partcomp_def, auto)
          hence E223:\<open>satpc(t,m,g)\<close> by auto
          hence E223:\<open>\<forall>n \<in> m . t`succ(n) = g ` <t`n, n>\<close>
            by(unfold satpc_def, auto)
          show \<open>succ(x)\<in>domain(\<Union>pcs(A, a, g))\<close>
          proof
        (*proof(rule exE[OF E22])*)
            show \<open> \<langle>succ(x), g ` <t`x, x>\<rangle> \<in> (\<Union>pcs(A, a, g))\<close> (*?*)
            proof
             (*t\<union>{\<langle>succ(x), g ` <t`x, x>\<rangle>}*)
              show \<open>cons(\<langle>succ(x), g ` <t`x, x>\<rangle>, t) \<in> pcs(A, a, g)\<close>
              proof(unfold pcs_def, rule CollectI)
                show \<open> cons(\<langle>succ(x),g ` \<langle>t ` x, x\<rangle>\<rangle>,t) \<in> Pow(nat \<times> A)\<close>
                  sorry
              next
                show \<open>\<exists>m. partcomp(A, cons(\<langle>succ(x), g ` \<langle>t ` x, x\<rangle>\<rangle>, t), m, a, g)\<close>
                  sorry
              qed
            next
              show \<open>\<langle>succ(x), g ` \<langle>t ` x, x\<rangle>\<rangle> \<in> cons(\<langle>succ(x), g ` \<langle>t ` x, x\<rangle>\<rangle>, t)\<close>
                by auto
            qed
(*
  where \<open>satpc(t,\<alpha>,g) == \<forall>n \<in> \<alpha> . t`succ(n) = g ` <t`n, n>\<close>
  where \<open>partcomp(A,t,m,a,g) == (t:succ(m)\<rightarrow>A) \<and> (t`0=a) \<and> satpc(t,m,g)\<close>
  where \<open>pcs(A,a,g) == {t\<in>Pow(nat*A). \<exists>m. partcomp(A,t,m,a,g)}\<close>
*)
          qed
        qed
      qed
    qed
  next
    show \<open>0 \<in> domain(\<Union>pcs(A, a, g))\<close>
      by (rule l2')
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
proof(rule func.function_apply_equality)
  show \<open>function(\<Union>pcs(A, a, g))\<close>
    by (rule l3)
next
  show \<open>\<langle>0, a\<rangle> \<in> \<Union>pcs(A, a, g)\<close>
    by (rule zainupcs)
qed
(*sketch - *)

lemma l6: \<open>satpc(\<Union>pcs(A, a, g), nat, g)\<close>
proof (unfold satpc_def)
  show \<open>\<forall>n\<in>nat.
       (\<Union>pcs(A, a, g)) ` succ(n) = g ` \<langle>(\<Union>pcs(A, a, g)) ` n, n\<rangle>\<close>
  proof (rule nat_induct_bound)
    show \<open>(\<Union>pcs(A, a, g)) ` 1 = g ` \<langle>(\<Union>pcs(A, a, g)) ` 0, 0\<rangle>\<close>
      sorry
  next
    fix x
    assume 1: \<open>x\<in>nat\<close>
    assume 2: \<open>(\<Union>pcs(A, a, g)) ` succ(x) =
         g ` \<langle>(\<Union>pcs(A, a, g)) ` x, x\<rangle>\<close>
    show \<open>(\<Union>pcs(A, a, g)) ` succ(succ(x)) =
         g ` \<langle>(\<Union>pcs(A, a, g)) ` succ(x), succ(x)\<rangle>\<close>
      sorry
  qed
qed

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
(*
  fixes A a g
  assumes H1:\<open>a \<in> A\<close>
  assumes H2:\<open>g : ((A*nat)\<rightarrow>A)\<close>
*)
theorem recursion:
  shows \<open>\<exists>!f. ((f \<in> (nat\<rightarrow>A)) \<and> ((f`0) = a) \<and> satpc(f,nat,g))\<close>
(* where \<open>satpc(t,\<alpha>,g) == \<forall>n \<in> \<alpha> . t`succ(n) = g ` <t`n, n>\<close> *)
(*
  fixes A n a1 a2 g
  assumes H11:\<open>a1 \<in> A\<close>
  assumes H12:\<open>a2 \<in> A\<close>
  assumes H2:\<open>g : ((A*n)\<rightarrow>A)\<close>
theorem finite_recursion:
  shows \<open>\<exists>!f. ((f \<in> (n\<rightarrow>A)) \<and> ((f`0) = a1) \<and> (f`n) = a2) \<and> satpc(f,n,g))\<close>
*)
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

(* Definition of addition *)
(*
locale rec_thm =
  fixes A a g
  assumes H1:\<open>a \<in> A\<close>
  assumes H2:\<open>g : ((A*nat)\<rightarrow>A)\<close>
theorem recursion:
  shows \<open>\<exists>!f. ((f \<in> (nat\<rightarrow>A)) \<and> ((f`0) = a) \<and> satpc(f,nat,g))\<close>
  oops
end
*)

definition add_g :: \<open>i\<close>
  where add_g_def : \<open>add_g == {\<langle>x,x\<rangle>. x\<in>nat}\<close>
(* {z \<in> nat*nat . \<langle>x,x\<rangle> } *)
theorem addition:
 \<open>\<exists>!f. ((f \<in> (nat\<rightarrow>A)) \<and> ((f`0) = a) \<and> satpc(f,nat,add_g))\<close>
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

end
