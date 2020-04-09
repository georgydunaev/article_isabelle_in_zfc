theory main imports ZF
begin
(* Main aim is to prove Recursion Theorem *)

definition satpc :: \<open>[i,i,i] \<Rightarrow> o \<close>
  where \<open>satpc(t,\<alpha>,g) == (
\<forall>n \<in> \<alpha> . (t`(succ(n))) = (g ` (<(t`n), n>)))\<close>
                            
(* m-step computation based on a and g *)
definition partcomp :: \<open>[i,i,i,i,i]=>o\<close>
  where \<open>partcomp(A,t,m,a,g) == (t:succ(m)\<rightarrow>A) \<and>
(t`0=a) \<and> satpc(t,succ(m),g)\<close>

(* F *)
definition pcs :: \<open>[i,i,i]\<Rightarrow>i\<close>
  where \<open>pcs(A,a,g) == {t\<in>Pow(nat*A). \<exists>m. partcomp(A,t,m,a,g)}\<close>

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



theorem requniqlem : \<open>\<And>f y. f \<in> nat -> A \<and>
           f ` 0 = a \<and>
           satpc(f, nat, g) \<Longrightarrow>
           y \<in> nat -> A \<and>
           y ` 0 = a \<and>
           satpc(y, nat, g) \<Longrightarrow>
           f \<subseteq> y\<close>
proof
  fix f
  assume H0:\<open>f \<in> nat -> A \<and> f ` 0 = a \<and> satpc(f, nat, g)\<close>
  fix t
  assume H1:\<open>t \<in> nat -> A \<and> t ` 0 = a \<and> satpc(t, nat, g)\<close>
  fix x
  assume H2:\<open>x \<in> f\<close>
(*
f \<in> nat -> A
f\<in>Pow(Sigma(nat,\<lambda>_.A)) ==== f \<in> Pow(nat \<times> A)
f\<subseteq>Sigma(nat,\<lambda>_.A)
*)
  from H1 have H11:\<open>t ` 0 = a\<close> by auto
  from H1 have H10:\<open>t \<in> nat -> A\<close> by auto
  from H0 have H01:\<open>f ` 0 = a\<close> by auto
  from H0 have H00:\<open>f \<in> nat -> A\<close> by auto
  then have \<open>f\<in>{f\<in>Pow(Sigma(nat,\<lambda>_.A)). nat\<subseteq>domain(f) & function(f)}\<close> by (unfold Pi_def)
  then have \<open>f\<in>Pow(nat \<times> A)\<close> by (rule CollectD1)
  then have Q:\<open>f\<subseteq>nat*A\<close> by auto
  from H2 and Q have J0:\<open>x\<in>nat*A\<close> by auto
  then have J:\<open>fst(x) \<in> nat\<close> by auto
  then have \<open>fst(x) = 0 \<or> (\<exists>y. fst(x) = succ(y))\<close>
  proof (rule natE)
    show \<open>fst(x) = 0 \<Longrightarrow>
    fst(x) = 0 \<or> (\<exists>y. fst(x) = succ(y))\<close>
      by auto
  next
    show \<open>\<And>xa. xa \<in> nat \<Longrightarrow>
          fst(x) = succ(xa) \<Longrightarrow>
          fst(x) = 0 \<or>
          (\<exists>y. fst(x) = succ(y))\<close>
      by auto
  qed

  show \<open>x \<in> t\<close>
  proof (rule natE[OF J])
    assume K:\<open>fst(x)=0\<close>
(*Pair_fst_snd_eq
(simp only: Pi_iff)
apply_iff
*)
    from J0 have M:\<open>x=<fst(x),snd(x)>\<close>
      by auto
    from K and M have M:\<open>x=<0,snd(x)>\<close> by auto
    (*from H01 have \<open>snd(x) = a\<close> 
      sorry*)
    from H00 and H01 have P1:\<open><0, a>\<in>f\<close>
      by (simp add: apply_iff)
    from H10 and H11 have P2:\<open><0, a>\<in>t\<close>
      by (simp add: apply_iff)
(*
apply_equality: "[| <a,b>: f;  f \<in> Pi(A,B) |] ==> f`a = b"
apply_equality2
*)
    from H2 and M have TYU:\<open><0,snd(x)>\<in>f\<close> by auto
    from TYU and P1 and H00 have EW:\<open>snd(x) = a\<close> by (rule apply_equality2)
    from EW and M have TY:\<open>x=<0, a>\<close> by auto
    from TY and P2 show \<open>x \<in> t\<close> by auto
  next
    fix n
    assume L1:\<open>n\<in>nat\<close>
    assume L2:\<open>fst(x) = succ(n)\<close>
    from H1 have H13:\<open>satpc(t, nat, g)\<close> by auto
    from H13 have H13:\<open>\<forall>n \<in> nat . (t`(succ(n))) = (g ` (<(t`n), n>))\<close> by (unfold satpc_def)
    have Y:\<open>(t`(succ(n))) = (g ` (<(t`n), n>))\<close> 
      by (rule bspec[OF H13 L1])
    have RI:\<open>succ(n)\<in>nat\<close>
      sorry
    from RI and Y have \<open><(succ(n)), (g ` (<(t`n), n>))>\<in>t\<close>
    (*proof (simp add: apply_iff)*)
      sorry
    show \<open>x \<in> t\<close>
      sorry
  qed
  (*show \<open>\<And>f y x.
       f \<in> nat -> A \<and>
       f ` 0 = a \<and> satpc(f, nat, a, g) \<Longrightarrow>
       y \<in> nat -> A \<and>
       y ` 0 = a \<and> satpc(y, nat, a, g) \<Longrightarrow>
       x \<in> f \<Longrightarrow> x \<in> y\<close>
    sorry*)
qed

theorem recursion:
  assumes H1:\<open>a \<in> A\<close>
  assumes H2:\<open>g : ((A*nat)\<rightarrow>A)\<close>
  shows \<open>\<exists>!f. ((f \<in> (nat\<rightarrow>A)) \<and> ((f`0) = a) \<and> satpc(f,nat,g))\<close>
proof 
  show \<open>\<exists>f. f \<in> nat -> A \<and> f ` 0 = a \<and> satpc(f, nat, g)\<close>
  proof 
    show \<open>pcs(A,a,g) \<in> nat -> A \<and> pcs(A,a,g) ` 0 = a \<and> satpc(pcs(A,a,g), nat, g)\<close>
    proof
      show \<open>pcs(A,a,g) \<in> nat -> A\<close>
        sorry
    next
      show \<open>pcs(A, a, g) ` 0 = a \<and> satpc(pcs(A, a, g), nat, g)\<close>
      proof 
        show \<open>pcs(A, a, g) ` 0 = a\<close>
          sorry
      next
        show \<open>satpc(pcs(A, a, g), nat, g)\<close>
          sorry
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
  proof
    show \<open> \<And>f y. f \<in> nat -> A \<and>
           f ` 0 = a \<and>
           satpc(f, nat, g) \<Longrightarrow>
           y \<in> nat -> A \<and>
           y ` 0 = a \<and>
           satpc(y, nat, g) \<Longrightarrow>
           f \<subseteq> y\<close>
      by (rule requniqlem)
  next
    show \<open>\<And>f y. f \<in> nat -> A \<and>
           f ` 0 = a \<and>
           satpc(f, nat, g) \<Longrightarrow>
           y \<in> nat -> A \<and>
           y ` 0 = a \<and>
           satpc(y, nat, g) \<Longrightarrow>
           y \<subseteq> f\<close>
      by (rule requniqlem)
  qed
qed





definition fite :: "[i, o, i, i] \<Rightarrow> i" (\<open>from _ if _ then _ else _\<close>)
  where "fite(A, \<phi>, a, b) == \<Union>{x\<in>A.(\<phi>\<and>x=a)\<or>((\<not>\<phi>)\<and>x=b)}"

definition ite :: "[o, i, i] \<Rightarrow> i" (\<open>myif _ then _ else _\<close>)
  where "ite(\<phi>, a, b) == \<Union>{x\<in>{a,b}.(\<phi>\<and>x=a)\<or>((\<not>\<phi>)\<and>x=b)}"

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

definition compat :: \<open>[i,i]\<Rightarrow>o\<close>
  where "compat(f1,f2) == \<forall>x\<in>(domain(f1)\<inter>domain(f2)).
\<forall>y1.\<forall>y2.\<langle>x,y1\<rangle> \<in> f1 \<and> \<langle>x,y2\<rangle> \<in> f2 \<longrightarrow> y1=y2"

definition compatset :: \<open>i\<Rightarrow>o\<close>
  where "compatset(S) == \<forall>f1\<in>S.\<forall>f2\<in>S. compat(f1,f2)" 

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