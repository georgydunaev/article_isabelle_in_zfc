theory additional imports recursion
begin

(*
  have \<open>f ` a = v\<close>
    sorry
  proof(rule mkel, rule apparg)
    show \<open>(\<Union>S)`a = v\<close> by (rule N)
    show \<open>a\<in>A\<close> by (rule T)
    oops
*)
 (*todo!*)
(*  show \<open>f ` a = v\<close> *)


(* Natural numbers are linearly ordered by \<in> *)


definition add_g2 :: \<open>i\<close>
  where add_g2_def : \<open>add_g2 == {p \<in> (nat \<times> nat) \<times> nat. snd(p) = succ(fst(fst(p)))}\<close>

theorem addg2subpow : \<open>add_g2 \<in> Pow((nat \<times> nat) \<times> nat)\<close>
proof
  show \<open>add_g2 \<subseteq> (nat \<times> nat) \<times> nat\<close>
  proof
    fix x
    assume \<open>x \<in> add_g2\<close>
    hence G:\<open>x \<in> {p \<in> (nat \<times> nat) \<times> nat . snd(p) = succ(fst(fst(p)))}\<close>
      by (unfold add_g2_def)
    show \<open>x \<in> (nat \<times> nat) \<times> nat\<close>
      by(rule CollectD1[OF G])
  qed
qed

lemma addg2dom : \<open>nat \<times> nat \<subseteq> domain(add_g2)\<close>
proof
  fix x
  assume xnn:\<open>x\<in>nat \<times> nat\<close>
  hence fxn:\<open>fst(x)\<in>nat\<close> by auto
  show \<open>x\<in>domain(add_g2)\<close>
  proof
(*snd(p) = succ(fst(fst(p)))*)
    show \<open>\<langle>x, succ(fst(x))\<rangle> \<in> add_g2\<close>
    proof(unfold add_g2_def, rule CollectI)
      show \<open>\<langle>x, succ(fst(x))\<rangle> \<in> (nat \<times> nat) \<times> nat\<close>
      proof
        show \<open>x\<in>nat \<times> nat\<close> by (rule xnn)
      next
        from fxn
        show \<open>succ(fst(x)) \<in> nat\<close> by auto
      qed
    next
      show \<open>snd(\<langle>x, succ(fst(x))\<rangle>) =
    succ(fst(fst(\<langle>x, succ(fst(x))\<rangle>)))\<close>
      proof(rule trans, rule pair.snd_conv)
        have \<open>x = fst(\<langle>x, succ(fst(x))\<rangle>)\<close>
          by (rule sym, rule pair.fst_conv)
        hence \<open> fst(x) = fst(fst(\<langle>x, succ(fst(x))\<rangle>))\<close>
          by(rule subst_context)
        thus \<open> succ(fst(x)) =
    succ(fst(fst(\<langle>x, succ(fst(x))\<rangle>)))\<close>
          by(rule subst_context)
        qed
    qed
  qed
qed

lemma addg2fun: \<open>function(add_g2)\<close>
proof(unfold function_def, unfold add_g2_def, rule allI, rule allI, rule impI, rule allI, rule impI)
  fix x y1 y2
  assume H1:\<open>\<langle>x, y1\<rangle> \<in> add_g2\<close>
  assume H2:\<open>\<langle>x, y1\<rangle> \<in> add_g2\<close>
  oops


(* 
then prove transfinite induction & recursion
then define Von Neumann hierarchy
then prove V=\<Union>(\<alpha>\<in>Ord).V\<alpha>
trying to rewrite everything without replacement
*)

subsection \<open>Only\<close>

text \<open>Quantifier "!x. P(x)" means "at most one object has property P"\<close>

definition Only1 :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close>  (binder \<open>!\<close> 10)
  where only1_def: \<open>!x. P(x) \<equiv> (\<forall>x.\<forall>y. P(x) \<and> P(y) \<longrightarrow> x = y)\<close>

lemma only1I [intro]: 
  assumes H: \<open>(\<And>x y. (\<lbrakk>P(x); P(y)\<rbrakk> \<Longrightarrow> x = y))\<close>
  shows \<open>!x. P(x)\<close>
  by (unfold only1_def, rule allI, rule allI, rule impI, rule H,
        erule conjunct1, erule conjunct2)

lemma only1D: \<open>!x. P(x) \<Longrightarrow> (\<And>x y. \<lbrakk>P(x); P(y)\<rbrakk> \<Longrightarrow> x = y)\<close>
  apply(unfold only1_def)
  apply(rule mp, rule spec, erule spec)
  apply(erule conjI, assumption)
  done

lemma only1E [elim]:
  assumes major: \<open>!x. P(x)\<close>
      and r: \<open>(\<And>x y. \<lbrakk>P(x); P(y)\<rbrakk> \<Longrightarrow> x = y) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
  by (rule r, rule only1D[OF major], assumption+)


lemma ex1newD1: \<open>\<exists>!x. P(x) \<Longrightarrow> \<exists>x. P(x)\<close>
  by auto

lemma ex1newD2: \<open>\<exists>!x. P(x) \<Longrightarrow> !x. P(x)\<close>
proof -
  assume Y:\<open>\<exists>!x. P(x)\<close>
  show \<open>(!x. P(x))\<close>
  proof(rule ex1E[OF Y])
    fix x
    assume Px:\<open>P(x)\<close>
    assume J:\<open>\<forall>y. P(y) \<longrightarrow> y = x\<close>
    show \<open>(!x. P(x))\<close>
    proof
      fix x1 x2
      assume Px1:\<open>P(x1)\<close>
      assume Px2:\<open>P(x2)\<close>
      show \<open>x1 = x2\<close>
      proof(rule trans, rule mp, rule spec[OF J], rule Px1)
        show \<open>x = x2\<close>
          by (rule sym, rule mp, rule spec[OF J], rule Px2)
      qed
    qed
  qed
qed

subsection \<open>Uniqueness\<close>

text \<open>Another uniqueness definition\<close>

lemma ex1new_def: \<open>\<exists>!x. P(x) \<equiv> (\<exists>x. P(x)) \<and> (!x. P(x))\<close>
proof (rule iff_reflection, rule iffI)
  assume Y:\<open>\<exists>!x. P(x)\<close>
  show \<open>(\<exists>x. P(x)) \<and> (!x. P(x))\<close>
  proof
    from Y show \<open>(\<exists>x. P(x))\<close> by auto
  next
    from Y show \<open>(!x. P(x))\<close> by (rule ex1newD2)
  qed
next
  assume Y:\<open>(\<exists>x. P(x)) \<and> (!x. P(x))\<close>
  hence Y2:\<open>(!x. P(x))\<close> by auto
  show \<open>\<exists>!x. P(x)\<close>
  proof
    from Y show \<open>(\<exists>x. P(x))\<close> by auto
  next
    show \<open>\<And>x y. P(x) \<Longrightarrow> P(y) \<Longrightarrow> x = y\<close>
      by (rule only1D[OF Y2], assumption+)
  qed
qed

lemma ex1newI: \<open>\<lbrakk>\<exists>x. P(x); !x. P(x)\<rbrakk> \<Longrightarrow> \<exists>!x. P(x)\<close>
  by (unfold ex1new_def, rule conjI, assumption+)

lemma ex1newE: \<open>\<exists>!x. P(x) \<Longrightarrow> (\<lbrakk>\<exists>x. P(x); !x. P(x)\<rbrakk> \<Longrightarrow> R) \<Longrightarrow> R\<close>
  apply (unfold ex1new_def)
  apply (assumption | erule exE conjE)+
  done
(*
lemma ex1newD1: \<open>\<exists>!x. P(x) \<Longrightarrow> \<exists>x. P(x)\<close>
  by (erule ex1newE)

lemma ex1newD2: \<open>\<exists>!x. P(x) \<Longrightarrow> !x. P(x)\<close>
  by (erule ex1newE)
*)

subsection\<open>Bounded existential quantifier\<close>

definition Bonly :: "[i, i \<Rightarrow> o] \<Rightarrow> o"
  where "Bonly(A, P) \<equiv> !x. x\<in>A \<and> P(x)"

syntax
  "_Bonly" :: "[pttrn, i, o] \<Rightarrow> o"  (\<open>(3!_\<in>_./ _)\<close> 10)
translations
  "!x\<in>A. P" \<rightleftharpoons> "CONST Bonly(A, \<lambda>x. P)"

lemma bonlyI [intro]: "[| !x. (x\<in>A \<and> P(x)) |] ==> !x\<in>A. P(x)"
  by (unfold Bonly_def, assumption)

lemma bonlyE [elim!]: "[| !x\<in>A. P(x);  [| !x. (x\<in>A \<and> P(x)) |] ==> Q |] ==> Q"
  by (unfold Bonly_def, blast)

definition Bex1 :: "[i, i \<Rightarrow> o] \<Rightarrow> o"
  where "Bex1(A, P) \<equiv> (\<exists>x\<in>A. P(x)) \<and> (!x\<in>A. P(x))"

syntax
  "_Bex1" :: "[pttrn, i, o] \<Rightarrow> o"  (\<open>(3\<exists>!_\<in>_./ _)\<close> 10)
translations
  "\<exists>!x\<in>A. P" \<rightleftharpoons> "CONST Bex1(A, \<lambda>x. P)"

lemma bex1I [intro]: "[| \<exists>x\<in>A. P(x) ; !x\<in>A. P(x) |] ==> \<exists>!x\<in>A. P(x)"
  by (unfold Bex1_def, auto)

lemma bex1E [elim!]: "[| \<exists>!x\<in>A. P(x);  [| \<exists>x\<in>A. P(x) ; !x\<in>A. P(x) |] ==> Q |] ==> Q"
  by (unfold Bex1_def, blast)


lemma mychoice:
  assumes D:\<open>\<forall>x\<in>A.\<exists>y. y\<in>B(x)\<close>
  shows \<open>\<exists>f. f\<in>Pi(A,B)\<close>
  oops

lemma basedomsig : \<open>domain(Sigma(A, B)) \<subseteq> A\<close>
proof
  fix x
  assume J:\<open>x \<in> domain(Sigma(A, B))\<close>
  show \<open>x\<in>A\<close>
  proof(rule domainE[OF J])
    fix y
    assume K:\<open>\<langle>x, y\<rangle> \<in> Sigma(A, B)\<close>
    show \<open>x\<in>A\<close>
      by (rule SigmaD1[OF K])
  qed
qed

lemma domsig:
  assumes H:\<open>\<forall>x\<in>A.\<exists>y. y\<in>B(x)\<close>
  shows \<open>A\<subseteq>domain(Sigma(A, B))\<close>
proof
  fix x
  assume L:\<open>x\<in>A\<close>
  have U:\<open>\<exists>y. y\<in>B(x)\<close>
    by (rule bspec[OF H L])
  show \<open>x \<in> domain(Sigma(A, B))\<close>
  proof(rule exE[OF U])
    fix y
    assume V:\<open>y\<in>B(x)\<close>
    show \<open>x \<in> domain(Sigma(A, B))\<close>
    proof
      show \<open>\<langle>x, y\<rangle> \<in> Sigma(A, B)\<close>
      proof
        show \<open>x\<in>A\<close> by (rule L)
      next
        show \<open>y\<in>B(x)\<close> by (rule V)
      qed
    qed
  qed
qed

lemma fuch:
  assumes H:\<open>\<forall>x\<in>A.\<exists>!y. P(x,y)\<close>
  shows \<open>\<forall>x\<in>A.\<exists>y. P(x,y)\<close>
proof
  fix x
  assume \<open>x\<in>A\<close>
  hence \<open>\<exists>!y. P(x,y)\<close>
    by (rule bspec[OF H])
  thus \<open>\<exists>y. P(x, y)\<close> 
    by auto
qed

lemma bfuch:
  assumes H:\<open>\<forall>x\<in>A.\<exists>!y\<in>B(x). P(x,y)\<close>
  shows \<open>\<forall>x\<in>A.\<exists>y\<in>B(x). P(x,y)\<close>
proof
  fix x
  assume \<open>x\<in>A\<close>
  hence \<open>\<exists>!y\<in>B(x). P(x,y)\<close>
    by (rule bspec[OF H])
  thus \<open>\<exists>y\<in>B(x). P(x, y)\<close> 
    by auto
qed

lemma mkfun:
  assumes H:\<open>\<forall>x\<in>A.\<exists>!y. y\<in>B(x)\<close>
  shows \<open>\<exists>f. f\<in>Pi(A,B)\<close>
proof
  show \<open>Sigma(A,B)\<in>Pi(A,B)\<close>
  proof(unfold Pi_def)
    show \<open>Sigma(A, B) \<in> {f \<in> Pow(Sigma(A, B)) . A \<subseteq> domain(f) \<and> function(f)}\<close>
    proof
      show \<open>Sigma(A, B) \<in> Pow(Sigma(A, B))\<close>
        by (rule PowI, auto)
    next
      show \<open>A \<subseteq> domain(Sigma(A, B)) \<and> function(Sigma(A, B))\<close>
      proof
        show \<open>A \<subseteq> domain(Sigma(A, B))\<close>
          by (rule domsig, rule fuch, rule H)
      next
        show \<open>function(Sigma(A, B))\<close>
        proof(rule functionI)
          fix x y1 y2
          assume J1:\<open>\<langle>x, y1\<rangle> \<in> Sigma(A, B)\<close>
          assume J2:\<open>\<langle>x, y2\<rangle> \<in> Sigma(A, B)\<close>
          show \<open>y1=y2\<close>
          proof(rule SigmaE[OF J1], rule SigmaE[OF J2])
            fix xa1 xa2 ya1 ya2
            assume M1:\<open>xa1 \<in> A\<close>
            assume M2:\<open>ya1 \<in> B(xa1)\<close>
            assume M3:\<open>\<langle>x, y1\<rangle> = \<langle>xa1, ya1\<rangle>\<close>
            assume M4:\<open>xa2 \<in> A\<close>
            assume M5:\<open>ya2 \<in> B(xa2)\<close>
            assume M6:\<open>\<langle>x, y2\<rangle> = \<langle>xa2, ya2\<rangle>\<close>

            from M3 have M31:\<open>x=xa1\<close> by (rule pair.Pair_inject1)
            from M6 have M61:\<open>x=xa2\<close> by (rule pair.Pair_inject1)
            from M1 and M31 have M1:\<open>x \<in> A\<close> by auto
            from M2 and M31 have M2:\<open>ya1 \<in> B(x)\<close> by auto
            from M5 and M61 have M5:\<open>ya2 \<in> B(x)\<close> by auto
            from M3 have M32:\<open>y1=ya1\<close> by (rule pair.Pair_inject2)
            from M6 have M62:\<open>y2=ya2\<close> by (rule pair.Pair_inject2)
            have \<open>\<exists>!y. y\<in>B(x)\<close> by(rule bspec[OF H M1])
            hence Q:\<open>!y. y\<in>B(x)\<close> by auto
            show \<open>y1=y2\<close>
            proof(rule only1D[OF Q])
              from M32 and M2 show \<open>y1 \<in> B(x)\<close>
                by auto
              from M62 and M5 show \<open>y2 \<in> B(x)\<close>
                by auto
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma splt:
  assumes H:\<open>f\<in>Pi(A,\<lambda>x. {y\<in>B(x). P(x,y)})\<close>
  shows \<open>f\<in>Pi(A,B)\<and>(\<forall>x\<in>A. P(x,f`x))\<close>
proof -
  from H
  have K:\<open>f\<in>{f\<in>Pow(Sigma(A,\<lambda>x. {y\<in>B(x). P(x,y)})). A\<subseteq>domain(f) & function(f)}\<close>
    by (unfold Pi_def)
  show ?thesis
  proof
    show \<open>f \<in> Pi(A, B)\<close>
      by (rule CollectE[OF K], unfold Pi_def, rule CollectI, auto)
  next
    show \<open>\<forall>x\<in>A. P(x, f ` x)\<close>
    proof
      fix x
      assume L:\<open>x\<in>A\<close>
      have R:\<open>(f`x)\<in>{y\<in>B(x). P(x,y)}\<close>
        by (rule func.apply_type[OF H L])
      show \<open>P(x, f ` x)\<close>
        by (rule CollectD2[OF R])
    qed
  qed
qed
(* f = {p\<in>Sigma(A,B). }*)

(*
proof(unfold Pi_def)
  show \<open> \<exists>f. f \<in> {f \<in> Pow(Sigma(A, B)) . A \<subseteq> domain(f) \<and> function(f)}\<close>
*)
lemma kjhg:
  assumes D:\<open>\<forall>x\<in>A.\<exists>!y\<in>B(x). P(x,y)\<close>
  shows \<open>\<exists>!f\<in>Pi(A,B).\<forall>x\<in>A. P(x, f`y)\<close>
proof
  have D1:\<open>\<forall>x\<in>A.\<exists>y\<in>B(x). P(x,y)\<close>
    by (rule bfuch[OF D])

  show \<open>\<exists>f\<in>Pi(A, B). \<forall>x\<in>A. P(x, f ` y)\<close>
  proof


    oops
(*rule splt*)

lemma kjhg:
  assumes D:\<open>\<forall>x\<in>A.\<exists>!y. y\<in>B \<and> <x,y>\<in>f\<close>
  shows \<open>f\<in>A\<rightarrow>B\<close>s
proof -(*rule PiI*)
  oops

theorem plus:
  shows
 \<open>\<exists>!g. ((g \<in> (nat\<rightarrow>(nat\<rightarrow>nat))) \<and> (\<forall>a\<in>nat.(((g`a)`0 = a) \<and> satpc(g`a,nat,add_g2))))\<close>
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

lemma hhc : 
  assumes 1:\<open>A\<subseteq>C\<close>
  assumes 2:\<open>a\<in>C\<close>
  shows \<open>cons(a,A)\<subseteq>C\<close>
proof
  from 1 and 2 show \<open>a \<in> C \<and> A \<subseteq> C\<close> by auto
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
end
