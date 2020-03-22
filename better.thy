theory better imports FOL
begin

subsection \<open>Signature\<close>

declare [[eta_contract = false]]

typedecl i
instance i :: "term" ..

axiomatization mem :: "[i, i] \<Rightarrow> o"  (infixl \<open>\<in>\<close> 50)  \<comment> \<open>membership relation\<close>
abbreviation not_mem :: "[i, i] \<Rightarrow> o"  (infixl \<open>\<notin>\<close> 50)  \<comment> \<open>negated membership relation\<close>
  where "x \<notin> y \<equiv> \<not> (x \<in> y)"

definition Subset :: "[i, i] \<Rightarrow> o"  (infixl \<open>\<subseteq>\<close> 50)  \<comment> \<open>subset relation\<close>
  where subset_def: "A \<subseteq> B \<equiv> \<forall>x. (x\<in>A \<longrightarrow> x\<in>B)"

lemma subsetI [intro!]:
    "(!!x. x\<in>A ==> x\<in>B) ==> A \<subseteq> B"
by (simp add: subset_def)

axiomatization
where
  axext:     "A \<subseteq> B \<and> B \<subseteq> A \<longrightarrow> A = B"


definition One :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close> (binder \<open>!\<close> 10)
  where one_def: \<open>(!m. P(m)) \<equiv> (\<forall>x1.\<forall>x2.(P(x1)\<and>P(x2)\<longrightarrow>x1=x2))\<close>

definition Eno :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close> (binder \<open>my?\<close> 10)
  where Eno_def: \<open>(my?m. P(m)) \<equiv> (\<exists>x1.\<exists>x2.(\<not>P(x1)\<and>\<not>P(x2)\<and>x1\<noteq>x2))\<close>

definition ExOne :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close> (binder \<open>my\<exists>!\<close> 10)
  where exone_def: \<open>(my\<exists>!m. P(m)) \<equiv> (\<exists>m. P(m))\<and>(!m. P(m))\<close>

definition AllEno :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close> (binder \<open>\<forall>?\<close> 10)
  where alleno_def: \<open>(\<forall>?m. P(m)) \<equiv> (\<forall>m. P(m))\<or>(my?m. P(m))\<close>

(*
axiomatization
  One :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close>  (binder \<open>!\<close> 10)(* and
  Ex :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close>  (binder \<open>\<exists>\<close> 10)*)
where
  oneI: \<open>(\<forall>x1.\<forall>x2.(P(x1)\<and>P(x2)\<longrightarrow>x1=x2)) \<Longrightarrow> (!m. P(m))\<close> 
*)
axiomatization
where
  axpair: \<open>\<forall>x.\<forall>y.\<exists>p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close>

theorem pairone : \<open>\<forall>x.\<forall>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close>
  apply(rule allI)
  apply(rule allI)
  apply(rule ex1I)
   apply(rule exE)

    apply(rule spec)
    apply(rule spec)
    apply(rule axpair)
(*  apply assumption

   apply(rule allI)
   apply(rule iffI)
*)
  oops
theorem pairone : \<open>\<forall>x.\<forall>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close>
proof 

(*
  assume c:\<open>\<And>x. \<And>y. \<exists>!p. \<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = y\<close>
*)
(*
  have \<open>\<And>x. \<And>y. \<exists>!p. \<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = y\<close>
  proof (rule ex1I)

 1. \<And>x y. \<forall>z. z \<in> ?a(x, y) \<longleftrightarrow>
               z = x \<or> z = y
 2. \<And>x y p.
       \<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = y \<Longrightarrow>
       p = ?a(x, y)
*)
have bad_c:\<open>\<And>x.\<And>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close>
proof -
  fix x
  (*presume K:\<open>\<And>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close>*)
  have K:\<open>\<And>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close> sorry
  (*from K show \<open>\<And>x.\<And>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close> by assumption*)
  (*show \<open>\<And>x.\<And>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close> by (rule K)*)
  (*from K show \<open>\<And>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close> by assumption*)
  show \<open>\<And>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close> by (rule K)
qed

(*bad
  have c:\<open>\<And>x.\<And>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close>
  proof (rule exE)
  have \<open>\<forall>xa. \<forall>ya. \<exists>p. \<forall>z. z \<in> p \<longleftrightarrow> z = xa \<or> z = ya\<close> by (rule axpair)
  then have \<open>\<forall>ya. \<exists>p. \<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = ya\<close> by (rule spec)
  then show \<open>\<exists>p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close> by (rule spec)
next
*)
have lemka:\<open>\<And>x.\<And>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close>
proof (rule mp)
  prefer 2
  fix x
  fix y
  have \<open>\<forall>xa. \<forall>ya. \<exists>p. \<forall>z. z \<in> p \<longleftrightarrow> z = xa \<or> z = ya\<close> by (rule axpair)
  then have \<open>\<forall>ya. \<exists>p. \<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = ya\<close> by (rule spec)
  then show \<open>\<exists>p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close> by (rule spec)
next
  fix x
  fix y
  have \<open>(\<exists>p. \<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = y)\<longrightarrow>(\<exists>!p. \<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = y)\<close> 
  proof(rule impI)
    show \<open> \<exists>p. \<forall>z. z \<in> p \<longleftrightarrow>
            z = x \<or> z = y \<Longrightarrow>
    \<exists>!p. \<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = y\<close>
    proof(erule exE)
      show\<open>\<And>p. \<forall>z. z \<in> p \<longleftrightarrow>
             z = x \<or> z = y \<Longrightarrow>
         \<exists>!p. \<forall>z. z \<in> p \<longleftrightarrow>
                  z = x \<or> z = y\<close> 
      proof(rule ex1I)
        fix p
        assume \<open>\<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = y\<close>
        then show \<open>\<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = y\<close> by assumption 
      next
        fix p1 p2
        assume H1:\<open>\<forall>z. z \<in> p1 \<longleftrightarrow> z = x \<or> z = y\<close>
        assume H2:\<open>\<forall>z. z \<in> p2 \<longleftrightarrow> z = x \<or> z = y\<close>
        show \<open>p1=p2\<close> 
        proof(rule mp[OF axext])
        show \<open>p1 \<subseteq> p2 \<and> p2 \<subseteq> p1\<close>
        proof(rule conjI)
          show \<open>p1 \<subseteq> p2\<close> 
          proof(rule subsetI)
            fix q
            assume aq:\<open>q \<in> p1\<close>
            from H1 have h1: \<open>q \<in> p1 \<longleftrightarrow> q = x \<or> q = y\<close> by (rule spec)
            from H2 have h2: \<open>q \<in> p2 \<longleftrightarrow> q = x \<or> q = y\<close> by (rule spec)
            from h1 and aq have bq:\<open>q = x \<or> q = y\<close> by (rule iffD1)
            from h2 and bq show \<open>q \<in> p2\<close> by (rule iffD2)
          qed
        next
          show \<open>p2 \<subseteq> p1\<close>
          proof(rule subsetI)
            fix q
            assume aq:\<open>q \<in> p2\<close>
            from H1 have h1: \<open>q \<in> p1 \<longleftrightarrow> q = x \<or> q = y\<close> by (rule spec)
            from H2 have h2: \<open>q \<in> p2 \<longleftrightarrow> q = x \<or> q = y\<close> by (rule spec)
            from h2 and aq have bq:\<open>q = x \<or> q = y\<close> by (rule iffD1)
            from h1 and bq show \<open>q \<in> p1\<close> by (rule iffD2)
          qed
        qed
      qed
    qed
  qed
qed
(*

  show \<open>(\<exists>p. \<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = y)\<longrightarrow>(\<exists>!p. \<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = y)\<close> 
    sorry

(*
  proof (rule spec)
proof (rule spec)
    apply(rule spec)
    apply(rule axpair)
  proof (rule impI)
*)

 (*rule ex1I*)
  have K:\<open>\<forall>z. z \<in> p \<longleftrightarrow> z = x \<or> z = y\<close> sorry
  
next
  
qed
*)
  have c:\<open>\<And>x.\<And>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close> by (rule lemka)
  from c have c:\<open>\<And>x.\<forall>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close> by (rule allI)
  from c show c:\<open>\<forall>x.\<forall>y.\<exists>!p.\<forall>z.(z\<in>p\<longleftrightarrow>(z=x\<or>z=y))\<close> by (rule allI)
  
qed
(*
(* preliminaries *)
definition Ind :: \<open>i\<Rightarrow>o\<close>
  where Ind_def : \<open>Ind(x) == 0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)\<close>
*)

end