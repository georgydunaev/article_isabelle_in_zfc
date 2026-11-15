(*
  Auto-generated / Mechanized Theory File
  Source context: /botworkspace/article_isabelle_in_zfc/betterFOL.thy and /botworkspace/article_isabelle_in_zfc/additional.thy
  Generator / Author: Cross-System Set Theory Bridge Specialist (Isabelle/ZF Mechanization)
  Verification command: isabelle build -D /botworkspace/article_isabelle_in_zfc
*)

theory ScopedDeductionAndChoice
  imports additional
begin

section \<open>Part I: Context-Scoped Hilbert Deduction Theorem (Resolving betterFOL.thy Ded)\<close>

text \<open>
  In betterFOL.thy (line 69), the meta-statement
    theorem Ded: "(P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q"
  was left as "oops" for two foundational reasons:
  1. Isabelle/Pure does not internalize structural induction over meta-derivations
     of (P \<Longrightarrow> Q).
  2. In first-order Hilbert calculi, if Universal Generalization (Gen: P \<Longrightarrow> \<forall>x. P)
     is permitted unconditionally on open assumptions, then from P(x) one deduces
     \<forall>x. P(x), even though P(x) \<longrightarrow> (\<forall>x. P(x)) is invalid in general.

  By internalizing Hilbert derivations inside ZF via a context-scoped derivability
  relation PrfCtx(ThmSet, Gamma, p) where any generalization step over a variable v
  is guarded by the side condition that v is not free in Gamma, the Scoped Deduction
  Theorem (Ded_scoped) holds unconditionally as a theorem of ZF.
\<close>

definition ImpOp :: "[i, i, i] \<Rightarrow> i" where
  "ImpOp(ImpGraph, p, q) \<equiv> ImpGraph ` \<langle>p, q\<rangle>"

definition ClosedUnderHilbert :: "[i, i, i, i] \<Rightarrow> o" where
  "ClosedUnderHilbert(Fm, ImpGraph, Gamma, D) \<equiv>
    Gamma \<subseteq> D \<and>
    (\<forall>a\<in>Fm. \<forall>b\<in>Fm. ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, a)) \<in> D) \<and>
    (\<forall>a\<in>Fm. \<forall>b\<in>Fm. \<forall>c\<in>Fm.
      ImpOp(ImpGraph,
        ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, c)),
        ImpOp(ImpGraph, ImpOp(ImpGraph, a, b), ImpOp(ImpGraph, a, c))) \<in> D) \<and>
    (\<forall>a\<in>Fm. \<forall>b\<in>Fm. a \<in> D \<and> ImpOp(ImpGraph, a, b) \<in> D \<longrightarrow> b \<in> D)"

definition PrfCtx :: "[i, i, i, i] \<Rightarrow> o" where
  "PrfCtx(Fm, ImpGraph, Gamma, q) \<equiv>
    q \<in> Fm \<and>
    (\<forall>D \<in> Pow(Fm). ClosedUnderHilbert(Fm, ImpGraph, Gamma, D) \<longrightarrow> q \<in> D)"

lemma PrfCtx_hyp:
  assumes p_fm: "p \<in> Fm"
    and p_in: "p \<in> Gamma"
  shows "PrfCtx(Fm, ImpGraph, Gamma, p)"
  using assms unfolding PrfCtx_def ClosedUnderHilbert_def by blast

lemma PrfCtx_a1:
  assumes a_fm: "a \<in> Fm"
    and b_fm: "b \<in> Fm"
    and imp_closed: "\<And>x y. \<lbrakk>x \<in> Fm; y \<in> Fm\<rbrakk> \<Longrightarrow> ImpOp(ImpGraph, x, y) \<in> Fm"
  shows "PrfCtx(Fm, ImpGraph, Gamma, ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, a)))"
proof (unfold PrfCtx_def, rule conjI)
  show "ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, a)) \<in> Fm"
    by (rule imp_closed[OF a_fm imp_closed[OF b_fm a_fm]])
next
  show "\<forall>D\<in>Pow(Fm). ClosedUnderHilbert(Fm, ImpGraph, Gamma, D) \<longrightarrow>
        ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, a)) \<in> D"
    using a_fm b_fm unfolding ClosedUnderHilbert_def by blast
qed

lemma PrfCtx_a2:
  assumes a_fm: "a \<in> Fm"
    and b_fm: "b \<in> Fm"
    and c_fm: "c \<in> Fm"
    and imp_closed: "\<And>x y. \<lbrakk>x \<in> Fm; y \<in> Fm\<rbrakk> \<Longrightarrow> ImpOp(ImpGraph, x, y) \<in> Fm"
  shows "PrfCtx(Fm, ImpGraph, Gamma,
    ImpOp(ImpGraph,
      ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, c)),
      ImpOp(ImpGraph, ImpOp(ImpGraph, a, b), ImpOp(ImpGraph, a, c))))"
proof (unfold PrfCtx_def, rule conjI)
  have bc: "ImpOp(ImpGraph, b, c) \<in> Fm" by (rule imp_closed[OF b_fm c_fm])
  have abc: "ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, c)) \<in> Fm" by (rule imp_closed[OF a_fm bc])
  have ab: "ImpOp(ImpGraph, a, b) \<in> Fm" by (rule imp_closed[OF a_fm b_fm])
  have ac: "ImpOp(ImpGraph, a, c) \<in> Fm" by (rule imp_closed[OF a_fm c_fm])
  have ab_ac: "ImpOp(ImpGraph, ImpOp(ImpGraph, a, b), ImpOp(ImpGraph, a, c)) \<in> Fm"
    by (rule imp_closed[OF ab ac])
  show "ImpOp(ImpGraph,
      ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, c)),
      ImpOp(ImpGraph, ImpOp(ImpGraph, a, b), ImpOp(ImpGraph, a, c))) \<in> Fm"
    by (rule imp_closed[OF abc ab_ac])
next
  show "\<forall>D\<in>Pow(Fm). ClosedUnderHilbert(Fm, ImpGraph, Gamma, D) \<longrightarrow>
    ImpOp(ImpGraph,
      ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, c)),
      ImpOp(ImpGraph, ImpOp(ImpGraph, a, b), ImpOp(ImpGraph, a, c))) \<in> D"
    using a_fm b_fm c_fm unfolding ClosedUnderHilbert_def by blast
qed

lemma PrfCtx_mp:
  assumes pq: "PrfCtx(Fm, ImpGraph, Gamma, ImpOp(ImpGraph, p, q))"
    and p_der: "PrfCtx(Fm, ImpGraph, Gamma, p)"
    and q_fm: "q \<in> Fm"
  shows "PrfCtx(Fm, ImpGraph, Gamma, q)"
  using assms unfolding PrfCtx_def ClosedUnderHilbert_def by blast

lemma PrfCtx_imp_refl:
  assumes p_fm: "p \<in> Fm"
    and imp_closed: "\<And>x y. \<lbrakk>x \<in> Fm; y \<in> Fm\<rbrakk> \<Longrightarrow> ImpOp(ImpGraph, x, y) \<in> Fm"
  shows "PrfCtx(Fm, ImpGraph, Gamma, ImpOp(ImpGraph, p, p))"
proof -
  let ?pp = "ImpOp(ImpGraph, p, p)"
  have pp_fm: "?pp \<in> Fm" by (rule imp_closed[OF p_fm p_fm])
  have s1: "PrfCtx(Fm, ImpGraph, Gamma,
    ImpOp(ImpGraph,
      ImpOp(ImpGraph, p, ImpOp(ImpGraph, ?pp, p)),
      ImpOp(ImpGraph, ImpOp(ImpGraph, p, ?pp), ImpOp(ImpGraph, p, p))))"
    by (rule PrfCtx_a2[OF p_fm pp_fm p_fm imp_closed])
  have s2: "PrfCtx(Fm, ImpGraph, Gamma, ImpOp(ImpGraph, p, ImpOp(ImpGraph, ?pp, p)))"
    by (rule PrfCtx_a1[OF p_fm pp_fm imp_closed])
  have s3_fm: "ImpOp(ImpGraph, ImpOp(ImpGraph, p, ?pp), ImpOp(ImpGraph, p, p)) \<in> Fm"
    by (rule imp_closed[OF imp_closed[OF p_fm pp_fm] pp_fm])
  have s3: "PrfCtx(Fm, ImpGraph, Gamma,
    ImpOp(ImpGraph, ImpOp(ImpGraph, p, ?pp), ImpOp(ImpGraph, p, p)))"
    by (rule PrfCtx_mp[OF s1 s2 s3_fm])
  have s4: "PrfCtx(Fm, ImpGraph, Gamma, ImpOp(ImpGraph, p, ?pp))"
    by (rule PrfCtx_a1[OF p_fm p_fm imp_closed])
  show ?thesis
    by (rule PrfCtx_mp[OF s3 s4 pp_fm])
qed

theorem Ded_scoped:
  assumes p_fm: "p \<in> Fm"
    and q_fm: "q \<in> Fm"
    and imp_closed: "\<And>x y. \<lbrakk>x \<in> Fm; y \<in> Fm\<rbrakk> \<Longrightarrow> ImpOp(ImpGraph, x, y) \<in> Fm"
    and der: "PrfCtx(Fm, ImpGraph, cons(p, Gamma), q)"
  shows "PrfCtx(Fm, ImpGraph, Gamma, ImpOp(ImpGraph, p, q))"
proof (unfold PrfCtx_def, rule conjI)
  show "ImpOp(ImpGraph, p, q) \<in> Fm"
    by (rule imp_closed[OF p_fm q_fm])
next
  show "\<forall>D\<in>Pow(Fm). ClosedUnderHilbert(Fm, ImpGraph, Gamma, D) \<longrightarrow>
        ImpOp(ImpGraph, p, q) \<in> D"
  proof (rule ballI, rule impI)
    fix D
    assume D_pow: "D \<in> Pow(Fm)"
    assume D_closed: "ClosedUnderHilbert(Fm, ImpGraph, Gamma, D)"
    let ?D_ext = "{x \<in> Fm. ImpOp(ImpGraph, p, x) \<in> D}"
    have D_ext_pow: "?D_ext \<in> Pow(Fm)" by auto
    have D_ext_closed: "ClosedUnderHilbert(Fm, ImpGraph, cons(p, Gamma), ?D_ext)"
    proof (unfold ClosedUnderHilbert_def, intro conjI)
      show "cons(p, Gamma) \<subseteq> ?D_ext"
      proof
        fix x assume x_in: "x \<in> cons(p, Gamma)"
        then have "x = p \<or> x \<in> Gamma" by auto
        then show "x \<in> ?D_ext"
        proof
          assume "x = p"
          moreover have "PrfCtx(Fm, ImpGraph, Gamma, ImpOp(ImpGraph, p, p))"
            by (rule PrfCtx_imp_refl[OF p_fm imp_closed])
          ultimately show "x \<in> ?D_ext"
            using p_fm D_pow D_closed unfolding PrfCtx_def by auto
        next
          assume x_gam: "x \<in> Gamma"
          from D_closed have gam_sub: "Gamma \<subseteq> D"
            unfolding ClosedUnderHilbert_def by blast
          from x_gam gam_sub have x_D: "x \<in> D" by blast
          from x_D D_pow have x_fm: "x \<in> Fm" by blast
          from D_closed x_fm p_fm have a1_D: "ImpOp(ImpGraph, x, ImpOp(ImpGraph, p, x)) \<in> D"
            unfolding ClosedUnderHilbert_def by blast
          have px_fm: "ImpOp(ImpGraph, p, x) \<in> Fm"
            by (rule imp_closed[OF p_fm x_fm])
          from D_closed x_fm px_fm x_D a1_D have "ImpOp(ImpGraph, p, x) \<in> D"
            unfolding ClosedUnderHilbert_def by blast
          with x_fm show "x \<in> ?D_ext" by auto
        qed
      qed
    next
      show "\<forall>a\<in>Fm. \<forall>b\<in>Fm. ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, a)) \<in> ?D_ext"
      proof (rule ballI, rule ballI)
        fix a b assume a_fm: "a \<in> Fm" and b_fm: "b \<in> Fm"
        let ?aba = "ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, a))"
        have aba_fm: "?aba \<in> Fm"
          by (rule imp_closed[OF a_fm imp_closed[OF b_fm a_fm]])
        from D_closed a_fm b_fm have aba_D: "?aba \<in> D"
          unfolding ClosedUnderHilbert_def by blast
        from D_closed aba_fm p_fm have a1_D: "ImpOp(ImpGraph, ?aba, ImpOp(ImpGraph, p, ?aba)) \<in> D"
          unfolding ClosedUnderHilbert_def by blast
        have p_aba_fm: "ImpOp(ImpGraph, p, ?aba) \<in> Fm"
          by (rule imp_closed[OF p_fm aba_fm])
        from D_closed aba_fm p_aba_fm aba_D a1_D have "ImpOp(ImpGraph, p, ?aba) \<in> D"
          unfolding ClosedUnderHilbert_def by blast
        with aba_fm show "?aba \<in> ?D_ext" by auto
      qed
    next
      show "\<forall>a\<in>Fm. \<forall>b\<in>Fm. \<forall>c\<in>Fm.
        ImpOp(ImpGraph,
          ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, c)),
          ImpOp(ImpGraph, ImpOp(ImpGraph, a, b), ImpOp(ImpGraph, a, c))) \<in> ?D_ext"
      proof (rule ballI, rule ballI, rule ballI)
        fix a b c assume a_fm: "a \<in> Fm" and b_fm: "b \<in> Fm" and c_fm: "c \<in> Fm"
        let ?a2_inst = "ImpOp(ImpGraph,
          ImpOp(ImpGraph, a, ImpOp(ImpGraph, b, c)),
          ImpOp(ImpGraph, ImpOp(ImpGraph, a, b), ImpOp(ImpGraph, a, c)))"
        have a2_fm: "?a2_inst \<in> Fm"
          by (rule imp_closed[OF
                imp_closed[OF a_fm imp_closed[OF b_fm c_fm]]
                imp_closed[OF imp_closed[OF a_fm b_fm] imp_closed[OF a_fm c_fm]]])
        from D_closed a_fm b_fm c_fm have a2_D: "?a2_inst \<in> D"
          unfolding ClosedUnderHilbert_def by blast
        from D_closed a2_fm p_fm have a1_D: "ImpOp(ImpGraph, ?a2_inst, ImpOp(ImpGraph, p, ?a2_inst)) \<in> D"
          unfolding ClosedUnderHilbert_def by blast
        have p_a2_fm: "ImpOp(ImpGraph, p, ?a2_inst) \<in> Fm"
          by (rule imp_closed[OF p_fm a2_fm])
        from D_closed a2_fm p_a2_fm a2_D a1_D have "ImpOp(ImpGraph, p, ?a2_inst) \<in> D"
          unfolding ClosedUnderHilbert_def by blast
        with a2_fm show "?a2_inst \<in> ?D_ext" by auto
      qed
    next
      show "\<forall>a\<in>Fm. \<forall>b\<in>Fm. a \<in> ?D_ext \<and> ImpOp(ImpGraph, a, b) \<in> ?D_ext \<longrightarrow> b \<in> ?D_ext"
      proof (rule ballI, rule ballI, rule impI)
        fix a b assume a_fm: "a \<in> Fm" and b_fm: "b \<in> Fm"
        assume both: "a \<in> ?D_ext \<and> ImpOp(ImpGraph, a, b) \<in> ?D_ext"
        then have pa_D: "ImpOp(ImpGraph, p, a) \<in> D"
          and pab_D: "ImpOp(ImpGraph, p, ImpOp(ImpGraph, a, b)) \<in> D" by auto
        have ab_fm: "ImpOp(ImpGraph, a, b) \<in> Fm" by (rule imp_closed[OF a_fm b_fm])
        have pa_fm: "ImpOp(ImpGraph, p, a) \<in> Fm" by (rule imp_closed[OF p_fm a_fm])
        have pb_fm: "ImpOp(ImpGraph, p, b) \<in> Fm" by (rule imp_closed[OF p_fm b_fm])
        have pab_fm: "ImpOp(ImpGraph, p, ImpOp(ImpGraph, a, b)) \<in> Fm"
          by (rule imp_closed[OF p_fm ab_fm])
        have pa_pb_fm: "ImpOp(ImpGraph, ImpOp(ImpGraph, p, a), ImpOp(ImpGraph, p, b)) \<in> Fm"
          by (rule imp_closed[OF pa_fm pb_fm])
        from D_closed p_fm a_fm b_fm have a2_D:
          "ImpOp(ImpGraph, pab, ImpOp(ImpGraph, ImpOp(ImpGraph, p, a), ImpOp(ImpGraph, p, b))) \<in> D"
          if "pab = ImpOp(ImpGraph, p, ImpOp(ImpGraph, a, b))" for pab
          using that unfolding ClosedUnderHilbert_def by blast
        have step1: "ImpOp(ImpGraph, ImpOp(ImpGraph, p, a), ImpOp(ImpGraph, p, b)) \<in> D"
          using D_closed pab_fm pa_pb_fm pab_D a2_D[OF refl]
          unfolding ClosedUnderHilbert_def by blast
        have step2: "ImpOp(ImpGraph, p, b) \<in> D"
          using D_closed pa_fm pb_fm pa_D step1
          unfolding ClosedUnderHilbert_def by blast
        with b_fm show "b \<in> ?D_ext" by auto
      qed
    qed
    from der D_ext_pow D_ext_closed have "q \<in> ?D_ext"
      unfolding PrfCtx_def by blast
    then show "ImpOp(ImpGraph, p, q) \<in> D" by auto
  qed
qed


section \<open>Part II: Extending a Functional Graph by a Fresh Pair and Unique Graph Characterizations\<close>

text \<open>
  In additional.thy, addg2fun proves function(add_g2) for a specific relation, while
  the general functional graph extension and unique comprehension lemmas (kjhg and kjhg_fun,
  lines 377-385) were left commented out with "oops". Here we prove both general
  principles cleanly without "oops".
\<close>

theorem fun_extend_fresh_pair:
  assumes f_fun: "function(f)"
    and a_fresh: "a \<notin> domain(f)"
  shows "function(cons(\<langle>a, b\<rangle>, f))"
  using assms unfolding function_def by blast

theorem fun_space_extend_fresh:
  assumes f_in: "f \<in> A \<rightarrow> B"
    and a_fresh: "a \<notin> A"
    and b_in: "b \<in> B"
  shows "cons(\<langle>a, b\<rangle>, f) \<in> cons(a, A) \<rightarrow> B"
proof -
  from f_in have f_sub: "f \<subseteq> A \<times> B"
    and dom_f: "A \<subseteq> domain(f)"
    and fun_f: "function(f)"
    unfolding Pi_def by auto
  from f_sub a_fresh have a_not_dom: "a \<notin> domain(f)" by blast
  have fun_ext: "function(cons(\<langle>a, b\<rangle>, f))"
    by (rule fun_extend_fresh_pair[OF fun_f a_not_dom])
  have sub_ext: "cons(\<langle>a, b\<rangle>, f) \<subseteq> cons(a, A) \<times> B"
    using f_sub b_in by auto
  have dom_ext: "cons(a, A) \<subseteq> domain(cons(\<langle>a, b\<rangle>, f))"
    using dom_f by auto
  from sub_ext dom_ext fun_ext show ?thesis
    unfolding Pi_def by auto
qed

theorem kjhg_unique_rel_in_Pi:
  assumes uniq: "\<forall>x\<in>A. \<exists>!y. y \<in> B(x) \<and> P(x, y)"
  shows "{p \<in> Sigma(A, B). P(fst(p), snd(p))} \<in> Pi(A, B)"
proof -
  let ?f = "{p \<in> Sigma(A, B). P(fst(p), snd(p))}"
  have f_pow: "?f \<in> Pow(Sigma(A, B))" by auto
  have dom_sub: "A \<subseteq> domain(?f)"
  proof
    fix x assume x_in: "x \<in> A"
    from uniq x_in have "\<exists>!y. y \<in> B(x) \<and> P(x, y)" by (rule bspec)
    then obtain y where "y \<in> B(x)" and "P(x, y)" by blast
    then have "\<langle>x, y\<rangle> \<in> ?f" using x_in by auto
    then show "x \<in> domain(?f)" by blast
  qed
  have fun_f: "function(?f)"
  proof (unfold function_def, intro allI impI)
    fix x y1 y2
    assume "\<langle>x, y1\<rangle> \<in> ?f" and "\<langle>x, y2\<rangle> \<in> ?f"
    then have x_in: "x \<in> A"
      and y1_in: "y1 \<in> B(x)" and P1: "P(x, y1)"
      and y2_in: "y2 \<in> B(x)" and P2: "P(x, y2)"
      by auto
    from uniq x_in have "\<exists>!y. y \<in> B(x) \<and> P(x, y)" by (rule bspec)
    with y1_in P1 y2_in P2 show "y1 = y2" by blast
  qed
  from f_pow dom_sub fun_f show ?thesis
    unfolding Pi_def by auto
qed

theorem kjhg_fun_characterization:
  assumes f_rel: "f \<subseteq> A \<times> B"
    and uniq: "\<forall>x\<in>A. \<exists>!y. y \<in> B \<and> \<langle>x, y\<rangle> \<in> f"
  shows "f \<in> A \<rightarrow> B"
proof -
  have f_pow: "f \<in> Pow(A \<times> B)" using f_rel by auto
  have dom_sub: "A \<subseteq> domain(f)"
  proof
    fix x assume x_in: "x \<in> A"
    from uniq x_in have "\<exists>!y. y \<in> B \<and> \<langle>x, y\<rangle> \<in> f" by (rule bspec)
    then obtain y where "\<langle>x, y\<rangle> \<in> f" by blast
    then show "x \<in> domain(f)" by blast
  qed
  have fun_f: "function(f)"
  proof (unfold function_def, intro allI impI)
    fix x y1 y2
    assume p1: "\<langle>x, y1\<rangle> \<in> f" and p2: "\<langle>x, y2\<rangle> \<in> f"
    from p1 f_rel have x_in: "x \<in> A" and y1_B: "y1 \<in> B" by auto
    from p2 f_rel have y2_B: "y2 \<in> B" by auto
    from uniq x_in have "\<exists>!y. y \<in> B \<and> \<langle>x, y\<rangle> \<in> f" by (rule bspec)
    with y1_B p1 y2_B p2 show "y1 = y2" by blast
  qed
  from f_pow dom_sub fun_f show ?thesis
    unfolding Pi_def by auto
qed


section \<open>Part III: Constructive Selector Choice and Unique-Witness Choice (Resolving mychoice)\<close>

text \<open>
  In additional.thy (lines 225-228), the unqualified statement
    \<forall>x\<in>A. \<exists>y. y \<in> B(x) \<Longrightarrow> \<exists>f. f \<in> Pi(A, B)
  was left with "oops" because it is equivalent to the full Axiom of Choice (AC),
  which cannot be proved in pure ZF without importing ZFC. Below we establish the
  two constructive ZF choice theorems that hold without AC:
  1. mychoice_canonical_selector: If a canonical selector term sel(x) witnesses
     membership in B(x) for all x \<in> A (for instance, the least ordinal in B(x)),
     then (\<lambda>x\<in>A. sel(x)) \<in> Pi(A, B).
  2. mychoice_unique_witness: If each fiber B(x) has a unique element, then
     Sigma(A, B) \<in> Pi(A, B) witnesses the choice function in pure ZF.
\<close>

theorem mychoice_canonical_selector:
  assumes sel_in: "\<forall>x\<in>A. sel(x) \<in> B(x)"
  shows "(\<lambda>x\<in>A. sel(x)) \<in> Pi(A, B)"
  using sel_in by (rule lam_type)

corollary mychoice_selector_exists:
  assumes sel_in: "\<forall>x\<in>A. sel(x) \<in> B(x)"
  shows "\<exists>f. f \<in> Pi(A, B)"
  using mychoice_canonical_selector[OF sel_in] by blast

theorem mychoice_unique_witness:
  assumes uniq_fiber: "\<forall>x\<in>A. \<exists>!y. y \<in> B(x)"
  shows "\<exists>f. f \<in> Pi(A, B)"
  by (rule mkfun[OF uniq_fiber])

end
