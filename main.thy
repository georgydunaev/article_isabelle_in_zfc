theory main imports ZF
begin

definition fite :: "[i, o, i, i] \<Rightarrow> i" (\<open>from _ if _ then _ else _\<close>)
  where "fite(A, \<phi>, a, b) == \<Union>{x\<in>A.(\<phi>\<and>x=a)\<or>((\<not>\<phi>)\<and>x=b)}"

definition ite :: "[o, i, i] \<Rightarrow> i" (\<open>myif _ then _ else _\<close>)
  where "ite(\<phi>, a, b) == \<Union>{x\<in>{a,b}.(\<phi>\<and>x=a)\<or>((\<not>\<phi>)\<and>x=b)}"

theorem thm1 : \<open>\<phi> \<Longrightarrow> ((myif \<phi> then a else b) = a)\<close>
proof (unfold ite_def)
  assume H:\<open>\<phi>\<close>
  have P:\<open>{x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} = {a}\<close>
  proof 
    show \<open> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} \<subseteq> {a}\<close>
    proof
      fix x
      assume G:\<open>x \<in>
         {x \<in> {a, b} .
          \<phi> \<and> x = a \<or>
          \<not> \<phi> \<and> x = b}\<close>
      have \<open>\<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b\<close> by (rule CollectE[OF G])
      show \<open>x\<in>{a}\<close>
        sorry
  next
    show \<open>{a} \<subseteq> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
    proof (*(rule subsetI) which rule is used here? *)
      show\<open>a \<in> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} \<and>
      0 \<subseteq> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
      proof
        show \<open>0 \<subseteq> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
          by blast
      next
        show \<open>a \<in> {x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b}\<close>
        proof 
          show \<open>a \<in> {a, b}\<close> by blast
        next
          show \<open>\<phi> \<and> a = a \<or> \<not> \<phi> \<and> a = b\<close>
          proof (rule disjI1)
            show \<open>\<phi> \<and> a = a\<close>
            proof
              show \<open>\<phi>\<close> by (rule H)
            next
              show \<open>a = a\<close> by blast
            qed
          qed
        qed
      qed
    qed
  qed
  (*find_theorems "\<Union>_=\<Union>_"*)
  have P1:\<open>\<Union>{x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} = \<Union>{a}\<close>
    by (rule IFOL.subst_context[OF P])
  (*find_theorems "Lam [_]. _"*)
  have P2:\<open>\<Union>{a} = a\<close> by (rule equalities.Union_singleton)
  (*find_theorems "\<Union>{_}"*)
  (*find_theorems "_=_\<Longrightarrow>_=_ \<Longrightarrow>_"*)
  show \<open>\<Union>{x \<in> {a, b} . \<phi> \<and> x = a \<or> \<not> \<phi> \<and> x = b} = a\<close>
    by (rule IFOL.trans[OF P1 P2])
qed

end