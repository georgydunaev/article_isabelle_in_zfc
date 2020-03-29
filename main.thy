theory main imports ZF
begin

definition fite :: "[i, o, i, i] \<Rightarrow> i" (\<open>from _ if _ then _ else _\<close>)
  where "fite(A, \<phi>, a, b) == \<Union>{x\<in>A.(\<phi>\<and>x=a)\<or>((\<not>\<phi>)\<and>x=b)}"

definition ite :: "[o, i, i] \<Rightarrow> i" (\<open>myif _ then _ else _\<close>)
  where "ite(\<phi>, a, b) == \<Union>{x\<in>{a,b}.(\<phi>\<and>x=a)\<or>((\<not>\<phi>)\<and>x=b)}"

theorem thm1 : \<open>(\<phi> \<longrightarrow> ((if \<phi> then a else b) = a))\<close>


end