theory omega_regular_languages

imports Main omega_regular_expressions  

begin

text \<open>Author: Benno Thalmann, last update: 12.2.2026, Addition to masterarbeit_benno_thalmann\<close>

text \<open>Omega_Regular_languages and Expressive Power Collection\<close>
definition omega_regular_languages :: "'a alphabet \<Rightarrow> 'a omega_language set" where "omega_regular_languages \<Sigma> = {L . \<exists> (r :: 'a omega_regular_expression) . omega_RE_well_defined r \<Sigma> \<and> L = language_omega_reg_exp r}"

proposition well_def_word_omega_reg_languages:
  assumes "omega_word \<in> L \<and> L \<in> omega_regular_languages \<Sigma>"
  shows "omega_word_well_defined omega_word \<Sigma>"
  using assms omega_word_in_omega_language_reg_is_well_defined unfolding omega_regular_languages_def by blast

proposition not_empty_omega_reg_languages:
  assumes "omega_regular_languages \<Sigma> \<noteq> {}"
  shows "finite \<Sigma>"
  using assms unfolding omega_regular_languages_def omega_RE_well_defined_def by blast

corollary inifinte_alphabet_implies_empty_omega_reg_lang: "infinite \<Sigma> \<Longrightarrow> omega_regular_languages \<Sigma> = {}"
  using not_empty_omega_reg_languages by blast

proposition empty_omega_reg_languages:
  assumes "omega_regular_languages \<Sigma> = {}"
  shows "infinite \<Sigma>"
proof(rule ccontr)
  assume "\<not> infinite \<Sigma>"
  hence "finite \<Sigma>" by simp
  hence "omega_RE_well_defined (Omega_power Empty_set) \<Sigma>" unfolding omega_RE_well_defined_def by simp
  hence "{} \<in> omega_regular_languages \<Sigma>" using omega_power_of_empty_lan unfolding omega_regular_languages_def by force
  thus False using assms by blast
qed

theorem inifinite_alphabet_omega: "infinite \<Sigma> \<longleftrightarrow> omega_regular_languages \<Sigma> = {}"
  using empty_omega_reg_languages inifinte_alphabet_implies_empty_omega_reg_lang by blast

theorem omega_reg_lang_nbas:
  assumes "infinite (UNIV :: 's set)" 
  shows "omega_regular_languages \<Sigma> = {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = omega_language_auto NFA_\<A>}"
  using assms expressive_power_auto_omega_RE_main unfolding omega_regular_languages_def by blast

theorem omega_reg_lang_dbas:
  assumes "infinite (UNIV :: 's set)" "infinite (UNIV :: 'a set)"
  shows "\<exists> \<Sigma> . omega_regular_languages \<Sigma> \<supset> {L . \<exists> (DFA_\<A> :: ('s, 'a) automaton) . auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = \<Sigma> \<and> L = omega_language_auto DFA_\<A>}"
proof -
  obtain NBA_\<A> :: "('s, 'a) automaton" where A: "auto_well_defined NBA_\<A> \<and> (\<nexists> DBA_\<A> :: ('s, 'a) automaton . auto_well_defined DBA_\<A> \<and> DFA_property DBA_\<A> \<and> alphabet DBA_\<A> = alphabet NBA_\<A> \<and> omega_language_auto DBA_\<A> = omega_language_auto NBA_\<A>)" using assms NBA_to_DBA by blast
  hence lan_in: "omega_language_auto NBA_\<A> \<in> omega_regular_languages (alphabet NBA_\<A>)" using assms omega_reg_lang_nbas by blast
  have not_in: "omega_language_auto NBA_\<A> \<notin> {L . \<exists> (DFA_\<A> :: ('s, 'a) automaton) . auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = (alphabet NBA_\<A>) \<and> L = omega_language_auto DFA_\<A>}" using A by blast
  have "{L . \<exists> (DFA_\<A> :: ('s, 'a) automaton) . auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = (alphabet NBA_\<A>) \<and> L = omega_language_auto DFA_\<A>} \<subseteq> {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = (alphabet NBA_\<A>) \<and> L = omega_language_auto NFA_\<A>}" by blast
  hence "{L . \<exists> (DFA_\<A> :: ('s, 'a) automaton) . auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = (alphabet NBA_\<A>) \<and> L = omega_language_auto DFA_\<A>} \<subseteq> omega_regular_languages (alphabet NBA_\<A>)" using assms omega_reg_lang_nbas by fast 
  hence "omega_regular_languages (alphabet NBA_\<A>) \<supset> {L . \<exists> (DFA_\<A> :: ('s, 'a) automaton) . auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = (alphabet NBA_\<A>) \<and> L = omega_language_auto DFA_\<A>}" using lan_in not_in by blast
  thus ?thesis by blast
qed

theorem omega_reg_lang_nbas_multis:
  assumes "infinite (UNIV :: 's set)" 
  shows "omega_regular_languages \<Sigma> = {L . \<exists> (NFA_\<A>_multi :: ('s, 'a) nfa_multi) . auto_well_defined_multi NFA_\<A>_multi \<and> alphabet_multi NFA_\<A>_multi = \<Sigma> \<and> L = omega_language_auto_multi NFA_\<A>_multi}"
proof -
  have reg: "omega_regular_languages \<Sigma> = {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = omega_language_auto NFA_\<A>}" using assms omega_reg_lang_nbas by blast
  have "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = omega_language_auto NFA_\<A>} = {L . \<exists> (NFA_\<A>_multi :: ('s, 'a) nfa_multi) . auto_well_defined_multi NFA_\<A>_multi \<and> alphabet_multi NFA_\<A>_multi = \<Sigma> \<and> L = omega_language_auto_multi NFA_\<A>_multi}" using assms expressive_power_multi_omega_nfa_main by blast
  thus ?thesis using reg by auto
qed

text \<open>closure properties\<close>
proposition omega_eg_lang_well_def: "L \<in> omega_regular_languages \<Sigma> \<Longrightarrow> omega_language_well_defined L \<Sigma>"
  using well_def_omega_REs_omega_language_is_well_def unfolding omega_regular_languages_def by fast

proposition omega_sigma_star_is_omega_regular:
  assumes "finite \<Sigma>"
  shows "omega_sigma_star \<Sigma> \<in> omega_regular_languages \<Sigma>"
proof -
  have "infinite (UNIV :: nat set)" by simp
  hence "\<exists> sigma_\<A> :: (nat, 'a) automaton . auto_well_defined sigma_\<A> \<and> alphabet sigma_\<A> = \<Sigma> \<and> omega_language_auto sigma_\<A> = omega_sigma_star \<Sigma>" using assms existence_of_omega_sigma_star_same_type by blast
  thus ?thesis using omega_reg_lang_nbas by auto
qed

proposition inter_is_omega_regular:
  assumes "L1 \<in> omega_regular_languages \<Sigma>1" "L2 \<in> omega_regular_languages \<Sigma>2"
  shows "L1 \<inter> L2 \<in> omega_regular_languages (\<Sigma>1 \<union> \<Sigma>2)"
proof - 
  have inf_nat: "infinite (UNIV :: nat set)" by simp
  hence "L1 \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>1 \<and> L = omega_language_auto NFA_\<A>} \<and> L2 \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>2 \<and> L = omega_language_auto NFA_\<A>}" using assms omega_reg_lang_nbas by blast
  hence "(\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>1 \<and> L1 = omega_language_auto NFA_\<A>) \<and> (\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>2 \<and> L2 = omega_language_auto NFA_\<A>)" by blast
  hence "\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>1 \<union> \<Sigma>2 \<and> L1 \<inter> L2 = omega_language_auto NFA_\<A>" using inf_nat existence_of_omega_inter_same_type by metis
  hence "L1 \<inter> L2 \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = (\<Sigma>1 \<union> \<Sigma>2) \<and> L = omega_language_auto NFA_\<A>}" by blast
  thus ?thesis using omega_reg_lang_nbas by blast
qed

proposition union_is_omega_regular:
  assumes "L1 \<in> omega_regular_languages \<Sigma>1" "L2 \<in> omega_regular_languages \<Sigma>2"
  shows "L1 \<union> L2 \<in> omega_regular_languages (\<Sigma>1 \<union> \<Sigma>2)"
proof - 
  obtain r1 r2 where "omega_RE_well_defined r1 \<Sigma>1 \<and> L1 = language_omega_reg_exp r1 \<and> omega_RE_well_defined r2 \<Sigma>2 \<and> L2 = language_omega_reg_exp r2" using assms unfolding omega_regular_languages_def by blast
  hence "omega_RE_well_defined (Omega_alternation r1 r2) (\<Sigma>1 \<union> \<Sigma>2) \<and> language_omega_reg_exp (Omega_alternation r1 r2) = L1 \<union> L2" unfolding omega_RE_well_defined_def by auto
  thus ?thesis unfolding omega_regular_languages_def by fast
qed

proposition concatenation_is_omega_regular:
  assumes "L1 \<in> regular_languages \<Sigma>1" "L2 \<in> omega_regular_languages \<Sigma>2"
  shows "concatenation_omega_language L1 L2 \<in> omega_regular_languages (\<Sigma>1 \<union> \<Sigma>2)"
proof - 
  obtain r1 r2 where "RE_well_defined r1 \<Sigma>1 \<and> L1 = language_reg_exp r1 \<and> omega_RE_well_defined r2 \<Sigma>2 \<and> L2 = language_omega_reg_exp r2" using assms unfolding regular_languages_def omega_regular_languages_def by blast
  hence "omega_RE_well_defined (Left_concatenation r1 r2) (\<Sigma>1 \<union> \<Sigma>2) \<and> language_omega_reg_exp (Left_concatenation r1 r2) = concatenation_omega_language L1 L2" unfolding omega_RE_well_defined_def RE_well_defined_def by auto 
  thus ?thesis unfolding omega_regular_languages_def by fast
qed

proposition omega_power_is_omega_regular:
  assumes "L \<in> regular_languages \<Sigma>"
  shows "omega_power_language L \<in> omega_regular_languages \<Sigma>"
proof - 
  obtain r where "RE_well_defined r \<Sigma> \<and> L = language_reg_exp r" using assms unfolding regular_languages_def by blast
  hence "omega_RE_well_defined (Omega_power r) \<Sigma> \<and> language_omega_reg_exp (Omega_power r) = omega_power_language L" unfolding omega_RE_well_defined_def RE_well_defined_def by auto
  thus ?thesis unfolding omega_regular_languages_def by blast
qed

end