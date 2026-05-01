theory omega_regular_languages

imports Main omega_regular_expressions

begin

text \<open>Author: Benno Thalmann, last update: 1.5.2026, Addition to masterarbeit_benno_thalmann\<close>

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
proposition omega_reg_lang_well_def: "L \<in> omega_regular_languages \<Sigma> \<Longrightarrow> omega_language_well_defined L \<Sigma>"
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

proposition comp_is_omega_regular:
  assumes "L \<in> omega_regular_languages \<Sigma>"
  shows "comp_omega_language \<Sigma> L \<in> omega_regular_languages \<Sigma>"
proof - 
  have inf_nat: "infinite (UNIV :: nat set)" by simp
  hence "L \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = omega_language_auto NFA_\<A>}" using assms omega_reg_lang_nbas by blast
  hence "\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = omega_language_auto NFA_\<A>" by blast
  hence "\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> comp_omega_language \<Sigma> L = omega_language_auto NFA_\<A>" using inf_nat existence_of_omega_comp_same_type by metis
  hence "comp_omega_language \<Sigma> L \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = omega_language_auto NFA_\<A>}" by blast
  thus ?thesis using omega_reg_lang_nbas by blast
qed

lemma relative_complement_omega:
  assumes "omega_language_well_defined L1 \<Sigma>" "omega_language_well_defined L2 \<Sigma>"
  shows "L1 - L2 = L1 \<inter> comp_omega_language \<Sigma> L2"
  using assms unfolding comp_omega_language_def omega_sigma_star_def omega_language_well_defined_def by blast

proposition relative_complement_is_omega_regular:
  assumes "L1 \<in> omega_regular_languages \<Sigma>" "L2 \<in> omega_regular_languages \<Sigma>"
  shows "(L1 - L2) \<in> omega_regular_languages \<Sigma>"
proof - 
  have "omega_language_well_defined L1 \<Sigma> \<and> omega_language_well_defined L2 \<Sigma>" using assms omega_reg_lang_well_def by blast
  hence equi: "L1 - L2 = L1 \<inter> comp_omega_language \<Sigma> L2" using relative_complement_omega by blast
  have "comp_omega_language \<Sigma> L2 \<in> omega_regular_languages \<Sigma>" using assms comp_is_omega_regular by blast
  thus ?thesis using inter_is_omega_regular assms equi by force
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




definition omega_word_pow2_ab :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where "omega_word_pow2_ab a b n = (if (\<exists> k . n = 2^k) then a else b)"

definition pump_omega_word_once :: "'a omega_word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a omega_word" where "pump_omega_word_once x i j = (\<lambda>n . if n < i then x n else if n < j + (j - i) then x (i + ((n - i) mod (j - i))) else x (n - (j - i)))"

definition pump_omega_run_once :: "'s omega_run \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 's omega_run" where "pump_omega_run_once r i j = (\<lambda>n . if n < i then r n else if n < j + (j - i) then r (i + ((n - i) mod (j - i))) else r (n - (j - i)))"

lemma mod_suc_not_zero:
  assumes "(d :: nat) > 0" "(Suc n) mod d \<noteq> 0"
  shows "(Suc n) mod d = n mod d + 1"
  using assms by (metis Suc_eq_plus1 mod_Suc)

lemma mod_suc_zero_pred:
  assumes "(d :: nat) > 0" "Suc n mod d = 0"
  shows "n mod d = d - 1"
  using assms by (metis diff_Suc_1 mod_Suc nat.distinct(1))

lemma NBA_singleton_run_pump:
  assumes "auto_well_defined \<A>" "omega_run_accepting r \<A> x" "i < j" "r i = r j"
  shows "pump_omega_word_once x i j \<in> omega_language_auto \<A>"
proof -
  let ?d = "j - i"
  let ?x = "pump_omega_word_once x i j"
  let ?r = "pump_omega_run_once r i j"
  have d_pos: "?d > 0" using assms by simp
  have run_def: "omega_pseudo_run_well_defined r \<A> (initial_state \<A>) x" using assms unfolding omega_run_accepting_def omega_run_well_defined_def by blast
  hence init: "?r 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using assms  unfolding pump_omega_run_once_def omega_pseudo_run_well_defined_def by auto
  {
    fix n
    consider (before) "n + 1 < i" | (enter) "n + 1 = i" | (loop) "i \<le> n \<and> n + 1 < j + ?d" | (exit) "n < j + ?d \<and> n + 1 = j + ?d" | (after) "j + ?d \<le> n" by linarith
    hence "(?r n, ?x n, ?r (n + 1)) \<in> transitions \<A>"
    proof cases
      case before thus ?thesis using run_def unfolding pump_omega_run_once_def pump_omega_word_once_def omega_pseudo_run_well_defined_def by auto
    next
      case enter
      hence "n = i - 1" using assms by simp
      hence rn: "?r n = r n" using enter unfolding pump_omega_run_once_def by fastforce
      have xn: "?x n = x n" using enter unfolding pump_omega_word_once_def by simp
      have "?r (n + 1) = r i" using enter unfolding pump_omega_run_once_def by simp
      thus ?thesis using rn xn run_def enter unfolding omega_pseudo_run_well_defined_def by auto
    next
      case loop
      define m where "m = i + ((n - i) mod ?d)"
      hence m_bounds: "i \<le> m \<and> m < j" using d_pos assms by (metis le_add1 le_add_diff_inverse less_or_eq_imp_le mod_less_divisor nat_add_left_cancel_less)
      have r_n: "?r n = r m" using loop unfolding pump_omega_run_once_def m_def by auto
      have x_n: "?x n = x m" using loop unfolding pump_omega_word_once_def m_def by auto
      consider (wrap) "(n + 1 - i) mod ?d = 0" | (nowrap) "(n + 1 - i) mod ?d \<noteq> 0" by blast
      thus ?thesis
      proof cases
        case wrap
        have "(n + 1 - i) = Suc (n - i)" using loop by linarith
        hence "(Suc (n - i)) mod ?d = 0" using wrap by simp
        hence "(n - i) mod ?d = ?d - 1" using d_pos mod_suc_zero_pred by metis
        hence "m = j - 1" using assms unfolding m_def by simp
        hence mj: "m + 1 = j" using assms by simp        
        have r_suc: "?r (n + 1) = r i" using loop wrap unfolding pump_omega_run_once_def by auto
        have "(r m, x m, r (m + 1)) \<in> transitions \<A>" using run_def unfolding omega_pseudo_run_well_defined_def by blast
        hence "(r m, x m, r j) \<in> transitions \<A>" using mj by simp
        hence "(r m, x m, r i) \<in> transitions \<A>" using assms by simp
        thus ?thesis using r_n x_n r_suc by simp
      next
        case nowrap
        have "(n + 1 - i) = Suc (n - i)" using loop by linarith
        hence "(n + 1 - i) mod ?d = (n - i) mod ?d + 1" using nowrap d_pos by (metis mod_suc_not_zero)
        hence "i + ((n + 1 - i) mod ?d) = m + 1" unfolding m_def by simp
        hence r_suc: "?r (n + 1) = r (m + 1)" using loop nowrap unfolding pump_omega_run_once_def by auto
        have "(r m, x m, r (m + 1)) \<in> transitions \<A>" using run_def m_bounds unfolding omega_pseudo_run_well_defined_def by auto
        thus ?thesis using r_n x_n r_suc by simp
      qed
    next
      case exit
      hence step1: "n + 1 - i = Suc (n - i)" using assms by linarith
      have "(n + 1 - i) mod ?d = 0" using exit assms by (metis Nat.add_diff_assoc2 less_imp_le_nat mod_add_self2 mod_self)
      hence "(Suc (n - i)) mod ?d = 0" using step1 by simp
      hence "(n - i) mod ?d = ?d - 1" using d_pos mod_suc_zero_pred by metis
      hence n_map: "i + ((n - i) mod ?d) = j - 1" using assms by simp
      hence r_n: "?r n = r (j - 1)" using exit unfolding pump_omega_run_once_def by auto
      have x_n: "?x n = x (j - 1)" using exit n_map unfolding pump_omega_word_once_def by auto
      have r_suc: "?r (n + 1) = r j" using exit unfolding pump_omega_run_once_def by simp
      have jm1_suc: "(j - 1) + 1 = j" using assms by simp
      have "(r (j - 1), x (j - 1), r ((j - 1) + 1)) \<in> transitions \<A>" using run_def unfolding omega_pseudo_run_well_defined_def by blast
      hence "(r (j - 1), x (j - 1), r j) \<in> transitions \<A>" using jm1_suc by simp
      thus ?thesis using r_n x_n r_suc by simp
    next
      case after
      hence r_n: "?r n = r (n - ?d)" unfolding pump_omega_run_once_def by simp
      have x_n: "?x n = x (n - ?d)" using after unfolding pump_omega_word_once_def by simp
      have "j + ?d \<le> n + 1" using after by simp
      hence r_suc: "?r (n + 1) = r ((n + 1) - ?d)" unfolding pump_omega_run_once_def by simp
      have "(n + 1) - ?d = (n - ?d) + 1" using after d_pos by linarith
      hence "?r (n + 1) = r ((n - ?d) + 1)" using r_suc by simp
      thus ?thesis using run_def r_n x_n unfolding omega_pseudo_run_well_defined_def by presburger
    qed
  }
  hence "\<forall> n . (?r n, ?x n, ?r (n + 1)) \<in> transitions \<A>" by blast
  hence well: "omega_run_well_defined ?r \<A> ?x" using init unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
  have acc_inf: "\<forall> n . \<exists> N > n . r N \<in> accepting_states \<A>" using assms unfolding omega_run_accepting_def by blast
  {
    fix n
    obtain M where M: "M > max n j + ?d \<and> r M \<in> accepting_states \<A>" using acc_inf by blast
    define N where "N = M + ?d"
    hence N: "N > n" using M by linarith
    have jd: "j + ?d \<le> N" using M unfolding N_def by linarith
    have "N - ?d = M" unfolding N_def by simp
    hence "?r N = r M" using jd unfolding pump_omega_run_once_def by force
    hence "\<exists> N > n. ?r N \<in> accepting_states \<A>" using N M by metis
  }
  hence "\<forall> n . \<exists> N > n . ?r N \<in> accepting_states \<A>" by blast
  hence "omega_run_accepting ?r \<A> ?x" using well unfolding omega_run_accepting_def by blast
  thus ?thesis unfolding omega_language_auto_def by blast
qed

lemma pow2_gap_not_pow2:
  assumes "d > 0" "d < (2::nat)^k"
  shows "\<not> (\<exists> l::nat . (2::nat)^k + d = (2::nat)^l)"
proof
  assume "\<exists> l::nat. (2::nat)^k + d = (2::nat)^l"
  then obtain l where l: "(2::nat)^k + d = (2::nat)^l" by blast
  consider "l \<le> k" | "k < l" by linarith
  thus False
  proof cases
    case 1
    hence "(2::nat)^l \<le> (2::nat)^k" by (simp add: power_increasing)
    thus False using l assms by linarith
  next
    case 2
    hence "Suc k \<le> l" by simp
    hence pow: "(2::nat)^(Suc k) \<le> (2::nat)^l" using one_le_numeral power_increasing by blast
    have "(2::nat)^k + d < (2::nat)^(Suc k)" using assms by simp
    thus False using l pow by linarith
  qed
qed

lemma pow2_pumped_word_neq:
  assumes "a \<noteq> b" "i < j" "j < 2^k"
  shows "pump_omega_word_once (omega_word_pow2_ab a b) i j \<noteq> omega_word_pow2_ab a b"
proof -
  let ?d = "j - i"
  have "pump_omega_word_once (omega_word_pow2_ab a b) i j (2^k + ?d) = omega_word_pow2_ab a b (2^k)" using assms unfolding pump_omega_word_once_def by fastforce
  hence left: "pump_omega_word_once (omega_word_pow2_ab a b) i j (2^k + ?d) = a" unfolding omega_word_pow2_ab_def by auto
  have d_pos: "?d > 0" using assms by simp
  have "?d < 2^k" using assms by simp
  hence "omega_word_pow2_ab a b (2^k + ?d) = b" using pow2_gap_not_pow2 d_pos unfolding omega_word_pow2_ab_def by presburger
  thus ?thesis using assms left by auto
qed

lemma singleton_NBA_pow2_impossible:
  assumes "a \<noteq> b" "auto_well_defined \<A>" "alphabet \<A> = {a, b}" "omega_language_auto \<A> = {omega_word_pow2_ab a b}"
  shows False
proof -
  obtain r where r: "omega_run_accepting r \<A> (omega_word_pow2_ab a b)" using assms unfolding omega_language_auto_def by blast
  define c where "c = card (states \<A>)"
  obtain k where k: "Suc c < 2^k" using less_exp by blast
  have finite_states: "finite (states \<A>)" using assms unfolding auto_well_defined_def by blast
  {
    fix n
    have "(r n, omega_word_pow2_ab a b n, r (n + 1)) \<in> transitions \<A>" using r unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
    hence "r n \<in> states \<A>" using assms unfolding auto_well_defined_def by fastforce
  }
  hence "r ` {..<Suc c} \<subseteq> states \<A>" by auto
  hence card_img: "card (r ` {..<Suc c}) \<le> c"  using finite_states c_def card_mono by blast
  have "\<not> inj_on r {..<Suc c}"
  proof
    assume inj: "inj_on r {..<Suc c}"
    hence "card (r ` {..<Suc c}) = Suc c" by (simp add: card_image)
    thus False using card_img by simp
  qed
  then obtain i j where ij: "i \<in> {..<Suc c} \<and> j \<in> {..<Suc c} \<and> i \<noteq> j \<and> r i = r j" unfolding inj_on_def by blast
  have exists_pq: "\<exists> p q . p < q \<and> q \<le> c \<and> r p = r q"
  proof -
    consider "i < j" | "j < i" using ij by linarith
    thus ?thesis
    proof cases
      case 1 thus ?thesis using ij by force
    next
      case 2 thus ?thesis using ij by force
    qed
  qed
  then obtain p q where pq: "p < q \<and> q \<le> c \<and> r p = r q" by blast
  hence q_lt_pow: "q < 2^k" using k by simp
  have "pump_omega_word_once (omega_word_pow2_ab a b) p q \<in> omega_language_auto \<A>" using NBA_singleton_run_pump assms r pq by blast
  hence pumped_eq: "pump_omega_word_once (omega_word_pow2_ab a b) p q = omega_word_pow2_ab a b" using assms by blast
  have  "pump_omega_word_once (omega_word_pow2_ab a b) p q \<noteq> omega_word_pow2_ab a b" using pow2_pumped_word_neq[of a b p q k] assms pq q_lt_pow by blast
  thus False using pumped_eq by blast
qed

theorem singleton_pow2_not_omega_regular:
  assumes "a \<noteq> b"
  shows "{omega_word_pow2_ab a b} \<notin> omega_regular_languages {a, b}"
proof
  assume assm: "{omega_word_pow2_ab a b} \<in> omega_regular_languages {a, b}"
  have "infinite (UNIV :: nat set)" by simp
  hence "omega_regular_languages {a, b} = {L . \<exists> (\<A> :: (nat, 'a) automaton) . auto_well_defined \<A> \<and> alphabet \<A> = {a,b} \<and> L = omega_language_auto \<A>}" using omega_reg_lang_nbas by blast
  then obtain \<A> :: "(nat, 'a) automaton" where A: "auto_well_defined \<A> \<and> alphabet \<A> = {a, b} \<and> omega_language_auto \<A> = {omega_word_pow2_ab a b}" using assm by auto
  thus False using singleton_NBA_pow2_impossible assms by metis
qed

theorem finite_not_implies_omega_regular:
  assumes "infinite (UNIV :: 'a set)"
  shows "\<exists> (L :: 'a omega_language) \<Sigma> . finite L \<and> finite \<Sigma> \<and> omega_language_well_defined L \<Sigma> \<and> L \<notin> omega_regular_languages \<Sigma>"
proof -
  obtain a where a: "a \<in> (UNIV :: 'a set)" by blast
  hence "\<exists> b . b \<in> (UNIV :: 'a set) - {a}" using assms ex_in_conv infinite_imp_nonempty infinite_remove by metis
  then obtain b where b: "b \<in> (UNIV :: 'a set) \<and> a \<noteq> b" by blast 
  have fin: "finite ({omega_word_pow2_ab a b} :: 'a omega_language)" by simp
  have fin_alph: "finite {a, b}" by simp
  have well_def: "omega_language_well_defined ({omega_word_pow2_ab a b} :: 'a omega_language) {a, b}" unfolding omega_language_well_defined_def omega_word_well_defined_def omega_word_pow2_ab_def by auto
  have "({omega_word_pow2_ab a b} :: 'a omega_language) \<notin> omega_regular_languages {a,b}" using singleton_pow2_not_omega_regular a b by fast
  thus ?thesis using fin fin_alph well_def by blast
qed

end