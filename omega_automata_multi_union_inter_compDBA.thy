theory omega_automata_multi_union_inter_compDBA

imports Main omega_automata_isomorphy

begin

text \<open>Author: Benno Thalmann, last update: 11.2.2026, Addition to masterarbeit_benno_thalmann\<close>

definition omega_pseudo_run_well_defined_multi :: "'s omega_run \<Rightarrow> ('s, 'a) nfa_multi \<Rightarrow> 's state \<Rightarrow> 'a omega_word \<Rightarrow> bool" where
  "omega_pseudo_run_well_defined_multi omega_prun \<A> s omega_word =
    (omega_prun 0 = s \<and> s \<in> states_multi \<A> \<and>
    (\<forall> i . (omega_prun i, omega_word i, omega_prun (i + 1)) \<in> transitions_multi \<A>))"

definition omega_prun_states_multi :: "'s omega_run \<Rightarrow> ('s, 'a) nfa_multi \<Rightarrow> bool" where "omega_prun_states_multi omega_prun \<A> = (\<forall> n . omega_prun n \<in> states_multi \<A>)"

theorem well_def_implies_omega_prun_states_multi:
  assumes "auto_well_defined_multi \<A>" "omega_pseudo_run_well_defined_multi omega_prun \<A> s omega_word"
  shows "omega_prun_states_multi omega_prun \<A>"
  using assms unfolding omega_pseudo_run_well_defined_multi_def auto_well_defined_multi_def omega_prun_states_multi_def by blast

definition omega_run_well_defined_multi :: "'s omega_run \<Rightarrow> ('s, 'a) nfa_multi \<Rightarrow> 'a omega_word \<Rightarrow> bool" where "omega_run_well_defined_multi omega_run \<A> omega_word = (omega_pseudo_run_well_defined_multi omega_run \<A> (omega_run 0) omega_word \<and> (omega_run 0) \<in> initial_states_multi \<A>)"

definition omega_run_accepting_multi :: "'s omega_run \<Rightarrow> ('s, 'a) nfa_multi \<Rightarrow> 'a omega_word \<Rightarrow> bool" where "omega_run_accepting_multi omega_run \<A> omega_word = (omega_run_well_defined_multi omega_run \<A> omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states_multi \<A>))"

definition omega_language_auto_multi :: "('s, 'a) nfa_multi \<Rightarrow> 'a omega_language" where "omega_language_auto_multi \<A> = {omega_word . \<exists> omega_run . omega_run_accepting_multi omega_run \<A> omega_word}"

theorem well_def_implies_omega_word_well_defined_multi:
  assumes "auto_well_defined_multi \<A>" "omega_pseudo_run_well_defined_multi omega_prun \<A> s omega_word"
  shows "omega_word_well_defined omega_word (alphabet_multi \<A>)"
  using assms unfolding omega_pseudo_run_well_defined_multi_def auto_well_defined_multi_def omega_word_well_defined_def by fast

corollary omega_word_in_omega_language_is_well_defined_multi:
  assumes "auto_well_defined_multi \<A>" "omega_word \<in> omega_language_auto_multi \<A>"
  shows "omega_word_well_defined omega_word (alphabet_multi \<A>)"
  using assms well_def_implies_omega_word_well_defined_multi unfolding omega_language_auto_multi_def omega_run_accepting_multi_def omega_run_well_defined_multi_def by fast

proposition automata_omega_language_are_well_defined_multi:
  assumes "auto_well_defined_multi \<A>"
  shows "omega_language_well_defined (omega_language_auto_multi \<A>) (alphabet_multi \<A>)"
  using assms omega_word_in_omega_language_is_well_defined_multi unfolding omega_language_well_defined_def by blast

proposition union_omega_language_well_defined:
  assumes "omega_language_well_defined L1 \<Sigma>1" "omega_language_well_defined L2 \<Sigma>2"
  shows "omega_language_well_defined (L1 \<union> L2) (\<Sigma>1 \<union> \<Sigma>2)"
  using assms unfolding omega_language_well_defined_def omega_word_well_defined_def by fast

corollary automata_union_omega_lang_well_defined_multi:
  assumes "auto_well_defined_multi \<A>1" "auto_well_defined_multi \<A>2"
  shows "omega_language_well_defined (omega_language_auto_multi \<A>1 \<union> omega_language_auto_multi \<A>2) (alphabet_multi \<A>1 \<union> alphabet_multi \<A>2)"
  using assms union_omega_language_well_defined automata_omega_language_are_well_defined_multi by metis

corollary omega_language_well_def_NFA_to_multi:
  assumes "auto_well_defined \<A>"
  shows "omega_language_well_defined (omega_language_auto_multi (NFA_to_multi \<A>)) (alphabet_multi (NFA_to_multi \<A>))"
  using NFA_to_multi_auto_well_defined assms automata_omega_language_are_well_defined_multi by blast

proposition omega_prun_on_NFA_to_multi: "omega_pseudo_run_well_defined omega_run \<A> s omega_word \<longleftrightarrow> omega_pseudo_run_well_defined_multi omega_run (NFA_to_multi \<A>) s omega_word"
  unfolding NFA_to_multi_def omega_pseudo_run_well_defined_def omega_pseudo_run_well_defined_multi_def by auto

text \<open>Main result for NFA_to_multi\<close>
theorem NFA_to_multi_omega_language_correctness: "omega_language_auto \<A> = omega_language_auto_multi (NFA_to_multi \<A>)"
proof -
  {
    fix omega_word assume "omega_word \<in> omega_language_auto \<A>"
    then obtain omega_run where "omega_pseudo_run_well_defined omega_run \<A> (initial_state \<A>) omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>)" unfolding omega_language_auto_def omega_run_accepting_def omega_run_well_defined_def by blast
    hence "omega_pseudo_run_well_defined_multi omega_run (NFA_to_multi \<A>) (initial_state \<A>) omega_word \<and> initial_state \<A> \<in> initial_states_multi (NFA_to_multi \<A>) \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states_multi (NFA_to_multi \<A>))" using omega_prun_on_NFA_to_multi unfolding NFA_to_multi_def by force
    hence "omega_run_well_defined_multi omega_run (NFA_to_multi \<A>) omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states_multi (NFA_to_multi \<A>))" unfolding omega_pseudo_run_well_defined_multi_def omega_run_well_defined_multi_def by argo
    hence "omega_word \<in> omega_language_auto_multi (NFA_to_multi \<A>)" unfolding omega_run_accepting_multi_def omega_language_auto_multi_def by blast
  }
  hence sub: "omega_language_auto \<A> \<subseteq> omega_language_auto_multi (NFA_to_multi \<A>)" by blast
  {
    fix omega_word assume "omega_word \<in> omega_language_auto_multi (NFA_to_multi \<A>)"
    then obtain omega_run where "omega_pseudo_run_well_defined_multi omega_run (NFA_to_multi \<A>) (omega_run 0) omega_word \<and> (omega_run 0) \<in> initial_states_multi (NFA_to_multi \<A>) \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states_multi (NFA_to_multi \<A>))" unfolding omega_language_auto_multi_def omega_run_accepting_multi_def omega_run_well_defined_multi_def by blast
    hence "omega_pseudo_run_well_defined omega_run \<A> (initial_state \<A>) omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>)" using omega_prun_on_NFA_to_multi unfolding NFA_to_multi_def by force
    hence "omega_word \<in> omega_language_auto \<A>" unfolding omega_run_well_defined_def omega_run_accepting_def omega_language_auto_def by auto
  }
  thus ?thesis using sub by blast
qed

corollary existence_of_omega_NFA_to_multi_same_type:
  assumes "auto_well_defined (NFA_\<A> :: ('s, 'a) automaton)"
  shows "\<exists> NFA_multi_\<A> :: ('s, 'a) nfa_multi . auto_well_defined_multi NFA_multi_\<A> \<and> alphabet NFA_\<A> = alphabet_multi NFA_multi_\<A> \<and> omega_language_auto NFA_\<A> = omega_language_auto_multi NFA_multi_\<A>"
  using assms NFA_to_multi_omega_language_correctness NFA_to_multi_auto_well_defined NFA_to_multi_alphabet by fast



text \<open>The union automaton for Büchi automata with the help of nfa_multi\<close>
corollary omega_language_well_def_union_multi_auto:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "omega_language_well_defined (omega_language_auto_multi (union_automaton_multi \<A>1 \<A>2)) (alphabet_multi (union_automaton_multi \<A>1 \<A>2))"
  using union_auto_well_defined assms automata_omega_language_are_well_defined_multi by blast




lemma trans_union_auto_A1_state2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" "s1 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  shows "s2 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
proof(rule ccontr)
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  assume assm: "s2 \<notin> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  have "auto_well_defined_multi ?\<A>" using assms union_auto_well_defined by auto
  hence "s2 \<in> states_multi ?\<A>" using assms well_def_trans_components_multi by fast
  hence "s2 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assm unfolding union_automaton_multi_def union_automaton_multi_helper_def by force  
  have well_def: "auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  have "transitions_multi ?\<A> = (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" unfolding union_automaton_multi_def union_automaton_multi_helper_def by force
  hence trans: "(s1, a, s2) \<in> (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" using assms by argo
  thus False using well_def well_def_trans_components assms assm cross_renaming_intersection_empty by fast
qed

lemma omega_prun_union_auto_first_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "omega_pseudo_run_well_defined_multi omega_prun (union_automaton_multi \<A>1 \<A>2) s omega_word" "s \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  shows "omega_pseudo_run_well_defined omega_prun (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) s omega_word"
proof -
  {
    fix i
    have in_states: "omega_prun i \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
    proof(induction i)
      case 0 thus ?case using assms unfolding omega_pseudo_run_well_defined_multi_def by blast
    next
      case (Suc i)
      have "(omega_prun i, omega_word i, omega_prun (Suc i)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" using assms unfolding omega_pseudo_run_well_defined_multi_def by simp 
      thus ?case using Suc assms trans_union_auto_A1_state2 by fast
    qed
    have trans: "(omega_prun i, omega_word i, omega_prun (i + 1)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" using assms unfolding omega_pseudo_run_well_defined_multi_def by blast
    hence "omega_prun (i + 1) \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms in_states trans_union_auto_A1_state2 by fast  
    hence "(omega_prun i, omega_word i, omega_prun (i + 1)) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using trans assms trans_union_auto_A1_trans by fast
  }
  hence "\<forall> i . (omega_prun i, omega_word i, omega_prun (i + 1)) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" by blast
  thus ?thesis using assms unfolding omega_pseudo_run_well_defined_def omega_pseudo_run_well_defined_multi_def by blast
qed

lemma trans_union_auto_A2_state2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" "s1 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  shows "s2 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
proof(rule ccontr)
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  assume assm: "s2 \<notin> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  have "auto_well_defined_multi ?\<A>" using assms union_auto_well_defined by auto
  hence "s2 \<in> states_multi ?\<A>" using assms well_def_trans_components_multi by fast
  hence "s2 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assm unfolding union_automaton_multi_def union_automaton_multi_helper_def by force  
  have well_def: "auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  have "transitions_multi ?\<A> = (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" unfolding union_automaton_multi_def union_automaton_multi_helper_def by force
  hence trans: "(s1, a, s2) \<in> (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" using assms by argo
  thus False using well_def well_def_trans_components assms assm cross_renaming_intersection_empty by fast
qed

lemma omega_prun_union_auto_first_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "omega_pseudo_run_well_defined_multi omega_prun (union_automaton_multi \<A>1 \<A>2) s omega_word" "s \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  shows "omega_pseudo_run_well_defined omega_prun (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) s omega_word"
proof -
  {
    fix i
    have in_states: "omega_prun i \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
    proof(induction i)
      case 0 thus ?case using assms unfolding omega_pseudo_run_well_defined_multi_def by blast
    next
      case (Suc i)
      have "(omega_prun i, omega_word i, omega_prun (Suc i)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" using assms unfolding omega_pseudo_run_well_defined_multi_def by simp 
      thus ?case using Suc assms trans_union_auto_A2_state2 by fast
    qed
    have trans: "(omega_prun i, omega_word i, omega_prun (i + 1)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" using assms unfolding omega_pseudo_run_well_defined_multi_def by blast
    hence "omega_prun (i + 1) \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms in_states trans_union_auto_A2_state2 by fast  
    hence "(omega_prun i, omega_word i, omega_prun (i + 1)) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using trans assms trans_union_auto_A2_trans by fast
  }
  hence "\<forall> i . (omega_prun i, omega_word i, omega_prun (i + 1)) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" by blast
  thus ?thesis using assms unfolding omega_pseudo_run_well_defined_def omega_pseudo_run_well_defined_multi_def by blast
qed

theorem omega_prun_union_auto_correct_left:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "omega_pseudo_run_well_defined_multi omega_prun (union_automaton_multi \<A>1 \<A>2) s omega_word"
  shows "omega_pseudo_run_well_defined omega_prun (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) s omega_word \<or> omega_pseudo_run_well_defined omega_prun (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) s omega_word"
proof - 
  have "s \<in> states_multi (union_automaton_multi \<A>1 \<A>2)" using assms unfolding omega_pseudo_run_well_defined_multi_def by blast
  hence "s \<in> (states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" unfolding union_automaton_multi_def union_automaton_multi_helper_def by auto
  hence "s \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<or> s \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" by blast
  thus ?thesis using assms omega_prun_union_auto_first_A1 omega_prun_union_auto_first_A2 by blast
qed

lemma no_omega_run_A2_init_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "omega_pseudo_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) omega_word"
  shows "False"
  using assms cross_renaming_intersection_empty cross_renaming_iso_automaton_auto_well_defined unfolding omega_pseudo_run_well_defined_def auto_well_defined_def by fast

lemma no_omega_run_A1_init_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "omega_pseudo_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) omega_word"
  shows "False"
  using assms cross_renaming_intersection_empty cross_renaming_iso_automaton_auto_well_defined unfolding omega_pseudo_run_well_defined_def auto_well_defined_def by blast

corollary omega_run_union_auto_correct_left:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "omega_run_well_defined_multi omega_run (union_automaton_multi \<A>1 \<A>2) omega_word"
  shows "omega_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) omega_word \<or> omega_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) omega_word"
proof -
  have "omega_run 0 \<in> initial_states_multi (union_automaton_multi \<A>1 \<A>2)" using assms unfolding omega_run_well_defined_multi_def by blast
  hence "omega_run 0 = initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<or> omega_run 0 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" unfolding union_automaton_multi_def union_automaton_multi_helper_def by auto 
  hence "omega_pseudo_run_well_defined_multi omega_run (union_automaton_multi \<A>1 \<A>2) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) omega_word \<or> omega_pseudo_run_well_defined_multi omega_run (union_automaton_multi \<A>1 \<A>2) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) omega_word" using assms unfolding omega_run_well_defined_multi_def by presburger
  hence "omega_pseudo_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) omega_word \<or> omega_pseudo_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) omega_word \<or> omega_pseudo_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) omega_word \<or> omega_pseudo_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) omega_word" using assms omega_prun_union_auto_correct_left by blast
  hence "omega_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) omega_word \<or> omega_pseudo_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) omega_word \<or> omega_pseudo_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) omega_word \<or> omega_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) omega_word" unfolding omega_run_well_defined_def by blast
  thus ?thesis using assms no_omega_run_A2_init_A1 no_omega_run_A1_init_A2 by blast
qed

lemma no_acc_A2_init_A1_omega:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "omega_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) omega_word" "omega_run n \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  shows "False"
proof - 
  have "omega_prun_states omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms cross_renaming_iso_automaton_auto_well_defined well_def_implies_omega_prun_states unfolding omega_run_well_defined_def by fast
  hence "\<forall> n . omega_run n \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" unfolding omega_prun_states_def by blast
  hence "omega_run n \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> omega_run n \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms by blast
  hence "omega_run n \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> omega_run n \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined unfolding auto_well_defined_def by auto
  thus ?thesis using cross_renaming_intersection_empty by blast
qed

lemma no_acc_A1_init_A2_omega:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "omega_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) omega_word" "omega_run n \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  shows "False"
proof - 
  have "omega_prun_states omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined well_def_implies_omega_prun_states unfolding omega_run_well_defined_def by fast
  hence "\<forall> n . omega_run n \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" unfolding omega_prun_states_def by blast
  hence "omega_run n \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<and> omega_run n \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms by blast
  hence "omega_run n \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<and> omega_run n \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms cross_renaming_iso_automaton_auto_well_defined unfolding auto_well_defined_def by auto
  thus ?thesis using cross_renaming_intersection_empty by blast
qed

theorem union_omega_language_left:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "omega_language_auto_multi (union_automaton_multi \<A>1 \<A>2) \<subseteq> omega_language_auto \<A>1 \<union> omega_language_auto \<A>2"
proof -
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  {
    fix omega_word assume "omega_word \<in> omega_language_auto_multi (union_automaton_multi \<A>1 \<A>2)"
    then obtain omega_run where "omega_run_accepting_multi omega_run ?\<A> omega_word" unfolding omega_language_auto_multi_def by auto
    hence acc: "omega_run_well_defined_multi omega_run ?\<A> omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states_multi ?\<A>)" unfolding omega_run_accepting_multi_def by blast
    hence "omega_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) omega_word \<or> omega_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) omega_word" using assms omega_run_union_auto_correct_left by blast
    then consider (case1) "omega_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) omega_word" | (case2) "omega_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) omega_word" by blast
    hence "omega_run_accepting omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) omega_word \<or> omega_run_accepting omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) omega_word"
    proof cases
      case case1
      {
        fix n
        obtain N where N: "N > n \<and> omega_run N \<in> accepting_states_multi ?\<A>" using acc by blast
        hence "omega_run N \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms case1 no_acc_A2_init_A1_omega unfolding union_automaton_multi_def union_automaton_multi_helper_def by fastforce
        hence "\<exists> N > n . omega_run N \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using N by blast
      }
      thus ?thesis using case1 unfolding omega_run_accepting_def by blast
    next
      case case2
      {
        fix n
        obtain N where N: "N > n \<and> omega_run N \<in> accepting_states_multi ?\<A>" using acc by blast
        hence "omega_run N \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms case2 no_acc_A1_init_A2_omega unfolding union_automaton_multi_def union_automaton_multi_helper_def by fastforce
        hence "\<exists> N > n . omega_run N \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using N by blast
      }
      thus ?thesis using case2 unfolding omega_run_accepting_def by blast
    qed
    hence "omega_word \<in> omega_language_auto (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<or> omega_word \<in> omega_language_auto (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" unfolding omega_language_auto_def by blast
    hence "omega_word \<in> omega_language_auto (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> omega_language_auto (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" by blast
  }
  thus ?thesis using assms cross_renaming_iso_automaton_omega_language by blast
qed

proposition omega_prun_union_auto_correct_right_A1:
  assumes "omega_pseudo_run_well_defined omega_prun (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) s omega_word"
  shows "omega_pseudo_run_well_defined_multi omega_prun (union_automaton_multi \<A>1 \<A>2) s omega_word"
  using assms unfolding omega_pseudo_run_well_defined_def union_automaton_multi_def union_automaton_multi_helper_def omega_pseudo_run_well_defined_multi_def by auto

corollary omega_run_union_auto_correct_right_A1:
  assumes "omega_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) omega_word"
  shows "omega_run_well_defined_multi omega_run (union_automaton_multi \<A>1 \<A>2) omega_word"
proof - 
  have "omega_pseudo_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) omega_word" using assms unfolding omega_run_well_defined_def by blast
  hence omega_run: "omega_pseudo_run_well_defined_multi omega_run (union_automaton_multi \<A>1 \<A>2) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) omega_word" using assms omega_prun_union_auto_correct_right_A1 by blast
  hence "omega_run 0 = initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<in> initial_states_multi (union_automaton_multi \<A>1 \<A>2)" unfolding omega_pseudo_run_well_defined_multi_def union_automaton_multi_def union_automaton_multi_helper_def by auto
  thus ?thesis using omega_run unfolding omega_run_well_defined_multi_def by argo
qed

proposition omega_prun_union_auto_correct_right_A2:
  assumes "omega_pseudo_run_well_defined omega_prun (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) s omega_word"
  shows "omega_pseudo_run_well_defined_multi omega_prun (union_automaton_multi \<A>1 \<A>2) s omega_word"
  using assms unfolding omega_pseudo_run_well_defined_def union_automaton_multi_def union_automaton_multi_helper_def omega_pseudo_run_well_defined_multi_def by auto

corollary omega_run_union_auto_correct_right_A2:
  assumes "omega_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) omega_word"
  shows "omega_run_well_defined_multi omega_run (union_automaton_multi \<A>1 \<A>2) omega_word"
proof - 
  have "omega_pseudo_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) omega_word" using assms unfolding omega_run_well_defined_def by blast
  hence omega_run: "omega_pseudo_run_well_defined_multi omega_run (union_automaton_multi \<A>1 \<A>2) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) omega_word" using assms omega_prun_union_auto_correct_right_A2 by blast
  hence "omega_run 0 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<and> initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<in> initial_states_multi (union_automaton_multi \<A>1 \<A>2)" unfolding omega_pseudo_run_well_defined_multi_def union_automaton_multi_def union_automaton_multi_helper_def by auto
  thus ?thesis using omega_run unfolding omega_run_well_defined_multi_def by argo
qed

corollary omega_run_union_auto_correct:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "omega_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) omega_word \<or> omega_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) omega_word"
  shows "omega_run_well_defined_multi omega_run (union_automaton_multi \<A>1 \<A>2) omega_word"
  using assms omega_run_union_auto_correct_right_A1 omega_run_union_auto_correct_right_A2 by blast

theorem union_omega_language_right:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "omega_language_auto \<A>1 \<union> omega_language_auto \<A>2 \<subseteq> omega_language_auto_multi (union_automaton_multi \<A>1 \<A>2)"
proof -
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  {
    fix omega_word assume "omega_word \<in> omega_language_auto \<A>1 \<union> omega_language_auto \<A>2"
    hence "omega_word \<in> omega_language_auto (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> omega_language_auto (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_omega_language by blast
    then obtain omega_run where "omega_run_accepting omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) omega_word \<or> omega_run_accepting omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) omega_word" unfolding omega_language_auto_def by auto
    hence "(omega_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))) \<or> (omega_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)))" unfolding omega_run_accepting_def by blast
    then consider (case1) "omega_run_well_defined omega_run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))" | (case2) "omega_run_well_defined omega_run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" by blast
    hence "omega_run_well_defined_multi omega_run ?\<A> omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states_multi ?\<A>)"
    proof cases
      case case1
      {
        fix n
        obtain N where N: "N > n \<and> omega_run N \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using case1 by blast
        hence "omega_run N \<in> accepting_states_multi ?\<A>" unfolding union_automaton_multi_def union_automaton_multi_helper_def by auto
        hence "\<exists> N > n . omega_run N \<in> accepting_states_multi ?\<A>" using N by blast
      }
      thus ?thesis using case1 omega_run_union_auto_correct assms by blast
    next
      case case2
      {
        fix n
        obtain N where N: "N > n \<and> omega_run N \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using case2 by blast
        hence "omega_run N \<in> accepting_states_multi ?\<A>" unfolding union_automaton_multi_def union_automaton_multi_helper_def by auto
        hence "\<exists> N > n . omega_run N \<in> accepting_states_multi ?\<A>" using N by blast
      }
      thus ?thesis using case2 omega_run_union_auto_correct assms by blast
    qed
    hence "omega_run_accepting_multi omega_run ?\<A> omega_word" unfolding omega_run_accepting_multi_def by blast
    hence "omega_word \<in> omega_language_auto_multi ?\<A>" unfolding omega_language_auto_multi_def by blast
  }
  thus ?thesis by blast
qed

text \<open>Union automaton multi language correctness:\<close>
theorem union_auto_omega_language_correctness:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "omega_language_auto_multi (union_automaton_multi \<A>1 \<A>2) = omega_language_auto \<A>1 \<union> omega_language_auto \<A>2"
  using union_omega_language_left union_omega_language_right assms by blast

theorem omega_union_main_multi:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> union_\<A> :: ('s \<times> nat, 'a) nfa_multi . auto_well_defined_multi union_\<A> \<and> alphabet_multi union_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> omega_language_auto_multi union_\<A> = omega_language_auto \<A>1 \<union> omega_language_auto \<A>2"
proof -
  have "\<exists> \<A>' :: ('s, 'a) automaton. auto_well_defined \<A>' \<and> alphabet \<A>' = alphabet \<A>2 \<and> omega_language_auto \<A>' = omega_language_auto \<A>2" using assms existence_soft_iso_auto_omega_lang by blast
  thus ?thesis using assms union_auto_omega_language_correctness union_auto_well_defined union_auto_alphabet by metis
qed





text \<open>Transformation of Büchi automata with multiple initial states to a NFA with only one initial state\<close>
corollary omega_language_well_def_normalize_multi_auto:
  assumes "auto_well_defined_multi \<A>"
  shows "omega_language_well_defined (omega_language_auto (normalize_nfa \<A>)) (alphabet (normalize_nfa \<A>))"
  using normalize_preserves_well_defined assms automata_omega_language_are_well_defined by blast

definition omega_run_transformation :: "'s omega_run \<Rightarrow> ('s + unit) omega_run" where "omega_run_transformation omega_run = (\<lambda>n . (if n = 0 then Inr() else (Inl (omega_run n))))"

proposition omega_run_transformation_left:
  assumes "auto_well_defined_multi \<A>" "omega_run_well_defined_multi omega_run \<A> omega_word"
  shows "omega_run_well_defined (omega_run_transformation omega_run) (normalize_nfa \<A>) omega_word"
proof - 
  have "(omega_run_transformation omega_run) 0 = initial_state (normalize_nfa \<A>)" using assms unfolding omega_run_transformation_def normalize_nfa_def by auto
  hence init: "(omega_run_transformation omega_run) 0 = initial_state (normalize_nfa \<A>) \<and> initial_state (normalize_nfa \<A>) \<in> states (normalize_nfa \<A>)" using assms normalize_preserves_well_defined unfolding auto_well_defined_def by blast
  {
    fix i
    have "((omega_run_transformation omega_run) i, omega_word i, (omega_run_transformation omega_run) (i + 1)) \<in> transitions (normalize_nfa \<A>)"
    proof(cases i)
      case 0
      hence trans: "(omega_run 0, omega_word 0, omega_run 1) \<in> transitions_multi \<A> \<and> omega_run 0 \<in> initial_states_multi \<A>" using assms unfolding omega_run_well_defined_multi_def omega_pseudo_run_well_defined_multi_def by force
      have "(omega_run_transformation omega_run) 0 = Inr()" unfolding omega_run_transformation_def by auto
      hence "(omega_run_transformation omega_run) 0 = Inr() \<and> (omega_run_transformation omega_run) 1 = Inl (omega_run 1)" using 0 unfolding omega_run_transformation_def by force
      thus ?thesis using trans 0 unfolding normalize_nfa_def by force
    next
      case(Suc nat)
      hence equi: "(omega_run_transformation omega_run) i = Inl (omega_run i) \<and> (omega_run_transformation omega_run) (i + 1) = Inl (omega_run (i + 1))" unfolding omega_run_transformation_def by force
      have "(omega_run i, omega_word i, omega_run (i + 1)) \<in> transitions_multi \<A>" using assms unfolding omega_run_well_defined_multi_def omega_pseudo_run_well_defined_multi_def by blast
      hence "(Inl (omega_run i), omega_word i, Inl (omega_run (i + 1))) \<in> transitions (normalize_nfa \<A>)" unfolding normalize_nfa_def by force
      thus ?thesis using equi by argo
    qed
  }
  hence "(\<forall> i . ((omega_run_transformation omega_run) i, omega_word i, (omega_run_transformation omega_run) (i + 1)) \<in> transitions (normalize_nfa \<A>))" by blast
  thus ?thesis using init assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by argo
qed

lemma nfa_multi_omega_language_left:
  assumes "auto_well_defined_multi \<A>"
  shows "omega_language_auto_multi \<A> \<subseteq> omega_language_auto (normalize_nfa \<A>)"
proof -
  let ?\<A> = "normalize_nfa \<A>"
  {
    fix omega_word assume "omega_word \<in> omega_language_auto_multi \<A>"
    then obtain omega_run where "omega_run_accepting_multi omega_run \<A> omega_word" unfolding omega_language_auto_multi_def by blast
    hence omega_run: "omega_run_well_defined_multi omega_run \<A> omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states_multi \<A>)" unfolding omega_run_accepting_multi_def by auto
    {
      fix n
      obtain N where N: "N > n \<and> omega_run N \<in> accepting_states_multi \<A>" using omega_run by fastforce
      hence "omega_run_transformation omega_run N = Inl (omega_run N)" unfolding omega_run_transformation_def by force
      hence "omega_run_transformation omega_run N \<in> accepting_states (normalize_nfa \<A>)" using N unfolding normalize_nfa_def by auto
      hence "\<exists> N > n . omega_run_transformation omega_run N \<in> accepting_states (normalize_nfa \<A>)" using N by blast
    }
    hence "omega_run_accepting (omega_run_transformation omega_run) (normalize_nfa \<A>) omega_word" using omega_run assms omega_run_transformation_left unfolding omega_run_accepting_def by blast
    hence "omega_word \<in> omega_language_auto (normalize_nfa \<A>)" unfolding omega_language_auto_def by blast 
  }
  thus ?thesis by auto
qed

lemma no_inr_in_omega_run:
  assumes "omega_run_accepting omega_run (normalize_nfa \<A>) omega_word"
  shows "\<forall> i \<noteq> 0 . omega_run i \<noteq> Inr()"
proof - 
  {
    fix i::nat assume assm: "i \<noteq> 0"
    hence "omega_run i \<noteq> Inr()"
    proof(induction i)
      case 0 thus ?case using assm by blast
    next
      case (Suc i)
      have "(omega_run i, omega_word i, omega_run (i + 1)) \<in> transitions (normalize_nfa \<A>)" using assms unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
      thus ?case using Suc unfolding normalize_nfa_def by force
    qed
  }
  thus ?thesis by blast
qed

definition omega_run_detransformation :: "('s + unit) omega_run \<Rightarrow> 's state \<Rightarrow>'s omega_run" where "omega_run_detransformation omega_run s = (\<lambda>n . (if n = 0 then s else (THE s . Inl s = omega_run n)))"

lemma unique_existence:
  assumes "(s :: ('s + unit)) \<noteq> Inr()"
  shows "\<exists>! s' . Inl s' = s"
  using assms sum.collapse(1) sum.collapse(2) by force

proposition omega_run_transformation_right:
  assumes "auto_well_defined_multi \<A>" "omega_run_accepting omega_run (normalize_nfa \<A>) omega_word"
  shows "\<exists> omega_run' . omega_run_accepting_multi omega_run' \<A> omega_word"
proof -
  let ?\<A> = "normalize_nfa \<A>"
  have props: "omega_run 0 = (initial_state ?\<A>) \<and> (initial_state ?\<A>) \<in> states ?\<A> \<and> (\<forall> n . (omega_run n, omega_word n, omega_run (n + 1)) \<in> transitions ?\<A>) \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states ?\<A>)" using assms unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
  hence "omega_run 0 = (initial_state ?\<A>) \<and> (omega_run 0, omega_word 0, omega_run 1) \<in> transitions ?\<A>" using add_cancel_right_left by metis
  hence "(Inr(), omega_word 0, omega_run 1) \<in> transitions ?\<A>" unfolding normalize_nfa_def by fastforce
  then obtain s s' where s: "s \<in> initial_states_multi \<A> \<and> (s, omega_word 0, s') \<in> transitions_multi \<A> \<and> Inl s' = omega_run 1" unfolding normalize_nfa_def by auto
  define omega_run' where "omega_run' = omega_run_detransformation omega_run s"
  have "omega_run' 0 \<in> initial_states_multi \<A>" using s unfolding omega_run'_def omega_run_detransformation_def by presburger
  hence init: "omega_run' 0 \<in> initial_states_multi \<A> \<and> omega_run' 0 \<in> states_multi \<A>" using assms unfolding auto_well_defined_multi_def by fast
  {
    fix n
    have "(omega_run' n, omega_word n, omega_run' (n + 1)) \<in> transitions_multi \<A>"
    proof(cases n)
      case 0
      have unique: "\<exists>! s' . Inl s' = omega_run 1" using s Inl_inject by metis
      have "omega_run' 1 = (THE s . Inl s = omega_run 1)" unfolding omega_run'_def omega_run_detransformation_def by auto
      hence o1: "omega_run' 1 = s'" using unique the1_equality s by fastforce
      have "omega_run' 0 = s" using s unfolding omega_run'_def omega_run_detransformation_def by auto
      thus ?thesis using s o1 0 by auto
    next
      case (Suc n)
      have trans: "(omega_run (Suc n), omega_word (Suc n), omega_run ((Suc n) + 1)) \<in> transitions ?\<A>" using props by blast
      have not_inr: "omega_run (Suc n) \<noteq> Inr() \<and> omega_run ((Suc n) + 1) \<noteq> Inr()" using assms no_inr_in_omega_run by auto
      hence unique1: "\<exists>! s . Inl s = omega_run (Suc n)" using unique_existence by fast
      then obtain s1 where s1: "Inl s1 = omega_run (Suc n)" by blast
      have "omega_run' (Suc n) = (THE s . Inl s = omega_run (Suc n))" unfolding omega_run'_def omega_run_detransformation_def by auto
      hence os1: "omega_run' (Suc n) = s1" using unique1 the1_equality s1 by fastforce
      have unique2: "\<exists>! s . Inl s = omega_run ((Suc n) + 1)" using not_inr unique_existence by fast
      then obtain s2 where s2: "Inl s2 = omega_run ((Suc n) + 1)" by blast
      have "omega_run' ((Suc n) + 1) = (THE s . Inl s = omega_run ((Suc n) + 1))" unfolding omega_run'_def omega_run_detransformation_def by auto
      hence os2: "omega_run' ((Suc n) + 1) = s2" using unique2 the1_equality s2 by fastforce
      have "(Inl s1, omega_word (Suc n), Inl s2) \<in> transitions ?\<A>" using trans s1 s2 by auto
      hence "(s1, omega_word (Suc n), s2) \<in> transitions_multi \<A>" unfolding normalize_nfa_def by auto
      thus ?thesis using os1 os2 Suc by blast
    qed
  }
  hence trans: "\<forall> n . (omega_run' n, omega_word n, omega_run' (n + 1)) \<in> transitions_multi \<A>" by blast 
  {
    fix n
    obtain N where N: "N > n \<and> omega_run N \<in> accepting_states ?\<A>" using props by blast
    hence "omega_run N \<noteq> Inr()" using assms no_inr_in_omega_run by fastforce
    hence unique: "\<exists>! s . Inl s = omega_run N" using unique_existence by fast
    then obtain sN where sN: "Inl sN = omega_run N \<and> omega_run N \<in> accepting_states ?\<A>" using N by blast
    have "omega_run' N = (THE s . Inl s = omega_run N)" using N unfolding omega_run'_def omega_run_detransformation_def by auto
    hence "omega_run' N = sN \<and> Inl sN \<in> accepting_states ?\<A>" using unique the1_equality sN by fastforce
    hence "omega_run' N \<in> accepting_states_multi \<A>" using accepting_states_normalize_nfa by fast
    hence "\<exists> N > n . omega_run' N \<in> accepting_states_multi \<A>" using N by blast
  }
  thus ?thesis using init trans unfolding omega_pseudo_run_well_defined_multi_def omega_run_well_defined_multi_def omega_run_accepting_multi_def by blast  
qed

lemma nfa_multi_omega_language_right:
  assumes "auto_well_defined_multi \<A>"
  shows "omega_language_auto (normalize_nfa \<A>) \<subseteq> omega_language_auto_multi \<A>"
  using assms omega_run_transformation_right unfolding omega_language_auto_def omega_language_auto_multi_def by blast

text \<open>Main result for the normalize_nfa automaton: omega_language equivalence\<close>
theorem normalize_nfa_omega_language_correctness:
  assumes "auto_well_defined_multi \<A>"
  shows "omega_language_auto_multi \<A> = omega_language_auto (normalize_nfa \<A>)"
  using assms nfa_multi_omega_language_left nfa_multi_omega_language_right by auto

corollary omega_nfa_multi_main:
  assumes "auto_well_defined_multi (NFA_multi_\<A> :: ('s, 'a) nfa_multi)"
  shows "\<exists> NFA_\<A> :: ('s + unit, 'a) automaton . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = alphabet_multi NFA_multi_\<A> \<and> omega_language_auto NFA_\<A> = omega_language_auto_multi NFA_multi_\<A>"
  using assms normalize_nfa_omega_language_correctness normalize_preserves_well_defined normalize_alphabet_multi by fast

corollary existence_of_omega_nfa_same_type:
  assumes "auto_well_defined_multi (NFA_multi_\<A> :: ('s, 'a) nfa_multi)" "infinite (UNIV :: 's set)"
  shows "\<exists> NFA_\<A> :: ('s, 'a) automaton . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = alphabet_multi NFA_multi_\<A> \<and> omega_language_auto NFA_\<A> = omega_language_auto_multi NFA_multi_\<A>"
  using assms existence_soft_iso_auto_omega_lang omega_nfa_multi_main by metis

theorem expressive_power_multi_omega_nfa_main:
  assumes "infinite (UNIV :: 's set)"
  shows "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = omega_language_auto NFA_\<A>} = {L . \<exists> (NFA_\<A>_multi :: ('s, 'a) nfa_multi) . auto_well_defined_multi NFA_\<A>_multi \<and> alphabet_multi NFA_\<A>_multi = \<Sigma> \<and> L = omega_language_auto_multi NFA_\<A>_multi}"
  using assms existence_of_omega_nfa_same_type existence_of_omega_NFA_to_multi_same_type by fastforce

text \<open>Union and general type conversion\<close>
theorem omega_union_main:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> union_\<A> :: ('s \<times> nat + unit, 'a) automaton . auto_well_defined union_\<A> \<and> alphabet union_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> omega_language_auto union_\<A> = omega_language_auto \<A>1 \<union> omega_language_auto \<A>2"
  using assms omega_union_main_multi omega_nfa_multi_main by metis

theorem existence_of_omega_union_same_type:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> union_\<A> :: ('s, 'a) automaton . auto_well_defined union_\<A> \<and> alphabet union_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> omega_language_auto union_\<A> = omega_language_auto \<A>1 \<union> omega_language_auto \<A>2"
proof -
  have "\<exists> union_\<A> :: ('s \<times> nat + unit, 'a) automaton . auto_well_defined union_\<A> \<and> alphabet union_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> omega_language_auto union_\<A> = omega_language_auto \<A>1 \<union> omega_language_auto \<A>2" using assms omega_union_main by blast 
  thus ?thesis using assms existence_soft_iso_auto_omega_lang by metis
qed

text \<open>Intersection of Büchi automata\<close>
proposition intersection_omega_language_well_defined:
  assumes "omega_language_well_defined L1 \<Sigma>1" "omega_language_well_defined L2 \<Sigma>2"
  shows "omega_language_well_defined (L1 \<inter> L2) (\<Sigma>1 \<union> \<Sigma>2)"
  using assms unfolding omega_language_well_defined_def omega_word_well_defined_def by fast

corollary automata_intersection_omega_lang_well_defined:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "omega_language_well_defined (omega_language_auto \<A>1 \<inter> omega_language_auto \<A>2) (alphabet \<A>1 \<union> alphabet \<A>2)"
  using assms intersection_omega_language_well_defined automata_omega_language_are_well_defined by metis


text \<open>Product omega transition function for the intersection omega automaton\<close>
definition product_omega_transitions :: "('s, 'a) automaton \<Rightarrow> ('t, 'a) automaton \<Rightarrow> (('s \<times> 't \<times> nat), 'a) transitions" where
  "product_omega_transitions \<A>1 \<A>2 = {((s1, t1, n), a, (s2, t2, m)) . (s1, a, s2) \<in> transitions \<A>1 \<and> (t1, a, t2) \<in> transitions \<A>2 \<and> n = 0 \<and> m = 0 \<and> s2 \<notin> accepting_states \<A>1} \<union>
    {((s1, t1, n), a, (s2, t2, m)) . (s1, a, s2) \<in> transitions \<A>1 \<and> (t1, a, t2) \<in> transitions \<A>2 \<and> n = 0 \<and> m = 1 \<and> s2 \<in> accepting_states \<A>1} \<union>
    {((s1, t1, n), a, (s2, t2, m)) . (s1, a, s2) \<in> transitions \<A>1 \<and> (t1, a, t2) \<in> transitions \<A>2 \<and> n = 1 \<and> m = 1 \<and> t2 \<notin> accepting_states \<A>2} \<union>
    {((s1, t1, n), a, (s2, t2, m)) . (s1, a, s2) \<in> transitions \<A>1 \<and> (t1, a, t2) \<in> transitions \<A>2 \<and> n = 1 \<and> m = 2 \<and> t2 \<in> accepting_states \<A>2} \<union>
    {((s1, t1, n), a, (s2, t2, m)) . (s1, a, s2) \<in> transitions \<A>1 \<and> (t1, a, t2) \<in> transitions \<A>2 \<and> n = 2 \<and> m = 0}"

definition intersection_omega_automaton :: "('s, 'a) automaton \<Rightarrow> ('t , 'a) automaton \<Rightarrow> (('s \<times> 't \<times> nat), 'a) automaton" where
  "intersection_omega_automaton \<A>1 \<A>2 = Automaton
    {(s1, s2, n) . s1 \<in> states \<A>1 \<and> s2 \<in> states \<A>2 \<and> n \<in> {0, 1, 2}}
    (alphabet \<A>1 \<union> alphabet \<A>2)
    (product_omega_transitions \<A>1 \<A>2)
    (initial_state \<A>1, initial_state \<A>2, 0)
    {(s1, s2, n) . s1 \<in> states \<A>1 \<and> s2 \<in> states \<A>2 \<and> n = 2}"

theorem well_def_intersection_omega_automaton:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "auto_well_defined (intersection_omega_automaton \<A>1 \<A>2)"
proof - 
  let ?\<A> = "intersection_omega_automaton \<A>1 \<A>2"
  have fin_s: "finite (states ?\<A>)" using assms unfolding intersection_omega_automaton_def auto_well_defined_def by auto
  have fin_a: "finite (alphabet ?\<A>)" using assms unfolding intersection_omega_automaton_def auto_well_defined_def by auto
  have init: "initial_state ?\<A> \<in> states ?\<A>" using assms unfolding intersection_omega_automaton_def auto_well_defined_def by auto
  have trans: "(\<forall> (s1, a, s2) \<in> transitions ?\<A> . s1 \<in> states ?\<A> \<and> a \<in> alphabet ?\<A> \<and> s2 \<in> states ?\<A>)"   using assms unfolding intersection_omega_automaton_def product_omega_transitions_def auto_well_defined_def by auto
  have "accepting_states ?\<A> \<subseteq> states ?\<A>" using assms unfolding intersection_omega_automaton_def auto_well_defined_def by auto
  thus ?thesis using fin_s fin_a init trans unfolding auto_well_defined_def by blast
qed

corollary omegalanguage_well_def_intersection_omega_automaton:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "omega_language_well_defined (omega_language_auto (intersection_omega_automaton \<A>1 \<A>2)) (alphabet (intersection_omega_automaton \<A>1 \<A>2))"
  using well_def_intersection_omega_automaton assms automata_omega_language_are_well_defined by blast

text \<open>Single_runs are well-defined\<close>
definition proj1_omega_run :: "('s \<times> 't \<times> nat) omega_run \<Rightarrow> 's omega_run" where "proj1_omega_run omega_run = (\<lambda>n . fst (omega_run n))"

definition proj2_omega_run :: "('s \<times> 't \<times> nat) omega_run \<Rightarrow> 't omega_run" where "proj2_omega_run omega_run = (\<lambda>n . fst (snd (omega_run n)))"

theorem single_omega_prun_correct: 
  assumes "omega_pseudo_run_well_defined omega_prun (intersection_omega_automaton \<A>1 \<A>2) (s1, s2, n) omega_word" 
  shows "omega_pseudo_run_well_defined (proj1_omega_run omega_prun) \<A>1 s1 omega_word \<and> omega_pseudo_run_well_defined (proj2_omega_run omega_prun) \<A>2 s2 omega_word"
proof - 
  have "omega_prun 0 = (s1, s2, n) \<and> (s1, s2, n) \<in> states (intersection_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_pseudo_run_well_defined_def by auto
  hence init: "(proj1_omega_run omega_prun) 0 = s1 \<and> s1 \<in> states \<A>1 \<and> (proj2_omega_run omega_prun) 0 = s2 \<and> s2 \<in> states \<A>2" unfolding proj1_omega_run_def proj2_omega_run_def intersection_omega_automaton_def by auto
  {
    fix i
    have trans: "(omega_prun i, omega_word i, omega_prun (i + 1)) \<in> transitions (intersection_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_pseudo_run_well_defined_def by auto
    then obtain r1 t1 k r2 t2 m where var: "omega_prun i = (r1, t1, k) \<and> omega_prun (i + 1) = (r2, t2, m)" using prod_cases3 by metis
    hence "(r1, omega_word i, r2) \<in> transitions \<A>1 \<and> (t1, omega_word i, t2) \<in> transitions \<A>2" using trans unfolding intersection_omega_automaton_def product_omega_transitions_def by auto
    hence "((proj1_omega_run omega_prun) i, omega_word i, (proj1_omega_run omega_prun) (i + 1)) \<in> transitions \<A>1 \<and> ((proj2_omega_run omega_prun) i, omega_word i, (proj2_omega_run omega_prun) (i + 1)) \<in> transitions \<A>2" using var unfolding proj1_omega_run_def proj2_omega_run_def by simp
  }
  thus ?thesis using init unfolding omega_pseudo_run_well_defined_def by simp
qed

corollary single_omega_run_correct: 
  assumes "omega_run_well_defined omega_run (intersection_omega_automaton \<A>1 \<A>2) omega_word"
  shows "omega_run_well_defined (proj1_omega_run omega_run) \<A>1 omega_word \<and> omega_run_well_defined (proj2_omega_run omega_run) \<A>2 omega_word"
  using assms single_omega_prun_correct unfolding omega_run_well_defined_def intersection_omega_automaton_def by force

lemma successor_of_0:
  assumes "omega_run_well_defined omega_run (intersection_omega_automaton \<A>1 \<A>2) omega_word" "snd (snd (omega_run i)) = 0"
  shows "snd (snd (omega_run (i + 1))) = 0 \<or> snd (snd (omega_run (i + 1))) = 1"
proof - 
  obtain s1 s2 where "omega_run i = (s1, s2, 0)" using assms prod.collapse by metis
  hence "((s1, s2, 0), omega_word i, omega_run (i + 1)) \<in> transitions (intersection_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by metis
  thus ?thesis unfolding intersection_omega_automaton_def product_omega_transitions_def by fastforce
qed

proposition existence_of_1:
  assumes "omega_run_well_defined omega_run (intersection_omega_automaton \<A>1 \<A>2) omega_word"
  shows "snd (snd (omega_run i)) = 0 \<and> snd (snd (omega_run j)) = 2 \<and> i < j \<Longrightarrow> \<exists> k . i < k \<and> snd (snd (omega_run (k - 1))) = 0 \<and> snd (snd (omega_run k)) = 1"
proof(induction "j - i" arbitrary: i)
  case 0 thus ?case using assms by simp
next
  case (Suc x)
  hence "snd (snd (omega_run (i + 1))) = 0 \<or> snd (snd (omega_run (i + 1))) = 1" using assms successor_of_0 by blast
  then consider (case1) "snd (snd (omega_run (i + 1))) = 0" | (case2) "snd (snd (omega_run (i + 1))) = 1" by argo
  thus ?case 
  proof cases
    case case1
    hence "snd (snd (omega_run (i + 1))) = 0 \<and> snd (snd (omega_run j)) = 2 \<and> i + 1 < j" using Suc Suc_1 add.left_commute add.right_neutral linorder_neqE_nat not_less_eq not_one_less_zero plus_1_eq_Suc by metis
    hence "snd (snd (omega_run (i + 1))) = 0 \<and> snd (snd (omega_run j)) = 2 \<and> i + 1 < j \<and> j - (i + 1) = x" using Suc by auto
    thus ?thesis using Suc add_lessD1 by blast
  next
    case case2
    hence "i < i + 1 \<and> snd (snd (omega_run i)) = 0 \<and> snd (snd (omega_run (i + 1))) = 1" using Suc by auto
    thus ?thesis by auto
  qed
qed

lemma single_omega_run_accepting_inter:
  assumes "omega_run_accepting omega_run (intersection_omega_automaton \<A>1 \<A>2) omega_word"
  shows "omega_run_accepting (proj1_omega_run omega_run) \<A>1 omega_word \<and> omega_run_accepting (proj2_omega_run omega_run) \<A>2 omega_word"
proof -
  have well_def: "omega_run_well_defined omega_run (intersection_omega_automaton \<A>1 \<A>2) omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (intersection_omega_automaton \<A>1 \<A>2))" using assms unfolding omega_run_accepting_def by auto
  hence omega_runs: "omega_run_well_defined (proj1_omega_run omega_run) \<A>1 omega_word \<and> omega_run_well_defined (proj2_omega_run omega_run) \<A>2 omega_word" using single_omega_run_correct by auto
  {
    fix n
    obtain N where N: "N > n \<and> omega_run N \<in> accepting_states (intersection_omega_automaton \<A>1 \<A>2)" using well_def by blast
    then obtain M where M: "M > N \<and> omega_run M \<in> accepting_states (intersection_omega_automaton \<A>1 \<A>2)" using well_def by blast
    then obtain s1 s2 where var: "omega_run M = (s1, s2, 2)" unfolding intersection_omega_automaton_def by auto
    obtain i where i: "i = M - 1" by simp
    hence equi: "omega_run M = omega_run (i + 1) \<and> M > n" using M N by simp
    have "(omega_run i, omega_word i, omega_run (i + 1)) \<in> transitions (intersection_omega_automaton \<A>1 \<A>2)" using well_def unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
    hence "(omega_run i, omega_word i, (s1, s2, 2)) \<in> transitions (intersection_omega_automaton \<A>1 \<A>2)" using equi var by simp
    hence "s2 \<in> accepting_states \<A>2" unfolding intersection_omega_automaton_def product_omega_transitions_def by fastforce
    hence "(proj2_omega_run omega_run) M \<in> accepting_states \<A>2 \<and> M > n" using var equi unfolding proj2_omega_run_def by simp
    hence "\<exists> M > n . (proj2_omega_run omega_run) M \<in> accepting_states \<A>2" by auto
  }
  hence inf2: "\<forall> n . \<exists> N > n . (proj2_omega_run omega_run) N \<in> accepting_states \<A>2" by simp
  {
    fix n
    obtain N where N: "N > n \<and> omega_run N \<in> accepting_states (intersection_omega_automaton \<A>1 \<A>2)" using well_def by blast
    then obtain s1 s2 where var: "omega_run N = (s1, s2, 2)" unfolding intersection_omega_automaton_def by auto
    have "(omega_run N, omega_word N, omega_run (N + 1)) \<in> transitions (intersection_omega_automaton \<A>1 \<A>2)" using well_def unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
    hence snd0: "snd (snd (omega_run (N + 1))) = 0" using var unfolding intersection_omega_automaton_def product_omega_transitions_def by auto
    obtain M where M: "M > N + 1 \<and> omega_run M \<in> accepting_states (intersection_omega_automaton \<A>1 \<A>2)" using well_def by blast
    hence "snd (snd (omega_run M)) = 2 \<and> M > N + 1" unfolding intersection_omega_automaton_def by auto
    hence "\<exists> k . (N + 1) < k \<and> snd (snd (omega_run (k - 1))) = 0 \<and> snd (snd (omega_run k)) = 1" using well_def snd0 existence_of_1 by blast
    then obtain k where k: "(N + 1) < k \<and> snd (snd (omega_run (k - 1))) = 0 \<and> snd (snd (omega_run k)) = 1" by auto
    then obtain r1 r2 t1 t2 where var2: "omega_run (k - 1) = (r1, r2, 0) \<and> omega_run k = (t1, t2, 1)" using eq_snd_iff by metis
    obtain i where i: "i = k - 1" by simp
    hence equi: "omega_run (k - 1) = omega_run i \<and> omega_run k = omega_run (i + 1)" using k by simp
    have "(omega_run i, omega_word i, omega_run (i + 1)) \<in> transitions (intersection_omega_automaton \<A>1 \<A>2)" using well_def unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
    hence "((r1, r2, 0), omega_word i, (t1, t2, 1)) \<in> transitions (intersection_omega_automaton \<A>1 \<A>2)" using equi var2 by simp
    hence "t1 \<in> accepting_states \<A>1" unfolding intersection_omega_automaton_def product_omega_transitions_def by simp
    hence "(proj1_omega_run omega_run) k \<in> accepting_states \<A>1 \<and> k > n" using var2 k N unfolding proj1_omega_run_def by simp
    hence "\<exists> k > n . (proj1_omega_run omega_run) k \<in> accepting_states \<A>1" by auto
  }
  thus ?thesis using omega_runs inf2 unfolding omega_run_accepting_def by auto
qed

theorem omega_inter_implication_product_to_single:
  assumes "omega_word \<in> omega_language_auto (intersection_omega_automaton \<A>1 \<A>2)"
  shows "omega_word \<in> omega_language_auto \<A>1 \<and> omega_word \<in> omega_language_auto \<A>2"
  using assms single_omega_run_accepting_inter unfolding omega_language_auto_def by blast


text \<open>Product_pruns are well-defined\<close>
fun product_omega_nat :: "'s omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 't omega_run \<Rightarrow> ('t, 'a) automaton \<Rightarrow> nat \<Rightarrow> nat" where
  "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 0 = 0" |
  "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (Suc n) = (if (product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 n = 0) then (if omega_run1 (Suc n) \<in> accepting_states \<A>1 then 1 else 0) else (if (product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 n = 1) then (if omega_run2 (Suc n) \<in> accepting_states \<A>2 then 2 else 1) else 0))"

lemma product_omega_nat_range: "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 i = 0 \<or> product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 i = 1 \<or> product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 i = 2"
  by(induction i) auto

definition product_omega_run :: "'s omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 't omega_run \<Rightarrow> ('t, 'a) automaton \<Rightarrow> ('s \<times> 't \<times> nat) omega_run" where "product_omega_run omega_run1 \<A>1 omega_run2 \<A>2 = (\<lambda>n . (omega_run1 n, omega_run2 n, product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 n))"

theorem product_omega_run_correct:
  assumes "omega_run_well_defined omega_run1 \<A>1 omega_word" "omega_run_well_defined omega_run2 \<A>2 omega_word"
  shows "omega_run_well_defined (product_omega_run omega_run1 \<A>1 omega_run2 \<A>2) (intersection_omega_automaton \<A>1 \<A>2) omega_word"
proof -
  let ?omega_run = "product_omega_run omega_run1 \<A>1 omega_run2 \<A>2"
  have states: "omega_run1 0 = initial_state \<A>1 \<and> initial_state \<A>1 \<in> states \<A>1 \<and> omega_run2 0 = initial_state \<A>2 \<and> initial_state \<A>2 \<in> states \<A>2" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by simp
  hence "?omega_run 0 = (initial_state \<A>1, initial_state \<A>2, 0)" unfolding product_omega_run_def by simp
  hence init: "?omega_run 0 = initial_state (intersection_omega_automaton \<A>1 \<A>2) \<and> initial_state (intersection_omega_automaton \<A>1 \<A>2) \<in> states (intersection_omega_automaton \<A>1 \<A>2)" using states unfolding intersection_omega_automaton_def by simp
  {
    fix i
    obtain s1 s2 t1 t2 where var: "omega_run1 i = s1 \<and> omega_run1 (i + 1) = s2 \<and> omega_run2 i = t1 \<and> omega_run2 (i + 1) = t2" by auto
    hence trans: "(s1, omega_word i, s2) \<in> transitions \<A>1 \<and> (t1, omega_word i, t2) \<in> transitions \<A>2" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
    then consider (case1) "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 i = 0" | (case2) "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 i = 1" | (case3) "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 i = 2" using product_omega_nat_range by metis
    hence "(?omega_run i, omega_word i, ?omega_run (i + 1)) \<in> transitions (intersection_omega_automaton \<A>1 \<A>2)"
    proof cases
      case case1
      consider (case4) "s2 \<in> accepting_states \<A>1" | (case5) "s2 \<notin> accepting_states \<A>1" by blast 
      thus ?thesis
      proof cases
        case case4
        hence "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 1" using case1 var by simp
        hence "(?omega_run i, omega_word i, ?omega_run (i + 1)) = ((s1, t1, 0), omega_word i, (s2, t2, 1))" using case1 var unfolding product_omega_run_def by simp
        thus ?thesis using trans case4 unfolding intersection_omega_automaton_def product_omega_transitions_def by auto
      next
        case case5
        hence "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 0" using case1 var by simp
        hence "(?omega_run i, omega_word i, ?omega_run (i + 1)) = ((s1, t1, 0), omega_word i, (s2, t2, 0))" using case1 var unfolding product_omega_run_def by simp
        thus ?thesis using trans case5 unfolding intersection_omega_automaton_def product_omega_transitions_def by auto
      qed
    next
      case case2
      consider (case4) "t2 \<in> accepting_states \<A>2" | (case5) "t2 \<notin> accepting_states \<A>2" by blast 
      thus ?thesis
      proof cases
        case case4
        hence "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 2" using case2 var by simp
        hence "(?omega_run i, omega_word i, ?omega_run (i + 1)) = ((s1, t1, 1), omega_word i, (s2, t2, 2))" using case2 var unfolding product_omega_run_def by simp
        thus ?thesis using trans case4 unfolding intersection_omega_automaton_def product_omega_transitions_def by auto
      next
        case case5
        hence "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 1" using case2 var by simp
        hence "(?omega_run i, omega_word i, ?omega_run (i + 1)) = ((s1, t1, 1), omega_word i, (s2, t2, 1))" using case2 var unfolding product_omega_run_def by simp
        thus ?thesis using trans case5 unfolding intersection_omega_automaton_def product_omega_transitions_def by auto
      qed
    next
      case case3
      hence "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 0" using var by simp
      hence "(?omega_run i, omega_word i, ?omega_run (i + 1)) = ((s1, t1, 2), omega_word i, (s2, t2, 0))" using case3 var unfolding product_omega_run_def by simp
      thus ?thesis using trans unfolding intersection_omega_automaton_def product_omega_transitions_def by auto 
    qed
  }
  thus ?thesis using init unfolding omega_pseudo_run_well_defined_def omega_run_well_defined_def by auto
qed

lemma successor_of_1:
  assumes "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 i = 1"
  shows "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 1 \<or> product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 2"
  using assms by simp

proposition existence_of_2: "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 i = 1 \<and> omega_run2 j \<in> accepting_states \<A>2 \<and> i < j \<Longrightarrow> \<exists> k . i < k \<and> product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 k = 2"
proof(induction "j - i" arbitrary: i)
  case 0 thus ?case by simp
next
  case (Suc x)
  hence "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 1 \<or> product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 2" using successor_of_1 by blast
  then consider (case1) "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 1" | (case2) "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 2" by argo
  thus ?case 
  proof cases
    case case1
    hence "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 1 \<and> omega_run2 j \<in> accepting_states \<A>2 \<and> i + 1 < j" using Suc product_omega_nat.simps(2) One_nat_def add.commute add_left_imp_eq linorder_neqE_nat nat_1_add_1 not_less_eq plus_1_eq_Suc zero_neq_one by metis
    hence "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (i + 1) = 1 \<and> omega_run2 j \<in> accepting_states \<A>2 \<and> i + 1 < j \<and> j - (i + 1) = x" using Suc by auto
    thus ?thesis using Suc add_lessD1 by blast
  next
    case case2 thus ?thesis by force
  qed
qed

lemma product_omega_run_accepting_inter: 
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "omega_run_accepting omega_run1 \<A>1 omega_word" "omega_run_accepting omega_run2 \<A>2 omega_word"
  shows "omega_run_accepting (product_omega_run omega_run1 \<A>1 omega_run2 \<A>2) (intersection_omega_automaton \<A>1 \<A>2) omega_word"
proof -
  have well_def: "omega_run_well_defined omega_run1 \<A>1 omega_word \<and> (\<forall> n . \<exists> N > n . omega_run1 N \<in> accepting_states \<A>1) \<and> omega_run_well_defined omega_run2 \<A>2 omega_word \<and> (\<forall> n . \<exists> N > n . omega_run2 N \<in> accepting_states \<A>2)" using assms unfolding omega_run_accepting_def by blast
  hence omega_run: "omega_run_well_defined (product_omega_run omega_run1 \<A>1 omega_run2 \<A>2) (intersection_omega_automaton \<A>1 \<A>2) omega_word" using product_omega_run_correct by blast
  {
    fix n
    obtain M where M: "M > n \<and> omega_run1 M \<in> accepting_states \<A>1" using well_def by blast
    then obtain N where N: "N > M \<and> omega_run1 N \<in> accepting_states \<A>1" using well_def by blast
    consider (case1) "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (N - 1) = 0" | (case2) "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (N - 1) = 1" | (case3) "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 (N - 1) = 2" using product_omega_nat_range by metis
    hence "\<exists> i > n . product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 i = 2"
    proof cases
      case case1
      have "Suc (N - 1) = N" using N by simp
      hence pon: "product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 N = 1" using case1 N product_omega_nat.simps(2) by metis
      obtain k where "k > N \<and> omega_run2 k \<in> accepting_states \<A>2" using well_def by blast
      then obtain K where K: "N < K \<and> product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 K = 2" using pon existence_of_2 by blast
      hence "K > n" using N M by auto
      thus ?thesis using K by blast
    next
      case case2
      obtain k where "k > (N - 1) \<and> omega_run2 k \<in> accepting_states \<A>2" using well_def by blast
      then obtain K where K: "(N - 1) < K \<and> product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 K = 2" using case2 existence_of_2 by blast
      hence "K > n" using N M by auto
      thus ?thesis using K by blast
    next
      case case3
      have "N - 1 \<ge> M" using N by force
      hence "N - 1 > n" using M by auto
      thus ?thesis using case3 by blast
    qed
    then obtain i where i: "i > n \<and> product_omega_nat omega_run1 \<A>1 omega_run2 \<A>2 i = 2" by blast
    hence equi: "(product_omega_run omega_run1 \<A>1 omega_run2 \<A>2) i = (omega_run1 i, omega_run2 i, 2)" unfolding product_omega_run_def by auto
    have "omega_prun_states omega_run1 \<A>1 \<and> omega_prun_states omega_run2 \<A>2" using well_def assms well_def_implies_omega_prun_states unfolding omega_run_well_defined_def by metis
    hence "omega_run1 i \<in> states \<A>1 \<and> omega_run2 i \<in> states \<A>2" unfolding omega_prun_states_def by simp
    hence "(product_omega_run omega_run1 \<A>1 omega_run2 \<A>2) i \<in> accepting_states (intersection_omega_automaton \<A>1 \<A>2)" using equi unfolding intersection_omega_automaton_def by auto
    hence "\<exists> i > n . (product_omega_run omega_run1 \<A>1 omega_run2 \<A>2) i \<in> accepting_states (intersection_omega_automaton \<A>1 \<A>2)" using i by fast
  }
  thus ?thesis using omega_run unfolding omega_run_accepting_def by auto
qed

theorem omega_inter_implication_single_to_product:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "omega_word \<in> omega_language_auto \<A>1" "omega_word \<in> omega_language_auto \<A>2"
  shows "omega_word \<in> omega_language_auto (intersection_omega_automaton \<A>1 \<A>2)"
  using assms product_omega_run_accepting_inter unfolding omega_language_auto_def by fast

theorem closed_under_omega_intersection: 
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "omega_word \<in> omega_language_auto (intersection_omega_automaton \<A>1 \<A>2) \<longleftrightarrow> omega_word \<in> omega_language_auto \<A>1 \<and> omega_word \<in> omega_language_auto \<A>2"
  using assms omega_inter_implication_single_to_product omega_inter_implication_product_to_single by metis

text \<open>Main result for intersection\<close>
theorem omega_language_intersection_correctness:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "omega_language_auto (intersection_omega_automaton \<A>1 \<A>2) = omega_language_auto \<A>1 \<inter> omega_language_auto \<A>2"
  using assms closed_under_omega_intersection by blast

proposition alphabet_omega_intersection: "alphabet (intersection_omega_automaton \<A>1 \<A>2) = alphabet \<A>1 \<union> alphabet \<A>2"
  unfolding intersection_omega_automaton_def by simp

text \<open>Intersection\<close>
theorem omega_intersection_main:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)"
  shows "\<exists> inter_\<A> :: (('s \<times> 't \<times> nat), 'a) automaton . auto_well_defined inter_\<A> \<and> alphabet inter_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> omega_language_auto inter_\<A> = omega_language_auto \<A>1 \<inter> omega_language_auto \<A>2"
  using omega_language_intersection_correctness well_def_intersection_omega_automaton alphabet_omega_intersection assms by metis

theorem existence_of_omega_inter_same_type:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> inter_\<A> :: ('s, 'a) automaton . auto_well_defined inter_\<A> \<and> alphabet inter_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> omega_language_auto inter_\<A> = omega_language_auto \<A>1 \<inter> omega_language_auto \<A>2"
  using assms omega_intersection_main existence_soft_iso_auto_omega_lang by metis


text \<open>Complementation of deterministic Büchi automata\<close>
definition comp_omega_automaton_DBA :: "('s, 'a) automaton \<Rightarrow> (('s \<times> nat), 'a) automaton" where 
  "comp_omega_automaton_DBA \<A> = Automaton
    ({(s, 1) | s . s \<in> states \<A>} \<union> {(s, 2) | s . s \<in> states \<A> \<and> s \<notin> accepting_states \<A>})
    (alphabet \<A>)
    ({((s1, 1), a, (s2, 1)) | s1 s2 a . (s1, a, s2) \<in> transitions \<A>} \<union> {((s1, 1), a, (s2, 2)) | s1 s2 a . (s1, a, s2) \<in> transitions \<A> \<and> s2 \<notin> accepting_states \<A>} \<union> {((s1, 2), a, (s2, 2)) | s1 s2 a . (s1, a, s2) \<in> transitions \<A> \<and> s1 \<notin> accepting_states \<A> \<and> s2 \<notin> accepting_states \<A>})
    (initial_state \<A>, 1)
    {(s, 2) | s . s \<in> states \<A> \<and> s \<notin> accepting_states \<A>}"

theorem well_def_comp_omega_automaton_DBA:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (comp_omega_automaton_DBA \<A>)"
  using assms unfolding comp_omega_automaton_DBA_def auto_well_defined_def by auto

corollary language_well_def_comp_omega_auto:
  assumes "auto_well_defined \<A>"
  shows "omega_language_well_defined (omega_language_auto (comp_omega_automaton_DBA \<A>)) (alphabet (comp_omega_automaton_DBA \<A>))"
  using well_def_comp_omega_automaton_DBA assms automata_omega_language_are_well_defined by blast

lemma only_accepting_states:
  assumes "auto_well_defined \<A>" "omega_run_well_defined omega_run (comp_omega_automaton_DBA \<A>) omega_word" "omega_run n \<in> accepting_states (comp_omega_automaton_DBA \<A>)" 
  shows "\<forall> N \<ge> n . omega_run N \<in> accepting_states (comp_omega_automaton_DBA \<A>)"
proof -
  have well_def: "auto_well_defined (comp_omega_automaton_DBA \<A>)" using assms well_def_comp_omega_automaton_DBA by auto
  have trans: "\<forall> i . (omega_run i, omega_word i, omega_run (i + 1)) \<in> transitions (comp_omega_automaton_DBA \<A>)" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
  hence states: "\<forall> i . omega_run i \<in> states (comp_omega_automaton_DBA \<A>)" using well_def_trans_components well_def by fast
  {
    fix N assume "N \<ge> n"
    hence "omega_run N \<in> accepting_states (comp_omega_automaton_DBA \<A>)"
    proof(induction "N - n" arbitrary: N)
      case 0 thus ?case using assms by simp
    next
      case (Suc x)
      hence "omega_run (N - 1) \<in> accepting_states (comp_omega_automaton_DBA \<A>)" by auto
      then obtain s where s: "omega_run (N - 1) = (s, 2)" unfolding comp_omega_automaton_DBA_def by force
      have "(N - 1) + 1 = N" using Suc by linarith
      hence "(omega_run (N - 1), omega_word (N - 1), omega_run N) \<in> transitions (comp_omega_automaton_DBA \<A>)" using trans by metis
      then obtain s' where "omega_run N = (s', 2)" using s unfolding comp_omega_automaton_DBA_def by auto
      hence "omega_run N \<in> states (comp_omega_automaton_DBA \<A>) \<and> omega_run N = (s', 2)" using states by fast
      thus ?case unfolding comp_omega_automaton_DBA_def by force
    qed
  }
  thus ?thesis by auto
qed

definition proj1_omega_run_comp :: "('s \<times> nat) omega_run \<Rightarrow> 's omega_run" where "proj1_omega_run_comp omega_run = (\<lambda>n . fst (omega_run n))" 

lemma existence_of_original_run:
  assumes "auto_well_defined \<A>" "omega_run_well_defined omega_run (comp_omega_automaton_DBA \<A>) omega_word"
  shows "omega_run_well_defined (proj1_omega_run_comp omega_run) \<A> omega_word"
proof -
  have props: "omega_run 0 = (initial_state (comp_omega_automaton_DBA \<A>)) \<and> (initial_state (comp_omega_automaton_DBA \<A>)) \<in> states (comp_omega_automaton_DBA \<A>) \<and> (\<forall> n . (omega_run n, omega_word n, omega_run (n + 1)) \<in> transitions (comp_omega_automaton_DBA \<A>))" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by fast
  hence init: "(proj1_omega_run_comp omega_run) 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using assms unfolding proj1_omega_run_comp_def comp_omega_automaton_DBA_def auto_well_defined_def by simp
  {
    fix n
    have "(omega_run n, omega_word n, omega_run (n + 1)) \<in> transitions (comp_omega_automaton_DBA \<A>)" using props by blast
    hence "((proj1_omega_run_comp omega_run) n, omega_word n, (proj1_omega_run_comp omega_run) (n + 1)) \<in> transitions \<A>" unfolding proj1_omega_run_comp_def comp_omega_automaton_DBA_def by force
  }
  thus ?thesis using init unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
qed

lemma comp_omega_language_words_left:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "omega_word \<in> omega_language_auto \<A>"
  shows "omega_word \<notin> omega_language_auto (comp_omega_automaton_DBA \<A>)"
proof(rule ccontr)
  assume "\<not> omega_word \<notin> omega_language_auto (comp_omega_automaton_DBA \<A>)"
  hence "omega_word \<in> omega_language_auto (comp_omega_automaton_DBA \<A>)" by blast
  then obtain omega_run where "omega_run_accepting omega_run (comp_omega_automaton_DBA \<A>) omega_word" unfolding omega_language_auto_def by blast
  hence props: "omega_run_well_defined omega_run (comp_omega_automaton_DBA \<A>) omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (comp_omega_automaton_DBA \<A>))" unfolding omega_run_accepting_def by blast
  hence proj: "omega_run_well_defined (proj1_omega_run_comp omega_run) \<A> omega_word" using assms existence_of_original_run by blast
  have existence: "\<exists> omega_run . omega_run_accepting omega_run \<A> omega_word" using assms unfolding omega_language_auto_def by blast
  have "omega_word_well_defined omega_word (alphabet \<A>)" using assms omega_word_in_omega_language_is_well_defined by blast
  hence "\<exists>! omega_run . omega_run_well_defined omega_run \<A> omega_word" using assms exists_only_one_omega_run_for_DFA by blast
  hence "omega_run_accepting (proj1_omega_run_comp omega_run) \<A> omega_word" using proj existence unfolding omega_run_accepting_def by blast
  hence acc: "\<forall> n . \<exists> N > n . (proj1_omega_run_comp omega_run) N \<in> accepting_states \<A>" unfolding omega_run_accepting_def by blast
  {
    fix i
    obtain n where n: "n > i \<and> omega_run n \<in> accepting_states (comp_omega_automaton_DBA \<A>)" using props by blast
    hence "\<forall> N \<ge> n . omega_run N \<in> accepting_states (comp_omega_automaton_DBA \<A>)" using assms props only_accepting_states by blast
    hence "\<forall> N \<ge> n . (proj1_omega_run_comp omega_run) N \<notin> accepting_states \<A>" unfolding proj1_omega_run_comp_def comp_omega_automaton_DBA_def by force
    hence "\<exists> n > i . \<forall> N \<ge> n . (proj1_omega_run_comp omega_run) N \<notin> accepting_states \<A>" using n by blast
  }
  hence "\<forall> i . \<exists> n > i . \<forall> N \<ge> n . (proj1_omega_run_comp omega_run) N \<notin> accepting_states \<A>" by blast
  thus False using acc nat_less_le by metis
qed

lemma comp_omega_language_words_right:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "omega_word_well_defined omega_word (alphabet \<A>)" "omega_word \<notin> omega_language_auto \<A>"
  shows "omega_word \<in> omega_language_auto (comp_omega_automaton_DBA \<A>)"
proof - 
  obtain omega_run where omega_run: "omega_run_well_defined omega_run \<A> omega_word" using assms exists_only_one_omega_run_for_DFA by blast
  hence "\<not> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>)" using assms unfolding omega_language_auto_def omega_run_accepting_def by blast
  hence "\<exists> n . \<forall> N > n . omega_run N \<notin> accepting_states \<A>" by blast
  then obtain n where n: "\<forall> N > n . omega_run N \<notin> accepting_states \<A>" by blast
  define omega_run_comp where "omega_run_comp = (\<lambda>k. (omega_run k, if k \<le> n then (1 :: nat) else (2 :: nat)))"
  have trans: "\<forall> n . (omega_run n, omega_word n, omega_run (n + 1)) \<in> transitions \<A>" using omega_run unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by simp
  hence "\<forall> n . omega_run n \<in> states \<A>" using assms well_def_trans_components by fast
  hence all_acc: "\<forall> k > n . omega_run_comp k \<in> states (comp_omega_automaton_DBA \<A>) \<and> omega_run_comp k \<in> accepting_states (comp_omega_automaton_DBA \<A>)" using n unfolding omega_run_comp_def comp_omega_automaton_DBA_def by auto
  {
    fix k
    have suc_k_n: "omega_run_comp (Suc (k + n)) \<in> accepting_states (comp_omega_automaton_DBA \<A>)" using all_acc by force
    have "Suc (k + n) > k" by simp
    hence "\<exists> N > k . omega_run_comp N \<in> accepting_states (comp_omega_automaton_DBA \<A>)" using suc_k_n by blast
  }
  hence acc: "\<forall> k . \<exists> N > k . omega_run_comp N \<in> accepting_states (comp_omega_automaton_DBA \<A>)" by simp
  have "omega_run 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using omega_run unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by simp
  hence "omega_run_comp 0 = (initial_state \<A>, 1)" unfolding omega_run_comp_def by auto
  hence start: "omega_run_comp 0 = initial_state (comp_omega_automaton_DBA \<A>)" unfolding comp_omega_automaton_DBA_def by auto
  have "auto_well_defined (comp_omega_automaton_DBA \<A>)" using assms well_def_comp_omega_automaton_DBA by auto
  hence init: "omega_run_comp 0 = initial_state (comp_omega_automaton_DBA \<A>) \<and> initial_state (comp_omega_automaton_DBA \<A>) \<in> states (comp_omega_automaton_DBA \<A>)" using start unfolding auto_well_defined_def by blast
  {
    fix i
    have trans_i: "(omega_run i, omega_word i, omega_run (i + 1)) \<in> transitions \<A>" using trans by simp
    consider (case1) "i < n" | (case2) "i = n" | (case3) "i > n" by linarith
    hence "(omega_run_comp i, omega_word i, omega_run_comp (i + 1)) \<in> transitions (comp_omega_automaton_DBA \<A>)"
    proof cases
      case case1
      hence "(omega_run_comp i, omega_word i, omega_run_comp (i + 1)) = ((omega_run i, 1), omega_word i, (omega_run (i + 1), 1))" unfolding omega_run_comp_def by auto
      thus ?thesis using trans_i unfolding comp_omega_automaton_DBA_def by auto
    next
      case case2
      hence equi: "(omega_run_comp i, omega_word i, omega_run_comp (i + 1)) = ((omega_run i, 1), omega_word i, (omega_run (i + 1), 2))" unfolding omega_run_comp_def by auto
      have "omega_run_comp (i + 1) \<in> accepting_states (comp_omega_automaton_DBA \<A>)" using all_acc case2 by auto
      thus ?thesis using equi trans_i unfolding comp_omega_automaton_DBA_def by auto
    next
      case case3
      hence equi: "(omega_run_comp i, omega_word i, omega_run_comp (i + 1)) = ((omega_run i, 2), omega_word i, (omega_run (i + 1), 2))" unfolding omega_run_comp_def by auto
      have "omega_run_comp i \<in> accepting_states (comp_omega_automaton_DBA \<A>) \<and> omega_run_comp (i + 1) \<in> accepting_states (comp_omega_automaton_DBA \<A>)" using all_acc case3 by auto
      thus ?thesis using equi trans_i unfolding comp_omega_automaton_DBA_def by force
    qed
  }
  hence "omega_run_well_defined omega_run_comp (comp_omega_automaton_DBA \<A>) omega_word" using init unfolding omega_pseudo_run_well_defined_def omega_run_well_defined_def by simp
  thus ?thesis using acc unfolding omega_run_accepting_def omega_language_auto_def by blast
qed

lemma word_omega_comp_automaton_DBA: 
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "omega_word_well_defined omega_word (alphabet \<A>)"
  shows "omega_word \<in> omega_language_auto \<A> \<longleftrightarrow> omega_word \<notin> omega_language_auto (comp_omega_automaton_DBA \<A>)"
  using assms comp_omega_language_words_left comp_omega_language_words_right by blast

lemma comp_omega_automaton_DBA_alphabet: "alphabet \<A> = alphabet (comp_omega_automaton_DBA \<A>)"
  unfolding comp_omega_automaton_DBA_def by auto

lemma word_on_comp_omega_automaton_DBA_is_well_defined:
  assumes "auto_well_defined \<A>" "omega_word \<in> omega_language_auto (comp_omega_automaton_DBA \<A>)"
  shows "omega_word_well_defined omega_word (alphabet \<A>)"
  using assms well_def_comp_omega_automaton_DBA omega_word_in_omega_language_is_well_defined comp_omega_automaton_DBA_alphabet by metis

text \<open>Main result for complementation\<close>
theorem comp_omega_automaton_DBA_language_correctness:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "omega_language_auto (comp_omega_automaton_DBA \<A>) = comp_omega_language (alphabet \<A>) (omega_language_auto \<A>)"
  using assms comp_omega_language_well_defined word_on_comp_omega_automaton_DBA_is_well_defined word_omega_comp_automaton_DBA word_comp_omega_language unfolding omega_language_well_defined_def by blast

corollary comp_comp_omega_language_auto:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "omega_language_auto \<A> = comp_omega_language (alphabet (comp_omega_automaton_DBA \<A>)) (omega_language_auto (comp_omega_automaton_DBA \<A>))"
  using assms comp_omega_automaton_DBA_language_correctness comp_comp_omega_language comp_omega_automaton_DBA_alphabet automata_omega_language_are_well_defined by metis

theorem comp_main_DBA:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)" "DFA_property \<A>"
  shows "\<exists> comp_\<A> :: (('s \<times> nat), 'a) automaton . auto_well_defined comp_\<A> \<and> alphabet comp_\<A> = alphabet \<A> \<and> omega_language_auto comp_\<A> = comp_omega_language (alphabet \<A>) (omega_language_auto \<A>)"
  using comp_omega_automaton_DBA_language_correctness well_def_comp_omega_automaton_DBA comp_omega_automaton_DBA_alphabet assms by metis

theorem existence_of_omega_comp_same_type_DBA:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)" "DFA_property \<A>" "infinite (UNIV :: 's set)"
  shows "\<exists> comp_\<A> :: ('s, 'a) automaton . auto_well_defined comp_\<A> \<and> alphabet comp_\<A> = alphabet \<A> \<and> omega_language_auto comp_\<A> = comp_omega_language (alphabet \<A>) (omega_language_auto \<A>)"
  using assms comp_main_DBA existence_soft_iso_auto_omega_lang by metis

end