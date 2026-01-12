theory automaton_reversal

imports Main automaton_nfa_multis

begin

text \<open>Author: Benno Thalmann, last update: 10.11.2025, Addition to masterarbeit_benno_thalmann\<close>

text \<open>Reversal language\<close>
definition rev_language :: "'a language \<Rightarrow> 'a language" where "rev_language L = image rev L"

proposition rev_rev_language: "rev_language (rev_language L) = L"
  unfolding rev_language_def by force

proposition rev_language_well_defined:
  assumes "language_well_defined L \<Sigma>"
  shows "language_well_defined (rev_language L) \<Sigma>"
proof -
  {
    fix word assume "word \<in> rev_language L"
    hence "rev word \<in> L" using rev_rev_language unfolding rev_language_def by blast
    hence "set (rev word) \<subseteq> \<Sigma>" using assms unfolding language_well_defined_def word_well_defined_def by blast
    hence "set word \<subseteq> \<Sigma>" by simp
    hence "word_well_defined word \<Sigma>" unfolding word_well_defined_def by blast
  }
  thus ?thesis unfolding language_well_defined_def by blast
qed

proposition rev_language_symmetry:  "L1 = rev_language L2 \<longleftrightarrow> rev_language L1 = L2"
  unfolding rev_language_def by force

text \<open>Transformation of NFA to its reversing automaton\<close>
definition reversal_nfa :: "('s, 'a) automaton \<Rightarrow> ('s, 'a) nfa_multi" where
  "reversal_nfa \<A> = NFA_multi
    (states \<A>)
    (alphabet \<A>)
    {(s2, a, s1) . (s1, a, s2) \<in> transitions \<A>}
    (accepting_states \<A>)
    {initial_state \<A>}"

proposition reversal_alphabet: "alphabet \<A> = alphabet_multi (reversal_nfa \<A>)"
  unfolding reversal_nfa_def by force

proposition reversal_preserves_well_defined:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined_multi (reversal_nfa \<A>)"
  using assms unfolding auto_well_defined_def auto_well_defined_multi_def reversal_nfa_def by auto

corollary language_well_def_rev_multi_auto:
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (language_auto_multi (reversal_nfa \<A>)) (alphabet_multi (reversal_nfa \<A>))"
  using reversal_preserves_well_defined assms automata_language_are_well_defined_multi by blast

lemma prun_on_rev_automaton_right_multi:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined_multi (rev prun) (reversal_nfa \<A>) ((rev prun) ! 0) (rev word)"
  shows "pseudo_run_well_defined prun \<A> (prun ! 0) word"
proof -
  have well_def: "auto_well_defined_multi (reversal_nfa \<A>)" using assms reversal_preserves_well_defined by blast
  have "length (rev prun) = length (rev word) + 1" using assms unfolding pseudo_run_well_defined_multi_def by blast
  hence lenp: "(rev prun) \<noteq> [] \<and> length prun = length word + 1" by force
  hence "prun \<noteq> []" by auto
  hence "prun ! 0 = last (rev prun)" using rev_simplifier by metis
  hence "prun ! 0 \<in> states_multi (reversal_nfa \<A>)" using well_def assms last_of_prun_is_state_multi by metis
  hence in_states: "prun ! 0 \<in> states \<A>" unfolding reversal_nfa_def by auto  
  have "\<forall> i < length (rev prun) - 1 . (rev prun ! i, rev word ! i, rev prun ! (i + 1)) \<in> transitions_multi (reversal_nfa \<A>)" using assms unfolding pseudo_run_well_defined_multi_def by blast
  hence i_step: "\<forall> i < length (rev prun) - 1 . (rev prun ! (i + 1), rev word ! i, rev prun ! i) \<in> transitions \<A>" unfolding reversal_nfa_def by simp
  {
    fix i assume assm: "i < length (rev prun) - 1"
    have len: "length prun = length (rev prun) \<and> length (rev prun) = length (rev word) + 1" using lenp by simp
    hence "i < length prun \<and> (i + 1) < length prun \<and> i < length word" using assm by auto
    hence "(prun ! (length (rev prun) - Suc i), word ! (length (rev word) - Suc i), prun ! (length (rev prun) - Suc (i + 1))) = (rev prun ! i, rev word ! i, rev prun ! (i + 1))" using len rev_nth length_rev by metis
    hence "(prun ! (length (rev prun) - Suc i), word ! (length (rev prun) - Suc (i + 1)), prun ! (length (rev prun) - Suc (i + 1))) = (rev prun ! i, rev word ! i, rev prun ! (i + 1))" using len by fastforce
  }
  hence "\<forall> i < length (rev prun) - 1 . (prun ! (length (rev prun) - Suc (i + 1)), word ! (length (rev prun) - Suc (i + 1)), prun ! (length (rev prun) - Suc i)) \<in> transitions \<A>" using i_step by simp
  hence i_step_rev: "\<forall> i < length prun - 1 . (prun ! (length prun - Suc (i + 1)), word ! (length prun - Suc (i + 1)), prun ! (length prun - Suc i)) \<in> transitions \<A>" by simp
  {
    fix j assume assm: "j < length prun - 1"
    then obtain i where i: "i = length prun - Suc (j + 1)" by simp
    hence equi: "j = length prun - Suc (i + 1) \<and> j + 1 = length prun - Suc i" using assm by force
    hence "i < length prun - 1" using i assm by linarith
    hence "(prun ! (length prun - Suc (i + 1)), word ! (length prun - Suc (i + 1)), prun ! (length prun - Suc i)) \<in> transitions \<A>" using i_step_rev by blast
    hence "(prun ! j, word ! j, prun ! (j + 1)) \<in> transitions \<A>" using equi by argo   
  }
  hence "\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>" by blast
  thus ?thesis using lenp in_states unfolding pseudo_run_well_defined_def by blast
qed

lemma prun_on_rev_automaton_left_multi:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined prun \<A> (prun ! 0) word"
  shows "pseudo_run_well_defined_multi (rev prun) (reversal_nfa \<A>) ((rev prun) ! 0) (rev word)"
proof -
  have "length prun = length word + 1" using assms unfolding pseudo_run_well_defined_def by blast
  hence lenp: "prun \<noteq> [] \<and> length (rev prun) = length (rev word) + 1" by force
  hence "(rev prun) \<noteq> []" by auto
  hence "(rev prun) ! 0 = last prun" using rev_simplifier by metis
  hence "(rev prun) ! 0 \<in> states \<A>" using assms last_of_prun_is_state by metis
  hence in_states: "(rev prun) ! 0 \<in> states_multi (reversal_nfa \<A>)" unfolding reversal_nfa_def by auto  
  have "\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>" using assms unfolding pseudo_run_well_defined_def by blast
  hence i_step: "\<forall> i < length prun - 1 . (prun ! (i + 1), word ! i, prun ! i) \<in> transitions_multi (reversal_nfa \<A>)" unfolding reversal_nfa_def by simp
  {
    fix i assume assm: "i < length prun - 1"
    have len: "length prun = length (rev prun) \<and> length prun = length word + 1" using lenp by simp
    hence "i < length (rev prun) \<and> (i + 1) < length (rev prun) \<and> i < length (rev word)" using assm by auto
    hence "(rev prun ! (length prun - Suc i), rev word ! (length word - Suc i), rev prun ! (length prun - Suc (i + 1))) = (prun ! i, word ! i, prun ! (i + 1))" using len rev_nth rev_rev_ident length_rev by metis
    hence "(rev prun ! (length prun - Suc i), rev word ! (length prun - Suc (i + 1)), rev prun ! (length prun - Suc (i + 1))) = (prun ! i, word ! i, prun ! (i + 1))" using len by fastforce
  }
  hence "\<forall> i < length prun - 1 . (rev prun ! (length prun - Suc (i + 1)), rev word ! (length prun - Suc (i + 1)), rev prun ! (length prun - Suc i)) \<in> transitions_multi (reversal_nfa \<A>)" using i_step by simp
  hence i_step_rev: "\<forall> i < length (rev prun) - 1 . (rev prun ! (length (rev prun) - Suc (i + 1)), rev word ! (length (rev prun) - Suc (i + 1)), rev prun ! (length (rev prun) - Suc i)) \<in> transitions_multi (reversal_nfa \<A>)" by simp
  {
    fix j assume assm: "j < length (rev prun) - 1"
    then obtain i where i: "i = length (rev prun) - Suc (j + 1)" by simp
    hence equi: "j = length (rev prun) - Suc (i + 1) \<and> j + 1 = length (rev prun) - Suc i" using assm by force
    hence "i < length (rev prun) - 1" using i assm by linarith
    hence "(rev prun ! (length (rev prun) - Suc (i + 1)), rev word ! (length (rev prun) - Suc (i + 1)), rev prun ! (length (rev prun) - Suc i)) \<in> transitions_multi (reversal_nfa \<A>)" using i_step_rev by blast
    hence "(rev prun ! j, rev word ! j, rev prun ! (j + 1)) \<in> transitions_multi (reversal_nfa \<A>)" using equi by argo   
  }
  hence "\<forall> i < length (rev prun) - 1 . (rev prun ! i, rev word ! i, rev prun ! (i + 1)) \<in> transitions_multi (reversal_nfa \<A>)" by blast
  thus ?thesis using lenp in_states unfolding pseudo_run_well_defined_multi_def by blast
qed

proposition prun_on_rev_automaton:
  assumes "auto_well_defined \<A>"
  shows "pseudo_run_well_defined prun \<A> (prun ! 0) word \<longleftrightarrow> pseudo_run_well_defined_multi (rev prun) (reversal_nfa \<A>) ((rev prun) ! 0) (rev word)"
  using prun_on_rev_automaton_left_multi prun_on_rev_automaton_right_multi assms by blast

corollary run_on_rev_automaton_left:
  assumes "auto_well_defined \<A>" "run_accepting run \<A> word"
  shows "run_accepting_multi (rev run) (reversal_nfa \<A>) (rev word)"
proof -
  have acc_def: "run_well_defined run \<A> word \<and> last run \<in> accepting_states \<A>" using assms unfolding run_accepting_def by auto
  hence "length run = length word + 1 \<and> run ! 0 = initial_state \<A> \<and> last run \<in> accepting_states \<A>" unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  hence first: "run \<noteq> [] \<and> run ! 0 = initial_state \<A> \<and> last run \<in> accepting_states \<A>" by force
  hence "run \<noteq> [] \<and> last (rev run) = initial_state \<A> \<and> last run \<in> accepting_states \<A>" using rev_simplifier by force
  hence "last (rev run) = initial_state \<A> \<and> rev run ! 0 \<in> accepting_states \<A>" using rev_simplifier by force
  hence props: "last (rev run) \<in> accepting_states_multi (reversal_nfa \<A>) \<and> rev run ! 0 \<in> initial_states_multi (reversal_nfa \<A>)" unfolding reversal_nfa_def by simp
  thus ?thesis using assms first acc_def prun_on_rev_automaton_left_multi unfolding run_accepting_def run_well_defined_def run_well_defined_multi_def run_accepting_multi_def by metis
qed

corollary run_on_rev_automaton_right:
  assumes "auto_well_defined \<A>" "run_accepting_multi (rev run) (reversal_nfa \<A>) (rev word)"
  shows "run_accepting run \<A> word"
proof -
  have acc_def: "run_well_defined_multi (rev run) (reversal_nfa \<A>) (rev word) \<and> last (rev run) \<in> accepting_states_multi (reversal_nfa \<A>)" using assms unfolding run_accepting_multi_def by auto
  hence "rev run ! 0 \<in> initial_states_multi (reversal_nfa \<A>) \<and> last (rev run) \<in> accepting_states_multi (reversal_nfa \<A>)" unfolding run_well_defined_multi_def by blast
  hence first: "rev run \<noteq> [] \<and> rev run ! 0 \<in> initial_states_multi (reversal_nfa \<A>) \<and> last (rev run) \<in> accepting_states_multi (reversal_nfa \<A>)" using acc_def unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by fastforce
  hence "rev run \<noteq> [] \<and> last run \<in> initial_states_multi (reversal_nfa \<A>) \<and> last (rev run) \<in> accepting_states_multi (reversal_nfa \<A>)" using rev_simplifier by force
  hence "last run \<in> initial_states_multi (reversal_nfa \<A>) \<and> run ! 0 \<in> accepting_states_multi (reversal_nfa \<A>)" using rev_simplifier by force
  hence props: "last run \<in> accepting_states \<A> \<and> run ! 0 = initial_state \<A>" unfolding reversal_nfa_def by simp
  thus ?thesis using assms first acc_def prun_on_rev_automaton_right_multi unfolding run_accepting_def run_well_defined_def run_well_defined_multi_def run_accepting_multi_def by metis
qed

proposition run_on_rev_automaton:
  assumes "auto_well_defined \<A>"
  shows "run_accepting run \<A> word \<longleftrightarrow> run_accepting_multi (rev run) (reversal_nfa \<A>) (rev word)"
  using assms run_on_rev_automaton_left run_on_rev_automaton_right by blast

text \<open>Main result for the reversal_nfa: reversed language equivalence\<close>
theorem rev_language_correctness:
  assumes "auto_well_defined \<A>"
  shows "rev_language (language_auto \<A>) = language_auto_multi (reversal_nfa \<A>)"
proof - 
  {
    fix word assume "word \<in> rev_language (language_auto \<A>)"
    hence "rev word \<in> language_auto \<A>" unfolding rev_language_def by auto
    hence "\<exists> run . run_accepting run \<A> (rev word)" unfolding language_auto_def by blast
    hence "\<exists> run . run_accepting_multi run (reversal_nfa \<A>) word" using assms run_on_rev_automaton by force
    hence "word \<in> language_auto_multi (reversal_nfa \<A>)" unfolding language_auto_multi_def by blast
  }
  hence left: "rev_language (language_auto \<A>) \<subseteq> language_auto_multi (reversal_nfa \<A>)" by auto
  {
    fix word assume "word \<in> language_auto_multi (reversal_nfa \<A>)"
    hence "\<exists> run . run_accepting_multi run (reversal_nfa \<A>) word" unfolding language_auto_multi_def by blast
    hence "\<exists> run . run_accepting run \<A> (rev word)" using assms run_on_rev_automaton rev_rev_ident by metis
    hence "rev word \<in> language_auto \<A>" unfolding language_auto_def by blast
    hence "word \<in> rev_language (language_auto \<A>)" unfolding rev_language_def by force
  }
  thus ?thesis using left by auto
qed

corollary rev_language_correctness_rev:
  assumes "auto_well_defined \<A>"
  shows "language_auto \<A> = rev_language (language_auto_multi (reversal_nfa \<A>))"
  using assms rev_language_correctness rev_rev_language unfolding rev_language_def by blast

theorem rev_main:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)"
  shows "\<exists> rev_multi_\<A> :: ('s, 'a) nfa_multi . auto_well_defined_multi rev_multi_\<A> \<and> alphabet_multi rev_multi_\<A> = alphabet \<A> \<and> language_auto_multi rev_multi_\<A> = rev_language (language_auto \<A>)"
  using rev_language_correctness reversal_preserves_well_defined reversal_alphabet assms by metis

theorem existence_of_rev_same_type:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> rev_\<A> :: ('s, 'a) automaton . auto_well_defined rev_\<A> \<and> alphabet rev_\<A> = alphabet \<A> \<and> language_auto rev_\<A> = rev_language (language_auto \<A>)"
  using assms rev_main nfa_multi_main existence_soft_iso_auto_lang by metis

theorem expressive_power_rev_main:
  assumes "infinite (UNIV :: 's set)" "L \<in> {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}"
  shows "rev_language L \<in> {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}"
  using assms existence_of_rev_same_type by blast

corollary expressive_power_rev_main_cor:
  assumes "infinite (UNIV :: 's set)" "rev_language L \<in> {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}"
  shows "L \<in> {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}"
proof -
  have "rev_language (rev_language L) \<in> {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" using assms expressive_power_rev_main by blast
  thus ?thesis using rev_rev_language by blast
qed

end