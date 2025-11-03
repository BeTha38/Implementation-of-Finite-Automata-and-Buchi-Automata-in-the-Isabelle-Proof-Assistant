theory automaton_reachability

imports Main masterarbeit_benno_thalmann

begin

text \<open>Author: Benno Thalmann, last update: 29.10.2025, Addition to masterarbeit_benno_thalmann\<close>

definition reachable_state :: "'s state \<Rightarrow> ('s, 'a) automaton \<Rightarrow> bool" where "reachable_state s \<A> = (\<exists> word run . run_well_defined run \<A> word \<and> last run = s)"

definition reachable_states :: "('s, 'a) automaton \<Rightarrow> 's states" where "reachable_states \<A> = {s . reachable_state s \<A>}"

proposition reachable_states_are_states:
  assumes "auto_well_defined \<A>"
  shows "reachable_states \<A> \<subseteq> states \<A>"
  using assms last_of_prun_is_state unfolding reachable_state_def reachable_states_def run_well_defined_def by fast

proposition initial_state_is_reachable: 
  assumes "auto_well_defined \<A>"
  shows "reachable_state (initial_state \<A>) \<A>"
proof - 
  have "run_well_defined [initial_state \<A>] \<A> []" using assms unfolding auto_well_defined_def run_well_defined_def pseudo_run_well_defined_def by auto
  thus ?thesis unfolding reachable_state_def by fastforce
qed

theorem inheritance_reachable_state:
  assumes "auto_well_defined \<A>" "reachable_state s1 \<A>" "(s1, a, s2) \<in> transitions \<A>"
  shows "reachable_state s2 \<A>"
proof - 
  obtain word run a where "run_well_defined run \<A> word \<and> last run = s1 \<and> (s1, a, s2) \<in> transitions \<A>" using assms unfolding reachable_state_def by blast
  hence "pseudo_run_well_defined run \<A> (initial_state \<A>) word \<and> last run = s1 \<and> (s1, a, s2) \<in> transitions \<A>" unfolding run_well_defined_def by auto
  hence "pseudo_run_well_defined (run @ [s2]) \<A> (initial_state \<A>) (word @ [a])" using assms prun_well_defined_induction_snoc by fast
  thus ?thesis using assms unfolding reachable_state_def run_well_defined_def by fastforce
qed



text \<open>First DFA Minimization Construction to get rid of unreachable States\<close>
definition reachable_automaton :: "('s, 'a) automaton \<Rightarrow> ('s, 'a) automaton"
  where "reachable_automaton \<A> = Automaton
    (reachable_states \<A>)
    (alphabet \<A>)
    {(s1, a, s2) \<in> transitions \<A> . reachable_state s1 \<A> \<and> reachable_state s2 \<A>}
    (initial_state \<A>)
    (accepting_states \<A> \<inter> reachable_states \<A>)"

proposition alphabet_reachable_auto: "alphabet \<A> = alphabet (reachable_automaton \<A>)"
  unfolding reachable_automaton_def by simp

proposition states_of_reachable_automaton:
  assumes "auto_well_defined \<A>"
  shows "s \<in> states (reachable_automaton \<A>) \<Longrightarrow> s \<in> states \<A>"
  using assms reachable_states_are_states unfolding reachable_automaton_def by auto

proposition max_reachable_states:
  assumes "auto_well_defined \<A>" "reachable_states \<A> = states \<A>"
  shows "reachable_automaton \<A> = \<A>"
proof - 
  have acc: "accepting_states \<A> \<inter> reachable_states \<A> = accepting_states \<A>" using assms unfolding auto_well_defined_def by auto
  have sub: "{(s1, a, s2) \<in> transitions \<A> . reachable_state s1 \<A> \<and> reachable_state s2 \<A>} \<subseteq> transitions \<A>" by auto
  {
    fix s1 s2 a assume assm: "(s1, a, s2) \<in> transitions \<A>"
    hence "s1 \<in> states \<A> \<and> s2 \<in> states \<A>" using well_def_trans_components assms by metis
    hence "s1 \<in> reachable_states \<A> \<and> s2 \<in> reachable_states \<A>" using assms by auto
    hence "(s1, a, s2) \<in> {(s1, a, s2) \<in> transitions \<A> . reachable_state s1 \<A> \<and> reachable_state s2 \<A>}" using assm unfolding reachable_states_def by blast
  }
  hence "transitions \<A> \<subseteq> {(s1, a, s2) \<in> transitions \<A> . reachable_state s1 \<A> \<and> reachable_state s2 \<A>}" by force
  hence "{(s1, a, s2) \<in> transitions \<A> . reachable_state s1 \<A> \<and> reachable_state s2 \<A>} = transitions \<A>" using sub by blast
  thus ?thesis using acc assms unfolding reachable_automaton_def by auto
qed

theorem well_def_reachable_automaton:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (reachable_automaton \<A>)"
proof - 
  let ?\<A> = "reachable_automaton \<A>"
  have states: "finite (states ?\<A>)" using assms reachable_states_are_states rev_finite_subset unfolding reachable_automaton_def auto_well_defined_def by fastforce 
  have alphabet: "finite (alphabet \<A>)" using assms unfolding reachable_automaton_def auto_well_defined_def by auto
  have init: "initial_state ?\<A> \<in> states ?\<A>" using assms initial_state_is_reachable unfolding reachable_automaton_def reachable_states_def by force
  have acc: "accepting_states ?\<A> \<subseteq> states ?\<A>" using assms unfolding reachable_automaton_def by auto
  have "\<forall> s1 s2 a . (s1, a, s2) \<in> transitions \<A> \<longrightarrow> a \<in> alphabet \<A>" using assms well_def_trans_components by fast
  hence trans: "\<forall> (s1, a, s2) \<in> transitions ?\<A> . s1 \<in> states ?\<A> \<and> s2 \<in> states ?\<A> \<and> a \<in> alphabet ?\<A>" unfolding reachable_automaton_def reachable_states_def by force
  thus ?thesis using states alphabet init acc trans unfolding auto_well_defined_def reachable_automaton_def by fastforce
qed

corollary language_well_def_reach_auto:
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (language_auto (reachable_automaton \<A>)) (alphabet (reachable_automaton \<A>))"
  using well_def_reachable_automaton assms automata_language_are_well_defined by blast

lemma prun_reachable_automaton_left:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined prun (reachable_automaton \<A>) s word"
  shows "pseudo_run_well_defined prun \<A> s word \<and> reachable_state s \<A>"
proof -
  have s: "s \<in> states (reachable_automaton \<A>)" using assms unfolding pseudo_run_well_defined_def by blast
  hence "s \<in> states \<A>" using assms reachable_states_are_states unfolding reachable_automaton_def by auto
  thus ?thesis using assms s unfolding pseudo_run_well_defined_def reachable_automaton_def reachable_states_def by auto
qed

corollary run_reachable_automaton_left:
  assumes "auto_well_defined \<A>" "run_well_defined run (reachable_automaton \<A>) word"
  shows "run_well_defined run \<A> word"
  using assms prun_reachable_automaton_left initial_state_is_reachable unfolding run_well_defined_def reachable_automaton_def by force

corollary prun_reachable_automaton_left_acc:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined prun (reachable_automaton \<A>) s word \<and> last prun \<in> accepting_states (reachable_automaton \<A>)"
  shows "pseudo_run_well_defined prun \<A> s word \<and> last prun \<in> accepting_states \<A> \<and> reachable_state s \<A>"
proof -
  have "last prun \<in> accepting_states \<A>" using assms unfolding reachable_automaton_def by simp
  thus ?thesis using assms prun_reachable_automaton_left by fast
qed

lemma prun_reachable_automaton_right:
  assumes "auto_well_defined \<A>"
  shows "pseudo_run_well_defined prun \<A> s word \<and> reachable_state s \<A> \<Longrightarrow> pseudo_run_well_defined prun (reachable_automaton \<A>) s word"
proof(induction word arbitrary: prun rule: rev_induct)
  case Nil
  hence init: "length prun = 1 \<and> prun ! 0 = s" unfolding pseudo_run_well_defined_def by auto
  hence "prun = [s]" using list_with_one_element by metis
  hence "s \<in> states (reachable_automaton \<A>)" using Nil unfolding reachable_automaton_def reachable_states_def by auto 
  hence "pseudo_run_well_defined prun (reachable_automaton \<A>) s []" using init unfolding pseudo_run_well_defined_def by auto
  thus ?case by blast
next
  have well_def: "auto_well_defined (reachable_automaton \<A>)" using assms well_def_reachable_automaton by blast
  case (snoc a word)
  hence "prun \<noteq> []" unfolding pseudo_run_well_defined_def by force
  then obtain prun' where prun: "prun = prun' @ [last prun]" using append_butlast_last_id by metis
  hence "pseudo_run_well_defined prun' \<A> s word \<and> (last prun', a, last prun) \<in> transitions \<A>" using snoc prun_well_defined_extension_snoc assms by metis 
  hence props: "pseudo_run_well_defined prun' (reachable_automaton \<A>) s word \<and> (last prun', a, last prun) \<in> transitions \<A>" using snoc by auto
  hence "reachable_state (last prun') \<A>" using well_def last_of_prun_is_state unfolding reachable_states_def reachable_automaton_def by fastforce
  hence "reachable_state (last prun') \<A> \<and> reachable_state (last prun) \<A>" using props assms inheritance_reachable_state by fast  
  hence "(last prun', a, last prun) \<in> transitions (reachable_automaton \<A>)" using props unfolding reachable_automaton_def by auto
  thus ?case using well_def prun props prun_well_defined_extension_snoc by metis
qed

corollary run_reachable_automaton_right:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word"
  shows "run_well_defined run (reachable_automaton \<A>) word"
proof - 
  have prun: "pseudo_run_well_defined run \<A> (initial_state \<A>) word" using assms unfolding run_well_defined_def by blast
  have "reachable_state (initial_state \<A>) \<A>" using assms initial_state_is_reachable by blast
  hence "pseudo_run_well_defined run (reachable_automaton \<A>) (initial_state \<A>) word" using assms prun prun_reachable_automaton_right by fast
  thus ?thesis using run_well_defined_def unfolding reachable_automaton_def by fastforce
qed

corollary prun_reachable_automaton_right_acc:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined prun \<A> s word \<and> last prun \<in> accepting_states \<A> \<and> reachable_state s \<A>"
  shows "pseudo_run_well_defined prun (reachable_automaton \<A>) s word \<and> last prun \<in> accepting_states (reachable_automaton \<A>)"
proof - 
  have "pseudo_run_well_defined prun (reachable_automaton \<A>) s word \<and> last prun \<in> accepting_states \<A>" using assms prun_reachable_automaton_right by fast
  hence "pseudo_run_well_defined prun (reachable_automaton \<A>) s word \<and> last prun \<in> accepting_states \<A> \<and> last prun \<in> states (reachable_automaton \<A>)" using assms well_def_reachable_automaton last_of_prun_is_state by fast
  thus ?thesis unfolding reachable_automaton_def reachable_states_def by auto
qed

proposition prun_reachable_automaton:
  assumes "auto_well_defined \<A>"
  shows "pseudo_run_well_defined prun \<A> s word \<and> reachable_state s \<A> \<longleftrightarrow> pseudo_run_well_defined prun (reachable_automaton \<A>) s word"
  using assms prun_reachable_automaton_left prun_reachable_automaton_right by fast

proposition run_reachable_automaton:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined run \<A> word \<longleftrightarrow> run_well_defined run (reachable_automaton \<A>) word"
  using assms run_reachable_automaton_left run_reachable_automaton_right by blast

proposition acc_prun_reachable_automaton:
  assumes "auto_well_defined \<A>"
  shows "pseudo_run_well_defined prun (reachable_automaton \<A>) s word \<and> last prun \<in> accepting_states (reachable_automaton \<A>) \<longleftrightarrow> pseudo_run_well_defined prun \<A> s word \<and> last prun \<in> accepting_states \<A> \<and> reachable_state s \<A>"
  using assms prun_reachable_automaton_right_acc prun_reachable_automaton_left_acc by metis

theorem DFA_property_reachable_automaton:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "DFA_property (reachable_automaton \<A>)"
proof -
  let ?\<A> = "reachable_automaton \<A>"
  {
    fix s1 a assume assm: "s1 \<in> states ?\<A> \<and> a \<in> alphabet ?\<A>"
    hence reach: "s1 \<in> states \<A> \<and> s1 \<in> reachable_states \<A> \<and> a \<in> alphabet \<A>" using reachable_states_are_states assms unfolding reachable_automaton_def by auto 
    hence "\<exists>! s2 \<in> states \<A> . (s1, a, s2) \<in> transitions \<A>" using assms unfolding DFA_property_def by auto
    hence "\<exists>! s2 \<in> states \<A> . (s1, a, s2) \<in> transitions \<A> \<and> s2 \<in> reachable_states \<A>" using assms reach inheritance_reachable_state unfolding reachable_states_def by fast
    hence "\<exists>! s2 \<in> states \<A> . (s1, a, s2) \<in> transitions \<A> \<and> s2 \<in> states ?\<A>" unfolding reachable_automaton_def by auto
    hence "\<exists>! s2 \<in> states ?\<A> . (s1, a, s2) \<in> transitions \<A>" using assms well_def_trans_components by metis
    hence "\<exists>! s2 \<in> states ?\<A> . (s1, a, s2) \<in> transitions ?\<A>" using assm unfolding reachable_automaton_def reachable_states_def by force
  }
  thus ?thesis unfolding DFA_property_def by auto
qed

theorem reachable_automaton_states:
  assumes "auto_well_defined \<A>"
  shows "states (reachable_automaton \<A>) = reachable_states (reachable_automaton \<A>)"
proof - 
  have "auto_well_defined (reachable_automaton \<A>)" using assms well_def_reachable_automaton by blast
  hence sub: "reachable_states (reachable_automaton \<A>) \<subseteq> states (reachable_automaton \<A>)" using reachable_states_are_states by blast
  {
    fix s assume "s \<in> states (reachable_automaton \<A>)"
    hence "s \<in> reachable_states \<A>" unfolding reachable_automaton_def by auto
    hence "reachable_state s \<A>" unfolding reachable_states_def by auto
    hence "\<exists> word run . run_well_defined run \<A> word \<and> last run = s" unfolding reachable_state_def by auto
    hence "\<exists> word run . run_well_defined run (reachable_automaton \<A>) word \<and> last run = s" using run_reachable_automaton assms by blast
    hence "reachable_state s (reachable_automaton \<A>)" unfolding reachable_state_def by auto
    hence "s \<in> reachable_states (reachable_automaton \<A>)" unfolding reachable_states_def by auto
  }
  hence "states (reachable_automaton \<A>) \<subseteq> reachable_states (reachable_automaton \<A>)" by auto
  thus ?thesis using sub by auto
qed

corollary reachable_reachable_automaton:
  assumes "auto_well_defined \<A>"
  shows "reachable_automaton \<A> = reachable_automaton (reachable_automaton \<A>)"
  using assms well_def_reachable_automaton reachable_automaton_states max_reachable_states by metis

definition connected_automaton :: "('s, 'a) automaton \<Rightarrow> bool" where "connected_automaton \<A> = (\<forall> s \<in> states \<A> . reachable_state s \<A>)"

proposition connected_auto_equi:
  assumes "auto_well_defined \<A>"
  shows "connected_automaton \<A> \<longleftrightarrow> states \<A> = reachable_states \<A>"
  using assms reachable_states_are_states unfolding connected_automaton_def reachable_states_def by blast

theorem reachable_automaton_connected:
  assumes "auto_well_defined \<A>"
  shows "connected_automaton (reachable_automaton \<A>)"
  using assms well_def_reachable_automaton connected_auto_equi reachable_automaton_states by blast

theorem reachable_automaton_language_correctness:
  assumes "auto_well_defined \<A>"
  shows "language_auto \<A> = language_auto (reachable_automaton \<A>)"
proof - 
  {
    fix word assume "word \<in> language_auto \<A>"
    hence "\<exists> run . run_well_defined run \<A> word \<and> last run \<in> accepting_states \<A>" unfolding language_auto_def run_accepting_def by auto
    hence "\<exists> run . run_well_defined run \<A> word \<and> last run \<in> accepting_states \<A> \<and> reachable_state (last run) \<A>" unfolding reachable_state_def by auto
    hence "\<exists> run . run_well_defined run (reachable_automaton \<A>) word \<and> last run \<in> accepting_states (reachable_automaton \<A>)" using assms run_reachable_automaton unfolding reachable_automaton_def reachable_states_def by auto
    hence "word \<in> language_auto (reachable_automaton \<A>)" unfolding run_accepting_def language_auto_def by auto
  }
  hence sub: "language_auto \<A> \<subseteq> language_auto (reachable_automaton \<A>)" by auto
  {
    fix word assume "word \<in> language_auto (reachable_automaton \<A>)"
    hence "\<exists> run . run_well_defined run (reachable_automaton \<A>) word \<and> last run \<in> accepting_states (reachable_automaton \<A>)" unfolding language_auto_def run_accepting_def by auto
    hence "\<exists> run . run_well_defined run \<A> word \<and> last run \<in> accepting_states \<A> \<and> reachable_state (last run) \<A>" using assms run_reachable_automaton unfolding reachable_automaton_def reachable_states_def by auto
    hence "word \<in> language_auto \<A>" unfolding run_accepting_def language_auto_def by auto
  }
  hence "language_auto (reachable_automaton \<A>) \<subseteq> language_auto \<A>" by auto
  thus ?thesis using sub by auto
qed

theorem reachable_main:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)"
  shows "\<exists> reach_\<A> :: ('s, 'a) automaton . auto_well_defined reach_\<A> \<and> alphabet reach_\<A> = alphabet \<A> \<and> language_auto reach_\<A> = language_auto \<A> \<and> connected_automaton reach_\<A>"
  using assms reachable_automaton_language_correctness alphabet_reachable_auto well_def_reachable_automaton reachable_automaton_connected by fast

end