theory automaton_minimization

imports Main automaton_reversal automaton_reachability

begin

text \<open>Author: Benno Thalmann, last update: 11.2.2026, Addition to masterarbeit_benno_thalmann\<close>

text \<open>Minimization using Brzozowski's algorithm\<close>
definition minimal_DFA_brz :: "('s, 'a) automaton \<Rightarrow> (('s states) states, 'a) automaton" where "minimal_DFA_brz \<A> = reachable_automaton (powerset_automaton_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))))"

theorem minimal_preserves_well_defined:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (minimal_DFA_brz \<A>)"
  using assms reversal_preserves_well_defined well_def_powerset_automaton_multi well_def_reachable_automaton unfolding minimal_DFA_brz_def by metis 

corollary language_well_def_min_DFA_auto:
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (language_auto (minimal_DFA_brz \<A>)) (alphabet (minimal_DFA_brz \<A>))"
  using minimal_preserves_well_defined assms automata_language_are_well_defined by blast

text \<open>Main result for the minimal_DFA_brz automaton: it is DFA\<close>
theorem minimal_DFA_DFA_property:
  assumes "auto_well_defined \<A>"
  shows "DFA_property (minimal_DFA_brz \<A>)"
proof -
  have well_def: "auto_well_defined_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))))" using assms reversal_preserves_well_defined well_def_powerset_automaton_multi well_def_reachable_automaton by metis
  hence well_def_final: "auto_well_defined (powerset_automaton_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))))" using well_def_powerset_automaton_multi by auto
  hence "DFA_property (powerset_automaton_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))))" using well_def DFA_property_powerset_automaton_multi by blast
  thus ?thesis using DFA_property_reachable_automaton well_def_final unfolding minimal_DFA_brz_def by blast
qed

text \<open>Main result for the minimal_DFA_brz automaton: language equivalence\<close>
theorem minimal_DFA_language_correctness:
  assumes "auto_well_defined \<A>"
  shows "language_auto \<A> = language_auto (minimal_DFA_brz \<A>)"
proof -
  have "rev_language (language_auto \<A>) = language_auto_multi (reversal_nfa \<A>) \<and> auto_well_defined_multi (reversal_nfa \<A>)" using assms reversal_preserves_well_defined rev_language_correctness by blast 
  hence "language_auto (powerset_automaton_multi (reversal_nfa \<A>)) = rev_language (language_auto \<A>) \<and> auto_well_defined (powerset_automaton_multi (reversal_nfa \<A>))" using well_def_powerset_automaton_multi powerset_automaton_language_correctness_multi by auto
  hence "language_auto (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))) = rev_language (language_auto \<A>) \<and> auto_well_defined (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))" using well_def_reachable_automaton reachable_automaton_language_correctness by blast
  hence "rev_language (language_auto_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))))) = rev_language (language_auto \<A>) \<and> auto_well_defined_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))))" using reversal_preserves_well_defined rev_language_correctness_rev by blast
  hence "language_auto_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))) = language_auto \<A> \<and> auto_well_defined_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))))" using rev_rev_language by metis  
  hence "language_auto (powerset_automaton_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))))) = language_auto \<A> \<and> auto_well_defined (powerset_automaton_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))))" using well_def_powerset_automaton_multi powerset_automaton_language_correctness_multi by blast
  hence "language_auto (reachable_automaton (powerset_automaton_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))))) = language_auto \<A> \<and> auto_well_defined (reachable_automaton (powerset_automaton_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))))))" using well_def_reachable_automaton reachable_automaton_language_correctness by blast
  thus ?thesis unfolding minimal_DFA_brz_def by argo
qed

theorem minimal_DFA_alphabet: "alphabet \<A> = alphabet (minimal_DFA_brz \<A>)"
proof - 
  have "alphabet \<A> = alphabet_multi (reversal_nfa \<A>)" unfolding reversal_nfa_def by simp
  hence "alphabet \<A> = alphabet (powerset_automaton_multi (reversal_nfa \<A>))" unfolding powerset_automaton_multi_def by simp
  hence "alphabet \<A> = alphabet (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))" unfolding reachable_automaton_def by simp
  hence "alphabet \<A> = alphabet_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))))" unfolding reversal_nfa_def by simp
  hence "alphabet \<A> = alphabet (powerset_automaton_multi (reversal_nfa (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))))" unfolding powerset_automaton_multi_def by simp
  thus ?thesis unfolding minimal_DFA_brz_def reachable_automaton_def by simp
qed

text \<open>Predicate for minimality\<close>
definition minimal_DFA_property :: "('s, 'a) automaton \<Rightarrow> bool" where "minimal_DFA_property \<A> = (auto_well_defined \<A> \<and> DFA_property \<A> \<and> (\<nexists> \<A>_minimal :: ('s, 'a) automaton . auto_well_defined \<A>_minimal \<and> alphabet \<A>_minimal = alphabet \<A> \<and> DFA_property \<A>_minimal \<and> language_auto \<A>_minimal = language_auto \<A> \<and> card (states \<A>_minimal) < card (states \<A>)))"

text \<open>Correctness of Brzozowski's algorithm\<close>
proposition minimal_auto_reachable_auto:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "\<exists> s \<in> states \<A> . \<not> reachable_state s \<A>"
  shows "auto_well_defined (reachable_automaton \<A>) \<and> alphabet (reachable_automaton \<A>) = alphabet \<A> \<and> DFA_property (reachable_automaton \<A>) \<and> language_auto \<A> = language_auto (reachable_automaton \<A>) \<and> card (states (reachable_automaton \<A>)) < card (states \<A>)"
proof - 
  have well_def: "auto_well_defined (reachable_automaton \<A>)" using assms well_def_reachable_automaton by blast
  obtain s where "s \<in> states \<A> \<and> \<not> reachable_state s \<A>" using assms by blast
  hence props: "finite (states \<A>) \<and> s \<in> states \<A> \<and> s \<notin> states (reachable_automaton \<A>)" using assms unfolding auto_well_defined_def reachable_automaton_def reachable_states_def by force
  have alpha: "alphabet (reachable_automaton \<A>) = alphabet \<A>" unfolding reachable_automaton_def by simp
  have "states (reachable_automaton \<A>) \<subseteq> states \<A>" using assms reachable_states_are_states unfolding reachable_automaton_def by auto
  hence "card (states (reachable_automaton \<A>)) < card (states \<A>)" using assms card_seteq leI props by metis
  thus ?thesis using assms alpha DFA_property_reachable_automaton reachable_automaton_language_correctness well_def by blast
qed

corollary not_minimal_when_not_reachable:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "\<exists> s \<in> states \<A> . \<not> reachable_state s \<A>"
  shows "\<not> minimal_DFA_property \<A>"
  using assms minimal_auto_reachable_auto unfolding minimal_DFA_property_def by blast

definition equivalent_states :: "'s state \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 's state \<Rightarrow> bool" where "equivalent_states s1 \<A> s2 = (\<forall> word . (\<exists> prun1 . pseudo_run_well_defined prun1 \<A> s1 word \<and> last prun1 \<in> accepting_states \<A>) \<longleftrightarrow> (\<exists> prun2 . pseudo_run_well_defined prun2 \<A> s2 word \<and> last prun2 \<in> accepting_states \<A>))"

proposition equivalent_states_reflexivity: "equivalent_states s \<A> s"
  unfolding equivalent_states_def by blast

proposition equivalent_states_symmetry: "equivalent_states s1 \<A> s2 \<longleftrightarrow> equivalent_states s2 \<A> s1"
  unfolding equivalent_states_def by blast

proposition equivalent_states_transitivity: 
  assumes "equivalent_states s1 \<A> s2" "equivalent_states s2 \<A> s3"
  shows "equivalent_states s1 \<A> s3"
  using assms unfolding equivalent_states_def by auto

proposition acc_equivalent_iff_acc_states: 
  assumes "auto_well_defined \<A>" "equivalent_states s1 \<A> s2"
  shows "s1 \<in> accepting_states \<A> \<longleftrightarrow> s2 \<in> accepting_states \<A>"
proof - 
  {
    fix s1 s2 assume assm: "s1 \<in> accepting_states \<A> \<and> equivalent_states s1 \<A> s2"
    hence "s1 \<in> states \<A>" using assms unfolding auto_well_defined_def by fast
    hence "pseudo_run_well_defined [s1] \<A> s1 [] \<and> last [s1] \<in> accepting_states \<A>" using assm unfolding pseudo_run_well_defined_def by force
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A> s2 [] \<and> last prun2 \<in> accepting_states \<A>" using assm unfolding equivalent_states_def by blast 
    then obtain prun2 where prun2: "pseudo_run_well_defined prun2 \<A> s2 [] \<and> last prun2 \<in> accepting_states \<A>" by blast
    hence "(prun2 ! 0) = s2 \<and> length prun2 = 1" unfolding pseudo_run_well_defined_def by auto
    hence "last prun2 = s2" using list_with_one_element by metis
    hence "s2 \<in> accepting_states \<A>" using prun2 by blast
  }
  hence left: "s1 \<in> accepting_states \<A> \<longrightarrow> s2 \<in> accepting_states \<A>" using assms by presburger
  {
    fix s1 s2 assume assm: "s2 \<in> accepting_states \<A> \<and> equivalent_states s1 \<A> s2"
    hence "s2 \<in> states \<A>" using assms unfolding auto_well_defined_def by fast
    hence "pseudo_run_well_defined [s2] \<A> s2 [] \<and> last [s2] \<in> accepting_states \<A>" using assm unfolding pseudo_run_well_defined_def by force
    hence "\<exists> prun1 . pseudo_run_well_defined prun1 \<A> s1 [] \<and> last prun1 \<in> accepting_states \<A>" using assm unfolding equivalent_states_def by blast 
    then obtain prun1 where prun1: "pseudo_run_well_defined prun1 \<A> s1 [] \<and> last prun1 \<in> accepting_states \<A>" by blast
    hence "(prun1 ! 0) = s1 \<and> length prun1 = 1" unfolding pseudo_run_well_defined_def by auto
    hence "last prun1 = s1" using list_with_one_element by metis
    hence "s1 \<in> accepting_states \<A>" using prun1 by blast
  }
  hence "s2 \<in> accepting_states \<A> \<longrightarrow> s1 \<in> accepting_states \<A>" using assms by presburger
  thus ?thesis using left by blast
qed

definition equivalent_states_transitions :: "'s state \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 's state \<Rightarrow> ('s, 'a) transitions" where "equivalent_states_transitions s1 \<A> s2 = {(s1', a, if s2' = s2 then s1 else s2') | s1' a s2'. (s1', a, s2') \<in> transitions \<A> \<and> s1' \<noteq> s2}"

definition equivalent_states_automaton :: "'s state \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 's state \<Rightarrow> ('s , 'a) automaton" where
  "equivalent_states_automaton s1 \<A> s2 = Automaton
    (states \<A> - {s2})
    (alphabet \<A>)
    (equivalent_states_transitions s1 \<A> s2)
    (if s2 = initial_state \<A> then s1 else initial_state \<A>)
    (accepting_states \<A> - {s2})"

lemma acc_states_equivalent_states_auto: "(if s2 \<in> accepting_states \<A> then accepting_states \<A> - {s2} else accepting_states \<A>) = accepting_states \<A> - {s2}"
  by force

lemma special_transition_equi_states_auto:
  assumes "(s, a, s1) \<in> transitions (equivalent_states_automaton s1 \<A> s2)"
  shows "(s, a, s1) \<in> transitions \<A> \<or> (s, a, s2) \<in> transitions \<A>"
proof -
  have "(s, a, s1) \<in> equivalent_states_transitions s1 \<A> s2" using assms unfolding equivalent_states_automaton_def by auto
  hence "(s, a, s1) \<in> {(s1', a, if s2' = s2 then s1 else s2') | s1' a s2'. (s1', a, s2') \<in> transitions \<A> \<and> s1' \<noteq> s2}" unfolding equivalent_states_transitions_def by blast
  hence "\<exists> s2' . (s, a, s2') \<in> transitions \<A> \<and> s1 = (if s2' = s2 then s1 else s2')" by blast
  thus ?thesis by metis
qed

theorem well_def_equi_states_automaton:
  assumes "auto_well_defined \<A>" "s1 \<in> states \<A>" "s2 \<in> states \<A>" "s1 \<noteq> s2"
  shows "auto_well_defined (equivalent_states_automaton s1 \<A> s2)"
proof - 
  let ?\<A> = "equivalent_states_automaton s1 \<A> s2"
  have finite: "finite (states ?\<A>) \<and> finite (alphabet ?\<A>)" using assms unfolding auto_well_defined_def equivalent_states_automaton_def by force
  have init: "initial_state ?\<A> \<in> states ?\<A>" using assms unfolding auto_well_defined_def equivalent_states_automaton_def by auto
  have acc: "accepting_states ?\<A> \<subseteq> states ?\<A>" using assms unfolding auto_well_defined_def equivalent_states_automaton_def by auto
  hence "\<forall> (s1, a, s2) \<in> transitions ?\<A> . s1 \<in> states ?\<A> \<and> a \<in> alphabet ?\<A> \<and> s2 \<in> states ?\<A>" using assms unfolding auto_well_defined_def equivalent_states_automaton_def equivalent_states_transitions_def by auto
  thus ?thesis using finite init acc unfolding auto_well_defined_def by blast
qed

corollary language_well_def_equi_auto:
  assumes "auto_well_defined \<A>" "s1 \<in> states \<A>" "s2 \<in> states \<A>" "s1 \<noteq> s2"
  shows "language_well_defined (language_auto (equivalent_states_automaton s1 \<A> s2)) (alphabet (equivalent_states_automaton s1 \<A> s2))"
  using well_def_equi_states_automaton assms automata_language_are_well_defined by metis

theorem equi_states_auto_has_smaller_card:
  assumes "auto_well_defined \<A>" "s1 \<in> states \<A>" "s2 \<in> states \<A>"
  shows "card (states (equivalent_states_automaton s1 \<A> s2)) < card (states \<A>)"
proof - 
  have finite: "finite (states \<A>)" using assms unfolding auto_well_defined_def by blast
  have "states (equivalent_states_automaton s1 \<A> s2) = states \<A> - {s2} \<and> s2 \<in> states \<A>" using assms unfolding equivalent_states_automaton_def by auto
  hence "states (equivalent_states_automaton s1 \<A> s2) \<subset> states \<A>" by blast
  thus ?thesis using finite psubset_card_mono by metis
qed

theorem DFA_property_equi_states_automaton:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "s1 \<in> states \<A>" "s2 \<in> states \<A>" "s1 \<noteq> s2"
  shows "DFA_property (equivalent_states_automaton s1 \<A> s2)"
proof -  
  let ?\<A> = "equivalent_states_automaton s1 \<A> s2"
  {
    fix s1' a assume assm: "s1' \<in> states ?\<A> \<and> a \<in> alphabet ?\<A>"
    hence "s1' \<in> states \<A> \<and> a \<in> alphabet \<A> \<and> s1' \<noteq> s2" unfolding equivalent_states_automaton_def by auto
    hence "\<exists>! s2' \<in> states \<A> . (s1', a, s2') \<in> transitions \<A> \<and> s1' \<noteq> s2" using assms unfolding DFA_property_def by simp
    then obtain s2' where s2': "s2' \<in> states \<A> \<and> (s1', a, s2') \<in> transitions \<A> \<and> s1' \<noteq> s2" by blast
    consider (case1) "s2' \<noteq> s2" | (case2) "s2' = s2" by blast
    hence existence: "\<exists> s2' \<in> states ?\<A> . (s1', a, s2') \<in> transitions ?\<A>"
    proof cases
      case case1 thus ?thesis using s2' unfolding equivalent_states_automaton_def equivalent_states_transitions_def by auto
    next
      case case2 thus ?thesis using assms s2' unfolding equivalent_states_automaton_def equivalent_states_transitions_def by auto
    qed
  }
  hence existence: "\<forall> s1 \<in> states ?\<A> . \<forall> a \<in> alphabet ?\<A> . \<exists> s2 \<in> states ?\<A> . (s1, a, s2) \<in> transitions ?\<A>" by blast
  {
    fix s1' a s2' y assume "s1' \<in> states ?\<A> \<and> a \<in> alphabet ?\<A> \<and> s2' \<in> states ?\<A> \<and> y \<in> states ?\<A> \<and> (s1', a, s2') \<in> transitions ?\<A> \<and> (s1', a, y) \<in> transitions ?\<A>"
    then obtain s2'' y' where states: "(s1', a, s2'') \<in> transitions \<A> \<and> s2' = (if s2'' = s2 then s1 else s2'') \<and> (s1', a, y') \<in> transitions \<A> \<and> y = (if y' = s2 then s1 else y')" unfolding equivalent_states_automaton_def equivalent_states_transitions_def by auto
    hence "s1' \<in> states \<A> \<and> a \<in> alphabet \<A> \<and> s2'' \<in> states \<A> \<and> y' \<in> states \<A>" using assms well_def_trans_components by metis
    hence "s2'' = y'" using assms states unfolding DFA_property_def by blast
    hence "s2' = y" using states by blast
  }
  thus ?thesis using existence unfolding DFA_property_def by blast
qed

lemma pseudo_run_without_element_left:
  assumes "auto_well_defined \<A>" "equivalent_states s1 \<A> s2" "s1 \<in> states \<A>" "s2 \<in> states \<A>" "s1 \<noteq> s2"
  shows "pseudo_run_well_defined prun2 \<A> s word \<and> s \<noteq> s2 \<and> last prun2 \<in> accepting_states \<A> \<Longrightarrow> \<exists> prun1 . pseudo_run_well_defined prun1 (equivalent_states_automaton s1 \<A> s2) s word \<and> last prun1 \<in> accepting_states (equivalent_states_automaton s1 \<A> s2)"
proof(induction word arbitrary: s prun2)
  let ?\<A> = "equivalent_states_automaton s1 \<A> s2"
  case Nil
  hence "length prun2 = 1 \<and> prun2 ! 0 = s \<and> last prun2 \<in> accepting_states \<A>" unfolding pseudo_run_well_defined_def by auto
  hence "s \<in> accepting_states \<A>" using list_with_one_element by metis
  hence "s \<in> accepting_states \<A> \<and> s \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  hence "s \<in> accepting_states ?\<A> \<and> s \<in> states ?\<A>" using Nil unfolding equivalent_states_automaton_def by auto
  hence "pseudo_run_well_defined [s] ?\<A> s [] \<and> s \<in> accepting_states ?\<A>" unfolding pseudo_run_well_defined_def by auto
  thus ?case using Nil by auto
next
  let ?\<A> = "equivalent_states_automaton s1 \<A> s2"
  case (Cons a word)
  hence props: "length prun2 > 1 \<and> prun2 ! 0 = s \<and> last prun2 \<in> accepting_states \<A>" unfolding pseudo_run_well_defined_def by force
  hence "prun2 \<noteq> [] \<and> prun2 ! 0 = s" by auto
  hence "prun2 = s # (tl prun2)" using list_properties_not_empty by fast
  hence "pseudo_run_well_defined (s # (tl prun2)) \<A> s (a # word)" using Cons by argo
  hence step: "pseudo_run_well_defined (tl prun2) \<A> ((tl prun2) ! 0) word \<and> (s, a, (tl prun2) ! 0) \<in> transitions \<A>" using assms prun_well_defined_extension_cons by fast
  have acc: "last (tl prun2) \<in> accepting_states \<A>" using props last_tl tl_more_elements by metis
  consider (case1) "(tl prun2) ! 0 \<noteq> s2" | (case2) "(tl prun2) ! 0 = s2" by blast
  thus ?case
  proof cases
    have well_def: "auto_well_defined ?\<A>" using assms well_def_equi_states_automaton by metis
    case case1
    hence "\<exists> prun1 . pseudo_run_well_defined prun1 ?\<A> ((tl prun2) ! 0) word \<and> last prun1 \<in> accepting_states ?\<A>" using Cons acc step by blast
    then obtain prun1 where prun1: "pseudo_run_well_defined prun1 ?\<A> ((tl prun2) ! 0) word \<and> last prun1 \<in> accepting_states ?\<A>" by blast
    hence "(tl prun2) ! 0 = prun1 ! 0 \<and> (s, a, (tl prun2) ! 0) \<in> transitions \<A>" using step unfolding pseudo_run_well_defined_def by argo
    hence "pseudo_run_well_defined prun1 ?\<A> (prun1 ! 0) word \<and> prun1 ! 0 \<noteq> s2 \<and> (s, a, prun1 ! 0) \<in> transitions \<A> \<and> last prun1 \<in> accepting_states ?\<A>" using prun1 case1 by argo
    hence "pseudo_run_well_defined prun1 ?\<A> (prun1 ! 0) word \<and> (s, a, prun1 ! 0) \<in> transitions ?\<A> \<and> last prun1 \<in> accepting_states ?\<A>" using Cons unfolding equivalent_states_automaton_def equivalent_states_transitions_def by auto
    hence props: "pseudo_run_well_defined (s # prun1) ?\<A> s (a # word) \<and> last prun1 \<in> accepting_states ?\<A>" using well_def prun_well_defined_extension_cons by fast
    hence "prun1 \<noteq> []" using prun1 unfolding pseudo_run_well_defined_def by force
    hence "last (s # prun1) \<in> accepting_states ?\<A>" using Cons props by auto
    thus ?thesis using props by blast
  next
    have well_def: "auto_well_defined ?\<A>" using assms well_def_equi_states_automaton by metis
    case case2
    hence trans: "pseudo_run_well_defined (tl prun2) \<A> s2 word \<and> (s, a, s2) \<in> transitions \<A> \<and> last (tl prun2) \<in> accepting_states \<A>" using step acc by fast
    hence "\<exists> prun1 . pseudo_run_well_defined prun1 \<A> s1 word \<and> last prun1 \<in> accepting_states \<A>" using assms unfolding equivalent_states_def by blast
    then obtain prun1 where "pseudo_run_well_defined prun1 \<A> s1 word \<and> last prun1 \<in> accepting_states \<A>" by blast
    hence "\<exists> prun1' . pseudo_run_well_defined prun1' ?\<A> s1 word \<and> last prun1' \<in> accepting_states ?\<A>" using Cons assms by fast
    then obtain prun1' where prun1': "pseudo_run_well_defined prun1' ?\<A> s1 word \<and> last prun1' \<in> accepting_states ?\<A>" by blast
    hence init: "s1 = prun1' ! 0" unfolding pseudo_run_well_defined_def by blast
    have "(s, a, s1) \<in> transitions ?\<A>" using trans Cons unfolding equivalent_states_automaton_def equivalent_states_transitions_def by auto
    hence props: "pseudo_run_well_defined (s # prun1') ?\<A> s (a # word) \<and> last prun1' \<in> accepting_states ?\<A>" using well_def prun_well_defined_extension_cons prun1' init by fast
    hence "prun1' \<noteq> []" using prun1' unfolding pseudo_run_well_defined_def by force
    hence "last (s # prun1') \<in> accepting_states ?\<A>" using Cons props by auto
    thus ?thesis using props by blast
  qed
qed

theorem equi_states_run_left:
  assumes "auto_well_defined \<A>" "equivalent_states s1 \<A> s2" "s1 \<in> states \<A>" "s2 \<in> states \<A>" "s1 \<noteq> s2" "run_accepting run \<A> word"
  shows "\<exists> run' . run_accepting run' (equivalent_states_automaton s1 \<A> s2) word"
proof -
  let ?\<A> = "equivalent_states_automaton s1 \<A> s2"
  have "run_well_defined run \<A> word \<and> last run \<in> accepting_states \<A>" using assms unfolding run_accepting_def by blast
  hence prun: "pseudo_run_well_defined run \<A> (initial_state \<A>) word \<and> last run \<in> accepting_states \<A>" using assms unfolding run_well_defined_def by blast
  consider (case1) "initial_state \<A> \<noteq> s2" | (case2) "initial_state \<A> = s2" by blast
  thus ?thesis
  proof cases
    case case1
    hence exi: "\<exists> prun1 . pseudo_run_well_defined prun1 ?\<A> (initial_state \<A>) word \<and> last prun1 \<in> accepting_states ?\<A>" using pseudo_run_without_element_left assms prun by metis
    have "initial_state \<A> = initial_state ?\<A>" using case1 unfolding equivalent_states_automaton_def by auto
    hence "\<exists> run' . run_well_defined run' ?\<A> word \<and> last run' \<in> accepting_states ?\<A>" using exi unfolding run_well_defined_def by auto
    thus ?thesis unfolding run_accepting_def by blast
  next
    case case2
    hence "\<exists> prun1 . pseudo_run_well_defined prun1 \<A> s1 word \<and> last prun1 \<in> accepting_states \<A>" using assms prun unfolding equivalent_states_def by blast
    hence exi: "\<exists> prun1 . pseudo_run_well_defined prun1 ?\<A> s1 word \<and> last prun1 \<in> accepting_states ?\<A>" using pseudo_run_without_element_left assms by fast
    have "s1 = initial_state ?\<A>" using case2 unfolding equivalent_states_automaton_def by auto
    hence "\<exists> run' . run_well_defined run' ?\<A> word \<and> last run' \<in> accepting_states ?\<A>" using exi unfolding run_well_defined_def by metis 
    thus ?thesis unfolding run_accepting_def by blast
  qed
qed

lemma pseudo_run_without_element_right:
  assumes "auto_well_defined \<A>" "equivalent_states s1 \<A> s2" "s1 \<in> states \<A>" "s2 \<in> states \<A>" "s1 \<noteq> s2"
  shows "pseudo_run_well_defined prun1 (equivalent_states_automaton s1 \<A> s2) s word \<and> last prun1 \<in> accepting_states (equivalent_states_automaton s1 \<A> s2) \<Longrightarrow> \<exists> prun2 . pseudo_run_well_defined prun2 \<A> s word \<and> last prun2 \<in> accepting_states \<A>"
proof(induction word arbitrary: s prun1)
  let ?\<A> = "equivalent_states_automaton s1 \<A> s2"
  case Nil
  hence "length prun1 = 1 \<and> prun1 ! 0 = s \<and> last prun1 \<in> accepting_states ?\<A>" unfolding pseudo_run_well_defined_def by auto
  hence "s \<in> accepting_states ?\<A>" using list_with_one_element by metis
  hence "s \<in> accepting_states \<A>" unfolding equivalent_states_automaton_def by simp
  hence "s \<in> accepting_states \<A> \<and> s \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  hence "pseudo_run_well_defined [s] \<A> s [] \<and> s \<in> accepting_states \<A>" unfolding pseudo_run_well_defined_def by auto
  thus ?case by auto
next
  let ?\<A> = "equivalent_states_automaton s1 \<A> s2"
  have well_def: "auto_well_defined ?\<A>" using assms well_def_equi_states_automaton by metis
  case (Cons a word)
  hence props: "length prun1 > 1 \<and> prun1 ! 0 = s \<and> last prun1 \<in> accepting_states ?\<A>" unfolding pseudo_run_well_defined_def by force
  hence "prun1 \<noteq> [] \<and> prun1 ! 0 = s" by auto
  hence "prun1 = s # (tl prun1)" using list_properties_not_empty by fast
  hence "pseudo_run_well_defined (s # (tl prun1)) ?\<A> s (a # word)" using Cons by argo
  hence step: "pseudo_run_well_defined (tl prun1) ?\<A> ((tl prun1) ! 0) word \<and> (s, a, (tl prun1) ! 0) \<in> transitions ?\<A>" using well_def prun_well_defined_extension_cons by fast
  have acc: "last (tl prun1) \<in> accepting_states ?\<A>" using props last_tl tl_more_elements by metis
  consider (case1) "(tl prun1) ! 0 \<noteq> s1" | (case2) "(tl prun1) ! 0 = s1" by blast
  thus ?case
  proof cases
    case case1
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A> ((tl prun1) ! 0) word \<and> last prun2 \<in> accepting_states \<A>" using Cons acc step by blast
    then obtain prun2 where prun2: "pseudo_run_well_defined prun2 \<A> ((tl prun1) ! 0) word \<and> last prun2 \<in> accepting_states \<A>" by blast
    hence "(tl prun1) ! 0 = prun2 ! 0 \<and> (s, a, (tl prun1) ! 0) \<in> transitions ?\<A>" using step unfolding pseudo_run_well_defined_def by argo 
    hence "pseudo_run_well_defined prun2 \<A> (prun2 ! 0) word \<and> prun2 ! 0 \<noteq> s1 \<and> (s, a, prun2 ! 0) \<in> transitions ?\<A> \<and> last prun2 \<in> accepting_states \<A>" using prun2 case1 by argo
    hence "pseudo_run_well_defined prun2 \<A> (prun2 ! 0) word \<and> (s, a, prun2 ! 0) \<in> transitions \<A> \<and> last prun2 \<in> accepting_states \<A>" unfolding equivalent_states_automaton_def equivalent_states_transitions_def by auto
    hence props: "pseudo_run_well_defined (s # prun2) \<A> s (a # word) \<and> last prun2 \<in> accepting_states \<A>" using assms prun_well_defined_extension_cons by fast
    hence "prun2 \<noteq> []" using prun2 unfolding pseudo_run_well_defined_def by force
    hence "last (s # prun2) \<in> accepting_states \<A>" using props by auto
    thus ?thesis using props by blast
  next
    case case2
    hence trans: "pseudo_run_well_defined (tl prun1) ?\<A> s1 word \<and> (s, a, s1) \<in> transitions ?\<A> \<and> last (tl prun1) \<in> accepting_states ?\<A>" using step acc by fast
    then consider (case3) "(s, a, s1) \<in> transitions \<A>" | (case4) "(s, a, s2) \<in> transitions \<A>" using special_transition_equi_states_auto by fast
    thus ?thesis
    proof cases
      case case3
      hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A> s1 word \<and> last prun2 \<in> accepting_states \<A>" using Cons trans by fast
      then obtain prun2 where prun2: "pseudo_run_well_defined prun2 \<A> s1 word \<and> last prun2 \<in> accepting_states \<A>" by blast
      hence init: "s1 = prun2 ! 0" unfolding pseudo_run_well_defined_def by blast
      hence props: "pseudo_run_well_defined (s # prun2) \<A> s (a # word) \<and> last prun2 \<in> accepting_states \<A>" using case3 assms prun_well_defined_extension_cons prun2 init by fast
      hence "prun2 \<noteq> []" using prun2 unfolding pseudo_run_well_defined_def by force
      hence "last (s # prun2) \<in> accepting_states \<A>" using Cons props by auto
      thus ?thesis using props by blast
    next
      case case4
      hence "\<exists> prun2' . pseudo_run_well_defined prun2' \<A> s1 word \<and> last prun2' \<in> accepting_states \<A>" using Cons trans by fast
      hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A> s2 word \<and> last prun2 \<in> accepting_states \<A>" using assms unfolding equivalent_states_def by blast
      then obtain prun2 where prun2: "pseudo_run_well_defined prun2 \<A> s2 word \<and> last prun2 \<in> accepting_states \<A>" by blast
      hence init: "s2 = prun2 ! 0" unfolding pseudo_run_well_defined_def by blast
      hence props: "pseudo_run_well_defined (s # prun2) \<A> s (a # word) \<and> last prun2 \<in> accepting_states \<A>" using case4 assms prun_well_defined_extension_cons prun2 init by fast
      hence "prun2 \<noteq> []" using prun2 unfolding pseudo_run_well_defined_def by force
      hence "last (s # prun2) \<in> accepting_states \<A>" using Cons props by auto
      thus ?thesis using props by blast
    qed
  qed
qed

theorem equi_states_run_right:
  assumes "auto_well_defined \<A>" "equivalent_states s1 \<A> s2" "s1 \<in> states \<A>" "s2 \<in> states \<A>" "s1 \<noteq> s2" "run_accepting run (equivalent_states_automaton s1 \<A> s2) word"
  shows "\<exists> run' . run_accepting run' \<A> word"
proof -
  let ?\<A> = "equivalent_states_automaton s1 \<A> s2"
  have "run_well_defined run ?\<A> word \<and> last run \<in> accepting_states ?\<A>" using assms unfolding run_accepting_def by blast
  hence prun: "pseudo_run_well_defined run ?\<A> (initial_state ?\<A>) word \<and> last run \<in> accepting_states ?\<A>" unfolding run_well_defined_def by blast
  hence exi: "\<exists> prun1 . pseudo_run_well_defined prun1 \<A> (initial_state ?\<A>) word \<and> last prun1 \<in> accepting_states \<A>" using pseudo_run_without_element_right assms prun by metis
  consider (case1) "initial_state \<A> \<noteq> s2" | (case2) "initial_state \<A> = s2" by blast
  thus ?thesis
  proof cases
    case case1
    hence "initial_state \<A> = initial_state ?\<A>" unfolding equivalent_states_automaton_def by auto
    hence "\<exists> run' . run_well_defined run' \<A> word \<and> last run' \<in> accepting_states \<A>" using exi unfolding run_well_defined_def by metis
    thus ?thesis unfolding run_accepting_def by blast
  next
    case case2
    hence "s1 = initial_state ?\<A>" unfolding equivalent_states_automaton_def by auto
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A> (initial_state \<A>) word \<and> last prun2 \<in> accepting_states \<A>" using case2 exi assms unfolding equivalent_states_def by simp
    hence "\<exists> run' . run_well_defined run' \<A> word \<and> last run' \<in> accepting_states \<A>" unfolding run_well_defined_def by blast
    thus ?thesis unfolding run_accepting_def by blast
  qed
qed

theorem equi_states_language_correctness:
  assumes "auto_well_defined \<A>" "equivalent_states s1 \<A> s2" "s1 \<in> states \<A>" "s2 \<in> states \<A>" "s1 \<noteq> s2"
  shows "language_auto \<A> = language_auto (equivalent_states_automaton s1 \<A> s2)"
  using assms equi_states_run_left equi_states_run_right unfolding language_auto_def by metis

definition distinguishable_automaton :: "('s, 'a) automaton \<Rightarrow> bool" where "distinguishable_automaton \<A> = (\<nexists> s1 s2 . s1 \<in> states \<A> \<and> s2 \<in> states \<A> \<and> equivalent_states s1 \<A> s2 \<and> s1 \<noteq> s2)"

lemma same_alphabet_equi_states: "alphabet \<A> = alphabet (equivalent_states_automaton s1 \<A> s2)"
  unfolding equivalent_states_automaton_def by auto

proposition minimal_auto_equi_states_auto:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "equivalent_states s1 \<A> s2" "s1 \<in> states \<A>" "s2 \<in> states \<A>" "s1 \<noteq> s2"
  shows "auto_well_defined (equivalent_states_automaton s1 \<A> s2) \<and> alphabet \<A> = alphabet (equivalent_states_automaton s1 \<A> s2) \<and> DFA_property (equivalent_states_automaton s1 \<A> s2) \<and> language_auto \<A> = language_auto (equivalent_states_automaton s1 \<A> s2) \<and> card (states (equivalent_states_automaton s1 \<A> s2)) < card (states \<A>)"
  using assms equi_states_language_correctness well_def_equi_states_automaton equi_states_auto_has_smaller_card DFA_property_equi_states_automaton same_alphabet_equi_states by metis

lemma minimality_property_left: "minimal_DFA_property \<A> \<Longrightarrow> connected_automaton \<A> \<and> distinguishable_automaton \<A>"
  using minimal_auto_equi_states_auto minimal_auto_reachable_auto unfolding connected_automaton_def minimal_DFA_property_def distinguishable_automaton_def by metis

text \<open>Right side needs more work:\<close>
lemma normal_trans_comb_auto_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" "s1 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  shows "(s1, a, s2) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
proof(rule ccontr)
  have not_in: "s1 \<notin> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms unfolding type_encode_automaton_def cross_renaming_iso_def by auto
  assume "(s1, a, s2) \<notin> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  hence "(s1, a, s2) \<notin> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" by blast
  hence "(s1, a, s2) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms unfolding union_automaton_multi_def union_automaton_multi_helper_def by auto
  hence "s1 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms well_def_trans_components cross_renaming_iso_automaton_auto_well_defined by fast
  thus False using not_in by blast
qed

corollary normal_trans_state_comb_auto_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" "s1 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  shows "s2 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  using assms well_def_trans_components cross_renaming_iso_automaton_auto_well_defined normal_trans_comb_auto_A1 by metis

lemma normal_trans_comb_auto_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" "s1 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  shows "(s1, a, s2) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
proof(rule ccontr)
  have not_in: "s1 \<notin> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms unfolding type_encode_automaton_def cross_renaming_iso_def by auto
  assume "(s1, a, s2) \<notin> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  hence "(s1, a, s2) \<notin> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" by blast
  hence "(s1, a, s2) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms unfolding union_automaton_multi_def union_automaton_multi_helper_def by auto
  hence "s1 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms well_def_trans_components cross_renaming_iso_automaton_auto_well_defined by fast
  thus False using not_in by blast
qed

corollary normal_trans_state_comb_auto_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" "s1 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  shows "s2 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  using assms well_def_trans_components cross_renaming_iso_automaton_auto_well_defined normal_trans_comb_auto_A2 by metis

lemma existence_of_original_state_A1:
  assumes "s \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  shows "\<exists> s' \<in> states \<A>1 . (s', 1) = s"
  using assms unfolding type_encode_automaton_def cross_renaming_iso_def by auto

lemma existence_of_original_state_A2:
  assumes "s \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  shows "\<exists> s' \<in> states \<A>2 . (s', 2) = s"
  using assms unfolding type_encode_automaton_def cross_renaming_iso_def by auto

lemma prun_A1_comb_auto:
  assumes "pseudo_run_well_defined prun \<A>1 s word \<and> last prun \<in> accepting_states \<A>1"
  shows "pseudo_run_well_defined_multi (map (cross_renaming_iso 1) prun) (union_automaton_multi \<A>1 \<A>2) (s, 1) word \<and> last (map (cross_renaming_iso 1) prun) \<in> accepting_states_multi (union_automaton_multi \<A>1 \<A>2)"
proof -
  have props: "length prun = length word + 1 \<and> (prun ! 0) = s \<and> s \<in> states \<A>1 \<and> (\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>1)" using assms unfolding pseudo_run_well_defined_def by blast
  hence len: "length (map (cross_renaming_iso 1) prun) = length word + 1" by auto
  have init: "(map (cross_renaming_iso 1) prun) ! 0 = (s, 1)" using props unfolding cross_renaming_iso_def by auto
  have state: "(s, 1) \<in> states_multi (union_automaton_multi \<A>1 \<A>2)" using props unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by auto
  {
    fix i assume "i < length (map (cross_renaming_iso 1) prun) - 1"
    hence assm: "i < length prun - 1" by auto
    hence "(prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>1" using props by blast
    hence "((map (cross_renaming_iso 1) prun) ! i, word ! i, (map (cross_renaming_iso 1) prun) ! (i + 1)) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assm unfolding type_encode_automaton_def by force
  }
  hence "\<forall> i < length (map (cross_renaming_iso 1) prun) - 1 . ((map (cross_renaming_iso 1) prun) ! i, word ! i, (map (cross_renaming_iso 1) prun) ! (i + 1)) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" by blast
  hence trans: "\<forall> i < length (map (cross_renaming_iso 1) prun) - 1 . ((map (cross_renaming_iso 1) prun) ! i, word ! i, (map (cross_renaming_iso 1) prun) ! (i + 1)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" unfolding union_automaton_multi_def union_automaton_multi_helper_def by force
  have acc: "(cross_renaming_iso 1 (last prun)) \<in> accepting_states_multi (union_automaton_multi \<A>1 \<A>2)" using assms unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def by fastforce
  have "prun \<noteq> []" using len by auto
  hence "last (map (cross_renaming_iso 1) prun) \<in> accepting_states_multi (union_automaton_multi \<A>1 \<A>2)" using last_map acc by metis
  thus ?thesis using len init state trans unfolding pseudo_run_well_defined_multi_def by blast
qed

lemma prun_A2_comb_auto:
  assumes "pseudo_run_well_defined prun \<A>2 s word \<and> last prun \<in> accepting_states \<A>2"
  shows "pseudo_run_well_defined_multi (map (cross_renaming_iso 2) prun) (union_automaton_multi \<A>1 \<A>2) (s, 2) word \<and> last (map (cross_renaming_iso 2) prun) \<in> accepting_states_multi (union_automaton_multi \<A>1 \<A>2)"
proof -
  have props: "length prun = length word + 1 \<and> (prun ! 0) = s \<and> s \<in> states \<A>2 \<and> (\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>2)" using assms unfolding pseudo_run_well_defined_def by blast
  hence len: "length (map (cross_renaming_iso 2) prun) = length word + 1" by auto
  have init: "(map (cross_renaming_iso 2) prun) ! 0 = (s, 2)" using props unfolding cross_renaming_iso_def by auto
  have state: "(s, 2) \<in> states_multi (union_automaton_multi \<A>1 \<A>2)" using props unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by auto
  {
    fix i assume "i < length (map (cross_renaming_iso 2) prun) - 1"
    hence assm: "i < length prun - 1" by auto
    hence "(prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>2" using props by blast
    hence "((map (cross_renaming_iso 2) prun) ! i, word ! i, (map (cross_renaming_iso 2) prun) ! (i + 1)) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assm unfolding type_encode_automaton_def by force
  }
  hence "\<forall> i < length (map (cross_renaming_iso 2) prun) - 1 . ((map (cross_renaming_iso 2) prun) ! i, word ! i, (map (cross_renaming_iso 2) prun) ! (i + 1)) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" by blast
  hence trans: "\<forall> i < length (map (cross_renaming_iso 2) prun) - 1 . ((map (cross_renaming_iso 2) prun) ! i, word ! i, (map (cross_renaming_iso 2) prun) ! (i + 1)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" unfolding union_automaton_multi_def union_automaton_multi_helper_def by force
  have acc: "(cross_renaming_iso 2 (last prun)) \<in> accepting_states_multi (union_automaton_multi \<A>1 \<A>2)" using assms unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def by fastforce
  have "prun \<noteq> []" using len by auto
  hence "last (map (cross_renaming_iso 2) prun) \<in> accepting_states_multi (union_automaton_multi \<A>1 \<A>2)" using last_map acc by metis
  thus ?thesis using len init state trans unfolding pseudo_run_well_defined_multi_def by blast
qed

lemma prun_comb_auto_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "pseudo_run_well_defined_multi prun1 (union_automaton_multi \<A>1 \<A>2) (s, 1) word \<and> last prun1 \<in> accepting_states_multi (union_automaton_multi \<A>1 \<A>2) \<Longrightarrow> \<exists> prun2 . pseudo_run_well_defined prun2 \<A>1 s word \<and> last prun2 \<in> accepting_states \<A>1"
proof(induction word arbitrary: prun1 s)
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  case Nil
  hence "length prun1 = 1 \<and> prun1 ! 0 = (s, 1) \<and> last prun1 \<in> accepting_states_multi ?\<A>" unfolding pseudo_run_well_defined_multi_def by auto
  hence "(s, 1) \<in> accepting_states_multi ?\<A>" using list_with_one_element by metis
  hence "s \<in> accepting_states \<A>1" unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by force
  hence "s \<in> accepting_states \<A>1 \<and> s \<in> states \<A>1" using assms unfolding auto_well_defined_def by blast
  hence "pseudo_run_well_defined [s] \<A>1 s [] \<and> s \<in> accepting_states \<A>1" unfolding pseudo_run_well_defined_def by auto
  thus ?case by auto
next
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  have well_def: "auto_well_defined_multi ?\<A>" using assms union_auto_well_defined by metis
  case (Cons a word)
  hence props: "length prun1 > 1 \<and> prun1 ! 0 = (s, 1) \<and> (s, 1) \<in> states_multi ?\<A> \<and> last prun1 \<in> accepting_states_multi ?\<A>" unfolding pseudo_run_well_defined_multi_def by force
  hence "prun1 \<noteq> [] \<and> prun1 ! 0 = (s, 1)" by auto
  hence "prun1 = (s, 1) # (tl prun1)" using list_properties_not_empty by metis
  hence "pseudo_run_well_defined_multi ((s, 1) # (tl prun1)) ?\<A> (s, 1) (a # word)" using Cons by argo
  hence step: "pseudo_run_well_defined_multi (tl prun1) ?\<A> ((tl prun1) ! 0) word \<and> ((s, 1), a, (tl prun1) ! 0) \<in> transitions_multi ?\<A>" using well_def prun_well_defined_extension_cons_multi by fast  
  have state: "(s, 1) \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using props unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by fastforce
  hence "(tl prun1) ! 0 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms normal_trans_state_comb_auto_A1 step by fast
  then obtain s' where " s' \<in> states \<A>1 \<and> (s', 1) = (tl prun1) ! 0" using existence_of_original_state_A1 by blast
  hence step_adapted: "pseudo_run_well_defined_multi (tl prun1) ?\<A> (s', 1) word \<and> ((s, 1), a, (s', 1)) \<in> transitions_multi ?\<A>" using step by auto  
  have acc: "last (tl prun1) \<in> accepting_states_multi ?\<A>" using props last_tl tl_more_elements by metis
  hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A>1 s' word \<and> last prun2 \<in> accepting_states \<A>1" using Cons acc step_adapted by blast
  then obtain prun2 where prun2: "pseudo_run_well_defined prun2 \<A>1 s' word \<and> last prun2 \<in> accepting_states \<A>1" by blast
  have "((s, 1), a, (s', 1)) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms step_adapted normal_trans_comb_auto_A1 state by fast
  hence "(s, a, s') \<in> transitions \<A>1" unfolding type_encode_automaton_def cross_renaming_iso_def by auto 
  hence props: "pseudo_run_well_defined (s # prun2) \<A>1 s (a # word) \<and> last prun2 \<in> accepting_states \<A>1" using assms prun2 prun_well_defined_induction_cons by fast
  hence "prun2 \<noteq> []" using prun2 unfolding pseudo_run_well_defined_def by force
  hence "last (s # prun2) \<in> accepting_states \<A>1" using props by auto
  thus ?case using props by blast
qed

lemma prun_comb_auto_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "pseudo_run_well_defined_multi prun1 (union_automaton_multi \<A>1 \<A>2) (s, 2) word \<and> last prun1 \<in> accepting_states_multi (union_automaton_multi \<A>1 \<A>2) \<Longrightarrow> \<exists> prun2 . pseudo_run_well_defined prun2 \<A>2 s word \<and> last prun2 \<in> accepting_states \<A>2"
proof(induction word arbitrary: prun1 s)
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  case Nil
  hence "length prun1 = 1 \<and> prun1 ! 0 = (s, 2) \<and> last prun1 \<in> accepting_states_multi ?\<A>" unfolding pseudo_run_well_defined_multi_def by auto
  hence "(s, 2) \<in> accepting_states_multi ?\<A>" using list_with_one_element by metis
  hence "s \<in> accepting_states \<A>2" unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by force
  hence "s \<in> accepting_states \<A>2 \<and> s \<in> states \<A>2" using assms unfolding auto_well_defined_def by blast
  hence "pseudo_run_well_defined [s] \<A>2 s [] \<and> s \<in> accepting_states \<A>2" unfolding pseudo_run_well_defined_def by auto
  thus ?case by auto
next
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  have well_def: "auto_well_defined_multi ?\<A>" using assms union_auto_well_defined by metis
  case (Cons a word)
  hence props: "length prun1 > 1 \<and> prun1 ! 0 = (s, 2) \<and> (s, 2) \<in> states_multi ?\<A> \<and> last prun1 \<in> accepting_states_multi ?\<A>" unfolding pseudo_run_well_defined_multi_def by force
  hence "prun1 \<noteq> [] \<and> prun1 ! 0 = (s, 2)" by auto
  hence "prun1 = (s, 2) # (tl prun1)" using list_properties_not_empty by metis
  hence "pseudo_run_well_defined_multi ((s, 2) # (tl prun1)) ?\<A> (s, 2) (a # word)" using Cons by argo
  hence step: "pseudo_run_well_defined_multi (tl prun1) ?\<A> ((tl prun1) ! 0) word \<and> ((s, 2), a, (tl prun1) ! 0) \<in> transitions_multi ?\<A>" using well_def prun_well_defined_extension_cons_multi by fast  
  have state: "(s, 2) \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using props unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by fastforce
  hence "(tl prun1) ! 0 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms normal_trans_state_comb_auto_A2 step by fast
  then obtain s' where " s' \<in> states \<A>2 \<and> (s', 2) = (tl prun1) ! 0" using existence_of_original_state_A2 by blast
  hence step_adapted: "pseudo_run_well_defined_multi (tl prun1) ?\<A> (s', 2) word \<and> ((s, 2), a, (s', 2)) \<in> transitions_multi ?\<A>" using step by auto  
  have acc: "last (tl prun1) \<in> accepting_states_multi ?\<A>" using props last_tl tl_more_elements by metis
  hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A>2 s' word \<and> last prun2 \<in> accepting_states \<A>2" using Cons acc step_adapted by blast
  then obtain prun2 where prun2: "pseudo_run_well_defined prun2 \<A>2 s' word \<and> last prun2 \<in> accepting_states \<A>2" by blast
  have "((s, 2), a, (s', 2)) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms step_adapted normal_trans_comb_auto_A2 state by fast
  hence "(s, a, s') \<in> transitions \<A>2" unfolding type_encode_automaton_def cross_renaming_iso_def by auto 
  hence props: "pseudo_run_well_defined (s # prun2) \<A>2 s (a # word) \<and> last prun2 \<in> accepting_states \<A>2" using assms prun2 prun_well_defined_induction_cons by fast
  hence "prun2 \<noteq> []" using prun2 unfolding pseudo_run_well_defined_def by force
  hence "last (s # prun2) \<in> accepting_states \<A>2" using props by auto
  thus ?case using props by blast
qed

definition equivalent_states_multi :: "'s state \<Rightarrow> ('s, 'a) nfa_multi \<Rightarrow> 's state \<Rightarrow> bool" where "equivalent_states_multi s1 \<A> s2 = (\<forall> word . (\<exists> prun1 . pseudo_run_well_defined_multi prun1 \<A> s1 word \<and> last prun1 \<in> accepting_states_multi \<A>) \<longleftrightarrow> (\<exists> prun2 . pseudo_run_well_defined_multi prun2 \<A> s2 word \<and> last prun2 \<in> accepting_states_multi \<A>))"

proposition equivalent_states_reflexivity_multi: "equivalent_states_multi s \<A> s"
  unfolding equivalent_states_multi_def by blast

proposition equivalent_states_symmetry_multi: "equivalent_states_multi s1 \<A> s2 \<longleftrightarrow> equivalent_states_multi s2 \<A> s1"
  unfolding equivalent_states_multi_def by blast

proposition equivalent_states_transitivity_multi: 
  assumes "equivalent_states_multi s1 \<A> s2" "equivalent_states_multi s2 \<A> s3"
  shows "equivalent_states_multi s1 \<A> s3"
  using assms unfolding equivalent_states_multi_def by auto

theorem equivalent_states_comb_to_solo_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 1)"
  shows "equivalent_states s1 \<A>1 s2"
proof -
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"  
  {
    fix word assume assm: "\<exists> prun1 . pseudo_run_well_defined prun1 \<A>1 s1 word \<and> last prun1 \<in> accepting_states \<A>1"
    hence "\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (s1, 1) word \<and> last prun1 \<in> accepting_states_multi ?\<A>" using prun_A1_comb_auto by fast
    hence "\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (s2, 1) word \<and> last prun2 \<in> accepting_states_multi ?\<A>" using assms assm unfolding equivalent_states_multi_def by blast
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A>1 s2 word \<and> last prun2 \<in> accepting_states \<A>1" using assms prun_comb_auto_A1 by fast
  }
  hence left: "\<forall> word . (\<exists> prun1 . pseudo_run_well_defined prun1 \<A>1 s1 word \<and> last prun1 \<in> accepting_states \<A>1) \<longrightarrow> (\<exists> prun2 . pseudo_run_well_defined prun2 \<A>1 s2 word \<and> last prun2 \<in> accepting_states \<A>1)" by blast
  {
    fix word assume assm: "\<exists> prun1 . pseudo_run_well_defined prun1 \<A>1 s2 word \<and> last prun1 \<in> accepting_states \<A>1"
    hence "\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (s2, 1) word \<and> last prun1 \<in> accepting_states_multi ?\<A>" using prun_A1_comb_auto by fast
    hence "\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (s1, 1) word \<and> last prun2 \<in> accepting_states_multi ?\<A>" using assms assm unfolding equivalent_states_multi_def by blast
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A>1 s1 word \<and> last prun2 \<in> accepting_states \<A>1" using assms prun_comb_auto_A1 by fast
  }
  thus ?thesis using left unfolding equivalent_states_def by blast
qed

theorem equivalent_states_comb_to_solo_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "equivalent_states_multi (s1, 2) (union_automaton_multi \<A>1 \<A>2) (s2, 2)"
  shows "equivalent_states s1 \<A>2 s2"
proof -
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"  
  {
    fix word assume assm: "\<exists> prun1 . pseudo_run_well_defined prun1 \<A>2 s2 word \<and> last prun1 \<in> accepting_states \<A>2"
    hence "\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (s2, 2) word \<and> last prun1 \<in> accepting_states_multi ?\<A>" using prun_A2_comb_auto by fast
    hence "\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (s1, 2) word \<and> last prun2 \<in> accepting_states_multi ?\<A>" using assms assm unfolding equivalent_states_multi_def by blast
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A>2 s1 word \<and> last prun2 \<in> accepting_states \<A>2" using assms prun_comb_auto_A2 by fast
  }
  hence left: "\<forall> word . (\<exists> prun1 . pseudo_run_well_defined prun1 \<A>2 s2 word \<and> last prun1 \<in> accepting_states \<A>2) \<longrightarrow> (\<exists> prun2 . pseudo_run_well_defined prun2 \<A>2 s1 word \<and> last prun2 \<in> accepting_states \<A>2)" by blast
  {
    fix word assume assm: "\<exists> prun1 . pseudo_run_well_defined prun1 \<A>2 s1 word \<and> last prun1 \<in> accepting_states \<A>2"
    hence "\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (s1, 2) word \<and> last prun1 \<in> accepting_states_multi ?\<A>" using prun_A2_comb_auto by fast
    hence "\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (s2, 2) word \<and> last prun2 \<in> accepting_states_multi ?\<A>" using assms assm unfolding equivalent_states_multi_def by blast
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A>2 s2 word \<and> last prun2 \<in> accepting_states \<A>2" using assms prun_comb_auto_A2 by fast
  }
  thus ?thesis using left unfolding equivalent_states_def by blast
qed

lemma cardinality_reach_auto:
  assumes "auto_well_defined \<A>"
  shows "card (states (reachable_automaton \<A>)) \<le> card (states \<A>)"
proof -
  have fin: "finite (states \<A>)" using assms unfolding auto_well_defined_def by blast
  have "states (reachable_automaton \<A>) \<subseteq> states \<A>" using assms reachable_states_are_states unfolding reachable_automaton_def by auto
  thus ?thesis using fin card_mono by blast
qed

theorem existence_smaller_distinguishable_auto: "auto_well_defined (\<A> :: ('s, 'a) automaton) \<and> DFA_property \<A> \<Longrightarrow> \<exists> smaller_\<A> :: ('s, 'a) automaton . auto_well_defined smaller_\<A> \<and> DFA_property smaller_\<A> \<and> alphabet smaller_\<A> = alphabet \<A> \<and> language_auto smaller_\<A> = language_auto \<A> \<and> card (states smaller_\<A>) \<le> card (states \<A>) \<and> distinguishable_automaton smaller_\<A>"
proof(induction "card (states \<A>)" arbitrary: \<A>)
  case 0 thus ?case unfolding auto_well_defined_def by auto
next
  case (Suc n)
  consider (case1) "distinguishable_automaton \<A>" | (case2) "\<not> distinguishable_automaton \<A>" by blast
  thus ?case
  proof cases
    case case1 thus ?thesis using Suc by blast
  next
    case case2
    then obtain s1 s2 where states: "s1 \<in> states \<A> \<and> s2 \<in> states \<A> \<and> equivalent_states s1 \<A> s2 \<and> s1 \<noteq> s2" unfolding distinguishable_automaton_def by blast
    let ?\<A> = "equivalent_states_automaton s1 \<A> s2"
    have props: "auto_well_defined ?\<A> \<and> DFA_property ?\<A> \<and> language_auto ?\<A> = language_auto \<A>" using Suc states well_def_equi_states_automaton DFA_property_equi_states_automaton equi_states_language_correctness by metis
    have finite: "finite (states \<A>)" using Suc unfolding auto_well_defined_def by blast 
    have "states ?\<A> = states \<A> - {s2} \<and> s2 \<in> states \<A>" using Suc states unfolding equivalent_states_automaton_def by auto
    hence "card (states ?\<A>) = card (states \<A>) - 1" using finite psubset_card_mono by auto
    hence card: "card (states ?\<A>) = n" using Suc by linarith
    hence card_smaller: "card (states ?\<A>) \<le> card (states \<A>)" using Suc by presburger
    have alpha: "alphabet ?\<A> = alphabet \<A>" unfolding equivalent_states_automaton_def by simp
    have "\<exists> \<A>_smaller :: ('s, 'a) automaton . auto_well_defined \<A>_smaller \<and> alphabet \<A>_smaller = alphabet ?\<A> \<and> DFA_property \<A>_smaller \<and> language_auto \<A>_smaller = language_auto ?\<A> \<and> card (states \<A>_smaller) \<le> card (states ?\<A>) \<and> distinguishable_automaton \<A>_smaller" using Suc props card by blast
    thus ?thesis using card_smaller props alpha by auto
  qed
qed

lemma reachable_auto_is_distinguishable:
  assumes "auto_well_defined \<A>" "distinguishable_automaton \<A>"
  shows "distinguishable_automaton (reachable_automaton \<A>)"
proof(rule ccontr)
  let ?\<A> = "reachable_automaton \<A>"
  assume "\<not> distinguishable_automaton ?\<A>"
  hence "\<exists> s1 s2 . s1 \<in> states ?\<A> \<and> s2 \<in> states ?\<A> \<and> equivalent_states s1 ?\<A> s2 \<and> s1 \<noteq> s2" unfolding distinguishable_automaton_def by blast
  then obtain s1 s2 where equi: "s1 \<in> states ?\<A> \<and> s2 \<in> states ?\<A> \<and> equivalent_states s1 ?\<A> s2 \<and> s1 \<noteq> s2" by blast
  hence states: "s1 \<in> states \<A> \<and> reachable_state s1 \<A> \<and> s2 \<in> states \<A> \<and> reachable_state s2 \<A> \<and> s1 \<noteq> s2" using assms reachable_states_are_states unfolding reachable_automaton_def reachable_states_def by auto
  {
    fix word assume assm: "\<exists> prun1 . pseudo_run_well_defined prun1 \<A> s1 word \<and> last prun1 \<in> accepting_states \<A>"
    hence "\<exists> prun1 . pseudo_run_well_defined prun1 ?\<A> s1 word \<and> last prun1 \<in> accepting_states ?\<A>" using assms states prun_reachable_automaton_right_acc by fast
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 ?\<A> s2 word \<and> last prun2 \<in> accepting_states ?\<A>" using equi unfolding equivalent_states_def by blast
    hence "\<exists> prun1 . pseudo_run_well_defined prun1 \<A> s2 word \<and> last prun1 \<in> accepting_states \<A>" using assms prun_reachable_automaton_left_acc by fast
  }
  hence left: "\<forall> word . (\<exists> prun1 . pseudo_run_well_defined prun1 \<A> s1 word \<and> last prun1 \<in> accepting_states \<A>) \<longrightarrow> (\<exists> prun2 . pseudo_run_well_defined prun2 \<A> s2 word \<and> last prun2 \<in> accepting_states \<A>)" by blast
  {
    fix word assume assm: "\<exists> prun1 . pseudo_run_well_defined prun1 \<A> s2 word \<and> last prun1 \<in> accepting_states \<A>"
    hence "\<exists> prun1 . pseudo_run_well_defined prun1 ?\<A> s2 word \<and> last prun1 \<in> accepting_states ?\<A>" using assms states prun_reachable_automaton_right_acc by fast
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 ?\<A> s1 word \<and> last prun2 \<in> accepting_states ?\<A>" using equi unfolding equivalent_states_def by blast
    hence "\<exists> prun1 . pseudo_run_well_defined prun1 \<A> s1 word \<and> last prun1 \<in> accepting_states \<A>" using assms prun_reachable_automaton_left_acc by fast
  }
  hence "equivalent_states s1 \<A> s2" using left unfolding equivalent_states_def by blast
  thus False using states assms unfolding distinguishable_automaton_def by blast
qed

lemma initial_states_comb_automaton_equi:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "language_auto \<A>1 = language_auto \<A>2"
  shows "equivalent_states_multi (initial_state \<A>1, 1) (union_automaton_multi \<A>1 \<A>2) (initial_state \<A>2, 2)"
proof -
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  {
    fix word assume "\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (initial_state \<A>1, 1) word \<and> last prun1 \<in> accepting_states_multi ?\<A>"
    hence "\<exists> prun1 . pseudo_run_well_defined prun1 \<A>1 (initial_state \<A>1) word \<and> last prun1 \<in> accepting_states \<A>1" using assms prun_comb_auto_A1 by fast
    hence "\<exists> run1 . run_well_defined run1 \<A>1 word \<and> last run1 \<in> accepting_states \<A>1" using assms unfolding run_well_defined_def by blast
    hence "\<exists> run2 . run_well_defined run2 \<A>2 word \<and> last run2 \<in> accepting_states \<A>2" using assms unfolding language_auto_def run_accepting_def by blast
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A>2 (initial_state \<A>2)  word \<and> last prun2 \<in> accepting_states \<A>2" using assms unfolding run_well_defined_def by blast
    hence "\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (initial_state \<A>2, 2) word \<and> last prun2 \<in> accepting_states_multi ?\<A>" using prun_A2_comb_auto by fast
  }
  hence left: "\<forall> word . (\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (initial_state \<A>1, 1) word \<and> last prun1 \<in> accepting_states_multi ?\<A>) \<longrightarrow> (\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (initial_state \<A>2, 2) word \<and> last prun2 \<in> accepting_states_multi ?\<A>)" by blast
  {
    fix word assume "\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (initial_state \<A>2, 2) word \<and> last prun1 \<in> accepting_states_multi ?\<A>"
    hence "\<exists> prun1 . pseudo_run_well_defined prun1 \<A>2 (initial_state \<A>2) word \<and> last prun1 \<in> accepting_states \<A>2" using assms prun_comb_auto_A2 by fast
    hence "\<exists> run1 . run_well_defined run1 \<A>2 word \<and> last run1 \<in> accepting_states \<A>2" using assms unfolding run_well_defined_def by blast
    hence "\<exists> run2 . run_well_defined run2 \<A>1 word \<and> last run2 \<in> accepting_states \<A>1" using assms unfolding language_auto_def run_accepting_def by blast
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A>1 (initial_state \<A>1)  word \<and> last prun2 \<in> accepting_states \<A>1" using assms unfolding run_well_defined_def by blast
    hence "\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (initial_state \<A>1, 1) word \<and> last prun2 \<in> accepting_states_multi ?\<A>" using prun_A1_comb_auto by fast
  }
  thus ?thesis using left unfolding equivalent_states_multi_def by blast
qed

lemma two_trans_one_state:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "(s1, a, s2) \<in> transitions \<A>" "(s1, a, s2') \<in> transitions \<A>"
  shows "s2 = s2'"
  using assms well_def_trans_components unfolding DFA_property_def by metis

lemma successors_comb_automaton_equi:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "DFA_property \<A>1" "DFA_property \<A>2" "(t1, a, s1) \<in> transitions \<A>1" "(t2, a, s2) \<in> transitions \<A>2" "equivalent_states_multi (t1, 1) (union_automaton_multi \<A>1 \<A>2) (t2, 2)"
  shows "equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)"
proof(rule ccontr)
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  have well_def: "auto_well_defined_multi ?\<A>" using assms union_auto_well_defined by blast
  assume assm: "\<not> equivalent_states_multi (s1, 1) ?\<A> (s2, 2)"
  have "cross_renaming_iso 1 t1 = (t1, 1) \<and> cross_renaming_iso 1 s1 = (s1, 1)" unfolding cross_renaming_iso_def by blast
  hence trans1: "((t1, 1), a, (s1, 1)) \<in> transitions_multi ?\<A>" using assms unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by force
  have "t1 \<in> states \<A>1" using assms well_def_trans_components by fast
  hence init1: "(t1, 1) \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" unfolding type_encode_automaton_def cross_renaming_iso_def by auto
  hence trans1': "((t1, 1), a, (s1, 1)) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms trans1 normal_trans_comb_auto_A1 by fast
  have "cross_renaming_iso 2 t2 = (t2, 2) \<and> cross_renaming_iso 2 s2 = (s2, 2)" unfolding cross_renaming_iso_def by blast
  hence trans2: "((t2, 2), a, (s2, 2)) \<in> transitions_multi ?\<A>" using assms unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by force
  have "t2 \<in> states \<A>2" using assms well_def_trans_components by fast
  hence init2: "(t2, 2) \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" unfolding type_encode_automaton_def cross_renaming_iso_def by auto
  hence trans2': "((t2, 2), a, (s2, 2)) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms trans2 normal_trans_comb_auto_A2 by fast
  have well_def1: "auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms cross_renaming_iso_automaton_auto_well_defined by blast
  have dfa1: "DFA_property (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms DFA_property_cross_renaming_iso_automaton by blast
  have well_def2: "auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by blast
  have dfa2: "DFA_property (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms DFA_property_cross_renaming_iso_automaton by blast
  {
    fix word assume assum: "\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (s1, 1) word \<and> last prun1 \<in> accepting_states_multi ?\<A>"
    hence "\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (s1, 1) word \<and> last prun1 \<in> accepting_states_multi ?\<A> \<and> prun1 ! 0 = (s1, 1)" unfolding pseudo_run_well_defined_multi_def by blast
    then obtain prun1 where prun1: "pseudo_run_well_defined_multi prun1 ?\<A> (s1, 1) word \<and> last prun1 \<in> accepting_states_multi ?\<A> \<and> prun1 ! 0 = (s1, 1)" by blast
    hence props: "pseudo_run_well_defined_multi ((t1, 1) # prun1) ?\<A> (t1, 1) (a # word) \<and> last prun1 \<in> accepting_states_multi ?\<A>" using well_def trans1 prun_well_defined_extension_cons_multi by fastforce
    have "prun1 \<noteq> []" using prun1 unfolding pseudo_run_well_defined_multi_def by force
    hence "last ((t1, 1) # prun1) \<in> accepting_states_multi ?\<A>" using props by auto
    hence "\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (t1, 1) (a # word) \<and> last prun1 \<in> accepting_states_multi ?\<A>" using props by blast
    hence "\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (t2, 2) (a # word) \<and> last prun2 \<in> accepting_states_multi ?\<A>" using assms unfolding equivalent_states_multi_def by blast
    then obtain prun2 where prun2: "pseudo_run_well_defined_multi prun2 ?\<A> (t2, 2) (a # word) \<and> last prun2 \<in> accepting_states_multi ?\<A>" by blast
    hence equi: "prun2 \<noteq> [] \<and> prun2 ! 0 = (t2, 2)" unfolding pseudo_run_well_defined_multi_def by force
    hence "prun2 ! 0 = (t2, 2) \<and> prun2 = (prun2 ! 0) # (tl prun2) \<and> (prun2 ! 0, a, (s2, 2)) \<in> transitions_multi ?\<A>" using list_properties_not_empty trans2 by metis
    hence props2: "pseudo_run_well_defined_multi ((prun2 ! 0) # (tl prun2)) ?\<A> (prun2 ! 0) (a # word) \<and> last prun2 \<in> accepting_states_multi ?\<A> \<and> (prun2 ! 0, a, (s2, 2)) \<in> transitions_multi ?\<A>" using prun2 by fastforce
    hence "length ((prun2 ! 0) # (tl prun2)) > 0" by force
    hence "(((prun2 ! 0) # (tl prun2)) ! 0, (a # word) ! 0, ((prun2 ! 0) # (tl prun2)) ! 1) \<in> transitions_multi ?\<A>" using props2 unfolding pseudo_run_well_defined_multi_def by force
    hence "(prun2 ! 0, a, (tl prun2) ! 0) \<in> transitions_multi ?\<A>" by simp
    hence "((t2, 2), a, (tl prun2) ! 0) \<in> transitions_multi ?\<A>" using equi by auto
    hence "((t2, 2), a, (tl prun2) ! 0) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms init2 normal_trans_comb_auto_A2 by fast     
    hence "(tl prun2) ! 0 = (s2, 2)" using well_def2 dfa2 trans2' two_trans_one_state by fast    
    hence props3: "pseudo_run_well_defined_multi (tl prun2) ?\<A> (s2, 2) word \<and> last prun2 \<in> accepting_states_multi ?\<A>" using well_def prun_well_defined_extension_cons_multi props2 by fastforce
    hence "(tl prun2) \<noteq> []" unfolding pseudo_run_well_defined_multi_def by force
    hence "last (tl prun2) \<in> accepting_states_multi ?\<A>" using props3 last_tl by metis    
    hence "\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (s2, 2) word \<and> last prun2 \<in> accepting_states_multi ?\<A>" using props3 by blast
  }
  hence left: "\<forall> word . (\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (s1, 1) word \<and> last prun1 \<in> accepting_states_multi ?\<A>) \<longrightarrow> (\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (s2, 2) word \<and> last prun2 \<in> accepting_states_multi ?\<A>)" by blast
  {
    fix word assume assum: "\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (s2, 2) word \<and> last prun2 \<in> accepting_states_multi ?\<A>"
    hence "\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (s2, 2) word \<and> last prun2 \<in> accepting_states_multi ?\<A> \<and> prun2 ! 0 = (s2, 2)" unfolding pseudo_run_well_defined_multi_def by blast
    then obtain prun2 where prun2: "pseudo_run_well_defined_multi prun2 ?\<A> (s2, 2) word \<and> last prun2 \<in> accepting_states_multi ?\<A> \<and> prun2 ! 0 = (s2, 2)" by blast
    hence props: "pseudo_run_well_defined_multi ((t2, 2) # prun2) ?\<A> (t2, 2) (a # word) \<and> last prun2 \<in> accepting_states_multi ?\<A>" using well_def trans2 prun_well_defined_extension_cons_multi by fastforce
    have "prun2 \<noteq> []" using prun2 unfolding pseudo_run_well_defined_multi_def by force
    hence "last ((t2, 2) # prun2) \<in> accepting_states_multi ?\<A>" using props by auto
    hence "\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (t2, 2) (a # word) \<and> last prun2 \<in> accepting_states_multi ?\<A>" using props by blast
    hence "\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (t1, 1) (a # word) \<and> last prun1 \<in> accepting_states_multi ?\<A>" using assms unfolding equivalent_states_multi_def by blast
    then obtain prun1 where prun1: "pseudo_run_well_defined_multi prun1 ?\<A> (t1, 1) (a # word) \<and> last prun1 \<in> accepting_states_multi ?\<A>" by blast
    hence equi: "prun1 \<noteq> [] \<and> prun1 ! 0 = (t1, 1)" unfolding pseudo_run_well_defined_multi_def by force
    hence "prun1 ! 0 = (t1, 1) \<and> prun1 = (prun1 ! 0) # (tl prun1) \<and> (prun1 ! 0, a, (s1, 1)) \<in> transitions_multi ?\<A>" using list_properties_not_empty trans1 by metis
    hence props2: "pseudo_run_well_defined_multi ((prun1 ! 0) # (tl prun1)) ?\<A> (prun1 ! 0) (a # word) \<and> last prun1 \<in> accepting_states_multi ?\<A> \<and> (prun1 ! 0, a, (s1, 1)) \<in> transitions_multi ?\<A>" using prun1 by fastforce
    hence "length ((prun1 ! 0) # (tl prun1)) > 0" by force
    hence "(((prun1 ! 0) # (tl prun1)) ! 0, (a # word) ! 0, ((prun1 ! 0) # (tl prun1)) ! 1) \<in> transitions_multi ?\<A>" using props2 unfolding pseudo_run_well_defined_multi_def by force
    hence "(prun1 ! 0, a, (tl prun1) ! 0) \<in> transitions_multi ?\<A>" by simp
    hence "((t1, 1), a, (tl prun1) ! 0) \<in> transitions_multi ?\<A>" using equi by auto
    hence "((t1, 1), a, (tl prun1) ! 0) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms init1 normal_trans_comb_auto_A1 by fast     
    hence "(tl prun1) ! 0 = (s1, 1)" using well_def1 dfa1 trans1' two_trans_one_state by fast    
    hence props3: "pseudo_run_well_defined_multi (tl prun1) ?\<A> (s1, 1) word \<and> last prun1 \<in> accepting_states_multi ?\<A>" using well_def prun_well_defined_extension_cons_multi props2 by fastforce
    hence "(tl prun1) \<noteq> []" unfolding pseudo_run_well_defined_multi_def by force
    hence "last (tl prun1) \<in> accepting_states_multi ?\<A>" using props3 last_tl by metis    
    hence "\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (s1, 1) word \<and> last prun1 \<in> accepting_states_multi ?\<A>" using props3 by blast
  }
  thus False using assm left unfolding equivalent_states_multi_def by blast
qed

lemma reachable_states_automaton_equi:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "DFA_property \<A>1" "DFA_property \<A>2" "language_auto \<A>1 = language_auto \<A>2"
  shows "run_well_defined run1 \<A>1 word \<and> run_well_defined run2 \<A>2 word \<Longrightarrow> equivalent_states_multi (last run1, 1) (union_automaton_multi \<A>1 \<A>2) (last run2, 2)"
proof(induction word arbitrary: run1 run2 rule: rev_induct)
  case Nil
  hence "length run1 = 1 \<and> length run2 = 1 \<and> (run1 ! 0) = initial_state \<A>1 \<and> (run2 ! 0) = initial_state \<A>2" unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence "run1 = [initial_state \<A>1] \<and> run2 = [initial_state \<A>2]" using list_with_one_element by fast
  hence "last run1 = initial_state \<A>1 \<and> last run2 = initial_state \<A>2" by auto
  thus ?case using assms initial_states_comb_automaton_equi by fastforce
next
  case (snoc a word)
  hence "run1 \<noteq> [] \<and> run2 \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain run1' run2' where "run1 = run1' @ [last run1] \<and> run2 = run2' @ [last run2]" using append_butlast_last_id by metis
  hence "run_well_defined (run1' @ [last run1]) \<A>1 (word @ [a]) \<and> run_well_defined (run2' @ [last run2]) \<A>2 (word @ [a])" using snoc by auto
  hence "run_well_defined run1' \<A>1 word \<and> (last run1', a, last run1) \<in> transitions \<A>1 \<and> run_well_defined run2' \<A>2 word \<and> (last run2', a, last run2) \<in> transitions \<A>2" using prun_well_defined_extension_snoc assms unfolding run_well_defined_def by metis
  hence "equivalent_states_multi (last run1', 1) (union_automaton_multi \<A>1 \<A>2) (last run2', 2) \<and> (last run1', a, last run1) \<in> transitions \<A>1 \<and> (last run2', a, last run2) \<in> transitions \<A>2" using snoc by blast
  thus ?case using successors_comb_automaton_equi assms by fast
qed

proposition connected_automaton_equi_states_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "DFA_property \<A>1" "DFA_property \<A>2" "connected_automaton \<A>1" "connected_automaton \<A>2" "language_auto \<A>1 = language_auto \<A>2" "alphabet \<A>1 = alphabet \<A>2"
  shows "\<forall> s1 \<in> states \<A>1 . \<exists> s2 \<in> states \<A>2 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)"
proof - 
  have "\<forall> s1 \<in> states \<A>1 . reachable_state s1 \<A>1" using assms unfolding connected_automaton_def by blast
  hence reach: "\<forall> s1 \<in> states \<A>1 . \<exists> word run . run_well_defined run \<A>1 word \<and> last run = s1" unfolding reachable_state_def by blast
  {
    fix s1 assume "s1 \<in> states \<A>1"
    hence "\<exists> word run . run_well_defined run \<A>1 word \<and> last run = s1" using reach by blast
    then obtain word run where run: "run_well_defined run \<A>1 word \<and> last run = s1" by blast
    hence "word_well_defined word (alphabet \<A>1)" using assms well_def_implies_word_well_defined unfolding run_well_defined_def by fast
    hence "word_well_defined word (alphabet \<A>2)" using assms unfolding word_well_defined_def by blast
    hence "\<exists> run . run_well_defined run \<A>2 word" using assms exists_only_one_run_for_DFA by fast
    then obtain run' where run': "run_well_defined run' \<A>2 word" by blast
    hence last: "last run' \<in> states \<A>2" using assms last_of_prun_is_state unfolding run_well_defined_def by fast
    hence "equivalent_states_multi (last run, 1) (union_automaton_multi \<A>1 \<A>2) (last run', 2)" using assms run run' reachable_states_automaton_equi by blast
    hence "\<exists> s2 \<in> states \<A>2 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using run last by auto
  }
  thus ?thesis by blast
qed

proposition connected_automaton_equi_states_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "DFA_property \<A>1" "DFA_property \<A>2" "connected_automaton \<A>1" "connected_automaton \<A>2" "language_auto \<A>1 = language_auto \<A>2" "alphabet \<A>1 = alphabet \<A>2"
  shows "\<forall> s2 \<in> states \<A>2 . \<exists> s1 \<in> states \<A>1 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)"
proof - 
  have "\<forall> s2 \<in> states \<A>2 . reachable_state s2 \<A>2" using assms unfolding connected_automaton_def by blast
  hence reach: "\<forall> s2 \<in> states \<A>2 . \<exists> word run . run_well_defined run \<A>2 word \<and> last run = s2" unfolding reachable_state_def by blast
  {
    fix s2 assume "s2 \<in> states \<A>2"
    hence "\<exists> word run . run_well_defined run \<A>2 word \<and> last run = s2" using reach by blast
    then obtain word run where run: "run_well_defined run \<A>2 word \<and> last run = s2" by blast
    hence "word_well_defined word (alphabet \<A>2)" using assms well_def_implies_word_well_defined unfolding run_well_defined_def by fast
    hence "word_well_defined word (alphabet \<A>1)" using assms unfolding word_well_defined_def by blast
    hence "\<exists> run . run_well_defined run \<A>1 word" using assms exists_only_one_run_for_DFA by fast
    then obtain run' where run': "run_well_defined run' \<A>1 word" by blast
    hence last: "last run' \<in> states \<A>1" using assms last_of_prun_is_state unfolding run_well_defined_def by fast
    hence "equivalent_states_multi (last run', 1) (union_automaton_multi \<A>1 \<A>2) (last run, 2)" using assms run run' reachable_states_automaton_equi by blast
    hence "\<exists> s1 \<in> states \<A>1 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using run last by auto
  }
  thus ?thesis by blast
qed

lemma existence_states_pigeonhole:
  assumes "finite (states \<A>1)" "finite (states \<A>m)" "card (states \<A>m) < card (states \<A>1)" "\<forall> s1 \<in> states \<A>1 . \<exists> s2 \<in> states \<A>m . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>m) (s2, 2)"
  shows "\<exists> s1 s2 s3. s1 \<in> states \<A>1 \<and> s2 \<in> states \<A>1 \<and> s3 \<in> states \<A>m \<and> s1 \<noteq> s2 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>m) (s3, 2) \<and> equivalent_states_multi (s2, 1) (union_automaton_multi \<A>1 \<A>m) (s3, 2)"
proof -
  obtain f where f: "\<forall> s1 \<in> states \<A>1 . f s1 \<in> states \<A>m \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>m) (f s1, 2)" using assms by metis
  hence "image f (states \<A>1) \<subseteq> states \<A>m" by blast
  hence "card (image f (states \<A>1)) \<le> card (states \<A>m)" using assms card_mono by metis
  hence "card (image f (states \<A>1)) < card (states \<A>1)" using assms by auto
  then obtain s1 s2 where states: "s1 \<in> states \<A>1 \<and> s2 \<in> states \<A>1 \<and> s1 \<noteq> s2 \<and> f s1 = f s2" using pigeonhole unfolding inj_on_def by blast
  hence "f s1 \<in> states \<A>m \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>m) (f s1, 2) \<and> equivalent_states_multi (s2, 1) (union_automaton_multi \<A>1 \<A>m) (f s2, 2)" using f by blast
  thus ?thesis using states by auto
qed

proposition minimality_property_right: 
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)" "DFA_property \<A>" "connected_automaton \<A>" "distinguishable_automaton \<A>"
  shows "minimal_DFA_property \<A>"
proof(rule ccontr)
  assume "\<not> minimal_DFA_property \<A>"
  hence "\<not> (auto_well_defined \<A> \<and> DFA_property \<A> \<and> (\<nexists> \<A>_minimal :: ('s, 'a) automaton . auto_well_defined \<A>_minimal \<and> alphabet \<A>_minimal = alphabet \<A> \<and> DFA_property \<A>_minimal \<and> language_auto \<A>_minimal = language_auto \<A> \<and> card (states \<A>_minimal) < card (states \<A>)))" unfolding minimal_DFA_property_def by blast
  hence "\<exists> \<A>_minimal :: ('s, 'a) automaton . auto_well_defined \<A>_minimal \<and> alphabet \<A>_minimal = alphabet \<A> \<and> DFA_property \<A>_minimal \<and> language_auto \<A>_minimal = language_auto \<A> \<and> card (states \<A>_minimal) < card (states \<A>)" using assms by blast
  then obtain \<A>_small :: "('s, 'a) automaton" where Asmall: "auto_well_defined \<A>_small \<and> alphabet \<A>_small = alphabet \<A> \<and> DFA_property \<A>_small \<and> language_auto \<A>_small = language_auto \<A> \<and> card (states \<A>_small) < card (states \<A>)" by blast
  hence "\<exists> \<A>_smaller :: ('s, 'a) automaton . auto_well_defined \<A>_smaller \<and> alphabet \<A>_smaller = alphabet \<A>_small \<and> DFA_property \<A>_smaller \<and> language_auto \<A>_smaller = language_auto \<A>_small \<and> card (states \<A>_smaller) \<le> card (states \<A>_small) \<and> distinguishable_automaton \<A>_smaller" using existence_smaller_distinguishable_auto by blast
  hence "\<exists> \<A>_smaller :: ('s, 'a) automaton . auto_well_defined \<A>_smaller \<and> alphabet \<A>_smaller = alphabet \<A> \<and> DFA_property \<A>_smaller \<and> language_auto \<A>_smaller = language_auto \<A> \<and> card (states \<A>_smaller) < card (states \<A>) \<and> distinguishable_automaton \<A>_smaller" using Asmall by auto
  then obtain \<A>_smaller :: "('s, 'a) automaton" where Asmaller: "auto_well_defined \<A>_smaller \<and> alphabet \<A>_smaller = alphabet \<A> \<and> DFA_property \<A>_smaller \<and> language_auto \<A>_smaller = language_auto \<A> \<and> card (states \<A>_smaller) < card (states \<A>) \<and> distinguishable_automaton \<A>_smaller" by blast  
  let ?\<A>_mini = "reachable_automaton \<A>_smaller"
  have well_def: "auto_well_defined ?\<A>_mini" using Asmaller well_def_reachable_automaton by blast
  have dfa: "DFA_property ?\<A>_mini" using Asmaller DFA_property_reachable_automaton by blast
  have lang: "language_auto ?\<A>_mini = language_auto \<A>" using Asmaller reachable_automaton_language_correctness by blast
  have con: "connected_automaton ?\<A>_mini" using Asmaller reachable_automaton_connected by fast
  have card: "card (states ?\<A>_mini) < card (states \<A>)" using Asmaller cardinality_reach_auto by fastforce
  have alpha: "alphabet ?\<A>_mini = alphabet \<A>" using Asmaller unfolding reachable_automaton_def by simp
  have "distinguishable_automaton ?\<A>_mini" using Asmaller reachable_auto_is_distinguishable by blast
  hence Amini: "auto_well_defined ?\<A>_mini \<and> alphabet ?\<A>_mini = alphabet \<A> \<and> DFA_property ?\<A>_mini \<and> language_auto ?\<A>_mini = language_auto \<A> \<and> card (states ?\<A>_mini) < card (states \<A>) \<and> connected_automaton ?\<A>_mini \<and> distinguishable_automaton ?\<A>_mini" using well_def dfa lang con card alpha by blast
  have fin: "finite (states \<A>) \<and> finite (states ?\<A>_mini)" using assms Amini unfolding auto_well_defined_def by fast
  have "\<forall> s1 \<in> states \<A> . \<exists> s2 \<in> states ?\<A>_mini . equivalent_states_multi (s1, 1) (union_automaton_multi \<A> ?\<A>_mini) (s2, 2)" using assms Amini connected_automaton_equi_states_A1 by metis
  hence "\<exists> s1 s2 s3. s1 \<in> states \<A> \<and> s2 \<in> states \<A> \<and> s3 \<in> states ?\<A>_mini \<and> s1 \<noteq> s2 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A> ?\<A>_mini) (s3, 2) \<and> equivalent_states_multi (s2, 1) (union_automaton_multi \<A> ?\<A>_mini) (s3, 2)" using card fin existence_states_pigeonhole by fastforce
  then obtain s1 s2 s3 where states: "s1 \<in> states \<A> \<and> s2 \<in> states \<A> \<and> s3 \<in> states ?\<A>_mini \<and> s1 \<noteq> s2 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A> ?\<A>_mini) (s3, 2) \<and> equivalent_states_multi (s2, 1) (union_automaton_multi \<A> ?\<A>_mini) (s3, 2)" by blast
  hence "s1 \<noteq> s2 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A> ?\<A>_mini) (s2, 1)" using equivalent_states_symmetry_multi equivalent_states_transitivity_multi by fast 
  hence "s1 \<noteq> s2 \<and> equivalent_states s1 \<A> s2" using assms Amini equivalent_states_comb_to_solo_A1 by metis
  thus False using assms states unfolding distinguishable_automaton_def by blast
qed

text \<open>Key Theorem: equivalence of minimal_DFA_property\<close>
theorem minimal_DFA_property_iff_connected_and_distinguishable:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "minimal_DFA_property \<A> \<longleftrightarrow> connected_automaton \<A> \<and> distinguishable_automaton \<A>"
  using assms minimality_property_right minimality_property_left by blast

lemma prun_minimization_left:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined prun (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))) S (rev word) \<and> s \<in> last prun" "S \<in> states (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))"
  shows "\<exists> prun' . pseudo_run_well_defined prun' \<A> s word \<and> last prun' \<in> S"
proof -
  have props: "pseudo_run_well_defined prun (powerset_automaton_multi (reversal_nfa \<A>)) S (rev word) \<and> s \<in> last prun" using assms prun_reachable_automaton reversal_preserves_well_defined well_def_powerset_automaton_multi states_of_reachable_automaton by fast
  hence "last prun \<noteq> {}" by blast
  hence "\<exists> prun' . \<exists> s' \<in> S . pseudo_run_well_defined_multi prun' (reversal_nfa \<A>) s' (rev word) \<and> last prun' = s" using props powerset_prun_right_multi assms reversal_preserves_well_defined by blast
  then obtain prun' s' where prun': "s' \<in> S \<and> pseudo_run_well_defined_multi prun' (reversal_nfa \<A>) s' (rev word) \<and> last prun' = s" by blast
  hence "s' = prun' ! 0 \<and> prun' \<noteq> []" unfolding pseudo_run_well_defined_multi_def by force
  hence "s' = prun' ! 0 \<and> s' = last (rev prun') \<and> s = ((rev prun') ! 0)" using prun' rev_simplifier by metis
  hence "pseudo_run_well_defined (rev prun') \<A> s word \<and> last (rev prun') \<in> S" using assms prun' prun_on_rev_automaton by fastforce
  thus ?thesis by fast
qed

lemma prun_minimization_right:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined prun \<A> s word \<and> last prun \<in> S" "S \<in> states (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))"
  shows "\<exists> pRun . pseudo_run_well_defined pRun (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))) S (rev word) \<and> s \<in> last pRun"
proof -
  have "s = prun ! 0 \<and> prun \<noteq> []" using assms unfolding pseudo_run_well_defined_def by fastforce
  hence "s = prun ! 0 \<and> last (rev prun) = s \<and> (rev prun ! 0) \<in> S" using assms rev_simplifier by metis
  hence props: "pseudo_run_well_defined_multi (rev prun) (reversal_nfa \<A>) (rev prun ! 0) (rev word) \<and> last (rev prun) = s \<and> (rev prun ! 0) \<in> S" using assms prun_on_rev_automaton by blast
  hence "S \<in> states (powerset_automaton_multi (reversal_nfa \<A>)) \<and> (rev prun ! 0) \<in> S" using assms states_of_reachable_automaton reversal_preserves_well_defined well_def_powerset_automaton_multi by fast
  hence "\<exists> pRun . pseudo_run_well_defined pRun (powerset_automaton_multi (reversal_nfa \<A>)) S (rev word) \<and> s \<in> last pRun" using props powerset_prun_left_multi assms reversal_preserves_well_defined well_def_powerset_automaton_multi by fast
  then obtain pRun where pRun: "pseudo_run_well_defined pRun (powerset_automaton_multi (reversal_nfa \<A>)) S (rev word) \<and> s \<in> last pRun" by blast
  have "reachable_state S (powerset_automaton_multi (reversal_nfa \<A>))" using assms unfolding reachable_automaton_def reachable_states_def by auto
  hence "pseudo_run_well_defined pRun (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))) S (rev word) \<and> s \<in> last pRun" using pRun assms prun_reachable_automaton reversal_preserves_well_defined well_def_powerset_automaton_multi by fast
  thus ?thesis by blast
qed

proposition prun_minimization:
  assumes "auto_well_defined \<A>" "S \<in> states (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))"
  shows "(\<exists> prun . pseudo_run_well_defined prun \<A> s word \<and> last prun \<in> S) \<longleftrightarrow> (\<exists> pRun . pseudo_run_well_defined pRun (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))) S (rev word) \<and> s \<in> last pRun)"
  using assms prun_minimization_left prun_minimization_right by fast

lemma accepting_states_initial_state_mini_left:
  assumes "S \<in> accepting_states (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))"
  shows "initial_state \<A> \<in> S"
proof - 
  have "S \<in> accepting_states (powerset_automaton_multi (reversal_nfa \<A>))" using assms unfolding reachable_automaton_def by auto
  hence "\<exists> s \<in> S . s \<in> accepting_states_multi (reversal_nfa \<A>)" using acc_states_powerset_automaton2_multi by blast
  then obtain s where "s \<in> S \<and> s \<in> accepting_states_multi (reversal_nfa \<A>)" by blast
  thus ?thesis unfolding reversal_nfa_def by force
qed

lemma accepting_states_initial_state_mini_right:
  assumes "auto_well_defined \<A>" "initial_state \<A> \<in> S" "S \<in> states (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))"
  shows "S \<in> accepting_states (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))"
proof - 
  have state: "S \<in> states (powerset_automaton_multi (reversal_nfa \<A>))" using assms states_of_reachable_automaton reversal_preserves_well_defined states_of_reachable_automaton well_def_powerset_automaton_multi unfolding reachable_automaton_def by fast
  have "initial_state \<A> \<in> accepting_states_multi (reversal_nfa \<A>)" using assms unfolding reversal_nfa_def by force
  hence "S \<in> accepting_states (powerset_automaton_multi (reversal_nfa \<A>))" using assms state acc_states_powerset_automaton1_multi unfolding powerset_automaton_multi_def by auto
  thus ?thesis using assms unfolding reachable_automaton_def by force
qed

proposition accepting_states_initial_state_mini:
  assumes "auto_well_defined \<A>" "S \<in> states (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))"
  shows "initial_state \<A> \<in> S \<longleftrightarrow> S \<in> accepting_states (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))"
  using assms accepting_states_initial_state_mini_left accepting_states_initial_state_mini_right by blast

theorem distiniguishability_brz_algo:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "connected_automaton \<A>"
  shows "distinguishable_automaton (reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>)))"
proof(rule ccontr)
  let ?\<A> = "reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))"
  have well_def: "auto_well_defined ?\<A>" using assms reversal_preserves_well_defined well_def_powerset_automaton_multi well_def_reachable_automaton by blast
  have connected: "connected_automaton ?\<A>" using assms reachable_automaton_connected reversal_preserves_well_defined well_def_powerset_automaton_multi by blast
  assume "\<not> distinguishable_automaton ?\<A>"
  hence "\<exists> s1 s2 . s1 \<in> states ?\<A> \<and> s2 \<in> states ?\<A> \<and> equivalent_states s1 ?\<A> s2 \<and> s1 \<noteq> s2" unfolding distinguishable_automaton_def by blast
  then obtain s1 s2 where equi: "s1 \<in> states ?\<A> \<and> s2 \<in> states ?\<A> \<and> equivalent_states s1 ?\<A> s2 \<and> s1 \<noteq> s2" by presburger
  hence "\<forall> word . (\<exists> prun1 . pseudo_run_well_defined prun1 ?\<A> s1 word \<and> last prun1 \<in> accepting_states ?\<A>) \<longleftrightarrow> (\<exists> prun2 . pseudo_run_well_defined prun2 ?\<A> s2 word \<and> last prun2 \<in> accepting_states ?\<A>)" unfolding equivalent_states_def by auto
  hence "\<forall> word . (\<exists> prun1 . pseudo_run_well_defined prun1 ?\<A> s1 word \<and> initial_state \<A> \<in> last prun1) \<longleftrightarrow> (\<exists> prun2 . pseudo_run_well_defined prun2 ?\<A> s2 word \<and> initial_state \<A> \<in> last prun2)" using assms accepting_states_initial_state_mini well_def last_of_prun_is_state by fast
  hence "\<forall> word . (\<exists> prun1 . pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (rev word) \<and> last prun1 \<in> s1) \<longleftrightarrow> (\<exists> prun2 . pseudo_run_well_defined prun2 \<A> (initial_state \<A>) (rev word) \<and> last prun2 \<in> s2)" using assms by (simp add: prun_minimization equi)
  hence "\<forall> word . (\<exists> run1 . run_well_defined run1 \<A> (rev word) \<and> last run1 \<in> s1) \<longleftrightarrow> (\<exists> run2 . run_well_defined run2 \<A> (rev word) \<and> last run2 \<in> s2)" unfolding run_well_defined_def by blast
  hence condition: "\<forall> word . (\<exists> run1 . run_well_defined run1 \<A> word \<and> last run1 \<in> s1) \<longleftrightarrow> (\<exists> run2 . run_well_defined run2 \<A> word \<and> last run2 \<in> s2)" using rev_swap by metis
  {
    fix s assume assm: "s \<in> s1"
    have "s1 \<in> states (powerset_automaton_multi (reversal_nfa \<A>))" using equi assms states_of_reachable_automaton reversal_preserves_well_defined states_of_reachable_automaton well_def_powerset_automaton_multi unfolding reachable_automaton_def by fast
    hence "s \<in> states_multi (reversal_nfa \<A>)" using assm states_of_powerset_automaton_multi by fast
    hence "s \<in> states \<A>" unfolding reversal_nfa_def by force
    hence "reachable_state s \<A>" using assms unfolding connected_automaton_def by blast
    then obtain word run where run: "run_well_defined run \<A> word \<and> last run = s" unfolding reachable_state_def by blast
    then obtain run' where run': "run_well_defined run' \<A> word \<and> last run' \<in> s2" using assm condition by blast
    hence "word_well_defined word (alphabet \<A>)" using assms well_def_implies_word_well_defined unfolding run_well_defined_def by fast
    hence "run = run'" using assms run run' exists_only_one_run_for_DFA by blast
    hence "s \<in> s2" using run run' by blast
  }
  hence left: "s1 \<subseteq> s2" by blast
  {
    fix s assume assm: "s \<in> s2"
    have "s2 \<in> states (powerset_automaton_multi (reversal_nfa \<A>))" using equi assms states_of_reachable_automaton reversal_preserves_well_defined states_of_reachable_automaton well_def_powerset_automaton_multi unfolding reachable_automaton_def by fast
    hence "s \<in> states_multi (reversal_nfa \<A>)" using assm states_of_powerset_automaton_multi by fast
    hence "s \<in> states \<A>" unfolding reversal_nfa_def by force
    hence "reachable_state s \<A>" using assms unfolding connected_automaton_def by blast
    then obtain word run where run: "run_well_defined run \<A> word \<and> last run = s" unfolding reachable_state_def by blast
    then obtain run' where run': "run_well_defined run' \<A> word \<and> last run' \<in> s1" using assm condition by blast
    hence "word_well_defined word (alphabet \<A>)" using assms well_def_implies_word_well_defined unfolding run_well_defined_def by fast
    hence "run = run'" using assms run run' exists_only_one_run_for_DFA by blast
    hence "s \<in> s1" using run run' by blast
  }
  hence "s1 = s2" using left by blast
  thus False using equi by blast
qed

text \<open>Main theorem for Brzozowki's algorithm\<close>
theorem brz_algo_correctness:
  assumes "auto_well_defined \<A>"
  shows "minimal_DFA_property (minimal_DFA_brz \<A>) \<and> language_auto \<A> = language_auto (minimal_DFA_brz \<A>) \<and> alphabet \<A> = alphabet (minimal_DFA_brz \<A>)"
proof - 
  let ?\<A> = "reachable_automaton (powerset_automaton_multi (reversal_nfa \<A>))"
  have well_def: "auto_well_defined ?\<A>" using assms reversal_preserves_well_defined well_def_powerset_automaton_multi well_def_reachable_automaton by blast
  have dfa: "DFA_property ?\<A>" using DFA_property_reachable_automaton DFA_property_powerset_automaton_multi assms reversal_preserves_well_defined well_def_powerset_automaton_multi by blast
  have "connected_automaton ?\<A>" using assms reachable_automaton_connected reversal_preserves_well_defined well_def_powerset_automaton_multi by blast
  hence dist: "distinguishable_automaton (minimal_DFA_brz \<A>)" using well_def dfa distiniguishability_brz_algo unfolding minimal_DFA_brz_def by blast
  have well_def_brz: "auto_well_defined (minimal_DFA_brz \<A>)" using well_def reversal_preserves_well_defined well_def_powerset_automaton_multi well_def_reachable_automaton unfolding minimal_DFA_brz_def by blast 
  have dfa_brz: "DFA_property (minimal_DFA_brz \<A>)" using DFA_property_reachable_automaton DFA_property_powerset_automaton_multi well_def reversal_preserves_well_defined well_def_powerset_automaton_multi unfolding minimal_DFA_brz_def by blast
  have "connected_automaton (minimal_DFA_brz \<A>)" using well_def reachable_automaton_connected reversal_preserves_well_defined well_def_powerset_automaton_multi unfolding minimal_DFA_brz_def by blast
  thus ?thesis using assms well_def_brz dfa_brz dist minimal_DFA_property_iff_connected_and_distinguishable minimal_DFA_language_correctness minimal_DFA_alphabet by metis
qed

corollary existence_min_dfa:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)"
  shows "\<exists> min_DFA_\<A> :: (('s states) states, 'a) automaton . minimal_DFA_property min_DFA_\<A> \<and> language_auto \<A> = language_auto min_DFA_\<A> \<and> alphabet \<A> = alphabet min_DFA_\<A>"
  using assms brz_algo_correctness by auto



text \<open>Uniqueness up to soft-isomorphy of minimal DFA:\<close>
lemma iso_auto_connected:
  assumes "auto_well_defined \<A>1" "connected_automaton \<A>1" "isomorphic_automata \<A>1 \<A>2"
  shows "connected_automaton \<A>2"
proof -
  have props: "\<forall> s \<in> states \<A>1 . (\<exists> word run . run_well_defined run \<A>1 word \<and> last run = s)" using assms unfolding connected_automaton_def reachable_state_def by auto
  {
    fix s assume assm: "s \<in> states \<A>2"
    then obtain f h where fh: "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms unfolding isomorphic_automata_def by presburger
    hence impl: "(\<forall> prun word s . pseudo_run_well_defined prun \<A>1 s word \<longrightarrow> pseudo_run_well_defined (map f prun) \<A>2 (f s) (map h word)) \<and> (\<forall> prun word s . pseudo_run_well_defined prun \<A>2 s word \<longrightarrow> pseudo_run_well_defined (map (inv_into (states \<A>1) f) prun) \<A>1 (inv_into (states \<A>1) f s) (map (inv_into (alphabet \<A>1) h) word))" using assms iso_prun_correct by metis
    then obtain s' where s': "s' \<in> states \<A>1 \<and> f s' = s" using assm fh bij_exist by metis
    then obtain word run where "run_well_defined run \<A>1 word \<and> last run = s'" using props by fast
    hence "pseudo_run_well_defined run \<A>1 (initial_state \<A>1) word \<and> last run = s'" unfolding run_well_defined_def by auto
    hence "pseudo_run_well_defined (map f run) \<A>2 (initial_state \<A>2) (map h word) \<and> last run = s'" using fh impl by metis
    hence run: "run_well_defined (map f run) \<A>2 (map h word) \<and> last run = s'" unfolding run_well_defined_def by auto
    hence "run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
    hence "last (map f run) = f (last run)" using last_map by auto
    hence "run_well_defined (map f run) \<A>2 (map h word) \<and> last (map f run) = s" using s' run by auto
    hence "reachable_state s \<A>2" unfolding reachable_state_def by blast
  }
  thus ?thesis using connected_automaton_def by blast
qed

lemma iso_auto_distinguishable:
  assumes "auto_well_defined \<A>1" "distinguishable_automaton \<A>1" "isomorphic_automata \<A>1 \<A>2"
  shows "distinguishable_automaton \<A>2"
proof(rule ccontr)
  have well_def: "auto_well_defined \<A>2" using assms iso_preserves_auto_well_defined by fast
  have props: "\<nexists> s1 s2 . s1 \<in> states \<A>1 \<and> s2 \<in> states \<A>1 \<and> equivalent_states s1 \<A>1 s2 \<and> s1 \<noteq> s2" using assms unfolding distinguishable_automaton_def by auto
  assume "\<not> distinguishable_automaton \<A>2"
  hence "\<exists> s1 s2 . s1 \<in> states \<A>2 \<and> s2 \<in> states \<A>2 \<and> equivalent_states s1 \<A>2 s2 \<and> s1 \<noteq> s2" unfolding distinguishable_automaton_def by auto
  then obtain s1 s2 where states: "s1 \<in> states \<A>2 \<and> s2 \<in> states \<A>2 \<and> equivalent_states s1 \<A>2 s2 \<and> s1 \<noteq> s2" by blast
  then obtain f h where fh: "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms unfolding isomorphic_automata_def by presburger
  hence impl: "(\<forall> prun word s . pseudo_run_well_defined prun \<A>1 s word \<longrightarrow> pseudo_run_well_defined (map f prun) \<A>2 (f s) (map h word)) \<and> (\<forall> prun word s . pseudo_run_well_defined prun \<A>2 s word \<longrightarrow> pseudo_run_well_defined (map (inv_into (states \<A>1) f) prun) \<A>1 (inv_into (states \<A>1) f s) (map (inv_into (alphabet \<A>1) h) word))" using assms iso_prun_correct by metis
  then obtain s1' where s1': "s1' \<in> states \<A>1 \<and> f s1' = s1" using states fh bij_exist by metis
  then obtain s2' where s2': "s2' \<in> states \<A>1 \<and> f s2' = s2" using states bij_exist fh by metis
  hence not_equi: "s2' \<noteq> s1'" using states s1' by blast
  {
    fix word assume "\<exists> prun1 . pseudo_run_well_defined prun1 \<A>1 s1' word \<and> last prun1 \<in> accepting_states \<A>1"
    then obtain prun1 where pr1: "pseudo_run_well_defined prun1 \<A>1 s1' word \<and> last prun1 \<in> accepting_states \<A>1" by auto
    hence word_well: "word_well_defined word (alphabet \<A>1)" using assms well_def_implies_word_well_defined by fast
    have prun1: "pseudo_run_well_defined (map f prun1) \<A>2 (f s1') (map h word) \<and> last prun1 \<in> accepting_states \<A>1" using impl pr1 by blast
    hence "prun1 \<noteq> []" unfolding pseudo_run_well_defined_def by force
    hence "last (map f prun1) = f (last prun1)" using last_map by blast
    hence "pseudo_run_well_defined (map f prun1) \<A>2 s1 (map h word) \<and> last (map f prun1) \<in> accepting_states \<A>2" using s1' prun1 fh by fast
    then obtain prun2 where "pseudo_run_well_defined prun2 \<A>2 s2 (map h word) \<and> last prun2 \<in> accepting_states \<A>2" using states unfolding equivalent_states_def by blast
    hence prun2: "pseudo_run_well_defined (map (inv_into (states \<A>1) f) prun2) \<A>1 (inv_into (states \<A>1) f s2) (map (inv_into (alphabet \<A>1) h) (map h word)) \<and> last prun2 \<in> accepting_states \<A>2" using impl by blast
    hence "prun2 \<noteq> []" unfolding pseudo_run_well_defined_def by force
    hence equi: "last (map (inv_into (states \<A>1) f) prun2) = (inv_into (states \<A>1) f) (last prun2)" using last_map by blast
    have "accepting_states \<A>1 \<subseteq> states \<A>1 \<and> accepting_states \<A>2 \<subseteq> states \<A>2" using assms well_def unfolding auto_well_defined_def by argo
    hence "image (inv_into (states \<A>1) f) (accepting_states \<A>2) = accepting_states \<A>1" using fh bij_betw_imp_surj_on bij_betw_inv_into_subset by metis
    hence in_acc: "last (map (inv_into (states \<A>1) f) prun2) \<in> accepting_states \<A>1" using equi prun2 by fast
    have word: "map (inv_into (alphabet \<A>1) h) (map h word) = word" using map_bij fh word_well unfolding word_well_defined_def by auto
    have "(inv_into (states \<A>1) f s2) = s2'" using fh states bij_betw_inv_into_left s2' by metis
    hence "pseudo_run_well_defined (map (inv_into (states \<A>1) f) prun2) \<A>1 s2' word \<and> last (map (inv_into (states \<A>1) f) prun2) \<in> accepting_states \<A>1" using in_acc prun2 word by argo
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A>1 s2' word \<and> last prun2 \<in> accepting_states \<A>1" by blast
  }
  hence left: "\<forall> word . (\<exists> prun1 . pseudo_run_well_defined prun1 \<A>1 s1' word \<and> last prun1 \<in> accepting_states \<A>1) \<longrightarrow> (\<exists> prun2 . pseudo_run_well_defined prun2 \<A>1 s2' word \<and> last prun2 \<in> accepting_states \<A>1)" by argo
  {
    fix word assume "\<exists> prun1 . pseudo_run_well_defined prun1 \<A>1 s2' word \<and> last prun1 \<in> accepting_states \<A>1"
    then obtain prun1 where pr1: "pseudo_run_well_defined prun1 \<A>1 s2' word \<and> last prun1 \<in> accepting_states \<A>1" by auto
    hence word_well: "word_well_defined word (alphabet \<A>1)" using assms well_def_implies_word_well_defined by fast
    have prun1: "pseudo_run_well_defined (map f prun1) \<A>2 (f s2') (map h word) \<and> last prun1 \<in> accepting_states \<A>1" using impl pr1 by blast
    hence "prun1 \<noteq> []" unfolding pseudo_run_well_defined_def by force
    hence "last (map f prun1) = f (last prun1)" using last_map by blast
    hence "pseudo_run_well_defined (map f prun1) \<A>2 s2 (map h word) \<and> last (map f prun1) \<in> accepting_states \<A>2" using s2' prun1 fh by fast
    then obtain prun2 where "pseudo_run_well_defined prun2 \<A>2 s1 (map h word) \<and> last prun2 \<in> accepting_states \<A>2" using states unfolding equivalent_states_def by blast
    hence prun2: "pseudo_run_well_defined (map (inv_into (states \<A>1) f) prun2) \<A>1 (inv_into (states \<A>1) f s1) (map (inv_into (alphabet \<A>1) h) (map h word)) \<and> last prun2 \<in> accepting_states \<A>2" using impl by blast
    hence "prun2 \<noteq> []" unfolding pseudo_run_well_defined_def by force
    hence equi: "last (map (inv_into (states \<A>1) f) prun2) = (inv_into (states \<A>1) f) (last prun2)" using last_map by blast
    have "accepting_states \<A>1 \<subseteq> states \<A>1 \<and> accepting_states \<A>2 \<subseteq> states \<A>2" using assms well_def unfolding auto_well_defined_def by argo
    hence "image (inv_into (states \<A>1) f) (accepting_states \<A>2) = accepting_states \<A>1" using fh bij_betw_imp_surj_on bij_betw_inv_into_subset by metis
    hence in_acc: "last (map (inv_into (states \<A>1) f) prun2) \<in> accepting_states \<A>1" using equi prun2 by fast
    have word: "map (inv_into (alphabet \<A>1) h) (map h word) = word" using map_bij fh word_well unfolding word_well_defined_def by auto
    have "(inv_into (states \<A>1) f s1) = s1'" using fh states bij_betw_inv_into_left s1' by metis
    hence "pseudo_run_well_defined (map (inv_into (states \<A>1) f) prun2) \<A>1 s1' word \<and> last (map (inv_into (states \<A>1) f) prun2) \<in> accepting_states \<A>1" using in_acc prun2 word by argo
    hence "\<exists> prun2 . pseudo_run_well_defined prun2 \<A>1 s1' word \<and> last prun2 \<in> accepting_states \<A>1" by blast
  }
  hence "\<forall> word . (\<exists> prun1 . pseudo_run_well_defined prun1 \<A>1 s2' word \<and> last prun1 \<in> accepting_states \<A>1) \<longrightarrow> (\<exists> prun2 . pseudo_run_well_defined prun2 \<A>1 s1' word \<and> last prun2 \<in> accepting_states \<A>1)" by argo
  hence "equivalent_states s1' \<A>1 s2'" using left unfolding equivalent_states_def by blast
  thus False using props not_equi s1' s2' by blast
qed

text \<open>theorem for minimality: type of automaton does not matter\<close>
theorem isomorphic_auto_is_minimal_DFA:
  assumes "minimal_DFA_property (\<A>1 :: ('s, 'a) automaton)" "soft_isomorphic_automata \<A>1 \<A>2"
  shows "minimal_DFA_property (\<A>2 :: ('t, 'a) automaton) \<and> language_auto \<A>1 = language_auto \<A>2 \<and> alphabet \<A>1 = alphabet \<A>2"
  using assms soft_implies_isomorphic iso_auto_distinguishable iso_auto_connected iso_preserves_auto_well_defined iso_preserves_DFA_property minimal_DFA_property_iff_connected_and_distinguishable language_soft_iso_correctness soft_implies_alphabet unfolding minimal_DFA_property_def by metis

theorem existence_of_min_dfa_same_type:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> min_DFA_\<A> :: ('s, 'a) automaton. minimal_DFA_property min_DFA_\<A> \<and> language_auto \<A> = language_auto min_DFA_\<A> \<and> alphabet \<A> = alphabet min_DFA_\<A>"
proof -
  obtain min_DFA_\<A> :: "(('s states) states, 'a) automaton" where mini: "minimal_DFA_property min_DFA_\<A> \<and> language_auto \<A> = language_auto min_DFA_\<A> \<and> alphabet \<A> = alphabet min_DFA_\<A>" using assms existence_min_dfa by blast
  hence "auto_well_defined min_DFA_\<A>" unfolding minimal_DFA_property_def by blast
  then obtain min_DFA_\<A>' :: "('s, 'a) automaton" where "soft_isomorphic_automata min_DFA_\<A> min_DFA_\<A>'" using assms existence_soft_iso_automaton by blast
  thus ?thesis using isomorphic_auto_is_minimal_DFA mini soft_implies_isomorphic by blast
qed



corollary connected_automaton_equi_states_A1_unique:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "DFA_property \<A>1" "DFA_property \<A>2" "connected_automaton \<A>1" "connected_automaton \<A>2" "distinguishable_automaton \<A>1" "distinguishable_automaton \<A>2" "language_auto \<A>1 = language_auto \<A>2" "alphabet \<A>1 = alphabet \<A>2"
  shows "\<forall> s1 \<in> states \<A>1 . \<exists>! s2 \<in> states \<A>2 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)"
proof(rule ccontr)
  assume "\<not> (\<forall> s1 \<in> states \<A>1 . \<exists>! s2 \<in> states \<A>2 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2))"
  then obtain s1 where "s1 \<in> states \<A>1 \<and> \<not> (\<exists>! s2 \<in> states \<A>2 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2))" by blast
  then obtain s2 s2' where states: "s2 \<in> states \<A>2 \<and> s2' \<in> states \<A>2 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2) \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2', 2) \<and> s2 \<noteq> s2'" using assms connected_automaton_equi_states_A1 by metis
  hence "equivalent_states_multi (s2', 2) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using equivalent_states_symmetry_multi equivalent_states_transitivity_multi by metis
  hence "equivalent_states s2' \<A>2 s2" using assms equivalent_states_comb_to_solo_A2 by fast
  hence "s2' = s2" using assms states unfolding distinguishable_automaton_def by blast
  thus False using states by blast
qed

corollary connected_automaton_equi_states_A2_unique:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "DFA_property \<A>1" "DFA_property \<A>2" "connected_automaton \<A>1" "connected_automaton \<A>2" "distinguishable_automaton \<A>1" "distinguishable_automaton \<A>2" "language_auto \<A>1 = language_auto \<A>2" "alphabet \<A>1 = alphabet \<A>2"
  shows "\<forall> s2 \<in> states \<A>2 . \<exists>! s1 \<in> states \<A>1 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)"
proof(rule ccontr)
  assume "\<not> (\<forall> s2 \<in> states \<A>2 . \<exists>! s1 \<in> states \<A>1 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2))"
  then obtain s2 where "s2 \<in> states \<A>2 \<and> \<not> (\<exists>! s1 \<in> states \<A>1 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2))" by blast
  then obtain s1 s1' where states: "s1 \<in> states \<A>1 \<and> s1' \<in> states \<A>1 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2) \<and> equivalent_states_multi (s1', 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2) \<and> s1 \<noteq> s1'" using assms connected_automaton_equi_states_A2 by metis
  hence "equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s1', 1)" using equivalent_states_symmetry_multi equivalent_states_transitivity_multi by metis
  hence "equivalent_states s1 \<A>1 s1'" using assms equivalent_states_comb_to_solo_A1 by fast
  hence "s1' = s1" using assms states unfolding distinguishable_automaton_def by blast
  thus False using states by blast
qed

proposition acc_equivalent_iff_acc_states_multi: 
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)"
  shows "s1 \<in> accepting_states \<A>1 \<longleftrightarrow> s2 \<in> accepting_states \<A>2"
proof - 
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  {
    fix s1 s2 assume assm: "s1 \<in> accepting_states \<A>1 \<and> equivalent_states_multi (s1, 1) ?\<A> (s2, 2)"
    hence "s1 \<in> states \<A>1" using assms unfolding auto_well_defined_def by fast
    hence "(s1, 1) \<in> states_multi ?\<A>" unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by force
    hence "(s1, 1) \<in> states_multi ?\<A> \<and> (s1, 1) \<in> accepting_states_multi ?\<A>" using assm unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by simp
    hence "pseudo_run_well_defined_multi [(s1, 1)] ?\<A> (s1, 1) [] \<and> last [(s1, 1)] \<in> accepting_states_multi ?\<A>" using assm unfolding pseudo_run_well_defined_multi_def by force
    hence "\<exists> prun2 . pseudo_run_well_defined_multi prun2 ?\<A> (s2, 2) [] \<and> last prun2 \<in> accepting_states_multi ?\<A>" using assm unfolding equivalent_states_multi_def by blast 
    then obtain prun2 where prun2: "pseudo_run_well_defined_multi prun2 ?\<A> (s2, 2) [] \<and> last prun2 \<in> accepting_states_multi ?\<A>" by blast
    hence "(prun2 ! 0) = (s2, 2) \<and> length prun2 = 1" unfolding pseudo_run_well_defined_multi_def by auto
    hence "last prun2 = (s2, 2)" using list_with_one_element by metis
    hence "s2 \<in> accepting_states \<A>2" using prun2 unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by auto
  }
  hence left: "s1 \<in> accepting_states \<A>1 \<longrightarrow> s2 \<in> accepting_states \<A>2" using assms by presburger
  {
    fix s1 s2 assume assm: "s2 \<in> accepting_states \<A>2 \<and> equivalent_states_multi (s1, 1) ?\<A> (s2, 2)"
    hence "s2 \<in> states \<A>2" using assms unfolding auto_well_defined_def by fast
    hence "(s2, 2) \<in> states_multi ?\<A>" unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by force
    hence "(s2, 2) \<in> states_multi ?\<A> \<and> (s2, 2) \<in> accepting_states_multi ?\<A>" using assm unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by simp
    hence "pseudo_run_well_defined_multi [(s2, 2)] ?\<A> (s2, 2) [] \<and> last [(s2, 2)] \<in> accepting_states_multi ?\<A>" using assm unfolding pseudo_run_well_defined_multi_def by force
    hence "\<exists> prun1 . pseudo_run_well_defined_multi prun1 ?\<A> (s1, 1) [] \<and> last prun1 \<in> accepting_states_multi ?\<A>" using assm unfolding equivalent_states_multi_def by blast 
    then obtain prun1 where prun1: "pseudo_run_well_defined_multi prun1 ?\<A> (s1, 1) [] \<and> last prun1 \<in> accepting_states_multi ?\<A>" by blast
    hence "(prun1 ! 0) = (s1, 1) \<and> length prun1 = 1" unfolding pseudo_run_well_defined_multi_def by auto
    hence "last prun1 = (s1, 1)" using list_with_one_element by metis
    hence "s1 \<in> accepting_states \<A>1" using prun1 unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def cross_renaming_iso_def by auto
  }
  hence "s2 \<in> accepting_states \<A>2 \<longrightarrow> s1 \<in> accepting_states \<A>1" using assms by presburger
  thus ?thesis using left by blast
qed

lemma properties_for_soft_iso:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('s, 'a) automaton)" "DFA_property \<A>1" "DFA_property \<A>2" "connected_automaton \<A>1" "connected_automaton \<A>2" "distinguishable_automaton \<A>1" "distinguishable_automaton \<A>2" "language_auto \<A>1 = language_auto \<A>2" "alphabet \<A>1 = alphabet \<A>2"
  shows "soft_isomorphic_automata \<A>1 \<A>2"
proof -
  let ?f = "\<lambda>s1 . THE s2. s2 \<in> states \<A>2 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)"
  {
    fix s1 assume assm: "s1 \<in> states \<A>1"
    then obtain s2 where s2: "s2 \<in> states \<A>2 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms connected_automaton_equi_states_A1_unique by metis
    have "\<exists>! s2 \<in> states \<A>2 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms assm connected_automaton_equi_states_A1_unique by metis
    hence "?f s1 = s2" using the1_equality s2 by fastforce
    hence "?f s1 \<in> states \<A>2" using s2 by blast
  }
  hence sub: "image ?f (states \<A>1) \<subseteq> states \<A>2" by blast
  {
    fix s2 assume assm: "s2 \<in> states \<A>2"
    then obtain s1 where s1: "s1 \<in> states \<A>1 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms connected_automaton_equi_states_A2_unique by metis
    hence "\<exists>! s2 \<in> states \<A>2 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms connected_automaton_equi_states_A1_unique by metis
    hence "?f s1 = s2" using s1 assm the1_equality by fastforce
    hence "s2 \<in> image ?f (states \<A>1)" using assm s1 by blast
  }
  hence im: "image ?f (states \<A>1) = states \<A>2" using sub by blast
  {
    fix s1 s1' assume assm: "s1 \<in> states \<A>1 \<and> s1' \<in> states \<A>1 \<and> ?f s1 = ?f s1'"
    hence s1: "s1 \<in> states \<A>1" by blast
    then obtain s2 where s2: "s2 \<in> states \<A>2 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms connected_automaton_equi_states_A1_unique by blast
    have "\<exists>! s2 \<in> states \<A>2 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms s1 connected_automaton_equi_states_A1_unique by metis
    hence f_s2: "?f s1 = s2" using the1_equality s2 by fastforce
    have s1': "s1' \<in> states \<A>1" using assm by blast
    then obtain s2' where s2': "s2' \<in> states \<A>2 \<and> equivalent_states_multi (s1', 1) (union_automaton_multi \<A>1 \<A>2) (s2', 2)" using assms connected_automaton_equi_states_A1_unique by blast
    have "\<exists>! s2 \<in> states \<A>2 . equivalent_states_multi (s1', 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms s1' connected_automaton_equi_states_A1_unique by metis
    hence "?f s1' = s2'" using the1_equality s2' by fastforce
    hence equi: "s2 = s2'" using assm f_s2 by blast    
    have "\<exists>! s1 \<in> states \<A>1 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using s2 assms connected_automaton_equi_states_A2_unique by metis
    hence "\<forall> s1 s1' . s1 \<in> states \<A>1 \<and> s1' \<in> states \<A>1 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2) \<and> equivalent_states_multi (s1', 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2) \<longrightarrow> s1 = s1'" by blast
    hence "s1 = s1'" using s1 s2 s1' s2' equi by blast
  }
  hence "inj_on ?f (states \<A>1)" unfolding inj_on_def by blast
  hence bij_f: "bij_betw ?f (states \<A>1) (states \<A>2)" using im unfolding bij_betw_def by blast
  have bij_h: "bij_betw id (alphabet \<A>1) (alphabet \<A>2)" using assms unfolding bij_betw_def by auto
  have "equivalent_states_multi (initial_state \<A>1, 1) (union_automaton_multi \<A>1 \<A>2) (initial_state \<A>2, 2)" using assms initial_states_comb_automaton_equi by blast
  hence init: "initial_state \<A>1 \<in> states \<A>1 \<and> initial_state \<A>2 \<in> states \<A>2 \<and> equivalent_states_multi (initial_state \<A>1, 1) (union_automaton_multi \<A>1 \<A>2) (initial_state \<A>2, 2)" using assms unfolding auto_well_defined_def by blast
  hence "\<exists>! s2 \<in> states \<A>2 . equivalent_states_multi (initial_state \<A>1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms connected_automaton_equi_states_A1_unique by metis
  hence f_init: "?f (initial_state \<A>1) = initial_state \<A>2" using init the1_equality by force
  {
    fix s1 assume assm: "s1 \<in> accepting_states \<A>1"
    hence s1: "s1 \<in> states \<A>1" using assms unfolding auto_well_defined_def by fast
    then obtain s2 where s2: "s2 \<in> states \<A>2 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms connected_automaton_equi_states_A1_unique by metis
    hence acc: "s2 \<in> accepting_states \<A>2" using assms assm acc_equivalent_iff_acc_states_multi by fast
    have "\<exists>! s2 \<in> states \<A>2 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms s1 connected_automaton_equi_states_A1_unique by metis
    hence "?f s1 = s2" using the1_equality s2 by fastforce
    hence "?f s1 \<in> accepting_states \<A>2" using acc by blast
  }
  hence sub_acc: "image ?f (accepting_states \<A>1) \<subseteq> accepting_states \<A>2" by blast
  {
    fix s2 assume assm: "s2 \<in> accepting_states \<A>2"
    hence s2: "s2 \<in> states \<A>2" using assms unfolding auto_well_defined_def by fast
    then obtain s1 where s1: "s1 \<in> states \<A>1 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms connected_automaton_equi_states_A2_unique by metis
    hence acc: "s1 \<in> accepting_states \<A>1" using assms assm acc_equivalent_iff_acc_states_multi by fast
    have "\<exists>! s2 \<in> states \<A>2 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms s1 connected_automaton_equi_states_A1_unique by metis
    hence "?f s1 = s2" using s1 s2 the1_equality by fastforce
    hence "s2 \<in> image ?f (accepting_states \<A>1)" using assm acc by blast
  }
  hence acc_im: "image ?f (accepting_states \<A>1) = accepting_states \<A>2" using sub_acc by blast
  {
    fix s1 a s2 assume assm: "(s1, a, s2) \<in> transitions \<A>1"
    hence states: "s1 \<in> states \<A>1 \<and> a \<in> alphabet \<A>1 \<and> s2 \<in> states \<A>1" using assms well_def_trans_components by metis
    then obtain t1 where t1: "t1 \<in> states \<A>2 \<and> equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (t1, 2)" using assms connected_automaton_equi_states_A1_unique by metis
    have "\<exists>! t1 \<in> states \<A>2 . equivalent_states_multi (s1, 1) (union_automaton_multi \<A>1 \<A>2) (t1, 2)" using assms states connected_automaton_equi_states_A1_unique by metis
    hence f_t1: "?f s1 = t1" using the1_equality t1 by fastforce
    have "a \<in> alphabet \<A>2" using assms states by argo
    then obtain t2 where trans: "(t1, a, t2) \<in> transitions \<A>2" using assms t1 unfolding DFA_property_def by fast
    hence t2: "t2 \<in> states \<A>2" using well_def_trans_components assms by fast
    hence equi: "equivalent_states_multi (s2, 1) (union_automaton_multi \<A>1 \<A>2) (t2, 2)" using assms successors_comb_automaton_equi assm trans t1 by fast
    have "\<exists>! t2 \<in> states \<A>2 . equivalent_states_multi (s2, 1) (union_automaton_multi \<A>1 \<A>2) (t2, 2)" using assms states connected_automaton_equi_states_A1_unique by metis
    hence "?f s2 = t2" using t2 equi the1_equality by fastforce
    hence "(?f s1, a, ?f s2) \<in> transitions \<A>2" using trans f_t1 by blast
  }
  hence sub_trans: "image (\<lambda>(s1, a, s2) . (?f s1, id a, ?f s2)) (transitions \<A>1) \<subseteq> transitions \<A>2" by auto
  {
    fix s1 a s2 assume assm: "(s1, a, s2) \<in> transitions \<A>2"
    hence states: "s1 \<in> states \<A>2 \<and> a \<in> alphabet \<A>2 \<and> s2 \<in> states \<A>2" using assms well_def_trans_components by metis
    then obtain t1 where t1: "t1 \<in> states \<A>1 \<and> equivalent_states_multi (t1, 1) (union_automaton_multi \<A>1 \<A>2) (s1, 2)" using assms connected_automaton_equi_states_A2_unique by metis
    hence "\<exists>! s1 \<in> states \<A>2 . equivalent_states_multi (t1, 1) (union_automaton_multi \<A>1 \<A>2) (s1, 2)" using assms connected_automaton_equi_states_A1_unique by metis
    hence f_t1: "?f t1 = s1" using the1_equality states t1 by fastforce
    have "a \<in> alphabet \<A>1" using assms states by argo
    then obtain t2 where trans: "(t1, a, t2) \<in> transitions \<A>1" using assms t1 unfolding DFA_property_def by fast
    hence t2: "t2 \<in> states \<A>1" using well_def_trans_components assms by fast
    hence equi: "equivalent_states_multi (t2, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms successors_comb_automaton_equi assm trans t1 by fast
    have "\<exists>! s2 \<in> states \<A>2 . equivalent_states_multi (t2, 1) (union_automaton_multi \<A>1 \<A>2) (s2, 2)" using assms t2 connected_automaton_equi_states_A1_unique by metis
    hence "?f t2 = s2" using states equi the1_equality by fastforce
    hence "(s1, a, s2) = (?f t1, id a, ?f t2) \<and> (t1, a, t2) \<in> transitions \<A>1" using trans f_t1 by force
    hence "(s1, a, s2) \<in> image (\<lambda>(s1, a, s2) . (?f s1, id a, ?f s2)) (transitions \<A>1)" by force
  }
  hence "transitions \<A>2 = image (\<lambda>(s1, a, s2) . (?f s1, id a, ?f s2)) (transitions \<A>1)" using sub_trans by auto
  thus ?thesis using acc_im f_init bij_f bij_h unfolding soft_isomorphic_automata_def by blast
qed

theorem minimal_DFAs_are_isomorphic:
  assumes "minimal_DFA_property (\<A>1 :: ('s, 'a) automaton)" "minimal_DFA_property (\<A>2 :: ('t, 'a) automaton)" "language_auto \<A>1 = language_auto \<A>2" "alphabet \<A>1 = alphabet \<A>2" "infinite (UNIV :: 's set)"
  shows "soft_isomorphic_automata \<A>1 \<A>2"
proof -
  obtain min_\<A>2 :: "('s, 'a) automaton" where soft_iso: "soft_isomorphic_automata \<A>2 min_\<A>2" using assms existence_soft_iso_automaton unfolding minimal_DFA_property_def by metis
  hence mini: "minimal_DFA_property min_\<A>2 \<and> language_auto \<A>1 = language_auto min_\<A>2 \<and> alphabet \<A>1 = alphabet min_\<A>2" using isomorphic_auto_is_minimal_DFA assms unfolding minimal_DFA_property_def by blast
  hence well_def: "auto_well_defined \<A>1 \<and> auto_well_defined \<A>2 \<and> auto_well_defined min_\<A>2" using assms unfolding minimal_DFA_property_def by blast
  hence "auto_well_defined \<A>1 \<and> auto_well_defined min_\<A>2 \<and> connected_automaton \<A>1 \<and> connected_automaton min_\<A>2 \<and> distinguishable_automaton \<A>1 \<and> distinguishable_automaton min_\<A>2" using assms mini minimality_property_left by metis
  hence "auto_well_defined \<A>1 \<and> auto_well_defined min_\<A>2 \<and> connected_automaton \<A>1 \<and> connected_automaton min_\<A>2 \<and> distinguishable_automaton \<A>1 \<and> distinguishable_automaton min_\<A>2 \<and>  DFA_property \<A>1 \<and> DFA_property min_\<A>2 \<and> language_auto \<A>1 = language_auto min_\<A>2 \<and> alphabet \<A>1 = alphabet min_\<A>2" using assms mini unfolding minimal_DFA_property_def by fast
  hence "soft_isomorphic_automata \<A>1 min_\<A>2" using properties_for_soft_iso by auto
  thus ?thesis using soft_iso soft_isomorphy_symmetry soft_iso_transitive well_def by blast
qed

text \<open>Main theorem for minimality: type of automaton does not matter\<close>
theorem minimal_DFA_unique_up_to_isomorphy:
  assumes "minimal_DFA_property (\<A>1 :: ('s, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "minimal_DFA_property (\<A>2 :: ('t, 'a) automaton) \<and> language_auto \<A>1 = language_auto \<A>2 \<and> alphabet \<A>1 = alphabet \<A>2 \<longleftrightarrow> soft_isomorphic_automata \<A>1 \<A>2"
  using assms minimal_DFAs_are_isomorphic isomorphic_auto_is_minimal_DFA by metis

end