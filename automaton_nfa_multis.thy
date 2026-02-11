theory automaton_nfa_multis

imports Main automaton_isomorphy

begin

text \<open>Author: Benno Thalmann, last update: 11.2.2026, Addition to masterarbeit_benno_thalmann\<close>

text \<open>Datatype of finite automata with multiple initial states\<close>
datatype ('s, 'a) nfa_multi = NFA_multi
  (states_multi : "'s states")
  (alphabet_multi : "'a alphabet")
  (transitions_multi : "('s , 'a) transitions")
  (initial_states_multi : "'s states")
  (accepting_states_multi : "'s states") 

definition auto_well_defined_multi :: "('s, 'a) nfa_multi \<Rightarrow> bool" where
  "auto_well_defined_multi \<A> =
    (finite (states_multi \<A>) \<and>
    finite (alphabet_multi \<A>) \<and>
    initial_states_multi \<A> \<subseteq> states_multi \<A> \<and>
    (\<forall> (s1, a, s2) \<in> transitions_multi \<A> . s1 \<in> states_multi \<A> \<and> a \<in> alphabet_multi \<A> \<and> s2 \<in> states_multi \<A>) \<and>
    accepting_states_multi \<A> \<subseteq> states_multi \<A>)"

lemma well_def_trans_components_multi:
  assumes "auto_well_defined_multi \<A>" "(s1, a, s2) \<in> transitions_multi \<A>"
  shows "s1 \<in> states_multi \<A> \<and> a \<in> alphabet_multi \<A> \<and> s2 \<in> states_multi \<A>"
  using assms unfolding auto_well_defined_multi_def by fast

definition pseudo_run_well_defined_multi :: "'s run \<Rightarrow> ('s, 'a) nfa_multi \<Rightarrow> 's state \<Rightarrow> 'a word \<Rightarrow> bool" where
  "pseudo_run_well_defined_multi prun \<A> s word =
    (length prun = length word + 1 \<and>
    (prun ! 0) = s \<and> s \<in> states_multi \<A> \<and>
    (\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions_multi \<A>))"

definition prun_states_multi :: "'s run \<Rightarrow> ('s, 'a) nfa_multi \<Rightarrow> bool" where "prun_states_multi prun \<A> = (set prun \<subseteq> states_multi \<A>)"

proposition prun_states_equivalence_multi: "prun_states_multi prun \<A> \<longleftrightarrow> (\<forall> s \<in> set prun . s \<in> states_multi \<A>)"
  unfolding prun_states_multi_def by auto

theorem well_def_implies_prun_states_multi:
  assumes "auto_well_defined_multi \<A>" "pseudo_run_well_defined_multi prun \<A> s word"
  shows "prun_states_multi prun \<A>"
proof(cases word)
  case Nil 
  hence "prun = [s] \<and> s \<in> states_multi \<A>" using assms list_with_one_element unfolding pseudo_run_well_defined_multi_def by force
  thus ?thesis using prun_states_equivalence_multi by fastforce
next
  let ?n = "length prun"
  case (Cons a word)
  hence len: "?n > 1" using assms unfolding pseudo_run_well_defined_multi_def by auto
  have prun_i: "\<forall> i < ?n - 1 . prun ! i \<in> states_multi \<A>" using well_def_trans_components_multi assms unfolding pseudo_run_well_defined_multi_def by fast
  have "\<forall> i < ?n - 1 . prun ! (i + 1) \<in> states_multi \<A>" using well_def_trans_components_multi assms unfolding pseudo_run_well_defined_multi_def by fast
  hence "prun ! (?n - 2 + 1) \<in> states_multi \<A>" using len by force
  hence "prun ! (?n - 1) \<in> states_multi \<A>" using len simple_math by metis
  hence "\<forall> i < ?n . prun ! i \<in> states_multi \<A>" using prun_i merge_one_more by simp
  thus ?thesis using prun_states_equivalence_multi in_set_conv_nth by metis
qed

corollary last_of_prun_is_state_multi:
  assumes "auto_well_defined_multi \<A>" "pseudo_run_well_defined_multi prun \<A> s word"
  shows "last prun \<in> states_multi \<A>"
proof -
  have "prun \<noteq> []" using assms unfolding pseudo_run_well_defined_multi_def by fastforce
  hence "last prun \<in> set prun" by auto
  thus ?thesis using assms well_def_implies_prun_states_multi unfolding prun_states_multi_def by fast
qed

lemma prun_well_defined_induction_cons_multi:
  assumes "auto_well_defined_multi \<A>" "pseudo_run_well_defined_multi prun \<A> state word" "(s, a, state) \<in> transitions_multi \<A>"
  shows "pseudo_run_well_defined_multi (s # prun) \<A> s (a # word)"
proof -
  have states: "s \<in> states_multi \<A> \<and> (s # prun) ! 0 = s" using assms well_def_trans_components_multi by force
  have props: "length prun = length word + 1 \<and> (\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions_multi \<A>) \<and> (prun ! 0) = state" using assms unfolding pseudo_run_well_defined_multi_def by blast
  hence len: "length (s # prun) = length (a # word) + 1" by force
  {
    fix i assume assm: "i < length (s # prun) - 1"
    hence "((s # prun) ! i, (a # word) ! i, (s # prun) ! (i + 1)) \<in> transitions_multi \<A>"
    proof(cases i)
      case 0 thus ?thesis using props assms by auto
    next
      case (Suc nat)
      then obtain j where j: "j = i - 1" by auto
      hence jmax: "j < length (s # prun) - 2" using assm Suc by fastforce
      have "((s # prun) ! i, (a # word) ! i, (s # prun) ! (i + 1)) = (prun ! j, word ! j, prun ! (j + 1))" using j Suc by auto
      thus ?thesis using props jmax by simp
    qed
  }
  thus ?thesis using states len unfolding pseudo_run_well_defined_multi_def by blast
qed

lemma prun_well_defined_cons_multi:
  assumes "auto_well_defined_multi \<A>" "pseudo_run_well_defined_multi (s # prun) \<A> s (a # word)"
  shows "pseudo_run_well_defined_multi prun \<A> (prun ! 0) word \<and> (s, a, (prun ! 0)) \<in> transitions_multi \<A>"
proof -
  have props: "length (s # prun) = length (a # word) + 1 \<and> (s # prun) ! 0 = s \<and> s \<in> states_multi \<A> \<and> (\<forall> i < length (s # prun) - 1 . ((s # prun) ! i, (a # word) ! i, (s # prun) ! (i + 1)) \<in> transitions_multi \<A>)" using assms unfolding pseudo_run_well_defined_multi_def by blast
  hence "length prun = length word + 1 \<and> ((s # prun) ! 0, (a # word) ! 0, (s # prun) ! (0 + 1)) \<in> transitions_multi \<A>" by auto
  hence len: "length prun = length word + 1 \<and> (s, a, prun ! 0) \<in> transitions_multi \<A>" by auto
  hence init: "prun ! 0 \<in> states_multi \<A>" using assms well_def_trans_components_multi by fast
  {
    fix i assume assm: "i < length prun - 1"
    then obtain j where j: "j = i + 1" by auto
    hence "j < length (s # prun) - 1" using assm by force
    hence i_step: "((s # prun) ! j, (a # word) ! j, (s # prun) ! (j + 1)) \<in> transitions_multi \<A>" using props by blast
    have "((s # prun) ! j, (a # word) ! j, (s # prun) ! (j + 1)) = (prun ! i, word ! i, prun ! (i + 1))" using j by auto
    hence "(prun ! i, word ! i, prun ! (i + 1)) \<in> transitions_multi \<A>" using i_step by argo
  }
  hence "\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions_multi \<A>" by blast
  thus ?thesis using len init unfolding pseudo_run_well_defined_multi_def by blast
qed

proposition prun_well_defined_extension_cons_multi:
  assumes "auto_well_defined_multi \<A>"
  shows "pseudo_run_well_defined_multi (s # prun) \<A> s (a # word) \<longleftrightarrow> pseudo_run_well_defined_multi prun \<A> (prun ! 0) word \<and> (s, a, (prun ! 0)) \<in> transitions_multi \<A>"
  using assms prun_well_defined_cons_multi prun_well_defined_induction_cons_multi by metis

lemma prun_well_defined_induction_snoc_multi:
  assumes "pseudo_run_well_defined_multi prun \<A> s' word" "(last prun, a, s) \<in> transitions_multi \<A>"
  shows "pseudo_run_well_defined_multi (prun @ [s]) \<A> s' (word @ [a])"
proof -
  let ?n = "length prun"
  let ?prun = "prun @ [s]"
  let ?word = "word @ [a]"
  have properties: "?n = length word + 1 \<and> ?n - 1 = length word \<and> prun \<noteq> [] \<and> prun ! 0 = s' \<and> prun ! 0 \<in> states_multi \<A>" using assms unfolding pseudo_run_well_defined_multi_def by auto
  hence snoc_transition_step: "\<forall> i < ?n - 1 . (?prun ! i, ?word ! i, ?prun ! (i + 1)) \<in> transitions_multi \<A>" using assms list_properties_length unfolding pseudo_run_well_defined_multi_def by metis
  have "?prun ! (?n - 1) = last prun \<and> ?prun ! ?n = s \<and> ?word ! (?n - 1) = a" using properties list_properties_not_empty nth_append_length by metis
  hence "(?prun ! (?n - 1), ?word ! (?n - 1), ?prun ! ((?n - 1) + 1)) \<in> transitions_multi \<A>" using properties assms by auto
  hence "\<forall> i < length ?prun - 1 . (?prun ! i, ?word ! i, ?prun ! (i + 1)) \<in> transitions_multi \<A>" using snoc_transition_step merge_one_more by simp
  thus ?thesis using properties list_properties_not_empty unfolding pseudo_run_well_defined_multi_def by force
qed

lemma last_transition_multi:
  assumes "pseudo_run_well_defined_multi (prun @ [s]) \<A> s' (word @ [a])"
  shows "(last prun, a, s) \<in> transitions_multi \<A>"
proof - 
  let ?n = "length (prun @ [s])"
  let ?prun = "prun @ [s]"
  let ?word = "word @ [a]"
  have "?n = length ?word + 1" using assms unfolding pseudo_run_well_defined_multi_def by blast
  hence properties: "?n > 1 \<and> ?n = length ?word + 1 \<and> ?prun \<noteq> []" by auto
  have "\<forall> i < ?n - 1 . (?prun ! i, ?word ! i, ?prun ! (i + 1)) \<in> transitions_multi \<A>" using assms unfolding pseudo_run_well_defined_multi_def by auto
  hence trans: "(?prun ! (?n - 2), ?word ! (?n - 2), ?prun ! (?n - 2 + 1)) \<in> transitions_multi \<A>" using properties by force
  have last: "?prun ! (length ?prun - 2) = last prun \<and> ?word ! (?n - 2) = a" using list_properties_not_empty properties by force
  have "prun \<noteq> []" using properties by auto
  hence "?prun ! (?n - 2 + 1) = s" by auto
  thus ?thesis using last trans by auto
qed

lemma prun_well_defined_snoc_multi:
  assumes "pseudo_run_well_defined_multi (prun @ [s]) \<A> s' (word @ [a])"
  shows "pseudo_run_well_defined_multi prun \<A> s' word \<and> (last prun, a, s) \<in> transitions_multi \<A>"
proof -
  let ?n = "length prun"
  let ?prun = "prun @ [s]"
  let ?word = "word @ [a]"
  have "length ?prun = length ?word + 1 \<and> ?prun ! 0 = s' \<and> s' \<in> states_multi \<A>" using assms unfolding pseudo_run_well_defined_multi_def by blast
  hence properties: "length ?prun = length ?word + 1 \<and> ?n - 1 = length word \<and> ?prun ! 0 = s' \<and> s' \<in> states_multi \<A>  \<and> prun \<noteq> []" by auto
  hence initial_state: "prun ! 0 = s' \<and> s' \<in> states_multi \<A>" using list_properties_not_empty by metis
  have "\<forall> i < ?n - 1 . (?prun ! i, ?word ! i, ?prun ! (i + 1)) \<in> transitions_multi \<A>" using assms unfolding pseudo_run_well_defined_multi_def by auto
  hence i_step: "\<forall> i < ?n - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions_multi \<A>" using properties list_properties_length by metis
  have "(last prun, a, s) \<in> transitions_multi \<A>" using assms last_transition_multi by fast
  thus ?thesis using properties initial_state i_step unfolding pseudo_run_well_defined_multi_def by auto
qed

proposition prun_well_defined_extension_snoc_multi: "pseudo_run_well_defined_multi (prun @ [s]) \<A> s' (word @ [a]) \<longleftrightarrow> pseudo_run_well_defined_multi prun \<A> s' word \<and> (last prun, a, s) \<in> transitions_multi \<A>"
  using prun_well_defined_snoc_multi prun_well_defined_induction_snoc_multi by metis

text \<open>Definition of an accepting run over a word\<close>
definition run_well_defined_multi :: "'s run \<Rightarrow> ('s, 'a) nfa_multi \<Rightarrow> 'a word \<Rightarrow> bool" where "run_well_defined_multi run \<A> word = (pseudo_run_well_defined_multi run \<A> (run ! 0) word \<and> (run ! 0) \<in> initial_states_multi \<A>)"

lemma run_well_defined_induction_snoc_multi:
  assumes "run_well_defined_multi (run @ [s]) \<A> (word @ [a])"
  shows "run_well_defined_multi run \<A> word \<and> (last run, a, s) \<in> transitions_multi \<A>"
proof -
  have props: "pseudo_run_well_defined_multi (run @ [s]) \<A> ((run @ [s]) ! 0) (word @ [a]) \<and> ((run @ [s]) ! 0) \<in> initial_states_multi \<A>" using assms unfolding run_well_defined_multi_def by blast
  hence "run \<noteq> []" unfolding pseudo_run_well_defined_multi_def by force
  hence "run ! 0 = (run @ [s]) ! 0" using list_properties_not_empty by fast
  thus ?thesis using assms prun_well_defined_extension_snoc_multi unfolding run_well_defined_multi_def by metis
qed

lemma run_well_defined_snoc_multi:
  assumes "run_well_defined_multi run \<A> word \<and> (last run, a, s) \<in> transitions_multi \<A>"
  shows "run_well_defined_multi (run @ [s]) \<A> (word @ [a])"
proof -
  have props: "pseudo_run_well_defined_multi run \<A> (run ! 0) word\<and> (run ! 0) \<in> initial_states_multi \<A>" using assms unfolding run_well_defined_multi_def by blast
  hence "run \<noteq> []" unfolding pseudo_run_well_defined_multi_def by force
  hence "run ! 0 = (run @ [s]) ! 0" using list_properties_not_empty by fast
  thus ?thesis using assms prun_well_defined_extension_snoc_multi unfolding run_well_defined_multi_def by metis
qed

corollary run_well_defined_extension_snoc_multi: "run_well_defined_multi (prun @ [s]) \<A> (word @ [a]) \<longleftrightarrow> run_well_defined_multi prun \<A> word \<and> (last prun, a, s) \<in> transitions_multi \<A>"
  using run_well_defined_induction_snoc_multi run_well_defined_snoc_multi by metis

definition run_accepting_multi :: "'s run \<Rightarrow> ('s, 'a) nfa_multi \<Rightarrow> 'a word \<Rightarrow> bool" where "run_accepting_multi run \<A> word = (run_well_defined_multi run \<A> word \<and> last run \<in> accepting_states_multi \<A>)"

definition language_auto_multi :: "('s, 'a) nfa_multi \<Rightarrow> 'a language" where "language_auto_multi \<A> = {word . \<exists> run . run_accepting_multi run \<A> word}"

theorem well_def_implies_word_well_defined_multi:
  assumes "auto_well_defined_multi \<A>" "pseudo_run_well_defined_multi prun \<A> s word"
  shows "word_well_defined word (alphabet_multi \<A>)"
proof - 
  have "length prun = length word + 1 \<and> (\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions_multi \<A>)" using assms unfolding pseudo_run_well_defined_multi_def by blast
  hence "\<forall> i < length word . word ! i \<in> alphabet_multi \<A>" using well_def_trans_components_multi assms by fastforce
  hence "\<forall> a \<in> set word . a \<in> alphabet_multi \<A>" using in_set_conv_nth by metis
  thus ?thesis using word_well_def_equivalence by fast
qed

corollary word_in_language_is_well_defined_multi:
  assumes "auto_well_defined_multi \<A>" "word \<in> language_auto_multi \<A>"
  shows "word_well_defined word (alphabet_multi \<A>)"
  using assms well_def_implies_word_well_defined_multi unfolding language_auto_multi_def run_accepting_multi_def run_well_defined_multi_def by auto

proposition automata_language_are_well_defined_multi:
  assumes "auto_well_defined_multi \<A>"
  shows "language_well_defined (language_auto_multi \<A>) (alphabet_multi \<A>)"
  using assms word_in_language_is_well_defined_multi unfolding language_well_defined_def by blast

corollary automata_union_lang_well_defined_multi:
  assumes "auto_well_defined_multi \<A>1" "auto_well_defined_multi \<A>2"
  shows "language_well_defined (language_auto_multi \<A>1 \<union> language_auto_multi \<A>2) (alphabet_multi \<A>1 \<union> alphabet_multi \<A>2)"
  using assms union_language_well_defined automata_language_are_well_defined_multi by metis

definition NFA_to_multi :: "('s, 'a) automaton \<Rightarrow> ('s, 'a) nfa_multi" where
  "NFA_to_multi \<A> = NFA_multi
    (states \<A>)
    (alphabet \<A>)
    (transitions \<A>)
    {initial_state \<A>}
    (accepting_states \<A>)"

proposition NFA_to_multi_auto_well_defined:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined_multi (NFA_to_multi \<A>)"
  using assms unfolding auto_well_defined_multi_def auto_well_defined_def NFA_to_multi_def by auto

corollary language_well_def_NFA_to_multi:
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (language_auto_multi (NFA_to_multi \<A>)) (alphabet_multi (NFA_to_multi \<A>))"
  using NFA_to_multi_auto_well_defined assms automata_language_are_well_defined_multi by blast

lemma NFA_to_multi_alphabet: "alphabet \<A> = alphabet_multi (NFA_to_multi \<A>)"
  unfolding NFA_to_multi_def by auto

proposition prun_on_NFA_to_multi: "pseudo_run_well_defined run \<A> s word \<longleftrightarrow> pseudo_run_well_defined_multi run (NFA_to_multi \<A>) s word"
  unfolding NFA_to_multi_def pseudo_run_well_defined_def pseudo_run_well_defined_multi_def by auto

text \<open>Main result for NFA_to_multi\<close>
theorem NFA_to_multi_language_correctness: "language_auto \<A> = language_auto_multi (NFA_to_multi \<A>)"
proof -
  {
    fix word assume "word \<in> language_auto \<A>"
    then obtain run where "pseudo_run_well_defined run \<A> (initial_state \<A>) word \<and> last run \<in> accepting_states \<A>" unfolding language_auto_def run_accepting_def run_well_defined_def by blast
    hence "pseudo_run_well_defined_multi run (NFA_to_multi \<A>) (initial_state \<A>) word \<and> initial_state \<A> \<in> initial_states_multi (NFA_to_multi \<A>) \<and> last run \<in> accepting_states_multi (NFA_to_multi \<A>)" using prun_on_NFA_to_multi unfolding NFA_to_multi_def by force
    hence "word \<in> language_auto_multi (NFA_to_multi \<A>)" unfolding pseudo_run_well_defined_multi_def run_well_defined_multi_def run_accepting_multi_def language_auto_multi_def by auto
  }
  hence sub: "language_auto \<A> \<subseteq> language_auto_multi (NFA_to_multi \<A>)" by blast
  {
    fix word assume "word \<in> language_auto_multi (NFA_to_multi \<A>)"
    then obtain run where "pseudo_run_well_defined_multi run (NFA_to_multi \<A>) (run ! 0) word \<and> (run ! 0) \<in> initial_states_multi (NFA_to_multi \<A>) \<and> last run \<in> accepting_states_multi (NFA_to_multi \<A>)" unfolding language_auto_multi_def run_accepting_multi_def run_well_defined_multi_def by blast
    hence "pseudo_run_well_defined run \<A> (initial_state \<A>) word \<and> last run \<in> accepting_states \<A>" using prun_on_NFA_to_multi unfolding NFA_to_multi_def by force
    hence "word \<in> language_auto \<A>" unfolding run_well_defined_def run_accepting_def language_auto_def by auto
  }
  thus ?thesis using sub by blast
qed

corollary existence_of_NFA_to_multi_same_type:
  assumes "auto_well_defined (NFA_\<A> :: ('s, 'a) automaton)"
  shows "\<exists> NFA_multi_\<A> :: ('s, 'a) nfa_multi . auto_well_defined_multi NFA_multi_\<A> \<and> alphabet NFA_\<A> = alphabet_multi NFA_multi_\<A> \<and> language_auto NFA_\<A> = language_auto_multi NFA_multi_\<A>"
  using assms NFA_to_multi_language_correctness NFA_to_multi_auto_well_defined NFA_to_multi_alphabet by fast




text \<open>Application: union automaton with the help of nfa_multi:\<close>
definition union_automaton_multi_helper :: "('s, 'a) automaton \<Rightarrow> ('s, 'a) automaton \<Rightarrow> ('s, 'a) nfa_multi" where
  "union_automaton_multi_helper \<A>1 \<A>2 = NFA_multi
    (states \<A>1 \<union> states \<A>2)
    (alphabet \<A>1 \<union> alphabet \<A>2)
    (transitions \<A>1 \<union> transitions \<A>2)
    {initial_state \<A>1, initial_state \<A>2}
    (accepting_states \<A>1 \<union> accepting_states \<A>2)"

proposition union_helper_auto_well_defined:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "auto_well_defined_multi (union_automaton_multi_helper \<A>1 \<A>2)"
  using assms unfolding union_automaton_multi_helper_def auto_well_defined_def auto_well_defined_multi_def by auto

corollary language_well_def_union_helper_multi_auto:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "language_well_defined (language_auto_multi (union_automaton_multi_helper \<A>1 \<A>2)) (alphabet_multi (union_automaton_multi_helper \<A>1 \<A>2))"
  using union_helper_auto_well_defined assms automata_language_are_well_defined_multi by blast

definition union_automaton_multi :: "('s, 'a) automaton \<Rightarrow> ('s, 'a) automaton \<Rightarrow> ('s \<times> nat, 'a) nfa_multi" where "union_automaton_multi \<A>1 \<A>2 = union_automaton_multi_helper (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"

proposition union_auto_well_defined:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "auto_well_defined_multi (union_automaton_multi \<A>1 \<A>2)"
  using assms cross_renaming_iso_automaton_auto_well_defined union_helper_auto_well_defined unfolding union_automaton_multi_def by metis

corollary language_well_def_union_multi_auto:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "language_well_defined (language_auto_multi (union_automaton_multi \<A>1 \<A>2)) (alphabet_multi (union_automaton_multi \<A>1 \<A>2))"
  using union_auto_well_defined assms automata_language_are_well_defined_multi by blast

proposition union_auto_alphabet: "alphabet_multi (union_automaton_multi \<A>1 \<A>2) = alphabet \<A>1 \<union> alphabet \<A>2"
  unfolding union_automaton_multi_def union_automaton_multi_helper_def type_encode_automaton_def by force

lemma trans_union_auto_A1_state:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" "s2 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  shows "s1 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
proof(rule ccontr)
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  assume assm: "s1 \<notin> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  have "auto_well_defined_multi ?\<A>" using assms union_auto_well_defined by auto
  hence "s1 \<in> states_multi ?\<A>" using assms well_def_trans_components_multi by fast
  hence "s1 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assm unfolding union_automaton_multi_def union_automaton_multi_helper_def by force  
  have well_def: "auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  have "transitions_multi ?\<A> = (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" unfolding union_automaton_multi_def union_automaton_multi_helper_def by force
  hence trans: "(s1, a, s2) \<in> (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" using assms by argo
  thus False using well_def well_def_trans_components assms assm cross_renaming_intersection_empty by fast
qed

lemma trans_union_auto_A1_trans:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" "s2 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  shows "(s1, a, s2) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
proof -
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  have well_def: "auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  have trans: "transitions_multi ?\<A> = (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" unfolding union_automaton_multi_def union_automaton_multi_helper_def by auto
  have props: "s1 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms trans_union_auto_A1_state by fast
  hence "(s1, a, s2) \<in> (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" using assms trans by argo
  thus ?thesis using well_def well_def_trans_components assms cross_renaming_intersection_empty by fast
qed

lemma prun_union_auto_first_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "pseudo_run_well_defined_multi prun (union_automaton_multi \<A>1 \<A>2) s word \<and> last prun \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<Longrightarrow> s \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
proof(induction word arbitrary: prun s)
  case Nil thus ?case using list_with_one_element unfolding pseudo_run_well_defined_multi_def by fastforce
next
  have well_def: "auto_well_defined_multi (union_automaton_multi \<A>1 \<A>2)" using assms union_auto_well_defined by blast
  case (Cons a word)
  hence "prun \<noteq> [] \<and> (prun ! 0) = s" unfolding pseudo_run_well_defined_multi_def by fastforce
  then obtain prun' where prun: "prun = s # prun'" using hd_Cons_tl hd_conv_nth by metis
  hence "pseudo_run_well_defined_multi (s # prun') (union_automaton_multi \<A>1 \<A>2) s (a # word) \<and> last prun \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using Cons by argo
  hence props: "pseudo_run_well_defined_multi prun' (union_automaton_multi \<A>1 \<A>2) (prun' ! 0) word \<and> (s, a, (prun' ! 0)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2) \<and> last prun \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using well_def prun_well_defined_extension_cons_multi by fast
  hence "prun' \<noteq> []" unfolding pseudo_run_well_defined_multi_def by force
  hence "last prun' = last prun" using prun list_properties_not_empty by auto
  hence "pseudo_run_well_defined_multi prun' (union_automaton_multi \<A>1 \<A>2) (prun' ! 0) word \<and> (s, a, (prun' ! 0)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2) \<and> last prun' \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using props by presburger
  hence "(prun' ! 0) \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> (s, a, (prun' ! 0)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" using Cons by fast
  thus ?case using assms trans_union_auto_A1_state by fast
qed

lemma prun_union_auto_correct_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "pseudo_run_well_defined_multi prun (union_automaton_multi \<A>1 \<A>2) s word \<and> last prun \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<Longrightarrow> pseudo_run_well_defined prun (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) s word"
proof(induction word arbitrary: prun s)
  case Nil
  hence "prun = [s] \<and> last prun = s \<and> last prun \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using list_with_one_element unfolding pseudo_run_well_defined_multi_def by fastforce
  thus ?case unfolding pseudo_run_well_defined_def by auto
next
  have well_def: "auto_well_defined_multi (union_automaton_multi \<A>1 \<A>2) \<and> auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms union_auto_well_defined cross_renaming_iso_automaton_auto_well_defined by blast
  case (Cons a word)
  hence "prun \<noteq> [] \<and> (prun ! 0) = s" unfolding pseudo_run_well_defined_multi_def by fastforce
  then obtain prun' where prun: "prun = s # prun'" using hd_Cons_tl hd_conv_nth by metis
  hence "pseudo_run_well_defined_multi (s # prun') (union_automaton_multi \<A>1 \<A>2) s (a # word) \<and> last prun \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using Cons by argo
  hence props: "pseudo_run_well_defined_multi prun' (union_automaton_multi \<A>1 \<A>2) (prun' ! 0) word \<and> (s, a, (prun' ! 0)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2) \<and> last prun \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using well_def prun_well_defined_extension_cons_multi by fast
  hence "prun' \<noteq> []" unfolding pseudo_run_well_defined_multi_def by force
  hence "last prun' = last prun" using prun list_properties_not_empty by auto
  hence prun': "pseudo_run_well_defined_multi prun' (union_automaton_multi \<A>1 \<A>2) (prun' ! 0) word \<and> (s, a, (prun' ! 0)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2) \<and> last prun' \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using props by presburger
  hence in_states: "(prun' ! 0) \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms prun_union_auto_first_A1 by blast
  have "pseudo_run_well_defined prun' (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (prun' ! 0) word \<and> (s, a, (prun' ! 0)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" using prun' assms Cons by blast
  hence "pseudo_run_well_defined prun' (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (prun' ! 0) word \<and> (s, a, (prun' ! 0)) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using in_states trans_union_auto_A1_trans assms by fast
  thus ?case using assms prun prun_well_defined_extension_cons well_def by fast
qed

lemma trans_union_auto_A2_state:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" "s2 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  shows "s1 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
proof(rule ccontr)
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  assume assm: "s1 \<notin> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  have "auto_well_defined_multi ?\<A>" using assms union_auto_well_defined by auto
  hence "s1 \<in> states_multi ?\<A>" using assms well_def_trans_components_multi by fast
  hence "s1 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assm unfolding union_automaton_multi_def union_automaton_multi_helper_def by force  
  have well_def: "auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  have "transitions_multi ?\<A> = (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" unfolding union_automaton_multi_def union_automaton_multi_helper_def by force
  hence "(s1, a, s2) \<in> (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" using assms by argo
  thus False using well_def well_def_trans_components assms assm cross_renaming_intersection_empty by fast
qed

lemma trans_union_auto_A2_trans:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" "s2 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  shows "(s1, a, s2) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
proof -
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  have well_def: "auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  have trans: "transitions_multi ?\<A> = (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" unfolding union_automaton_multi_def union_automaton_multi_helper_def by auto
  have props: "s1 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<and> s2 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms trans_union_auto_A2_state by fast
  hence "(s1, a, s2) \<in> (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" using assms trans by argo
  thus ?thesis using well_def well_def_trans_components assms cross_renaming_intersection_empty by fast
qed

lemma prun_union_auto_first_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "pseudo_run_well_defined_multi prun (union_automaton_multi \<A>1 \<A>2) s word \<and> last prun \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<Longrightarrow> s \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
proof(induction word arbitrary: prun s)
  case Nil thus ?case using list_with_one_element unfolding pseudo_run_well_defined_multi_def by fastforce
next
  have well_def: "auto_well_defined_multi (union_automaton_multi \<A>1 \<A>2)" using assms union_auto_well_defined by blast
  case (Cons a word)
  hence "prun \<noteq> [] \<and> (prun ! 0) = s" unfolding pseudo_run_well_defined_multi_def by fastforce
  then obtain prun' where prun: "prun = s # prun'" using hd_Cons_tl hd_conv_nth by metis
  hence "pseudo_run_well_defined_multi (s # prun') (union_automaton_multi \<A>1 \<A>2) s (a # word) \<and> last prun \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using Cons by argo
  hence props: "pseudo_run_well_defined_multi prun' (union_automaton_multi \<A>1 \<A>2) (prun' ! 0) word \<and> (s, a, (prun' ! 0)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2) \<and> last prun \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using well_def prun_well_defined_extension_cons_multi by fast
  hence "prun' \<noteq> []" unfolding pseudo_run_well_defined_multi_def by force
  hence "last prun' = last prun" using prun list_properties_not_empty by auto
  hence "pseudo_run_well_defined_multi prun' (union_automaton_multi \<A>1 \<A>2) (prun' ! 0) word \<and> (s, a, (prun' ! 0)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2) \<and> last prun' \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using props by presburger
  hence "(prun' ! 0) \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<and> (s, a, (prun' ! 0)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" using Cons by fast
  thus ?case using assms trans_union_auto_A2_state by fast
qed

lemma prun_union_auto_correct_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "pseudo_run_well_defined_multi prun (union_automaton_multi \<A>1 \<A>2) s word \<and> last prun \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<Longrightarrow> pseudo_run_well_defined prun (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) s word"
proof(induction word arbitrary: prun s) 
  case Nil
  hence "prun = [s] \<and> last prun = s \<and> last prun \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using list_with_one_element unfolding pseudo_run_well_defined_multi_def by fastforce
  thus ?case unfolding pseudo_run_well_defined_def by auto
next
  have well_def: "auto_well_defined_multi (union_automaton_multi \<A>1 \<A>2) \<and> auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms union_auto_well_defined cross_renaming_iso_automaton_auto_well_defined by blast
  case (Cons a word)
  hence "prun \<noteq> [] \<and> (prun ! 0) = s" unfolding pseudo_run_well_defined_multi_def by fastforce
  then obtain prun' where prun: "prun = s # prun'" using hd_Cons_tl hd_conv_nth by metis
  hence "pseudo_run_well_defined_multi (s # prun') (union_automaton_multi \<A>1 \<A>2) s (a # word) \<and> last prun \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using Cons by argo
  hence props: "pseudo_run_well_defined_multi prun' (union_automaton_multi \<A>1 \<A>2) (prun' ! 0) word \<and> (s, a, (prun' ! 0)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2) \<and> last prun \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using well_def prun_well_defined_extension_cons_multi by fast
  hence "prun' \<noteq> []" unfolding pseudo_run_well_defined_multi_def by force
  hence "last prun' = last prun" using prun list_properties_not_empty by auto
  hence prun': "pseudo_run_well_defined_multi prun' (union_automaton_multi \<A>1 \<A>2) (prun' ! 0) word \<and> (s, a, (prun' ! 0)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2) \<and> last prun' \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using props by presburger
  hence in_states: "(prun' ! 0) \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms prun_union_auto_first_A2 by blast
  have "pseudo_run_well_defined prun' (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (prun' ! 0) word \<and> (s, a, (prun' ! 0)) \<in> transitions_multi (union_automaton_multi \<A>1 \<A>2)" using prun' assms Cons by blast
  hence "pseudo_run_well_defined prun' (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (prun' ! 0) word \<and> (s, a, (prun' ! 0)) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using in_states trans_union_auto_A2_trans assms by fast
  thus ?case using assms prun prun_well_defined_extension_cons well_def by fast
qed

theorem prun_union_auto_correct_left:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "pseudo_run_well_defined_multi prun (union_automaton_multi \<A>1 \<A>2) s word"
  shows "pseudo_run_well_defined prun (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) s word \<or> pseudo_run_well_defined prun (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) s word"
proof -
  have "last prun \<in> states_multi (union_automaton_multi \<A>1 \<A>2)" using assms last_of_prun_is_state_multi union_auto_well_defined by metis
  hence "last prun \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<or> last prun \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" unfolding union_automaton_multi_def union_automaton_multi_helper_def by force
  thus ?thesis using assms prun_union_auto_correct_A1 prun_union_auto_correct_A2 by blast
qed

lemma no_run_A2_init_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "pseudo_run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) word"
  shows "False"
  using assms cross_renaming_intersection_empty cross_renaming_iso_automaton_auto_well_defined unfolding pseudo_run_well_defined_def auto_well_defined_def by fast

lemma no_run_A1_init_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "pseudo_run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) word"
  shows "False"
  using assms cross_renaming_intersection_empty cross_renaming_iso_automaton_auto_well_defined unfolding pseudo_run_well_defined_def auto_well_defined_def by blast

corollary run_union_auto_correct_left:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "run_well_defined_multi run (union_automaton_multi \<A>1 \<A>2) word"
  shows "run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) word \<or> run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) word"
proof -
  have "run ! 0 \<in> initial_states_multi (union_automaton_multi \<A>1 \<A>2)" using assms unfolding run_well_defined_multi_def by blast
  hence "run ! 0 = initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<or> run ! 0 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" unfolding union_automaton_multi_def union_automaton_multi_helper_def by auto
  hence "pseudo_run_well_defined_multi run (union_automaton_multi \<A>1 \<A>2) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) word \<or> pseudo_run_well_defined_multi run (union_automaton_multi \<A>1 \<A>2) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) word" using assms unfolding run_well_defined_multi_def by presburger
  hence "pseudo_run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) word \<or> pseudo_run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) word \<or> pseudo_run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) word \<or> pseudo_run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) word" using assms prun_union_auto_correct_left by blast
  hence "run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) word \<or> pseudo_run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) word \<or> pseudo_run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) word \<or> run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) word" unfolding run_well_defined_def by blast
  thus ?thesis using assms no_run_A2_init_A1 no_run_A1_init_A2 by blast
qed

lemma no_acc_A2_init_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) word" "last run \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  shows "False"
proof - 
  have "last run \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined unfolding auto_well_defined_def by auto
  hence "last run \<notin> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using cross_renaming_intersection_empty by blast
  thus ?thesis using assms last_of_prun_is_state cross_renaming_iso_automaton_auto_well_defined unfolding run_well_defined_def by fast
qed

lemma no_acc_A1_init_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) word" "last run \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  shows "False"
proof - 
  have "last run \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms cross_renaming_iso_automaton_auto_well_defined unfolding auto_well_defined_def by auto
  hence "last run \<notin> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using cross_renaming_intersection_empty by blast
  thus ?thesis using assms last_of_prun_is_state cross_renaming_iso_automaton_auto_well_defined unfolding run_well_defined_def by fast
qed

theorem union_language_left:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "language_auto_multi (union_automaton_multi \<A>1 \<A>2) \<subseteq> language_auto \<A>1 \<union> language_auto \<A>2"
proof -
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  {
    fix word assume "word \<in> language_auto_multi (union_automaton_multi \<A>1 \<A>2)"
    then obtain run where "run_accepting_multi run ?\<A> word" unfolding language_auto_multi_def by auto
    hence "run_well_defined_multi run ?\<A> word \<and> last run \<in> accepting_states_multi ?\<A>" unfolding run_accepting_multi_def by blast
    hence "(run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) word \<or> run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) word) \<and> (last run \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<or> last run \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" using assms run_union_auto_correct_left unfolding union_automaton_multi_def union_automaton_multi_helper_def by auto
    hence "run_accepting run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) word \<or> run_accepting run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) word" using assms no_acc_A2_init_A1 no_acc_A1_init_A2 unfolding run_accepting_def by blast
    hence "word \<in> language_auto (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<or> word \<in> language_auto (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" unfolding language_auto_def by blast
    hence "word \<in> language_auto (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> language_auto (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" by blast
  }
  thus ?thesis using assms cross_renaming_iso_automaton_same_language by blast
qed

proposition prun_union_auto_correct_right_A1:
  assumes "pseudo_run_well_defined prun (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) s word"
  shows "pseudo_run_well_defined_multi prun (union_automaton_multi \<A>1 \<A>2) s word"
  using assms unfolding pseudo_run_well_defined_def union_automaton_multi_def union_automaton_multi_helper_def pseudo_run_well_defined_multi_def by auto

corollary run_union_auto_correct_right_A1:
  assumes "run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) word"
  shows "run_well_defined_multi run (union_automaton_multi \<A>1 \<A>2) word"
proof - 
  have "pseudo_run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) word" using assms unfolding run_well_defined_def by blast
  hence prun: "pseudo_run_well_defined_multi run (union_automaton_multi \<A>1 \<A>2) (initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) word" using assms prun_union_auto_correct_right_A1 by blast
  hence "run ! 0 = initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<in> initial_states_multi (union_automaton_multi \<A>1 \<A>2)" unfolding pseudo_run_well_defined_multi_def union_automaton_multi_def union_automaton_multi_helper_def by auto
  thus ?thesis using prun unfolding run_well_defined_multi_def by argo
qed

proposition prun_union_auto_correct_right_A2:
  assumes "pseudo_run_well_defined prun (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) s word"
  shows "pseudo_run_well_defined_multi prun (union_automaton_multi \<A>1 \<A>2) s word"
  using assms unfolding pseudo_run_well_defined_def union_automaton_multi_def union_automaton_multi_helper_def pseudo_run_well_defined_multi_def by auto

corollary run_union_auto_correct_right_A2:
  assumes "run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) word"
  shows "run_well_defined_multi run (union_automaton_multi \<A>1 \<A>2) word"
proof - 
  have "pseudo_run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) word" using assms unfolding run_well_defined_def by blast
  hence prun: "pseudo_run_well_defined_multi run (union_automaton_multi \<A>1 \<A>2) (initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)) word" using assms prun_union_auto_correct_right_A2 by blast
  hence "run ! 0 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<and> initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<in> initial_states_multi (union_automaton_multi \<A>1 \<A>2)" unfolding pseudo_run_well_defined_multi_def union_automaton_multi_def union_automaton_multi_helper_def by auto
  thus ?thesis using prun unfolding run_well_defined_multi_def by argo
qed

theorem prun_union_auto_correct:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" 
  shows "pseudo_run_well_defined prun (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) s word \<or> pseudo_run_well_defined prun (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) s word \<longleftrightarrow> pseudo_run_well_defined_multi prun (union_automaton_multi \<A>1 \<A>2) s word"
  using assms prun_union_auto_correct_right_A1 prun_union_auto_correct_right_A2 prun_union_auto_correct_left by metis

corollary run_union_auto_correct:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" 
  shows "run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) word \<or> run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) word \<longleftrightarrow> run_well_defined_multi run (union_automaton_multi \<A>1 \<A>2) word"
  using assms run_union_auto_correct_right_A1 run_union_auto_correct_right_A2 run_union_auto_correct_left by metis

theorem union_language_right:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "language_auto \<A>1 \<union> language_auto \<A>2 \<subseteq> language_auto_multi (union_automaton_multi \<A>1 \<A>2)"
proof -
  let ?\<A> = "union_automaton_multi \<A>1 \<A>2"
  {
    fix word assume "word \<in> language_auto \<A>1 \<union> language_auto \<A>2"
    hence "word \<in> language_auto (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<union> language_auto (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_same_language by blast
    then obtain run where "run_accepting run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) word \<or> run_accepting run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) word" unfolding language_auto_def by auto
    hence "(run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) word \<and> last run \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) \<or> (run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) word \<and> last run \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" unfolding run_accepting_def by blast
    hence "run_well_defined_multi run ?\<A> word \<and> (last run \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<or> last run \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" using assms run_union_auto_correct by blast
    hence "run_well_defined_multi run ?\<A> word \<and> last run \<in> accepting_states_multi ?\<A>" unfolding union_automaton_multi_def union_automaton_multi_helper_def by simp
    hence "run_accepting_multi run ?\<A> word" unfolding run_accepting_multi_def by blast
    hence "word \<in> language_auto_multi ?\<A>" unfolding language_auto_multi_def by blast
  }
  thus ?thesis by blast
qed

text \<open>Union automaton multi language correctness:\<close>
theorem union_auto_language_correctness:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "language_auto_multi (union_automaton_multi \<A>1 \<A>2) = language_auto \<A>1 \<union> language_auto \<A>2"
  using union_language_left union_language_right assms by blast

theorem union_main_better_multi:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> union_\<A> :: ('s \<times> nat, 'a) nfa_multi . auto_well_defined_multi union_\<A> \<and> alphabet_multi union_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> language_auto_multi union_\<A> = language_auto \<A>1 \<union> language_auto \<A>2"
proof -
  have "\<exists> \<A>' :: ('s, 'a) automaton. auto_well_defined \<A>' \<and> alphabet \<A>' = alphabet \<A>2 \<and> language_auto \<A>' = language_auto \<A>2" using assms existence_soft_iso_auto_lang by blast
  thus ?thesis using assms union_auto_language_correctness union_auto_well_defined union_auto_alphabet by metis
qed



text \<open>Powerset construction for NFA_multis\<close>
definition powerset_transitions_multi :: "('s, 'a) nfa_multi \<Rightarrow> ('s states, 'a) transitions" where "powerset_transitions_multi \<A> = {(S1, a, S2) . S1 \<in> Pow (states_multi \<A>) \<and> a \<in> alphabet_multi \<A> \<and> S2 = {s2 . \<exists> s1 \<in> S1 . (s1, a, s2) \<in> transitions_multi \<A>}}"

text \<open>Powerset automaton for NFAs with multiple initial states\<close>
definition powerset_automaton_multi :: "('s, 'a) nfa_multi \<Rightarrow> ('s states, 'a) automaton" where
  "powerset_automaton_multi \<A> = Automaton
    (Pow (states_multi \<A>))
    (alphabet_multi \<A>)
    (powerset_transitions_multi \<A>)
    {s . s \<in> initial_states_multi \<A>}
    {S \<in> Pow (states_multi \<A>) . S \<inter> (accepting_states_multi \<A>) \<noteq> {}}"

lemma states_of_powerset_automaton_multi:
  assumes "S \<in> states (powerset_automaton_multi \<A>) \<and> s \<in> S"
  shows "s \<in> states_multi \<A>"
  using assms unfolding powerset_automaton_multi_def by auto

lemma acc_states_powerset_automaton1_multi:
  assumes "s \<in> accepting_states_multi \<A>" "S \<in> Pow (states_multi \<A>)" "s \<in> S"
  shows "S \<in> accepting_states (powerset_automaton_multi \<A>)"
  using assms unfolding powerset_automaton_multi_def by auto

lemma acc_states_powerset_automaton2_multi: 
  assumes "S \<in> accepting_states (powerset_automaton_multi \<A>)"
  shows "\<exists> s \<in> S . s \<in> accepting_states_multi \<A>"
  using assms unfolding powerset_automaton_multi_def by auto

lemma s2_in_S2_multi:
  assumes "(s1, a, s2) \<in> transitions_multi \<A>" "s1 \<in> S1" "(S1, a, S2) \<in> transitions (powerset_automaton_multi \<A>)"
  shows "s2 \<in> S2"
  using assms unfolding powerset_automaton_multi_def powerset_transitions_multi_def by auto

text \<open>The powerset automaton multi is well-defined\<close>
theorem well_def_powerset_automaton_multi:
  assumes "auto_well_defined_multi \<A>"
  shows "auto_well_defined (powerset_automaton_multi \<A>)"
  using assms unfolding powerset_automaton_multi_def auto_well_defined_def auto_well_defined_multi_def powerset_transitions_multi_def by auto

corollary language_well_def_powerset_multi_auto:
  assumes "auto_well_defined_multi \<A>"
  shows "language_well_defined (language_auto (powerset_automaton_multi \<A>)) (alphabet (powerset_automaton_multi \<A>))"
  using well_def_powerset_automaton_multi assms automata_language_are_well_defined by blast

lemma powerset_automaton_state_existence_multi:
  assumes "auto_well_defined_multi \<A>" "S1 \<in> states (powerset_automaton_multi \<A>)" "a \<in> alphabet (powerset_automaton_multi \<A>)"
  shows "\<exists> S2 \<in> states (powerset_automaton_multi \<A>) . (S1, a, S2) \<in> transitions (powerset_automaton_multi \<A>)"
  using assms well_def_trans_components_multi unfolding powerset_automaton_multi_def powerset_transitions_multi_def by fastforce

lemma powerset_automaton_DFA_uniqueness_multi:
  assumes "(S1, a, S2) \<in> transitions (powerset_automaton_multi \<A>)" "(S1, a, S2') \<in> transitions (powerset_automaton_multi \<A>)"
  shows "S2 = S2'"
  using assms well_def_trans_components_multi unfolding powerset_automaton_multi_def powerset_transitions_multi_def by force

text \<open>The powerset automaton multi results in a DFA\<close>
theorem DFA_property_powerset_automaton_multi:
  assumes "auto_well_defined_multi \<A>"
  shows "DFA_property (powerset_automaton_multi \<A>)"
  using assms powerset_automaton_state_existence_multi powerset_automaton_DFA_uniqueness_multi unfolding DFA_property_def by metis

lemma powerset_prun_left_multi:
  assumes "auto_well_defined_multi \<A>" "S \<in> states (powerset_automaton_multi \<A>) \<and> s \<in> S"
  shows "pseudo_run_well_defined_multi prun \<A> s word \<Longrightarrow> \<exists> pRun . pseudo_run_well_defined pRun (powerset_automaton_multi \<A>) S word \<and> last prun \<in> last pRun"
proof(induction word arbitrary: prun rule: rev_induct)
  let ?\<A> = "powerset_automaton_multi \<A>"
  case Nil
  hence "prun = [s]" using list_with_one_element unfolding pseudo_run_well_defined_multi_def by fastforce
  hence "last prun = s" by auto
  hence "pseudo_run_well_defined [S] ?\<A> S [] \<and> last prun \<in> S" using assms unfolding pseudo_run_well_defined_def by force
  thus ?case by auto
next
  let ?\<A> = "powerset_automaton_multi \<A>"
  have well_def_auto: "auto_well_defined ?\<A>" using assms well_def_powerset_automaton_multi by blast
  case (snoc a word)
  hence "prun \<noteq> []" unfolding pseudo_run_well_defined_multi_def by force
  then obtain prun' where "prun = prun' @ [last prun]" using append_butlast_last_id by metis
  hence "pseudo_run_well_defined_multi prun' \<A> s word \<and> (last prun', a, last prun) \<in> transitions_multi \<A>" using prun_well_defined_extension_snoc_multi snoc by metis  
  then obtain pRun where pRun: "pseudo_run_well_defined pRun ?\<A> S word \<and> last prun' \<in> last pRun \<and> (last prun', a, last prun) \<in> transitions_multi \<A>" using snoc by blast
  hence a: "a \<in> alphabet ?\<A>" using assms well_def_trans_components_multi unfolding powerset_automaton_multi_def by force
  have "last pRun \<in> states ?\<A>" using last_of_prun_is_state well_def_auto pRun by fast
  then obtain S2 where S2: "(last pRun, a, S2) \<in> transitions ?\<A>" using powerset_automaton_state_existence_multi a assms by metis
  hence s: "last prun \<in> last (pRun @ [S2])" using pRun last_snoc s2_in_S2_multi by metis
  have "pseudo_run_well_defined (pRun @ [S2]) ?\<A> S (word @ [a])" using prun_well_defined_extension_snoc S2 pRun by fast
  thus ?case using s by blast
qed

lemma powerset_run_left_multi:
  assumes "auto_well_defined_multi \<A>" 
  shows "run_well_defined_multi run \<A> word \<Longrightarrow> \<exists> Run . run_well_defined Run (powerset_automaton_multi \<A>) word \<and> last run \<in> last Run"
proof(induction word arbitrary: run rule: rev_induct)
  let ?\<A> = "powerset_automaton_multi \<A>"
  have "auto_well_defined ?\<A>" using assms well_def_powerset_automaton_multi by blast
  hence init: "initial_state ?\<A> \<in> states ?\<A>" using assms unfolding auto_well_defined_def by blast 
  case Nil
  hence "run = [run ! 0] \<and> last run \<in> initial_states_multi \<A>" using list_with_one_element unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by fastforce
  hence "run_well_defined [initial_state ?\<A>] ?\<A> [] \<and> last run \<in> last [initial_state ?\<A>]" using init unfolding run_well_defined_def pseudo_run_well_defined_def powerset_automaton_multi_def by force
  thus ?case by auto
next
  let ?\<A> = "powerset_automaton_multi \<A>"
  have well_def_auto: "auto_well_defined ?\<A>" using assms well_def_powerset_automaton_multi by blast
  case (snoc a word)
  hence well_def: "run_well_defined_multi run \<A> (word @ [a])" using assms by auto
  hence "run \<noteq> []" unfolding pseudo_run_well_defined_multi_def run_well_defined_multi_def by force
  then obtain run' where "run = run' @ [last run]" using append_butlast_last_id by metis
  hence "run_well_defined_multi run' \<A> word \<and> (last run', a, last run) \<in> transitions_multi \<A>" using run_well_defined_extension_snoc_multi well_def by metis
  then obtain Run where Run: "run_well_defined Run ?\<A> word \<and> last run' \<in> last Run \<and> (last run', a, last run) \<in> transitions_multi \<A>" using snoc by blast
  hence a: "a \<in> alphabet ?\<A>" using assms well_def_trans_components_multi unfolding powerset_automaton_multi_def by force
  have "last Run \<in> states ?\<A>" using last_of_prun_is_state well_def_auto Run unfolding run_well_defined_def by fast
  then obtain S2 where S2: "(last Run, a, S2) \<in> transitions ?\<A>" using powerset_automaton_state_existence_multi a assms by metis
  hence s: "last run \<in> last (Run @ [S2])" using Run last_snoc s2_in_S2_multi by metis
  have "run_well_defined (Run @ [S2]) ?\<A> (word @ [a])" using prun_well_defined_extension_snoc S2 Run unfolding run_well_defined_def by fast
  thus ?case using s by blast
qed

lemma powerset_language_left_multi:
  assumes "auto_well_defined_multi \<A>"
  shows "language_auto_multi \<A> \<subseteq> language_auto (powerset_automaton_multi \<A>)"
proof -
  let ?\<A> = "powerset_automaton_multi \<A>"
  have well_def_auto: "auto_well_defined ?\<A>" using assms well_def_powerset_automaton_multi by blast
  {
    fix word assume "word \<in> language_auto_multi \<A>"
    then obtain run where "run_accepting_multi run \<A> word" unfolding language_auto_multi_def by auto
    hence run: "run_well_defined_multi run \<A> word \<and> last run \<in> accepting_states_multi \<A>" unfolding run_accepting_multi_def by auto
    hence accepting: "last run \<in> accepting_states_multi \<A>" using run by auto
    obtain Run where Run: "run_well_defined Run ?\<A> word \<and> last run \<in> last Run" using run assms powerset_run_left_multi by blast
    hence "last Run \<in> states ?\<A>" using last_of_prun_is_state well_def_auto Run unfolding run_well_defined_def by fast
    hence "last Run \<in> accepting_states ?\<A>" using accepting Run acc_states_powerset_automaton1 unfolding powerset_automaton_multi_def by auto
    hence "run_well_defined Run ?\<A> word \<and> last Run \<in> accepting_states ?\<A>" using Run by auto
    hence "word \<in> language_auto ?\<A>" unfolding language_auto_def run_accepting_def by auto
  }
  thus ?thesis by auto
qed

lemma powerset_transition_implies_transition_multi:
  assumes "(S1, a, S2) \<in> transitions (powerset_automaton_multi \<A>)" "S2 \<noteq> {}"
  shows "S1 \<noteq> {} \<and> (\<forall> s2 \<in> S2 . \<exists> s1 \<in> S1 . (s1, a, s2) \<in> transitions_multi \<A>)" 
  using assms unfolding powerset_automaton_multi_def powerset_transitions_multi_def by auto

lemma powerset_prun_right_multi: "pseudo_run_well_defined pRun (powerset_automaton_multi \<A>) S word \<and> last pRun \<noteq> {} \<Longrightarrow> \<forall> s \<in> last pRun . \<exists> prun . \<exists> s' \<in> S . pseudo_run_well_defined_multi prun \<A> s' word \<and> last prun = s"
proof(induction word arbitrary: pRun rule: rev_induct)
  let ?\<A> = "powerset_automaton_multi \<A>"
  case Nil
  hence "pRun = [S] \<and> S \<in> states ?\<A>" using list_with_one_element unfolding pseudo_run_well_defined_def by fastforce
  hence props: "last pRun = S \<and> S \<in> states ?\<A>" by auto
  {
    fix s assume "s \<in> last pRun"
    hence "s \<in> S \<and> s \<in> states_multi \<A>" using props Nil unfolding powerset_automaton_multi_def by auto
    hence "pseudo_run_well_defined_multi [s] \<A> s [] \<and> s \<in> S" unfolding pseudo_run_well_defined_multi_def by auto
  }
  thus ?case by fastforce
next
  let ?\<A> = "powerset_automaton_multi \<A>"
  case (snoc a word)
  hence length: "length pRun = length (word @ [a]) + 1 \<and> last pRun \<noteq> {}" unfolding pseudo_run_well_defined_def by blast
  hence "pRun \<noteq> [] \<and> last pRun \<noteq> {}" by auto
  then obtain pRun' where pRun': "pRun = pRun' @ [last pRun]" using append_butlast_last_id by metis
  hence "pseudo_run_well_defined (pRun' @ [last pRun]) ?\<A> S (word @ [a]) \<and> last pRun \<noteq> {}" using snoc by auto
  hence trans: "(last pRun', a, last pRun) \<in> transitions ?\<A> \<and> last pRun \<noteq> {}" using last_transition by fast
  hence not_empty: "last pRun' \<noteq> {}" using powerset_transition_implies_transition_multi length by metis
  have "pseudo_run_well_defined pRun' ?\<A> S word" using pRun' prun_well_defined_extension_snoc snoc by metis
  hence existence: "\<forall> s \<in> last pRun' . \<exists> prun . \<exists> s' \<in> S. pseudo_run_well_defined_multi prun \<A> s' word \<and> last prun = s" using snoc not_empty by blast
  have trans_in_trans: "\<forall> s' \<in> last pRun . \<exists> s'' \<in> last pRun' . (s'', a, s') \<in> transitions_multi \<A>" using trans powerset_transition_implies_transition_multi by fast
  {
    fix s' assume "\<exists> s'' \<in> last pRun' . (s'', a, s') \<in> transitions_multi \<A> \<and> s' \<in> last pRun" 
    then obtain s'' where s'': "s'' \<in> last pRun' \<and> (s'', a, s') \<in> transitions_multi \<A>" by auto
    then obtain prun s''' where "pseudo_run_well_defined_multi prun \<A> s''' word \<and> s''' \<in> S \<and> s'' = last prun" using existence by auto
    hence "pseudo_run_well_defined_multi (prun @ [s']) \<A> s''' (word @ [a]) \<and> s''' \<in> S \<and> s' = last (prun @ [s'])" using s'' prun_well_defined_extension_snoc_multi snoc by fastforce 
    hence "\<exists> prun . \<exists> s''' \<in> S . pseudo_run_well_defined_multi prun \<A> s''' (word @ [a]) \<and> last prun = s'" by auto
  }
  thus ?case using trans_in_trans by auto
qed

corollary powerset_run_right_multi:
  assumes "run_well_defined Run (powerset_automaton_multi \<A>) word \<and> last Run \<noteq> {}"
  shows "\<forall> s \<in> last Run . \<exists> run . run_well_defined_multi run \<A> word \<and> last run = s"
proof -   
  have "pseudo_run_well_defined Run (powerset_automaton_multi \<A>) (initial_state (powerset_automaton_multi \<A>))  word \<and> last Run \<noteq> {}" using assms unfolding run_well_defined_def by auto
  hence "\<forall> s \<in> last Run . \<exists> run . \<exists> s' \<in> (initial_state (powerset_automaton_multi \<A>)) . pseudo_run_well_defined_multi run \<A> s' word \<and> last run = s" using assms powerset_prun_right_multi by blast
  hence "\<forall> s \<in> last Run . \<exists> run . \<exists> s' \<in> initial_states_multi \<A> . pseudo_run_well_defined_multi run \<A> s' word \<and> last run = s" unfolding powerset_automaton_multi_def by auto
  thus ?thesis unfolding pseudo_run_well_defined_multi_def run_well_defined_multi_def by fast
qed

lemma powerset_language_right_multi: "language_auto (powerset_automaton_multi \<A>) \<subseteq> language_auto_multi \<A>"
proof -
  let ?\<A> = "powerset_automaton_multi \<A>"
  {
    fix word assume "word \<in> language_auto ?\<A>"
    then obtain Run where "run_accepting Run ?\<A> word" unfolding language_auto_def by auto
    hence Run: "run_well_defined Run ?\<A> word \<and> last Run \<in> accepting_states ?\<A>" unfolding run_accepting_def by auto
    hence existence: "\<exists> s \<in> last Run . s \<in> accepting_states_multi \<A> \<and> last Run \<noteq> {}" using acc_states_powerset_automaton2_multi by auto
    then obtain s where "s \<in> last Run \<and> s \<in> accepting_states_multi \<A>" by auto
    then obtain run where "run_well_defined_multi run \<A> word \<and> last run \<in> accepting_states_multi \<A>" using existence Run powerset_run_right_multi by metis
    hence "word \<in> language_auto_multi \<A>" unfolding run_accepting_multi_def language_auto_multi_def by auto
  }
  thus ?thesis by auto
qed

text \<open>Main result for the powerset automaton multi: language equivalence\<close>
theorem powerset_automaton_language_correctness_multi:
  assumes "auto_well_defined_multi \<A>"
  shows "language_auto_multi \<A> = language_auto (powerset_automaton_multi \<A>)"
  using assms powerset_language_left_multi powerset_language_right_multi by auto

lemma powerset_automaton_alphabet_multi: "alphabet_multi \<A> = alphabet (powerset_automaton_multi \<A>)"
  unfolding powerset_automaton_multi_def by auto

text \<open>Main result for the powerset automaton multi\<close>
theorem powerset_automaton_correctness:
  assumes "auto_well_defined_multi \<A>"
  shows "auto_well_defined (powerset_automaton_multi \<A>) \<and> DFA_property (powerset_automaton_multi \<A>) \<and> language_auto_multi \<A> = language_auto (powerset_automaton_multi \<A>)"
  using well_def_powerset_automaton_multi powerset_automaton_language_correctness_multi DFA_property_powerset_automaton_multi assms by blast

corollary existence_of_nfa_multi_same_type:
  assumes "auto_well_defined_multi (NFA_multi_\<A> :: ('s, 'a) nfa_multi)" "infinite (UNIV :: 's set)"
  shows "\<exists> DFA_\<A> :: ('s, 'a) automaton. auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = alphabet_multi NFA_multi_\<A> \<and> language_auto DFA_\<A> = language_auto_multi NFA_multi_\<A>"
  using assms powerset_automaton_correctness existence_of_DFA_same_type powerset_automaton_alphabet_multi by fast




text \<open>Transformation of finite automata with multiple initial states to a NFA with only one initial state without powerset automaton\<close>
definition normalize_nfa :: "('s, 'a) nfa_multi \<Rightarrow> ('s + unit, 'a) automaton" where
  "normalize_nfa \<A> = Automaton
    ((image Inl (states_multi \<A>)) \<union> {Inr()})
    (alphabet_multi \<A>)
    ((image (\<lambda>(s1, a, s2) . (Inl s1, a, Inl s2)) (transitions_multi \<A>)) \<union> {(Inr(), a, Inl s') | s s' a . s \<in> initial_states_multi \<A> \<and> (s, a, s') \<in> transitions_multi \<A>})
    (Inr())
    (if initial_states_multi \<A> \<inter> accepting_states_multi \<A> \<noteq> {} then {Inr()} \<union> (image Inl (accepting_states_multi \<A>)) else (image Inl (accepting_states_multi \<A>)))"

lemma normalize_alphabet_multi: "alphabet_multi \<A> = alphabet (normalize_nfa \<A>)"
  unfolding normalize_nfa_def by auto

lemma accepting_states_normalize_nfa: "Inl s \<in> accepting_states (normalize_nfa \<A>) \<longrightarrow> s \<in> accepting_states_multi \<A>"
  unfolding normalize_nfa_def by auto

proposition normalize_preserves_well_defined:
  assumes "auto_well_defined_multi \<A>"
  shows "auto_well_defined (normalize_nfa \<A>)"
proof -
  let ?\<A> = "normalize_nfa \<A>"
  have states: "finite (states ?\<A>)" using assms unfolding normalize_nfa_def auto_well_defined_multi_def by auto
  have alpha: "finite (alphabet ?\<A>)" using assms unfolding normalize_nfa_def auto_well_defined_multi_def by force
  have init: "initial_state ?\<A> \<in> states ?\<A>" using assms unfolding normalize_nfa_def auto_well_defined_multi_def by force
  have trans: "\<forall> (s1, a, s2) \<in> transitions ?\<A> . s1 \<in> states ?\<A> \<and> s2 \<in> states ?\<A> \<and> a \<in> alphabet ?\<A>" using assms unfolding normalize_nfa_def auto_well_defined_multi_def by fastforce
  have acc: "accepting_states ?\<A> \<subseteq> states ?\<A>" using assms unfolding normalize_nfa_def auto_well_defined_multi_def by auto
  thus ?thesis using states alpha init trans acc unfolding auto_well_defined_def by fastforce
qed

corollary language_well_def_normalize_multi_auto:
  assumes "auto_well_defined_multi \<A>"
  shows "language_well_defined (language_auto (normalize_nfa \<A>)) (alphabet (normalize_nfa \<A>))"
  using normalize_preserves_well_defined assms automata_language_are_well_defined by blast

definition run_transformation :: "'s run \<Rightarrow> ('s + unit) run" where "run_transformation run = Inr() # map Inl (tl run)"

lemma run_transformation_i:
  assumes "0 < i \<and> i < length run - 1"
  shows "(run_transformation run) ! i = Inl (run ! i) \<and> (run_transformation run) ! (i + 1) = Inl (run ! (i + 1))"
proof - 
  have len: "length (run_transformation run) = length run" using assms unfolding run_transformation_def by force
  hence i: "(run_transformation run) ! i = Inl (run ! i)" using assms unfolding run_transformation_def by (simp add: less_imp_diff_less nth_tl)
  have "0 < Suc i \<and> Suc i < length run" using assms by auto
  hence "(run_transformation run) ! (i + 1) = Inl (run ! (i + 1))" using len tl_list_run_spezial unfolding run_transformation_def by fastforce
  thus ?thesis using i by blast
qed

lemma run_transformation_i_spezial:
  assumes "0 < i \<and> i < length run"
  shows "(run_transformation run) ! i = Inl (run ! i)"
  using assms tl_list_run_spezial unfolding run_transformation_def by force

proposition run_transformation_left:
  assumes "auto_well_defined_multi \<A>" "run_well_defined_multi run \<A> word"
  shows "run_well_defined (run_transformation run) (normalize_nfa \<A>) word"
proof - 
  have "length run > 0" using assms unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by auto
  hence len: "length (run_transformation run) = length run" unfolding run_transformation_def by auto
  hence length: "length (run_transformation run) = length word + 1" using assms unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by argo
  have "(run_transformation run) ! 0 = initial_state (normalize_nfa \<A>)" using assms unfolding run_transformation_def normalize_nfa_def by auto
  hence init: "(run_transformation run) ! 0 = initial_state (normalize_nfa \<A>) \<and> initial_state (normalize_nfa \<A>) \<in> states (normalize_nfa \<A>)" using assms normalize_preserves_well_defined unfolding auto_well_defined_def by blast
  {
    fix i assume assm: "i < length run - 1"
    hence "((run_transformation run) ! i, word ! i, (run_transformation run) ! (i + 1)) \<in> transitions (normalize_nfa \<A>)"
    proof(cases i)
      case 0
      hence trans: "(run ! 0, word ! 0, run ! 1) \<in> transitions_multi \<A> \<and> run ! 0 \<in> initial_states_multi \<A>" using assms assm unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by force
      have "(run_transformation run) ! 0 = Inr()" unfolding run_transformation_def by auto
      hence "(run_transformation run) ! 0 = Inr() \<and> (run_transformation run) ! 1 = Inl (run ! 1)" using assm 0 run_transformation_i_spezial by force
      thus ?thesis using trans 0 unfolding normalize_nfa_def by force
    next
      case(Suc nat)
      hence equi: "(run_transformation run) ! i = Inl (run ! i) \<and> (run_transformation run) ! (i + 1) = Inl (run ! (i + 1))" using assm run_transformation_i by blast
      have "(run ! i, word ! i, run ! (i + 1)) \<in> transitions_multi \<A>" using assms assm unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by blast
      hence "(Inl (run ! i), word ! i, Inl (run ! (i + 1))) \<in> transitions (normalize_nfa \<A>)" unfolding normalize_nfa_def by force
      thus ?thesis using equi by argo
    qed
  }
  hence "(\<forall> i < length (run_transformation run) - 1 . ((run_transformation run) ! i, word ! i, (run_transformation run) ! (i + 1)) \<in> transitions (normalize_nfa \<A>))" using len by presburger
  thus ?thesis using length init assms unfolding run_well_defined_def pseudo_run_well_defined_def by argo
qed

lemma nfa_multi_run_left_i:
  assumes "auto_well_defined_multi \<A>" "run_well_defined_multi run \<A> word" "length run > 1"
  shows "run_well_defined (run_transformation run) (normalize_nfa \<A>) word \<and> Inl (last run) = last (run_transformation run)"
proof - 
  have well_def: "run_well_defined (run_transformation run) (normalize_nfa \<A>) word" using assms run_transformation_left by blast
  have "length run - 1 > 0 \<and> length run - 1 < length run" using assms by auto
  hence equi: "(run_transformation run) ! (length run - 1) = Inl (run ! (length run - 1))" using run_transformation_i_spezial by blast
  have len: "length (run_transformation run) = length run" using assms unfolding run_transformation_def by auto
  hence "run \<noteq> [] \<and> run_transformation run \<noteq> []" using assms by fastforce
  hence "last run = run ! (length run - 1) \<and> last (run_transformation run) = (run_transformation run) ! (length run - 1)" using list_properties_not_empty len by metis
  hence "Inl (last run) = last (run_transformation run)" using equi by argo
  thus ?thesis using well_def assms by blast
qed

lemma nfa_multi_language_left:
  assumes "auto_well_defined_multi \<A>"
  shows "language_auto_multi \<A> \<subseteq> language_auto (normalize_nfa \<A>)"
proof -
  let ?\<A> = "normalize_nfa \<A>"
  {
    fix word assume "word \<in> language_auto_multi \<A>"
    then obtain run where "run_accepting_multi run \<A> word" unfolding language_auto_multi_def by blast
    hence run: "run_well_defined_multi run \<A> word \<and> last run \<in> accepting_states_multi \<A>" unfolding run_accepting_multi_def by auto
    have "length run \<ge> 1" using run unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by presburger
    then consider (case1) "length run = 1" | (case2) "length run > 1" by linarith
    hence "\<exists> Run . run_well_defined Run ?\<A> word \<and> last Run \<in> accepting_states ?\<A>"
    proof cases
      case case1
      hence "last run \<in> initial_states_multi \<A> \<and> last run \<in> accepting_states_multi \<A>" using run list_with_one_element unfolding run_well_defined_multi_def by metis
      hence inr: "Inr() \<in> accepting_states ?\<A>" unfolding normalize_nfa_def by auto
      have well_def: "run_well_defined (run_transformation run) ?\<A> word" using run_transformation_left assms run by auto
      have "run_transformation run = [Inr()]" using list_with_one_element Nil_is_map_conv case1 unfolding run_transformation_def by metis
      hence "last (run_transformation run) \<in> accepting_states ?\<A>" using list_with_one_element inr by auto
      thus ?thesis using well_def by blast
    next
      case case2
      hence well_def: "run_well_defined (run_transformation run) ?\<A> word \<and> Inl (last run) = last (run_transformation run)" using run assms nfa_multi_run_left_i by blast
      have "Inl (last run) \<in> accepting_states ?\<A>" using run unfolding normalize_nfa_def by simp
      thus ?thesis using well_def by auto
    qed
    hence "word \<in> language_auto ?\<A>" unfolding language_auto_def run_accepting_def by auto
  }
  thus ?thesis by auto
qed

proposition run_transformation_right_base:
  assumes "auto_well_defined_multi \<A>" "run_well_defined run (normalize_nfa \<A>) []" "last run \<in> accepting_states (normalize_nfa \<A>)"
  shows "\<exists> run' . run_well_defined_multi run' \<A> [] \<and> last run' \<in> accepting_states_multi \<A>"
proof - 
  let ?\<A> = "normalize_nfa \<A>"
  have "length run = 1 \<and> run ! 0 = Inr()" using assms unfolding run_well_defined_def pseudo_run_well_defined_def normalize_nfa_def by force
  hence "run = [Inr()]" using list_with_one_element by metis
  hence "initial_states_multi \<A> \<inter> accepting_states_multi \<A> \<noteq> {}" using assms unfolding normalize_nfa_def by force
  then obtain s where s: "s \<in> initial_states_multi \<A> \<and> s \<in> accepting_states_multi \<A>" by auto
  hence "s \<in> initial_states_multi \<A> \<and> s \<in> states_multi \<A> \<and> s \<in> accepting_states_multi \<A>" using assms unfolding auto_well_defined_multi_def by fast
  hence "run_well_defined_multi [s] \<A> [] \<and> s \<in> accepting_states_multi \<A>" using assms unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by auto
  thus ?thesis by auto
qed

proposition run_transformation_right:
  assumes "auto_well_defined_multi \<A>"
  shows "run_well_defined run (normalize_nfa \<A>) (word @ [a]) \<Longrightarrow> \<exists> run' . run_well_defined_multi run' \<A> (word @ [a]) \<and> Inl (last run') = last run"
proof(induction word arbitrary: run a rule: rev_induct)
  case Nil
  let ?\<A> = "normalize_nfa \<A>"
  have well_def: "auto_well_defined ?\<A>" using assms normalize_preserves_well_defined by blast
  hence init: "run ! 0 = Inr()" using Nil unfolding run_well_defined_def pseudo_run_well_defined_def normalize_nfa_def by fastforce
  have "(run ! 0, [a] ! 0, run ! 1) \<in> transitions ?\<A>" using Nil unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "(Inr(), [a] ! 0, run ! 1) \<in> transitions ?\<A>" using init by auto
  hence "\<exists> s s' . s \<in> initial_states_multi \<A> \<and> (s, [a] ! 0, s') \<in> transitions_multi \<A> \<and> (run ! 1) = Inl s'" unfolding normalize_nfa_def by auto
  then obtain s s' where "s \<in> initial_states_multi \<A> \<and> (s, [a] ! 0, s') \<in> transitions_multi \<A> \<and> (run ! 1) = Inl s'" by blast
  hence "s \<in> initial_states_multi \<A> \<and> s \<in> states_multi \<A> \<and> (s, [a] ! 0, s') \<in> transitions_multi \<A> \<and> (run ! 1) = Inl s'" using assms unfolding auto_well_defined_multi_def by fast
  hence run: "run_well_defined_multi [s, s'] \<A> [a] \<and> (run ! 1) = Inl (last [s, s'])" unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by auto
  have "length run = 2 \<and> run \<noteq> []" using Nil unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "last run = run ! 1" using list_properties_not_empty by fastforce
  thus ?case using run by auto
next
  let ?\<A> = "normalize_nfa \<A>"
  have well_def: "auto_well_defined ?\<A>" using assms normalize_preserves_well_defined by auto
  case (snoc a' word)
  hence well_def_run: "run_well_defined run ?\<A> ((word @ [a']) @ [a])" using well_def by blast
  hence "run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain run' where "run = run' @ [last run]" using append_butlast_last_id by metis
  hence trans: "run_well_defined run' ?\<A> (word @ [a']) \<and> (last run', a, last run) \<in> transitions ?\<A>" using prun_well_defined_extension_snoc well_def_run well_def unfolding run_well_defined_def by metis
  hence "\<exists> run''. run_well_defined_multi run'' \<A> (word @ [a']) \<and> Inl (last run'') = last run'" using snoc by blast
  then obtain run'' where obtained_run: "run_well_defined_multi run'' \<A> (word @ [a']) \<and> Inl (last run'') = last run' \<and> (last run', a, last run) \<in> transitions ?\<A>" using trans by blast
  hence "\<exists> s' . Inl s' = last run" unfolding normalize_nfa_def by force
  then obtain s' where s': "Inl s' = last run" by blast
  hence "run_well_defined_multi run'' \<A> (word @ [a']) \<and> (last run'', a, s') \<in> transitions_multi \<A>" using obtained_run unfolding normalize_nfa_def by force
  hence "run_well_defined_multi (run'' @ [s']) \<A> ((word @ [a']) @ [a]) \<and> Inl s' = last run" using s' run_well_defined_extension_snoc_multi assms by fast
  thus ?case by force
qed

lemma nfa_multi_language_right:
  assumes "auto_well_defined_multi \<A>"
  shows "language_auto (normalize_nfa \<A>) \<subseteq> language_auto_multi \<A>"
proof -
  let ?\<A> = "normalize_nfa \<A>"
  {
    fix word assume "word \<in> language_auto ?\<A>"
    then obtain run where "run_accepting run ?\<A> word" unfolding language_auto_def by fast
    hence run: "run_well_defined run ?\<A> word \<and> last run \<in> accepting_states ?\<A>" unfolding run_accepting_def by blast
    hence "\<exists> run' . run_well_defined_multi run' \<A> word \<and> last run' \<in> accepting_states_multi \<A>"
    proof(cases word)
      case Nil thus ?thesis using assms run run_transformation_right_base by fast
    next
      case(Cons a list)
      hence "word \<noteq> []" by auto
      then obtain word' where "word = word' @ [last word]" using append_butlast_last_id by metis
      then obtain run' where "run_well_defined_multi run' \<A> word \<and> Inl (last run') = last run" using assms run_transformation_right run by metis
      hence "run_well_defined_multi run' \<A> word \<and> Inl (last run') \<in> accepting_states ?\<A>" using run by auto
      thus ?thesis using accepting_states_normalize_nfa by fast
      qed
    hence "word \<in> language_auto_multi \<A>" unfolding language_auto_multi_def run_accepting_multi_def by auto
  }
  thus ?thesis by auto
qed

text \<open>Main result for the normalize_nfa automaton: language equivalence\<close>
theorem normalize_nfa_language_correctness:
  assumes "auto_well_defined_multi \<A>"
  shows "language_auto_multi \<A> = language_auto (normalize_nfa \<A>)"
  using assms nfa_multi_language_left nfa_multi_language_right by auto

corollary nfa_multi_main:
  assumes "auto_well_defined_multi (NFA_multi_\<A> :: ('s, 'a) nfa_multi)"
  shows "\<exists> NFA_\<A> :: ('s + unit, 'a) automaton . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = alphabet_multi NFA_multi_\<A> \<and> language_auto NFA_\<A> = language_auto_multi NFA_multi_\<A>"
  using assms normalize_nfa_language_correctness normalize_preserves_well_defined normalize_alphabet_multi by fast

corollary existence_of_nfa_same_type:
  assumes "auto_well_defined_multi (NFA_multi_\<A> :: ('s, 'a) nfa_multi)" "infinite (UNIV :: 's set)"
  shows "\<exists> NFA_\<A> :: ('s, 'a) automaton . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = alphabet_multi NFA_multi_\<A> \<and> language_auto NFA_\<A> = language_auto_multi NFA_multi_\<A>"
  using assms existence_soft_iso_auto_lang nfa_multi_main by metis

theorem expressive_power_multi_nfa_main:
  assumes "infinite (UNIV :: 's set)"
  shows "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>} = {L . \<exists> (NFA_\<A>_multi :: ('s, 'a) nfa_multi) . auto_well_defined_multi NFA_\<A>_multi \<and> alphabet_multi NFA_\<A>_multi = \<Sigma> \<and> L = language_auto_multi NFA_\<A>_multi}"
  using assms existence_of_nfa_same_type existence_of_NFA_to_multi_same_type by fastforce

text \<open>Union and general type conversion\<close>
theorem union_main_better:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> union_\<A> :: ('s \<times> nat + unit, 'a) automaton . auto_well_defined union_\<A> \<and> alphabet union_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> language_auto union_\<A> = language_auto \<A>1 \<union> language_auto \<A>2"
  using assms union_main_better_multi nfa_multi_main by metis

theorem existence_of_union_same_type:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> union_\<A> :: ('s, 'a) automaton . auto_well_defined union_\<A> \<and> alphabet union_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> language_auto union_\<A> = language_auto \<A>1 \<union> language_auto \<A>2"
proof -
  have "\<exists> union_\<A> :: ('s \<times> nat + unit, 'a) automaton . auto_well_defined union_\<A> \<and> alphabet union_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> language_auto union_\<A> = language_auto \<A>1 \<union> language_auto \<A>2" using assms union_main_better by blast 
  thus ?thesis using assms existence_soft_iso_auto_lang by metis
qed

end