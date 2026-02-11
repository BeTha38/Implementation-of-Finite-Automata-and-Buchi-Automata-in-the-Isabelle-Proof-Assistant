theory masterarbeit_benno_thalmann

imports Main list_and_set_theorems

begin

text \<open>Author: Benno Thalmann, Date: 02.01.2025, Master Thesis in Comptuer Science, University of Fribourg\<close>
text \<open>Last updated: 11.2.2026\<close>

text \<open>Type definitions\<close>
type_synonym 'a symbol = "'a"
type_synonym 'a alphabet = "'a symbol set"
type_synonym 'a word = "'a symbol list" 
type_synonym 'a language = "'a word set"

text \<open>Predicate if word is over an alphabet\<close>
definition word_well_defined :: "'a word \<Rightarrow> 'a alphabet \<Rightarrow> bool" where "word_well_defined word \<Sigma> = (set word \<subseteq> \<Sigma>)"

proposition word_well_def_equivalence: "word_well_defined word \<Sigma> \<longleftrightarrow> (\<forall> a \<in> set word . a \<in> \<Sigma>)"
  unfolding word_well_defined_def by auto

lemma word_well_def_snoc: "word_well_defined (word @ [a]) \<Sigma> \<longleftrightarrow> word_well_defined word \<Sigma> \<and> a \<in> \<Sigma>"
  unfolding word_well_defined_def by auto

lemma word_well_def_cons: "word_well_defined (a # word) \<Sigma> \<longleftrightarrow> word_well_defined word \<Sigma> \<and> a \<in> \<Sigma>"
  unfolding word_well_defined_def by auto

proposition word_well_def_append: "word_well_defined (word1 @ word2) \<Sigma> \<longleftrightarrow> word_well_defined word1 \<Sigma> \<and> word_well_defined word2 \<Sigma>"
  unfolding word_well_defined_def by auto

definition language_well_defined :: "'a language \<Rightarrow> 'a alphabet \<Rightarrow> bool" where "language_well_defined L \<Sigma> = (\<forall> word \<in> L . word_well_defined word \<Sigma>)"




text \<open>Type definitions\<close>
type_synonym 's state = "'s"
type_synonym 's states = "'s state set"
type_synonym ('s, 'a) transition = "('s state \<times> 'a symbol \<times> 's state)"
type_synonym ('s, 'a) transitions = "('s, 'a) transition set"
type_synonym 's run = "'s state list"

text \<open>Datatype of finite automata\<close>
datatype ('s, 'a) automaton = Automaton
  (states : "'s states")
  (alphabet : "'a alphabet")
  (transitions : "('s , 'a) transitions")
  (initial_state : "'s state")
  (accepting_states : "'s states")

text \<open>Predicate for well-definedness\<close>
definition auto_well_defined :: "('s, 'a) automaton \<Rightarrow> bool" where
  "auto_well_defined \<A> =
    (finite (states \<A>) \<and>
    finite (alphabet \<A>) \<and>
    initial_state \<A> \<in> states \<A> \<and>
    (\<forall> (s1, a, s2) \<in> transitions \<A> . s1 \<in> states \<A> \<and> a \<in> alphabet \<A> \<and> s2 \<in> states \<A>) \<and>
    accepting_states \<A> \<subseteq> states \<A>)"

proposition NFA_is_finite:
  assumes "auto_well_defined \<A>"
  shows "finite (accepting_states \<A>) \<and> finite (transitions \<A>)"
proof - 
  have accepting_states: "finite (accepting_states \<A>)" using assms finite_subset unfolding auto_well_defined_def by auto
  have finite: "finite {(s1, a, s2) . s1 \<in> states \<A> \<and> a \<in> alphabet \<A> \<and> s2 \<in> states \<A>}" using assms unfolding auto_well_defined_def by simp
  have "transitions \<A> \<subseteq> {(s1, a, s2) . s1 \<in> states \<A> \<and> a \<in> alphabet \<A> \<and> s2 \<in> states \<A>}" using assms unfolding auto_well_defined_def by fast
  hence "finite (transitions \<A>)" using assms finite_subset finite by blast
  thus ?thesis using accepting_states by auto
qed

lemma at_least_one_state:
  assumes "auto_well_defined \<A>"
  shows "card (states \<A>) > 0"
proof(rule ccontr)
  assume "\<not> card (states \<A>) > 0"
  hence card: "card (states \<A>) = 0" by blast
  have "initial_state \<A> \<in> states \<A> \<and> finite (states \<A>)" using assms unfolding auto_well_defined_def by blast
  thus False using card by auto
qed

lemma well_def_trans_components:
  assumes "auto_well_defined \<A>" "(s1, a, s2) \<in> transitions \<A>"
  shows "s1 \<in> states \<A> \<and> a \<in> alphabet \<A> \<and> s2 \<in> states \<A>"
  using assms unfolding auto_well_defined_def by fast

text \<open>Predicate for DFAs\<close>
definition DFA_property :: "('s, 'a) automaton \<Rightarrow> bool" where "DFA_property \<A> = (\<forall> s1 \<in> states \<A> . \<forall> a \<in> alphabet \<A> . \<exists>! s2 \<in> states \<A> . (s1, a, s2) \<in> transitions \<A>)"


 



text \<open>First property for well-definedness of a pseudo-run\<close>
definition pseudo_run_well_defined :: "'s run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 's state \<Rightarrow> 'a word \<Rightarrow> bool" where
  "pseudo_run_well_defined prun \<A> s word =
    (length prun = length word + 1 \<and>
    prun ! 0 = s \<and> s \<in> states \<A> \<and>
    (\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>))"

definition prun_states :: "'s run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> bool" where "prun_states prun \<A> = (set prun \<subseteq> states \<A>)"

proposition prun_states_equivalence: "prun_states prun \<A> \<longleftrightarrow> (\<forall> s \<in> set prun . s \<in> states \<A>)"
  unfolding prun_states_def by auto

lemma prun_states_snoc: "prun_states prun \<A> \<and> s \<in> states \<A> \<longleftrightarrow> prun_states (prun @ [s]) \<A>"
  unfolding prun_states_def by auto

theorem well_def_implies_prun_states:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined prun \<A> s word"
  shows "prun_states prun \<A>"
proof(cases word)
  case Nil 
  hence "prun = [s] \<and> s \<in> states \<A>" using assms list_with_one_element unfolding pseudo_run_well_defined_def by force
  thus ?thesis using prun_states_equivalence by fastforce
next
  let ?n = "length prun"
  case (Cons a word)
  hence len: "?n > 1" using assms unfolding pseudo_run_well_defined_def by auto
  have prun_i: "\<forall> i < ?n - 1 . prun ! i \<in> states \<A>" using well_def_trans_components assms unfolding pseudo_run_well_defined_def by fast
  have "\<forall> i < ?n - 1 . prun ! (i + 1) \<in> states \<A>" using well_def_trans_components assms unfolding pseudo_run_well_defined_def by fast
  hence "prun ! (?n - 2 + 1) \<in> states \<A>" using len by force
  hence "prun ! (?n - 1) \<in> states \<A>" using len simple_math by metis
  hence "\<forall> i < ?n . prun ! i \<in> states \<A>" using prun_i merge_one_more by simp
  thus ?thesis using prun_states_equivalence in_set_conv_nth by metis
qed

corollary last_of_prun_is_state:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined prun \<A> s word"
  shows "last prun \<in> states \<A>"
proof -
  have "prun \<noteq> []" using assms unfolding pseudo_run_well_defined_def by fastforce
  hence "last prun \<in> set prun" by auto
  thus ?thesis using assms well_def_implies_prun_states unfolding prun_states_def by fast
qed

theorem well_def_implies_word_well_defined:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined prun \<A> s word"
  shows "word_well_defined word (alphabet \<A>)"
proof - 
  have "length prun = length word + 1 \<and> (\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>)" using assms unfolding pseudo_run_well_defined_def by blast
  hence "\<forall> i < length word . word ! i \<in> alphabet \<A>" using well_def_trans_components assms by fastforce
  hence "\<forall> a \<in> set word . a \<in> alphabet \<A>" using in_set_conv_nth by metis
  thus ?thesis using word_well_def_equivalence by fast
qed

lemma prun_well_defined_induction_cons:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined prun \<A> state word" "(s, a, state) \<in> transitions \<A>"
  shows "pseudo_run_well_defined (s # prun) \<A> s (a # word)"
proof -
  have states: "s \<in> states \<A> \<and> (s # prun) ! 0 = s" using assms well_def_trans_components by force
  have props: "length prun = length word + 1 \<and> (\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>) \<and> (prun ! 0) = state" using assms unfolding pseudo_run_well_defined_def by blast
  hence len: "length (s # prun) = length (a # word) + 1" by force
  {
    fix i assume assm: "i < length (s # prun) - 1"
    hence "((s # prun) ! i, (a # word) ! i, (s # prun) ! (i + 1)) \<in> transitions \<A>"
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
  thus ?thesis using states len unfolding pseudo_run_well_defined_def by blast
qed

lemma prun_well_defined_cons:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined (s # prun) \<A> s (a # word)"
  shows "pseudo_run_well_defined prun \<A> (prun ! 0) word \<and> (s, a, (prun ! 0)) \<in> transitions \<A>"
proof -
  have props: "length (s # prun) = length (a # word) + 1 \<and> (s # prun) ! 0 = s \<and> s \<in> states \<A> \<and> (\<forall> i < length (s # prun) - 1 . ((s # prun) ! i, (a # word) ! i, (s # prun) ! (i + 1)) \<in> transitions \<A>)" using assms unfolding pseudo_run_well_defined_def by blast
  hence "length prun = length word + 1 \<and> ((s # prun) ! 0, (a # word) ! 0, (s # prun) ! (0 + 1)) \<in> transitions \<A>" by auto
  hence len: "length prun = length word + 1 \<and> (s, a, prun ! 0) \<in> transitions \<A>" by auto
  hence init: "prun ! 0 \<in> states \<A>" using assms well_def_trans_components by fast
  {
    fix i assume assm: "i < length prun - 1"
    then obtain j where j: "j = i + 1" by auto
    hence "j < length (s # prun) - 1" using assm by force
    hence i_step: "((s # prun) ! j, (a # word) ! j, (s # prun) ! (j + 1)) \<in> transitions \<A>" using props by blast
    have "((s # prun) ! j, (a # word) ! j, (s # prun) ! (j + 1)) = (prun ! i, word ! i, prun ! (i + 1))" using j by auto
    hence "(prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>" using i_step by argo
  }
  hence "\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>" by blast
  thus ?thesis using len init unfolding pseudo_run_well_defined_def by blast
qed

proposition prun_well_defined_extension_cons:
  assumes "auto_well_defined \<A>"
  shows "pseudo_run_well_defined (s # prun) \<A> s (a # word) \<longleftrightarrow> pseudo_run_well_defined prun \<A> (prun ! 0) word \<and> (s, a, (prun ! 0)) \<in> transitions \<A>"
  using assms prun_well_defined_cons prun_well_defined_induction_cons by metis

lemma prun_well_defined_induction_snoc:
  assumes "pseudo_run_well_defined prun \<A> s' word" "(last prun, a, s) \<in> transitions \<A>"
  shows "pseudo_run_well_defined (prun @ [s]) \<A> s' (word @ [a])"
proof -
  let ?n = "length prun"
  let ?prun = "prun @ [s]"
  let ?word = "word @ [a]"
  have properties: "?n = length word + 1 \<and> ?n - 1 = length word \<and> prun \<noteq> [] \<and> prun ! 0 = s' \<and> prun ! 0 \<in> states \<A>" using assms unfolding pseudo_run_well_defined_def by auto
  hence snoc_transition_step: "\<forall> i < ?n - 1 . (?prun ! i, ?word ! i, ?prun ! (i + 1)) \<in> transitions \<A>" using assms list_properties_length unfolding pseudo_run_well_defined_def by metis
  have "?prun ! (?n - 1) = last prun \<and> ?prun ! ?n = s \<and> ?word ! (?n - 1) = a" using properties list_properties_not_empty nth_append_length by metis
  hence "(?prun ! (?n - 1), ?word ! (?n - 1), ?prun ! ((?n - 1) + 1)) \<in> transitions \<A>" using properties assms by auto
  hence "\<forall> i < length ?prun - 1 . (?prun ! i, ?word ! i, ?prun ! (i + 1)) \<in> transitions \<A>" using snoc_transition_step merge_one_more by simp
  thus ?thesis using properties list_properties_not_empty unfolding pseudo_run_well_defined_def by force
qed

lemma last_transition:
  assumes "pseudo_run_well_defined (prun @ [s]) \<A> s' (word @ [a])"
  shows "(last prun, a, s) \<in> transitions \<A>"
proof - 
  let ?n = "length (prun @ [s])"
  let ?prun = "prun @ [s]"
  let ?word = "word @ [a]"
  have "?n = length ?word + 1" using assms unfolding pseudo_run_well_defined_def by blast
  hence properties: "?n > 1 \<and> ?n = length ?word + 1 \<and> ?prun \<noteq> []" by auto
  have "\<forall> i < ?n - 1 . (?prun ! i, ?word ! i, ?prun ! (i + 1)) \<in> transitions \<A>" using assms unfolding pseudo_run_well_defined_def by auto
  hence trans: "(?prun ! (?n - 2), ?word ! (?n - 2), ?prun ! (?n - 2 + 1)) \<in> transitions \<A>" using properties by force
  have last: "?prun ! (length ?prun - 2) = last prun \<and> ?word ! (?n - 2) = a" using list_properties_not_empty properties by force
  have "prun \<noteq> []" using properties by auto
  hence "?prun ! (?n - 2 + 1) = s" by auto
  thus ?thesis using last trans by auto
qed

lemma prun_well_defined_snoc:
  assumes "pseudo_run_well_defined (prun @ [s]) \<A> s' (word @ [a])"
  shows "pseudo_run_well_defined prun \<A> s' word \<and> (last prun, a, s) \<in> transitions \<A>"
proof -
  let ?n = "length prun"
  let ?prun = "prun @ [s]"
  let ?word = "word @ [a]"
  have "length ?prun = length ?word + 1 \<and> ?prun ! 0 = s' \<and> s' \<in> states \<A>" using assms unfolding pseudo_run_well_defined_def by blast
  hence properties: "length ?prun = length ?word + 1 \<and> ?n - 1 = length word \<and> ?prun ! 0 = s' \<and> s' \<in> states \<A>  \<and> prun \<noteq> []" by auto
  hence initial_state: "prun ! 0 = s' \<and> s' \<in> states \<A>" using list_properties_not_empty by metis
  have "\<forall> i < ?n - 1 . (?prun ! i, ?word ! i, ?prun ! (i + 1)) \<in> transitions \<A>" using assms unfolding pseudo_run_well_defined_def by auto
  hence i_step: "\<forall> i < ?n - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>" using properties list_properties_length by metis
  have "(last prun, a, s) \<in> transitions \<A>" using assms last_transition by fast
  thus ?thesis using properties initial_state i_step unfolding pseudo_run_well_defined_def by auto
qed

proposition prun_well_defined_extension_snoc: "pseudo_run_well_defined (prun @ [s]) \<A> s' (word @ [a]) \<longleftrightarrow> pseudo_run_well_defined prun \<A> s' word \<and> (last prun, a, s) \<in> transitions \<A>"
  using prun_well_defined_snoc prun_well_defined_induction_snoc by metis

text \<open>For a well-defined word, there is exactly one pseudo_run on a DFA\<close>
theorem exists_only_one_prun_for_DFA:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "word_well_defined word (alphabet \<A>) \<Longrightarrow> \<forall> s \<in> states \<A> . \<exists>! prun . pseudo_run_well_defined prun \<A> s word"
proof(induction word rule: rev_induct)
  case Nil
  {
    fix s assume "s \<in> states \<A>"
    hence existence: "pseudo_run_well_defined [s] \<A> s []" unfolding pseudo_run_well_defined_def by auto
    {
      fix prun1 prun2 assume "pseudo_run_well_defined prun1 \<A> s [] \<and> pseudo_run_well_defined prun2 \<A> s []"
      hence "length prun1 = 1 \<and> prun1 ! 0 = s \<and> length prun2 = 1 \<and> prun2 ! 0 = s" using assms unfolding pseudo_run_well_defined_def by auto 
      hence "prun1 = prun2" using list_with_one_element by metis
    }
    hence "\<exists>! prun . pseudo_run_well_defined prun \<A> s []" using existence by blast
  }
  thus ?case by auto
next
  case (snoc a word)
  {
    fix s assume "s \<in> states \<A>"
    hence existence: "\<exists>! prun . pseudo_run_well_defined prun \<A> s word \<and> a \<in> alphabet \<A>" using snoc word_well_def_snoc by metis
    then obtain prun s' where prun: "pseudo_run_well_defined prun \<A> s word \<and> (last prun, a, s') \<in> transitions \<A>" using assms snoc last_of_prun_is_state unfolding DFA_property_def by metis 
    hence well_def: "pseudo_run_well_defined (prun @ [s']) \<A> s (word @ [a])" using prun_well_defined_extension_snoc by fast
    {
      fix pruna prunb assume assm: "pseudo_run_well_defined pruna \<A> s (word @ [a]) \<and> pseudo_run_well_defined prunb \<A> s (word @ [a])"
      hence "pruna \<noteq> [] \<and> prunb \<noteq> []" unfolding pseudo_run_well_defined_def by force
      then obtain prunA sA prunB sB where pruns: "pruna = (prunA @ [sA]) \<and> prunb = (prunB @ [sB])" using append_butlast_last_id by metis
      hence "pseudo_run_well_defined prunA \<A> s word \<and> pseudo_run_well_defined prunB \<A> s word" using prun_well_defined_extension_snoc assm by fast
      hence equi: "prunA = prunB" using assm existence by auto
      have "(last prunA, a, sA) \<in> transitions \<A> \<and> (last prunB, a, sB) \<in> transitions \<A>" using assm pruns prun_well_defined_extension_snoc by fast
      hence "pruna = prunb" using assms equi pruns well_def_trans_components unfolding DFA_property_def by metis
    }
    hence "\<exists>! prun . pseudo_run_well_defined prun \<A> s (word @ [a])" using well_def by blast
  }
  thus ?case by blast
qed

text \<open>Definition of an accepting run over a word\<close>
definition run_well_defined :: "'s run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a word \<Rightarrow> bool" where "run_well_defined run \<A> word = pseudo_run_well_defined run \<A> (initial_state \<A>) word"

corollary exists_only_one_run_for_DFA:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "word_well_defined word (alphabet \<A>)"
  shows "\<exists>! run . run_well_defined run \<A> word"
  using assms exists_only_one_prun_for_DFA unfolding auto_well_defined_def run_well_defined_def by fast

definition run_accepting :: "'s run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a word \<Rightarrow> bool" where "run_accepting run \<A> word = (run_well_defined run \<A> word \<and> last run \<in> accepting_states \<A>)"

text \<open>Definition of a language accepted by an automaton\<close>
definition language_auto :: "('s, 'a) automaton \<Rightarrow> 'a language" where "language_auto \<A> = {word . \<exists> run . run_accepting run \<A> word}"

lemma no_acc_states:
  assumes "accepting_states \<A> = {}"
  shows "language_auto \<A> = {}"
  using assms unfolding language_auto_def run_accepting_def by blast

text \<open>If the automaton is well-defined, then the accepted words will be well-defined\<close>
corollary word_in_language_is_well_defined:
  assumes "auto_well_defined \<A>" "word \<in> language_auto \<A>"
  shows "word_well_defined word (alphabet \<A>)"
  using assms well_def_implies_word_well_defined unfolding language_auto_def run_accepting_def run_well_defined_def by auto

corollary not_well_def_words_not_in_language:
  assumes "auto_well_defined \<A>" "\<not> word_well_defined word (alphabet \<A>)"
  shows "word \<notin> language_auto \<A>"
  using assms word_in_language_is_well_defined by auto

proposition automata_language_are_well_defined:
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (language_auto \<A>) (alphabet \<A>)"
  using assms word_in_language_is_well_defined unfolding language_well_defined_def by blast





text \<open>More about general languages\<close>
definition sigma_star :: "'a alphabet \<Rightarrow> 'a language" where "sigma_star \<Sigma> = {word . word_well_defined word \<Sigma>}"

proposition sigma_star_well_defined: "language_well_defined (sigma_star \<Sigma>) \<Sigma>"
  unfolding sigma_star_def language_well_defined_def by blast

lemma language_subset_of_sigma_star:
  assumes "language_well_defined L \<Sigma>"
  shows "L \<subseteq> sigma_star \<Sigma>"
  using assms unfolding sigma_star_def language_well_defined_def by auto

lemma subsets_of_sigma_star:
  assumes "L \<subseteq> sigma_star \<Sigma>"
  shows "language_well_defined L \<Sigma>"
  using assms unfolding sigma_star_def language_well_defined_def by blast

proposition language_well_def_iff: "L \<subseteq> sigma_star \<Sigma> \<longleftrightarrow> language_well_defined L \<Sigma>"
  using language_subset_of_sigma_star subsets_of_sigma_star by blast

definition \<A>_sigma_star :: "'a alphabet \<Rightarrow> (nat, 'a) automaton" where "\<A>_sigma_star \<Sigma> = Automaton {0} \<Sigma> {(0, a, 0) | a .  a \<in> \<Sigma>} 0 {0}"

corollary \<A>_sigma_star_alphabet: "alphabet (\<A>_sigma_star \<Sigma>) = \<Sigma>" unfolding \<A>_sigma_star_def by simp

proposition \<A>_sigma_star_well_def:
  assumes "finite \<Sigma>"
  shows "auto_well_defined (\<A>_sigma_star \<Sigma>)"
  using assms unfolding \<A>_sigma_star_def auto_well_defined_def by force

proposition sigma_star_auto_language_left:
  assumes "word \<in> language_auto (\<A>_sigma_star \<Sigma>)" "finite \<Sigma>"
  shows "word \<in> sigma_star \<Sigma>"
  using assms word_in_language_is_well_defined \<A>_sigma_star_well_def unfolding \<A>_sigma_star_def sigma_star_def by fastforce

proposition sigma_star_auto_language_right: "word \<in> sigma_star \<Sigma> \<Longrightarrow> word \<in> language_auto (\<A>_sigma_star \<Sigma>)"
proof(induction word rule: rev_induct)
  case Nil
  have "pseudo_run_well_defined [0] (\<A>_sigma_star \<Sigma>) (initial_state (\<A>_sigma_star \<Sigma>)) [] \<and> last [0] \<in> accepting_states (\<A>_sigma_star \<Sigma>)" unfolding \<A>_sigma_star_def pseudo_run_well_defined_def by force
  thus ?case unfolding run_well_defined_def run_accepting_def language_auto_def by blast 
next
  case (snoc a word)
  hence "word_well_defined word \<Sigma> \<and> a \<in> \<Sigma>" using word_well_def_snoc unfolding sigma_star_def by fast
  hence "word \<in> sigma_star \<Sigma> \<and> a \<in> \<Sigma>" unfolding sigma_star_def by blast
  hence "word \<in> language_auto (\<A>_sigma_star \<Sigma>) \<and> a \<in> \<Sigma>" using snoc by blast
  then obtain run where "pseudo_run_well_defined run (\<A>_sigma_star \<Sigma>) (initial_state (\<A>_sigma_star \<Sigma>)) word \<and> last run \<in> accepting_states (\<A>_sigma_star \<Sigma>) \<and> a \<in> \<Sigma>" unfolding language_auto_def run_accepting_def run_well_defined_def by fast
  hence "pseudo_run_well_defined run (\<A>_sigma_star \<Sigma>) (initial_state (\<A>_sigma_star \<Sigma>)) word \<and> last run = 0 \<and> (0, a, 0) \<in> transitions (\<A>_sigma_star \<Sigma>)" unfolding \<A>_sigma_star_def by simp
  hence "pseudo_run_well_defined (run @ [0]) (\<A>_sigma_star \<Sigma>) (initial_state (\<A>_sigma_star \<Sigma>)) (word @ [a])" using prun_well_defined_extension_snoc by fastforce
  hence "pseudo_run_well_defined (run @ [0]) (\<A>_sigma_star \<Sigma>) (initial_state (\<A>_sigma_star \<Sigma>)) (word @ [a]) \<and> last (run @ [0]) = 0" by simp
  thus ?case unfolding run_well_defined_def run_accepting_def language_auto_def \<A>_sigma_star_def by auto
qed

theorem equivalence_of_sigma_star_lang:
  assumes "finite \<Sigma>"
  shows "sigma_star \<Sigma> = language_auto (\<A>_sigma_star \<Sigma>)"
  using assms sigma_star_auto_language_left sigma_star_auto_language_right by blast

definition comp_language :: "'a alphabet \<Rightarrow> 'a language \<Rightarrow> 'a language" where "comp_language \<Sigma> L = sigma_star \<Sigma> - L"

proposition comp_language_well_defined: "language_well_defined (comp_language \<Sigma> L) \<Sigma>"
  using sigma_star_well_defined unfolding comp_language_def language_well_defined_def by blast

lemma comp_language_symmetry:
  assumes "language_well_defined L1 \<Sigma>" "language_well_defined L2 \<Sigma>" "L1 = comp_language \<Sigma> L2"
  shows "comp_language \<Sigma> L1 = L2"
  using assms unfolding comp_language_def sigma_star_def language_well_defined_def by fast

proposition comp_language_characteristic:
  assumes "language_well_defined L \<Sigma>"
  shows "comp_language \<Sigma> L \<union> L = sigma_star \<Sigma> \<and> comp_language \<Sigma> L \<inter> L = {}"
  using assms language_subset_of_sigma_star unfolding comp_language_def by auto

lemma word_comp_language1:
  assumes "word \<in> L"
  shows "word \<notin> comp_language \<Sigma> L"
  using assms unfolding comp_language_def by auto

lemma word_comp_language2:
  assumes "word_well_defined word \<Sigma>" "word \<notin> L"
  shows "word \<in> comp_language \<Sigma> L"
  using assms unfolding comp_language_def sigma_star_def by auto

proposition word_comp_language:
  assumes "word_well_defined word \<Sigma>"
  shows "word \<in> L \<longleftrightarrow> word \<notin> comp_language \<Sigma> L"
  using assms word_comp_language1 word_comp_language2 by blast

theorem comp_comp_language: 
  assumes "language_well_defined L \<Sigma>"
  shows "comp_language \<Sigma> (comp_language \<Sigma> L) = L"
  using assms comp_language_symmetry comp_language_well_defined by blast

text \<open>We can show equivalence of explicit languages using the following theorem:\<close>
lemma language_equivalence_right:
  assumes "language_well_defined L1 \<Sigma>" "language_well_defined L2 \<Sigma>" "L1 \<union> comp_language \<Sigma> L2 = sigma_star \<Sigma> \<and> L1 \<inter> comp_language \<Sigma> L2 = {}"
  shows "L1 = L2"
proof(rule ccontr)
  assume "L1 \<noteq> L2"
  then obtain word where word: "(word \<in> L1 \<and> word \<notin> L2) \<or> (word \<in> L2 \<and> word \<notin> L1)" by blast
  hence well_def_word: "word_well_defined word \<Sigma>" using assms unfolding language_well_defined_def by fast
  consider (case1) "word \<in> L1 \<and> word \<notin> L2" | (case2) "word \<in> L2 \<and> word \<notin> L1" using word by fast
  thus False
  proof cases
    case case1 thus ?thesis using assms word_comp_language well_def_word by blast
  next
    case case2 thus ?thesis using assms word_comp_language well_def_word unfolding comp_language_def by auto
  qed
qed

theorem eqiuvalence_of_languages:
  assumes "language_well_defined L1 \<Sigma>" "language_well_defined L2 \<Sigma>"
  shows "L1 = L2 \<longleftrightarrow> L1 \<union> comp_language \<Sigma> L2 = sigma_star \<Sigma> \<and> L1 \<inter> comp_language \<Sigma> L2 = {}"
proof - 
  have left: "L1 = L2 \<longrightarrow> L1 \<union> comp_language \<Sigma> L2 = sigma_star \<Sigma> \<and> L1 \<inter> comp_language \<Sigma> L2 = {}" using assms comp_language_characteristic by blast
  have "L1 \<union> comp_language \<Sigma> L2 = sigma_star \<Sigma> \<and> L1 \<inter> comp_language \<Sigma> L2 = {} \<longrightarrow> L1 = L2" using assms language_equivalence_right by auto
  thus ?thesis using left by linarith
qed



text \<open>Complementation automaton\<close>
definition comp_automaton :: "('s, 'a) automaton \<Rightarrow> ('s , 'a) automaton" where 
  "comp_automaton \<A> = Automaton
    (states \<A>)
    (alphabet \<A>)
    (transitions \<A>)
    (initial_state \<A>)
    {s \<in> states \<A> . s \<notin> accepting_states \<A>}"

theorem well_def_comp_automaton:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (comp_automaton \<A>)"
  using assms unfolding comp_automaton_def auto_well_defined_def by auto

corollary language_well_def_comp_auto:
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (language_auto (comp_automaton \<A>)) (alphabet (comp_automaton \<A>))"
  using well_def_comp_automaton assms automata_language_are_well_defined by blast

theorem DFA_property_comp_automaton:
  assumes "DFA_property \<A>"
  shows "DFA_property (comp_automaton \<A>)"
  using assms unfolding comp_automaton_def DFA_property_def by auto

lemma comp_automaton_acc_states:
  assumes "s \<in> states \<A>"
  shows "s \<in> accepting_states \<A> \<longleftrightarrow> s \<notin> accepting_states (comp_automaton \<A>)"
  using assms unfolding comp_automaton_def by auto

proposition prun_on_comp_automaton: "pseudo_run_well_defined run \<A> s word \<longleftrightarrow> pseudo_run_well_defined run (comp_automaton \<A>) s word"
  unfolding comp_automaton_def pseudo_run_well_defined_def by auto

lemma comp_language_words_left:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "word \<in> language_auto \<A>"
  shows "word \<notin> language_auto (comp_automaton \<A>)"
proof -
  let ?comp\<A> = "comp_automaton \<A>"
  obtain run where run_acc: "run_accepting run \<A> word" using assms unfolding language_auto_def by auto 
  hence "last run \<in> accepting_states \<A>" unfolding run_accepting_def by auto
  hence last: "last run \<notin> accepting_states ?comp\<A>" unfolding comp_automaton_def by auto
  have "run_well_defined run \<A> word" using run_acc unfolding run_accepting_def by auto
  hence run: "run_well_defined run ?comp\<A> word" using prun_on_comp_automaton unfolding run_well_defined_def comp_automaton_def by force
  have "DFA_property ?comp\<A> \<and> auto_well_defined ?comp\<A> \<and> word_well_defined word (alphabet ?comp\<A>)" using assms well_def_comp_automaton DFA_property_comp_automaton word_in_language_is_well_defined unfolding comp_automaton_def word_well_defined_def by fastforce
  hence "\<exists>! run . run_well_defined run ?comp\<A> word" using exists_only_one_run_for_DFA by blast
  hence "\<nexists> run . run_accepting run ?comp\<A> word" using last run unfolding run_accepting_def by auto
  thus ?thesis unfolding language_auto_def by auto
qed

lemma comp_language_words_right:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "word_well_defined word (alphabet \<A>)" "word \<notin> language_auto (comp_automaton \<A>)"
  shows "word \<in> language_auto \<A>"
proof -
  let ?comp\<A> = "comp_automaton \<A>"
  have "word_well_defined word (alphabet ?comp\<A>)" using assms unfolding comp_automaton_def word_well_defined_def by auto
  then obtain run where run: "run_well_defined run ?comp\<A> word" using assms well_def_comp_automaton DFA_property_comp_automaton exists_only_one_run_for_DFA by blast
  hence s: "last run \<in> states \<A>" using last_of_prun_is_state run assms prun_on_comp_automaton unfolding run_well_defined_def by metis
  have "\<nexists> run . run_accepting run ?comp\<A> word" using assms unfolding language_auto_def by auto
  hence "\<not> run_accepting run ?comp\<A> word" by auto
  hence "last run \<notin> accepting_states ?comp\<A>" using run unfolding run_accepting_def by auto
  hence acc: "last run \<in> accepting_states \<A>" using comp_automaton_acc_states s by fast
  have "run_well_defined run \<A> word" using run prun_on_comp_automaton unfolding run_well_defined_def comp_automaton_def by force
  hence "run_accepting run \<A> word" using acc unfolding run_accepting_def by auto
  thus ?thesis unfolding language_auto_def by auto
qed

lemma word_comp_automaton: 
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "word_well_defined word (alphabet \<A>)"
  shows "word \<in> language_auto \<A> \<longleftrightarrow> word \<notin> language_auto (comp_automaton \<A>)"
  using assms comp_language_words_left comp_language_words_right by auto

lemma comp_automaton_alphabet: "alphabet \<A> = alphabet (comp_automaton \<A>)"
  unfolding comp_automaton_def by auto

lemma word_on_comp_automaton_is_well_defined:
  assumes "auto_well_defined \<A>" "word \<in> language_auto (comp_automaton \<A>)"
  shows "word_well_defined word (alphabet \<A>)"
  using assms well_def_comp_automaton word_in_language_is_well_defined comp_automaton_alphabet by metis

text \<open>Main result for complementation\<close>
theorem comp_automaton_language_correctness:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "language_auto (comp_automaton \<A>) = comp_language (alphabet \<A>) (language_auto \<A>)"
  using assms comp_language_well_defined word_on_comp_automaton_is_well_defined word_comp_automaton word_comp_language unfolding language_well_defined_def by blast

corollary comp_comp_language_auto:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "language_auto \<A> = comp_language (alphabet (comp_automaton \<A>)) (language_auto (comp_automaton \<A>))"
  using assms comp_automaton_language_correctness comp_comp_language comp_automaton_alphabet automata_language_are_well_defined by metis





text \<open>NFA to DFA conversion with powerset automaton\<close>
definition powerset_transitions :: "('s, 'a) automaton \<Rightarrow> ('s states, 'a) transitions" where "powerset_transitions \<A> = {(S1, a, S2) . S1 \<in> Pow (states \<A>) \<and> a \<in> alphabet \<A> \<and> S2 = {s2 . \<exists> s1 \<in> S1 . (s1, a, s2) \<in> transitions \<A>}}"

text \<open>Powerset automaton\<close>
definition powerset_automaton :: "('s, 'a) automaton \<Rightarrow> ('s states, 'a) automaton" where
  "powerset_automaton \<A> = Automaton
    (Pow (states \<A>))
    (alphabet \<A>)
    (powerset_transitions \<A>)
    {initial_state \<A>}
    {S \<in> Pow (states \<A>) . S \<inter> (accepting_states \<A>) \<noteq> {}}"

lemma powerset_automaton_alphabet: "alphabet \<A> = alphabet (powerset_automaton \<A>)"
  unfolding powerset_automaton_def by auto

lemma acc_states_powerset_automaton1:
  assumes "s \<in> accepting_states \<A>" "S \<in> Pow (states \<A>)" "s \<in> S"
  shows "S \<in> accepting_states (powerset_automaton \<A>)"
  using assms unfolding powerset_automaton_def by auto

lemma acc_states_powerset_automaton2: 
  assumes "S \<in> accepting_states (powerset_automaton \<A>)"
  shows "\<exists> s \<in> S . s \<in> accepting_states \<A>"
  using assms unfolding powerset_automaton_def by auto

lemma s2_in_S2:
  assumes "(s1, a, s2) \<in> transitions \<A>" "s1 \<in> S1" "(S1, a, S2) \<in> transitions (powerset_automaton \<A>)"
  shows "s2 \<in> S2"
  using assms unfolding powerset_automaton_def powerset_transitions_def by auto

text \<open>The powerset automaton is well-defined\<close>
theorem well_def_powerset_automaton:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (powerset_automaton \<A>)"
  using assms unfolding powerset_automaton_def auto_well_defined_def powerset_transitions_def by auto

corollary language_well_def_powerset_auto:
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (language_auto (powerset_automaton \<A>)) (alphabet (powerset_automaton \<A>))"
  using well_def_powerset_automaton assms automata_language_are_well_defined by blast

lemma powerset_automaton_state_existence:
  assumes "auto_well_defined \<A>" "S1 \<in> states (powerset_automaton \<A>)" "a \<in> alphabet (powerset_automaton \<A>)"
  shows "\<exists> S2 \<in> states (powerset_automaton \<A>) . (S1, a, S2) \<in> transitions (powerset_automaton \<A>)"
  using assms well_def_trans_components unfolding powerset_automaton_def powerset_transitions_def by fastforce

lemma powerset_automaton_DFA_uniqueness:
  assumes "(S1, a, S2) \<in> transitions (powerset_automaton \<A>)" "(S1, a, S2') \<in> transitions (powerset_automaton \<A>)"
  shows "S2 = S2'"
  using assms well_def_trans_components unfolding powerset_automaton_def powerset_transitions_def by force

text \<open>The powerset automaton results in a DFA\<close>
theorem DFA_property_powerset_automaton:
  assumes "auto_well_defined \<A>"
  shows "DFA_property (powerset_automaton \<A>)"
  using assms powerset_automaton_state_existence powerset_automaton_DFA_uniqueness unfolding DFA_property_def by metis

lemma powerset_prun_left:
  assumes "auto_well_defined \<A>" 
  shows "pseudo_run_well_defined prun \<A> s word \<Longrightarrow> \<exists> pRun . \<exists> S \<in> states (powerset_automaton \<A>) . pseudo_run_well_defined pRun (powerset_automaton \<A>) S word \<and> s \<in> S \<and> last prun \<in> last pRun"
proof(induction word arbitrary: prun rule: rev_induct)
  let ?\<A> = "powerset_automaton \<A>"
  case Nil
  hence "prun = [s] \<and> s \<in> states \<A>" using list_with_one_element unfolding pseudo_run_well_defined_def by fastforce
  hence "last prun = s \<and> s \<in> states \<A>" by auto
  hence "pseudo_run_well_defined [{s}] ?\<A> {s} [] \<and> last prun = s \<and> {s} \<in> states ?\<A>" unfolding powerset_automaton_def pseudo_run_well_defined_def by force 
  thus ?case by force
next
  let ?\<A> = "powerset_automaton \<A>"
  have well_def_auto: "auto_well_defined ?\<A>" using assms well_def_powerset_automaton by blast
  case (snoc a word)
  hence "prun \<noteq> []" unfolding pseudo_run_well_defined_def by force
  then obtain prun' where "prun = prun' @ [last prun]" using append_butlast_last_id by metis
  hence "pseudo_run_well_defined prun' \<A> s word \<and> (last prun', a, last prun) \<in> transitions \<A>" using prun_well_defined_extension_snoc snoc by metis
  then obtain pRun S where pRun: "pseudo_run_well_defined pRun ?\<A> S word \<and> s \<in> S \<and> S \<in> states ?\<A> \<and> last prun' \<in> last pRun \<and> (last prun', a, last prun) \<in> transitions \<A>" using snoc by blast
  hence a: "a \<in> alphabet ?\<A>" using assms well_def_trans_components unfolding powerset_automaton_def by force
  have "last pRun \<in> states ?\<A>" using last_of_prun_is_state well_def_auto pRun by fast
  then obtain S2 where S2: "(last pRun, a, S2) \<in> transitions ?\<A>" using powerset_automaton_state_existence a assms by metis
  hence s: "last prun \<in> last (pRun @ [S2])" using pRun last_snoc s2_in_S2 by metis
  have "pseudo_run_well_defined (pRun @ [S2]) ?\<A> S (word @ [a]) \<and> s \<in> S \<and> S \<in> states ?\<A>" using prun_well_defined_extension_snoc S2 pRun by fast
  thus ?case using s by blast
qed

lemma powerset_run_left:
  assumes "auto_well_defined \<A>" 
  shows "run_well_defined run \<A> word \<Longrightarrow> \<exists> Run . run_well_defined Run (powerset_automaton \<A>) word \<and> last run \<in> last Run"
proof(induction word arbitrary: run rule: rev_induct)
  let ?\<A> = "powerset_automaton \<A>"
  have "auto_well_defined ?\<A>" using assms well_def_powerset_automaton by blast
  hence init: "initial_state ?\<A> \<in> states ?\<A>" using assms unfolding auto_well_defined_def by blast
  case Nil
  hence "run = [initial_state \<A>]" using list_with_one_element unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce
  hence "last run = initial_state \<A>" by auto
  hence "run_well_defined [{last run}] ?\<A> []" using init unfolding powerset_automaton_def run_well_defined_def pseudo_run_well_defined_def by force
  thus ?case by auto
next
  let ?\<A> = "powerset_automaton \<A>"
  have well_def_auto: "auto_well_defined ?\<A>" using assms well_def_powerset_automaton by blast
  case (snoc a word)
  hence well_def: "run_well_defined run \<A> (word @ [a])" using assms by auto
  hence "run \<noteq> []" unfolding pseudo_run_well_defined_def run_well_defined_def by force
  then obtain run' where "run = run' @ [last run]" using append_butlast_last_id by metis
  hence "run_well_defined run' \<A> word \<and> (last run', a, last run) \<in> transitions \<A>" using prun_well_defined_extension_snoc well_def unfolding run_well_defined_def by metis  
  then obtain Run where Run: "run_well_defined Run ?\<A> word \<and> last run' \<in> last Run \<and> (last run', a, last run) \<in> transitions \<A>" using snoc by blast
  hence a: "a \<in> alphabet ?\<A>" using assms well_def_trans_components unfolding powerset_automaton_def by force
  have "last Run \<in> states ?\<A>" using last_of_prun_is_state well_def_auto Run unfolding run_well_defined_def by fast
  then obtain S2 where S2: "(last Run, a, S2) \<in> transitions ?\<A>" using powerset_automaton_state_existence a assms by metis
  hence s: "last run \<in> last (Run @ [S2])" using Run last_snoc s2_in_S2 by metis
  have "run_well_defined (Run @ [S2]) ?\<A> (word @ [a])" using prun_well_defined_extension_snoc S2 Run unfolding run_well_defined_def by fast
  thus ?case using s by blast
qed

lemma powerset_language_left:
  assumes "auto_well_defined \<A>"
  shows "language_auto \<A> \<subseteq> language_auto (powerset_automaton \<A>)"
proof -
  let ?\<A> = "powerset_automaton \<A>"
  {
    fix word assume "word \<in> language_auto \<A>"
    then obtain run where "run_accepting run \<A> word" unfolding language_auto_def by auto
    hence run: "run_well_defined run \<A> word \<and> last run \<in> accepting_states \<A>" unfolding run_accepting_def by auto
    hence accepting: "last run \<in> accepting_states \<A>" using run by auto
    obtain Run where Run: "run_well_defined Run ?\<A> word \<and> last run \<in> last Run" using run assms powerset_run_left by blast
    hence "last Run \<in> states ?\<A>" using assms using well_def_powerset_automaton last_of_prun_is_state unfolding run_well_defined_def by fast
    hence "last Run \<in> accepting_states ?\<A>" using accepting Run acc_states_powerset_automaton1 unfolding powerset_automaton_def by auto
    hence "run_well_defined Run ?\<A> word \<and> last Run \<in> accepting_states ?\<A>" using Run by auto
    hence "word \<in> language_auto ?\<A>" unfolding language_auto_def run_accepting_def by auto
  }
  thus ?thesis by auto
qed

lemma powerset_transition_implies_transition:
  assumes "(S1, a, S2) \<in> transitions (powerset_automaton \<A>)" "S2 \<noteq> {}"
  shows "S1 \<noteq> {} \<and> (\<forall> s2 \<in> S2 . \<exists> s1 \<in> S1 . (s1, a, s2) \<in> transitions \<A>)" 
  using assms unfolding powerset_automaton_def powerset_transitions_def by auto

lemma powerset_prun_right: "pseudo_run_well_defined pRun (powerset_automaton \<A>) S word \<and> last pRun \<noteq> {} \<Longrightarrow> \<forall> s \<in> last pRun . \<exists> prun . \<exists> s' \<in> S . pseudo_run_well_defined prun \<A> s' word \<and> last prun = s"
proof(induction word arbitrary: pRun rule: rev_induct)
  let ?\<A> = "powerset_automaton \<A>"
  case Nil
  hence "pRun = [S] \<and> S \<in> states ?\<A>" using list_with_one_element unfolding pseudo_run_well_defined_def by fastforce
  hence props: "last pRun = S \<and> S \<in> states ?\<A>" by auto
  {
    fix s assume "s \<in> last pRun"
    hence "s \<in> S \<and> s \<in> states \<A>" using props Nil unfolding powerset_automaton_def by auto
    hence "pseudo_run_well_defined [s] \<A> s [] \<and> s \<in> S" unfolding pseudo_run_well_defined_def by auto
  }
  thus ?case by fastforce
next
  let ?\<A> = "powerset_automaton \<A>"
  case (snoc a word)
  hence well_def: "pseudo_run_well_defined pRun ?\<A> S (word @ [a]) \<and> last pRun \<noteq> {}" by blast
  hence length: "length pRun = length (word @ [a]) + 1 \<and> last pRun \<noteq> {}" unfolding pseudo_run_well_defined_def by blast
  hence "pRun \<noteq> [] \<and> last pRun \<noteq> {}" by auto
  then obtain pRun' where pRun': "pRun = pRun' @ [last pRun]" using append_butlast_last_id by metis
  hence "pseudo_run_well_defined (pRun' @ [last pRun]) ?\<A> S (word @ [a]) \<and> last pRun \<noteq> {}" using well_def by auto
  hence trans: "(last pRun', a, last pRun) \<in> transitions ?\<A> \<and> last pRun \<noteq> {}" using last_transition by fast
  hence not_empty: "last pRun' \<noteq> {}" using powerset_transition_implies_transition length by metis
  have "pseudo_run_well_defined pRun' ?\<A> S word" using pRun' prun_well_defined_extension_snoc well_def by metis
  hence existence: "\<forall> s \<in> last pRun' . \<exists> prun . \<exists> s' \<in> S. pseudo_run_well_defined prun \<A> s' word \<and> last prun = s" using snoc not_empty by blast
  have trans_in_trans: "\<forall> s' \<in> last pRun . \<exists> s'' \<in> last pRun' . (s'', a, s') \<in> transitions \<A>" using trans powerset_transition_implies_transition by fast
  {
    fix s' assume "\<exists> s'' \<in> last pRun' . (s'', a, s') \<in> transitions \<A> \<and> s' \<in> last pRun" 
    then obtain s'' where s'': "s'' \<in> last pRun' \<and> (s'', a, s') \<in> transitions \<A>" by auto
    then obtain prun s''' where "pseudo_run_well_defined prun \<A> s''' word \<and> s''' \<in> S \<and> s'' = last prun" using existence by auto
    hence "pseudo_run_well_defined (prun @ [s']) \<A> s''' (word @ [a]) \<and> s''' \<in> S \<and> s' = last (prun @ [s'])" using s'' prun_well_defined_extension_snoc snoc by fastforce 
    hence "\<exists> prun . \<exists> s''' \<in> S . pseudo_run_well_defined prun \<A> s''' (word @ [a]) \<and> last prun = s'" by auto
  }
  thus ?case using trans_in_trans by auto
qed

corollary powerset_run_right: "run_well_defined Run (powerset_automaton \<A>) word \<and> last Run \<noteq> {} \<Longrightarrow> \<forall> s \<in> last Run . \<exists> run . run_well_defined run \<A> word \<and> last run = s"
  using powerset_prun_right unfolding run_well_defined_def powerset_automaton_def by force

lemma powerset_language_right: "language_auto (powerset_automaton \<A>) \<subseteq> language_auto \<A>"
proof -
  let ?\<A> = "powerset_automaton \<A>"
  {
    fix word assume "word \<in> language_auto ?\<A>"
    then obtain Run where "run_accepting Run ?\<A> word" unfolding language_auto_def by auto
    hence Run: "run_well_defined Run ?\<A> word \<and> last Run \<in> accepting_states ?\<A>" unfolding run_accepting_def by auto
    hence existence: "\<exists> s \<in> last Run . s \<in> accepting_states \<A> \<and> last Run \<noteq> {}" using acc_states_powerset_automaton2 by auto
    then obtain s where "s \<in> last Run \<and> s \<in> accepting_states \<A>" by auto
    then obtain run where "run_well_defined run \<A> word \<and> last run \<in> accepting_states \<A>" using existence Run powerset_run_right by metis
    hence "word \<in> language_auto \<A>" unfolding run_accepting_def language_auto_def by auto
  }
  thus ?thesis by auto
qed

text \<open>Main result for the powerset automaton: language equivalence\<close>
theorem powerset_automaton_language_correctness:
  assumes "auto_well_defined \<A>"
  shows "language_auto \<A> = language_auto (powerset_automaton \<A>)"
  using assms powerset_language_left powerset_language_right by auto

text \<open>Main result for the powerset automaton\<close>
theorem powerset_automaton_correctness:
  assumes "auto_well_defined \<A>"
  shows "DFA_property (powerset_automaton \<A>) \<and> language_auto \<A> = language_auto (powerset_automaton \<A>)"
  using powerset_automaton_language_correctness DFA_property_powerset_automaton assms by auto





text \<open>Intersection and union languages are well defined\<close>
proposition intersection_language_well_defined:
  assumes "language_well_defined L1 \<Sigma>1" "language_well_defined L2 \<Sigma>2"
  shows "language_well_defined (L1 \<inter> L2) (\<Sigma>1 \<union> \<Sigma>2)"
  using assms unfolding language_well_defined_def word_well_defined_def by fast

corollary automata_intersection_lang_well_defined:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "language_well_defined (language_auto \<A>1 \<inter> language_auto \<A>2) (alphabet \<A>1 \<union> alphabet \<A>2)"
  using assms intersection_language_well_defined automata_language_are_well_defined by metis

proposition union_language_well_defined:
  assumes "language_well_defined L1 \<Sigma>1" "language_well_defined L2 \<Sigma>2"
  shows "language_well_defined (L1 \<union> L2) (\<Sigma>1 \<union> \<Sigma>2)"
  using assms unfolding language_well_defined_def word_well_defined_def by fast

corollary automata_union_lang_well_defined:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "language_well_defined (language_auto \<A>1 \<union> language_auto \<A>2) (alphabet \<A>1 \<union> alphabet \<A>2)"
  using assms union_language_well_defined automata_language_are_well_defined by metis

text \<open>Product transition function for the product automaton\<close>
definition product_transitions :: "('s, 'a) transitions \<Rightarrow> ('t, 'a) transitions \<Rightarrow> (('s \<times> 't), 'a) transitions" where "product_transitions \<delta>1 \<delta>2 = {((s1, t1), a, (s2, t2)) . (s1, a, s2) \<in> \<delta>1 \<and> (t1, a, t2) \<in> \<delta>2}"

text \<open>Since the inter and union product automata just differ in the accepting states, we will work with a more general product automaton\<close>
definition product_automaton :: "('s, 'a) automaton \<Rightarrow> ('t , 'a) automaton \<Rightarrow> ('s \<times> 't) states \<Rightarrow> (('s \<times> 't), 'a) automaton" where
  "product_automaton \<A>1 \<A>2 F = Automaton
    {(s1, s2) . s1 \<in> states \<A>1 \<and> s2 \<in> states \<A>2}
    (alphabet \<A>1 \<union> alphabet \<A>2)
    (product_transitions (transitions \<A>1) (transitions \<A>2))
    (initial_state \<A>1, initial_state \<A>2)
    (F)"

text \<open>Product automaton for intersection\<close>
definition intersection_automaton :: "('s, 'a) automaton \<Rightarrow> ('t , 'a) automaton \<Rightarrow> (('s \<times> 't), 'a) automaton" where "intersection_automaton \<A>1 \<A>2 = product_automaton \<A>1 \<A>2 {(s1, s2) . s1 \<in> accepting_states \<A>1 \<and> s2 \<in> accepting_states \<A>2}"

lemma well_def_inter_acc_states:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "accepting_states (intersection_automaton \<A>1 \<A>2) \<subseteq> states (intersection_automaton \<A>1 \<A>2)"
  using assms unfolding auto_well_defined_def intersection_automaton_def product_automaton_def by auto

text \<open>Product automaton for union\<close>
definition union_automaton :: "('s, 'a) automaton \<Rightarrow> ('t , 'a) automaton \<Rightarrow> (('s \<times> 't), 'a) automaton" where "union_automaton \<A>1 \<A>2 = product_automaton \<A>1 \<A>2 {(s1, s2) . s1 \<in> states \<A>1 \<and> s2 \<in> states \<A>2 \<and> (s1 \<in> accepting_states \<A>1 \<or> s2 \<in> accepting_states \<A>2)}"

lemma well_def_union_acc_states:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "accepting_states (union_automaton \<A>1 \<A>2) \<subseteq> states (union_automaton \<A>1 \<A>2)"
  using assms unfolding auto_well_defined_def union_automaton_def product_automaton_def by auto

text \<open>Predicate inheritance for the more general product automaton\<close>
theorem product_automaton_inheritance:
  assumes "\<forall> F . P (product_automaton \<A>1 \<A>2 F)"
  shows "P (intersection_automaton \<A>1 \<A>2) \<and> P (union_automaton \<A>1 \<A>2)"
  using assms unfolding intersection_automaton_def union_automaton_def by auto

text \<open>The product automaton is well-defined\<close>
theorem well_def_product_automaton:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "accepting_states (product_automaton \<A>1 \<A>2 F) \<subseteq> states (product_automaton \<A>1 \<A>2 F)"
  shows "auto_well_defined (product_automaton \<A>1 \<A>2 F)"
  using assms unfolding product_automaton_def product_transitions_def auto_well_defined_def by auto

corollary language_well_def_product_auto:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "accepting_states (product_automaton \<A>1 \<A>2 F) \<subseteq> states (product_automaton \<A>1 \<A>2 F)"
  shows "language_well_defined (language_auto (product_automaton \<A>1 \<A>2 F)) (alphabet (product_automaton \<A>1 \<A>2 F))"
  using well_def_product_automaton assms automata_language_are_well_defined by blast

text \<open>Hence, the intersection and union product automata are well-defined\<close>
corollary well_def_inter_union_automata:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "auto_well_defined (intersection_automaton \<A>1 \<A>2) \<and> auto_well_defined (union_automaton \<A>1 \<A>2)"
proof - 
  have inter: "auto_well_defined (intersection_automaton \<A>1 \<A>2)" using assms well_def_inter_acc_states well_def_product_automaton unfolding intersection_automaton_def by metis
  have "auto_well_defined (union_automaton \<A>1 \<A>2)" using assms well_def_union_acc_states well_def_product_automaton unfolding union_automaton_def by fast
  thus ?thesis using inter by auto
qed

corollary language_well_def_inter_union_auto:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" 
  shows "language_well_defined (language_auto (intersection_automaton \<A>1 \<A>2)) (alphabet (intersection_automaton \<A>1 \<A>2)) \<and> language_well_defined (language_auto (union_automaton \<A>1 \<A>2)) (alphabet (union_automaton \<A>1 \<A>2))"
  using well_def_inter_union_automata assms automata_language_are_well_defined by blast

text \<open>Given two DFAs on the same alphabet, then the product automaton is DFA\<close>
theorem DFA_property_product_automaton:
  assumes "DFA_property \<A>1" "DFA_property \<A>2" "alphabet \<A>1 = alphabet \<A>2"
  shows "DFA_property (product_automaton \<A>1 \<A>2 F)"
proof -
  let ?\<A> = "product_automaton \<A>1 \<A>2 F"
  {
    fix s1 s2 a assume "(s1, s2) \<in> states ?\<A> \<and> a \<in> alphabet ?\<A>"
    hence "s1 \<in> states \<A>1 \<and> s2 \<in> states \<A>2 \<and> a \<in> alphabet \<A>1 \<and> a \<in> alphabet \<A>2" using assms unfolding product_automaton_def by auto
    hence "(\<exists>! t1 . t1 \<in> states \<A>1 \<and> (s1, a, t1) \<in> transitions \<A>1) \<and> (\<exists>! t2 . t2 \<in> states \<A>2 \<and> (s2, a, t2) \<in> transitions \<A>2)" using assms unfolding DFA_property_def by auto
    hence "\<exists>! (t1, t2) . (t1, t2) \<in> states ?\<A> \<and> ((s1, s2), a, (t1, t2)) \<in> transitions ?\<A>" unfolding product_transitions_def product_automaton_def by auto
  }
  thus ?thesis unfolding DFA_property_def by fast
qed

text \<open>Hence, given two DFAs on the same alphabet, then the intersection and union product automata are DFAs\<close>
corollary DFA_property_product_inter_union:
  assumes "DFA_property \<A>1" "DFA_property \<A>2" "alphabet \<A>1 = alphabet \<A>2"
  shows "DFA_property (intersection_automaton \<A>1 \<A>2) \<and> DFA_property (union_automaton \<A>1 \<A>2)"
  using assms DFA_property_product_automaton product_automaton_inheritance by metis

text \<open>Product_pruns are well-defined\<close>
theorem product_prun_correct:
  assumes "pseudo_run_well_defined prun1 \<A>1 s1 word" "pseudo_run_well_defined prun2 \<A>2 s2 word"
  shows "pseudo_run_well_defined (zip prun1 prun2) (product_automaton \<A>1 \<A>2 F) (s1, s2) word"
  using assms unfolding pseudo_run_well_defined_def product_automaton_def product_transitions_def by force

corollary product_run_correct:
  assumes "run_well_defined run1 \<A>1 word" "run_well_defined run2 \<A>2 word"
  shows "run_well_defined (zip run1 run2) (product_automaton \<A>1 \<A>2 F) word"
  using assms product_prun_correct unfolding run_well_defined_def product_automaton_def by fastforce

lemma product_run_accepting_inter: 
  assumes "run_accepting run1 \<A>1 word" "run_accepting run2 \<A>2 word"
  shows "run_accepting (zip run1 run2) (intersection_automaton \<A>1 \<A>2) word"
proof -
  let ?\<A> = "intersection_automaton \<A>1 \<A>2"
  let ?run = "zip run1 run2"
  have "run1 \<noteq> [] \<and> run2 \<noteq> [] \<and> length run1 = length run2" using assms unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by force
  hence last: "last ?run = (last run1, last run2)" using last_zip by blast
  have "last run1 \<in> accepting_states \<A>1 \<and> last run2 \<in> accepting_states \<A>2" using assms unfolding run_accepting_def by auto 
  hence acc_state: "(last run1, last run2) \<in> accepting_states ?\<A>" unfolding intersection_automaton_def product_automaton_def by auto
  have "run_well_defined ?run ?\<A> word" using assms product_run_correct unfolding intersection_automaton_def run_accepting_def by blast
  thus ?thesis using last acc_state unfolding run_accepting_def by auto
qed

theorem inter_implication_single_to_product:
  assumes "word \<in> language_auto \<A>1" "word \<in> language_auto \<A>2"
  shows "word \<in> language_auto (intersection_automaton \<A>1 \<A>2)"
  using assms product_run_accepting_inter unfolding language_auto_def by blast


text\<open>To prove equivalences of languages of product automata one needs as addition to the product run also the individual runs\<close>
text \<open>Single_runs are well-defined\<close>
theorem single_prun_correct: 
  assumes "pseudo_run_well_defined prun (product_automaton \<A>1 \<A>2 F) (s1, s2) word" 
  shows "pseudo_run_well_defined (map fst prun) \<A>1 s1 word \<and> pseudo_run_well_defined (map snd prun) \<A>2 s2 word"
  using assms unfolding pseudo_run_well_defined_def product_automaton_def product_transitions_def by force

corollary single_run_correct: 
  assumes "run_well_defined run (product_automaton \<A>1 \<A>2 F) word" 
  shows "run_well_defined (map fst run) \<A>1 word \<and> run_well_defined (map snd run) \<A>2 word"
  using assms single_prun_correct unfolding run_well_defined_def product_automaton_def by force

lemma single_run_accepting_inter:
  assumes "run_accepting run (intersection_automaton \<A>1 \<A>2) word"
  shows "run_accepting (map fst run) \<A>1 word \<and> run_accepting (map snd run) \<A>2 word"
proof -
  let ?\<A> = "(intersection_automaton \<A>1 \<A>2)"
  let ?run1 = "(map fst run)"
  let ?run2 = "(map snd run)"
  have "run_well_defined run ?\<A> word" using assms well_def_inter_union_automata unfolding run_accepting_def by auto
  hence "length run = length word + 1 \<and> run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "run \<noteq> [] \<and> last run = run ! (length run - 1)" using list_properties_not_empty by metis
  hence "last run = (last ?run1, last ?run2)" using assms by (simp add: last_map)
  hence acc_states: "last ?run1 \<in> accepting_states \<A>1 \<and> last ?run2 \<in> accepting_states \<A>2" using assms unfolding run_accepting_def intersection_automaton_def product_automaton_def by auto
  have "run_well_defined ?run1 \<A>1 word \<and> run_well_defined ?run2 \<A>2 word " using assms single_run_correct unfolding intersection_automaton_def run_accepting_def by blast
  thus ?thesis using acc_states unfolding run_accepting_def by auto
qed

theorem inter_implication_product_to_single:
  assumes "word \<in> language_auto (intersection_automaton \<A>1 \<A>2)"
  shows "word \<in> language_auto \<A>1 \<and> word \<in> language_auto \<A>2"
  using assms single_run_accepting_inter unfolding language_auto_def by blast

theorem closed_under_intersection: "word \<in> language_auto (intersection_automaton \<A>1 \<A>2) \<longleftrightarrow> word \<in> language_auto \<A>1 \<and> word \<in> language_auto \<A>2"
  using inter_implication_single_to_product inter_implication_product_to_single by metis

text \<open>Main result for intersection\<close>
theorem language_intersection_correctness: "language_auto (intersection_automaton \<A>1 \<A>2) = language_auto \<A>1 \<inter> language_auto \<A>2"
  using closed_under_intersection by auto

proposition alphabet_intersection: "alphabet (intersection_automaton \<A>1 \<A>2) = alphabet \<A>1 \<union> alphabet \<A>2"
  unfolding intersection_automaton_def product_automaton_def by simp



text \<open>Finally one can prove the equivalences of languages for union, given the alphabet is identical\<close>
lemma product_run_accepting_union_\<A>1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "DFA_property \<A>2" "alphabet \<A>1 = alphabet \<A>2" "run_accepting run1 \<A>1 word"
  shows "\<exists> run2 . run_accepting (zip run1 run2) (union_automaton \<A>1 \<A>2) word"
proof -
  let ?\<A> = "union_automaton \<A>1 \<A>2"
  obtain run2 where "run_well_defined run2 \<A>2 word" using assms exists_only_one_run_for_DFA well_def_implies_word_well_defined unfolding run_accepting_def run_well_defined_def word_well_defined_def by metis
  hence runs: "run_well_defined run1 \<A>1 word \<and> run_well_defined run2 \<A>2 word" using assms unfolding run_accepting_def by auto
  hence "run1 \<noteq> [] \<and> run2 \<noteq> [] \<and> length run1 = length run2" unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence last: "last (zip run1 run2) = (last run1, last run2)" using last_zip by metis
  have "last run1 \<in> accepting_states \<A>1 \<and> last run2 \<in> states \<A>2" using assms runs last_of_prun_is_state unfolding run_accepting_def run_well_defined_def by auto
  hence acc_state: "(last run1, last run2) \<in> accepting_states ?\<A>" using assms unfolding union_automaton_def product_automaton_def auto_well_defined_def by auto
  have "run_well_defined (zip run1 run2) ?\<A> word" using assms runs product_run_correct unfolding union_automaton_def run_accepting_def by blast
  thus ?thesis using last acc_state unfolding run_accepting_def by auto
qed

lemma product_run_accepting_union_\<A>2:
  assumes "auto_well_defined \<A>1" "DFA_property \<A>1" "auto_well_defined \<A>2" "alphabet \<A>1 = alphabet \<A>2" "run_accepting run2 \<A>2 word"
  shows "\<exists> run1 . run_accepting (zip run1 run2) (union_automaton \<A>1 \<A>2) word"
proof -
  let ?\<A> = "union_automaton \<A>1 \<A>2"
  obtain run1 where "run_well_defined run1 \<A>1 word" using assms exists_only_one_run_for_DFA well_def_implies_word_well_defined unfolding run_accepting_def word_well_defined_def run_well_defined_def by metis
  hence runs: "run_well_defined run1 \<A>1 word \<and> run_well_defined run2 \<A>2 word" using assms unfolding run_accepting_def by auto
  hence "run1 \<noteq> [] \<and> run2 \<noteq> [] \<and> length run1 = length run2" unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence last: "last (zip run1 run2) = (last run1, last run2)" using last_zip by metis
  have "last run2 \<in> accepting_states \<A>2 \<and> last run1 \<in> states \<A>1" using assms runs last_of_prun_is_state unfolding run_accepting_def run_well_defined_def by auto
  hence acc_state: "(last run1, last run2) \<in> accepting_states ?\<A>" using assms unfolding union_automaton_def product_automaton_def auto_well_defined_def by fastforce
  have "run_well_defined (zip run1 run2) ?\<A> word" using assms runs product_run_correct unfolding union_automaton_def run_accepting_def by blast
  thus ?thesis using last acc_state unfolding run_accepting_def by auto
qed

lemma union_implication_\<A>1_to_product:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "DFA_property \<A>2" "alphabet \<A>1 = alphabet \<A>2" "word \<in> language_auto \<A>1"
  shows "word \<in> language_auto (union_automaton \<A>1 \<A>2)"
  using assms product_run_accepting_union_\<A>1 word_in_language_is_well_defined unfolding language_auto_def by blast

lemma union_implication_\<A>2_to_product:
  assumes "auto_well_defined \<A>1" "DFA_property \<A>1" "auto_well_defined \<A>2" "alphabet \<A>1 = alphabet \<A>2" "word \<in> language_auto \<A>2"
  shows "word \<in> language_auto (union_automaton \<A>1 \<A>2)"
  using assms product_run_accepting_union_\<A>2 word_in_language_is_well_defined unfolding language_auto_def by blast

theorem union_implication_single_to_product:
  assumes "auto_well_defined \<A>1" "DFA_property \<A>1" "auto_well_defined \<A>2" "DFA_property \<A>2" "alphabet \<A>1 = alphabet \<A>2" "word \<in> language_auto \<A>1 \<or> word \<in> language_auto \<A>2"
  shows "word \<in> language_auto (union_automaton \<A>1 \<A>2)" 
  using union_implication_\<A>1_to_product union_implication_\<A>2_to_product assms by blast

lemma single_run_accepting_union:
  assumes "run_accepting run (union_automaton \<A>1 \<A>2) word"
  shows "run_accepting (map fst run) \<A>1 word \<or> run_accepting (map snd run) \<A>2 word "
proof -
  let ?\<A> = "(union_automaton \<A>1 \<A>2)"
  let ?run1 = "(map fst run)"
  let ?run2 = "(map snd run)"
  have "run_well_defined run ?\<A> word" using assms well_def_inter_union_automata unfolding run_accepting_def by auto
  hence "length run = length word + 1 \<and> run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "run \<noteq> [] \<and> last run = run ! (length run - 1)" using list_properties_not_empty by metis
  hence "last run = (last ?run1, last ?run2)" using assms by (simp add: last_map)
  hence acc_states: "last ?run1 \<in> accepting_states \<A>1 \<or> last ?run2 \<in> accepting_states \<A>2" using assms unfolding run_accepting_def union_automaton_def product_automaton_def by auto
  hence "run_well_defined ?run1 \<A>1 word \<and> run_well_defined ?run2 \<A>2 word " using assms single_run_correct unfolding union_automaton_def run_accepting_def by blast
  thus ?thesis using acc_states run_accepting_def by metis
qed

theorem union_implication_product_to_single:
  assumes "word \<in> language_auto (union_automaton \<A>1 \<A>2)"
  shows "word \<in> language_auto \<A>1 \<or> word \<in> language_auto \<A>2"
  using assms single_run_accepting_union unfolding language_auto_def by blast

theorem closed_under_union:
  assumes "auto_well_defined \<A>1" "DFA_property \<A>1" "auto_well_defined \<A>2" "DFA_property \<A>2" "alphabet \<A>1 = alphabet \<A>2"
  shows "word \<in> language_auto (union_automaton \<A>1 \<A>2) \<longleftrightarrow> word \<in> language_auto \<A>1 \<or> word \<in> language_auto \<A>2"
  using union_implication_single_to_product union_implication_product_to_single assms by metis

text \<open>Main result for union\<close>
theorem language_union_correctness:
  assumes "auto_well_defined \<A>1" "DFA_property \<A>1" "auto_well_defined \<A>2" "DFA_property \<A>2" "alphabet \<A>1 = alphabet \<A>2"
  shows "language_auto (union_automaton \<A>1 \<A>2) = language_auto \<A>1 \<union> language_auto \<A>2"
  using assms closed_under_union by auto

proposition alphabet_union:
  assumes "alphabet \<A>1 = alphabet \<A>2"
  shows "alphabet (union_automaton \<A>1 \<A>2) = alphabet \<A>1"
  using assms unfolding union_automaton_def product_automaton_def by force

text \<open>Main result of this theory: expressive power of NFAs and DFAs\<close>
theorem NFA_to_DFA:
  assumes "auto_well_defined (NFA_\<A> :: ('s, 'a) automaton)"
  shows "\<exists> DFA_\<A> :: ('s states, 'a) automaton . auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = alphabet NFA_\<A> \<and> language_auto DFA_\<A> = language_auto NFA_\<A>"
  using powerset_automaton_correctness well_def_powerset_automaton powerset_automaton_alphabet assms by fast

theorem DFA_to_NFA:
  assumes "auto_well_defined (DFA_\<A> :: ('s, 'a) automaton)" "DFA_property DFA_\<A>"
  shows "\<exists> NFA_\<A> :: ('s, 'a) automaton. auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = alphabet DFA_\<A> \<and> language_auto NFA_\<A> = language_auto DFA_\<A>"
  using assms by auto

text \<open>Sigma_Star\<close>
theorem sigma_star_main:
  assumes "finite \<Sigma>"
  shows "\<exists> sigma_\<A> :: (nat , 'a) automaton . auto_well_defined sigma_\<A> \<and> alphabet sigma_\<A> = \<Sigma> \<and> language_auto sigma_\<A> = sigma_star \<Sigma>"
  using assms \<A>_sigma_star_alphabet \<A>_sigma_star_well_def equivalence_of_sigma_star_lang by metis

text \<open>Complementation\<close>
theorem comp_main:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)" "DFA_property \<A>"
  shows "\<exists> comp_\<A> :: ('s , 'a) automaton . auto_well_defined comp_\<A> \<and> alphabet comp_\<A> = alphabet \<A> \<and> language_auto comp_\<A> = comp_language (alphabet \<A>) (language_auto \<A>)"
  using comp_automaton_language_correctness well_def_comp_automaton comp_automaton_alphabet assms by fast

text \<open>Intersection\<close>
theorem intersection_main:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)"
  shows "\<exists> inter_\<A> :: (('s \<times> 't), 'a) automaton . auto_well_defined inter_\<A> \<and> alphabet inter_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> language_auto inter_\<A> = language_auto \<A>1 \<inter> language_auto \<A>2"
  using language_intersection_correctness well_def_inter_union_automata alphabet_intersection assms by metis

text \<open>Union\<close>
theorem union_main:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "DFA_property \<A>1" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "DFA_property \<A>2" "alphabet \<A>1 = alphabet \<A>2"
  shows "\<exists> union_\<A> :: (('s \<times> 't), 'a) automaton . auto_well_defined union_\<A> \<and> alphabet union_\<A> = alphabet \<A>1 \<and> language_auto union_\<A> = language_auto \<A>1 \<union> language_auto \<A>2"
  using language_union_correctness well_def_inter_union_automata alphabet_union assms by metis

text \<open>Main result of this theory: Combinations\<close>
theorem
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "alphabet \<A>1 = alphabet \<A>2"
  shows "(\<exists> comp_\<A> :: ('s states, 'a) automaton . auto_well_defined comp_\<A> \<and> alphabet comp_\<A> = alphabet \<A>1 \<and> language_auto comp_\<A> = comp_language (alphabet \<A>1) (language_auto \<A>1)) \<and> (\<exists> inter_\<A> :: (('s \<times> 't), 'a) automaton . auto_well_defined inter_\<A> \<and> alphabet inter_\<A> = alphabet \<A>1 \<and> language_auto inter_\<A> = language_auto \<A>1 \<inter> language_auto \<A>2) \<and> (\<exists> union_\<A> :: (('s states \<times> 't states), 'a) automaton . auto_well_defined union_\<A> \<and> alphabet union_\<A> = alphabet \<A>1 \<and> language_auto union_\<A> = language_auto \<A>1 \<union> language_auto \<A>2)"
proof -
  obtain \<A>3 :: "('s states, 'a) automaton" where A3: "auto_well_defined \<A>3 \<and> alphabet \<A>3 = alphabet \<A>1 \<and> DFA_property \<A>3 \<and> language_auto \<A>3 = language_auto \<A>1" using assms NFA_to_DFA by metis
  hence main1: "\<exists> \<A>4 :: ('s states, 'a) automaton . auto_well_defined \<A>4 \<and> alphabet \<A>4 = alphabet \<A>1 \<and> language_auto \<A>4 = comp_language (alphabet \<A>1) (language_auto \<A>1)" using comp_main by metis
  have main2: "\<exists> \<A>5 :: (('s \<times> 't), 'a) automaton . auto_well_defined \<A>5 \<and> alphabet \<A>5 = alphabet \<A>1 \<and> language_auto \<A>5 = language_auto \<A>1 \<inter> language_auto \<A>2" using intersection_main assms by fast
  obtain \<A>6 :: "('t states, 'a) automaton" where "auto_well_defined \<A>6 \<and> alphabet \<A>6 = alphabet \<A>2 \<and> DFA_property \<A>6 \<and> language_auto \<A>6 = language_auto \<A>2" using NFA_to_DFA assms by metis
  hence "\<exists> \<A>7 :: (('s states \<times> 't states), 'a) automaton . auto_well_defined \<A>7 \<and> alphabet \<A>7 = alphabet \<A>1 \<and> language_auto \<A>7 = language_auto \<A>1 \<union> language_auto \<A>2" using A3 union_main assms by metis
  thus ?thesis using main1 main2 by auto
qed

end