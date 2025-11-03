theory automaton_examples

imports Main automaton_minimization automaton_iterativ regular_expressions regular_grammars

begin

text \<open>Author: Benno Thalmann, last update: 29.10.2025, Addition to masterarbeit_benno_thalmann\<close>

text \<open>Examples: Transitions and Automata\<close> 
definition \<delta>_A :: "(nat, nat) transitions" where "\<delta>_A = {(0, 1, 0), (0, 0, 1), (1, 0, 1), (1, 1, 0)}"
definition \<delta>_B :: "(nat, nat) transitions" where "\<delta>_B = {(0, 1, 0), (0, 0, 1), (1, 0, 0), (1, 1, 1)}"

definition \<A>_A :: "(nat, nat) automaton" where "\<A>_A = Automaton {0, 1} {0, 1} \<delta>_A 0 {1}"
definition \<A>_B :: "(nat, nat) automaton" where "\<A>_B = Automaton {0, 1} {0, 1} \<delta>_B 0 {0}"

text \<open>Well-definedness for examples\<close>
theorem well_def_examples: "auto_well_defined \<A>_A \<and> auto_well_defined \<A>_B"
  unfolding auto_well_defined_def \<A>_A_def \<delta>_A_def \<A>_B_def \<delta>_B_def by auto

text \<open>DFA_property for examples\<close>
theorem DFA_property_examples: "DFA_property \<A>_A \<and> DFA_property \<A>_B"
  unfolding \<A>_A_def \<A>_B_def \<delta>_A_def \<delta>_B_def DFA_property_def by force

text \<open>Example NFA (accepts same language as \<A>_A, proof later)\<close>
definition \<A>_NFA :: "(nat, nat) automaton" where "\<A>_NFA = Automaton {0, 1} {0, 1} {(0, 0, 0), (0, 1, 0), (0, 0, 1)} 0 {1}"

theorem well_def_\<A>_NFA: "auto_well_defined \<A>_NFA \<and> \<not> DFA_property \<A>_NFA"
  unfolding auto_well_defined_def \<A>_NFA_def DFA_property_def by force

text \<open>Example word for the example automata\<close>
definition word_ex :: "nat word" where "word_ex = [0, 0, 0]"

value "word_well_defined word_ex (alphabet \<A>_A)"
value "run_well_defined [0, 1, 1, 1] \<A>_A word_ex"
value "run_well_defined [0, 1, 1, 1] \<A>_B word_ex"

text \<open>The return-run function works for DFA's:\<close>
proposition "return_run word_ex \<A>_A = [0, 1, 1, 1]"
  unfolding return_run_def word_ex_def \<A>_A_def \<delta>_A_def by fastforce

text \<open>Since we analyzed runs, we want to explore words and languages\<close>
value "\<A>_A"
value "word_ex"
value "run_accepting [0, 1, 1, 1] \<A>_A word_ex"

text \<open>Although the definition of run_accepting is correct and will be used to prove properties of languages, the use for the examples is limited\<close>
lemma run_accepting_example: "run_accepting [0, 1, 1, 1] \<A>_A word_ex"
proof -
  {
    fix i :: nat assume "i < 3" 
    then consider (case1) "i = 0" | (case2) "i = 1" | (case3) "i = 2" by fastforce
    hence "i < 3 \<Longrightarrow> ([0, 1, 1, 1] ! i, word_ex ! i, [0, 1, 1, 1] ! (i + 1)) \<in> transitions \<A>_A"
    proof cases
      case case1 thus ?thesis unfolding \<A>_A_def word_ex_def \<delta>_A_def by auto
    next
      case case2 thus ?thesis unfolding \<A>_A_def word_ex_def \<delta>_A_def by auto
    next
      case case3 thus ?thesis unfolding \<A>_A_def word_ex_def \<delta>_A_def by auto
    qed
  }
  thus ?thesis unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def \<A>_A_def word_ex_def by force
qed

proposition "word_ex \<in> language_auto \<A>_A"
  using run_accepting_example unfolding language_auto_def by auto

text \<open>Language equivalence for \<A>_A and \<A>_NFA\<close>
lemma empty_word_\<A>_A: "[] \<notin> language_auto \<A>_A"
proof(rule ccontr)
  assume "\<not> [] \<notin> language_auto \<A>_A"
  then obtain run where run: "run_accepting run \<A>_A []" unfolding language_auto_def by auto
  hence "length run = length [] + 1 \<and> run \<noteq> [] \<and> (run ! 0) = initial_state \<A>_A" unfolding pseudo_run_well_defined_def run_well_defined_def run_accepting_def by auto
  hence "run = [0]" using list_with_one_element unfolding \<A>_A_def by fastforce
  hence "\<not> run_accepting run \<A>_A []" unfolding run_accepting_def \<A>_A_def by auto
  thus False using run by auto
qed

lemma words_\<A>_A_left:
  assumes "word \<noteq> []" "word \<in> language_auto \<A>_A"
  shows "last word = 0"
proof - 
  obtain run where run_acc: "run_accepting run \<A>_A word" using assms unfolding language_auto_def by auto
  let ?n = "length run"
  have run: "run_well_defined run \<A>_A word \<and> last run = 1" using run_acc unfolding run_accepting_def \<A>_A_def by auto
  hence "run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "?n = length word + 1 \<and> last run = run ! (?n - 1)" using run list_properties_not_empty unfolding run_well_defined_def pseudo_run_well_defined_def by metis
  hence properties: "?n = length word + 1 \<and> last run = run ! (?n - 1) \<and> ?n > 1" using assms by auto
  have "\<forall> i < ?n - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions \<A>_A" using run unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  hence "(run ! (?n - 2), word ! (?n - 2), run ! (?n - 2 + 1)) \<in> transitions \<A>_A" using properties run by auto
  hence "(run ! (?n - 2), word ! (?n - 2), 1) \<in> transitions \<A>_A" using run properties by force
  hence "word ! (?n - 2) = 0" unfolding \<A>_A_def \<delta>_A_def by auto
  thus ?thesis using list_properties_not_empty properties by fastforce
qed

lemma words_\<A>_A_right:
  assumes "word_well_defined word (alphabet \<A>_A)" "word \<noteq> []" "last word = 0"
  shows "word \<in> language_auto \<A>_A"
proof - 
  obtain run where run: "run_well_defined run \<A>_A word" using DFA_property_examples assms exists_only_one_run_for_DFA well_def_examples by blast
  let ?n = "length run"
  have "run \<noteq> []" using run unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence properties: "?n = length word + 1 \<and> last run = run ! (?n - 1)" using run list_properties_not_empty unfolding run_well_defined_def pseudo_run_well_defined_def by metis
  hence length_run: "?n > 1" using assms by auto
  hence last_word: "word ! (?n - 2) = last word" using list_properties_not_empty properties by fastforce
  have "\<forall> i < ?n - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions \<A>_A" using run unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence "(run ! (?n - 2), word ! (?n - 2), run ! (?n - 2 + 1)) \<in> transitions \<A>_A" using length_run by force
  hence "(run ! (?n - 2), 0, run ! (?n - 2 + 1)) \<in> transitions \<A>_A" using assms last_word by auto
  hence "run ! (?n - 2 + 1) = 1" unfolding \<A>_A_def \<delta>_A_def by auto
  hence "run ! (?n - 1) = 1" using length_run properties by auto
  hence "last run = 1" using properties by auto
  hence "run_accepting run \<A>_A word" using run unfolding run_accepting_def \<A>_A_def by auto
  thus ?thesis unfolding language_auto_def by auto
qed

theorem words_\<A>_A:
  assumes "word_well_defined word (alphabet \<A>_A)" "word \<noteq> []"
  shows "last word = 0 \<longleftrightarrow> word \<in> language_auto \<A>_A"
  using words_\<A>_A_left words_\<A>_A_right assms by blast

lemma empty_word_\<A>_NFA: "[] \<notin> language_auto \<A>_NFA"
proof(rule ccontr)
  assume "\<not> [] \<notin> language_auto \<A>_NFA"
  then obtain run where run: "run_accepting run \<A>_NFA []" unfolding language_auto_def by blast
  hence "length run = length [] + 1 \<and> run \<noteq> [] \<and> (run ! 0) = initial_state \<A>_NFA" unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by auto
  hence "run = [0]" using list_with_one_element unfolding \<A>_NFA_def by force
  hence "\<not> run_accepting run \<A>_NFA []" unfolding run_accepting_def \<A>_NFA_def by auto
  thus False using run by auto
qed

lemma words_\<A>_NFA_left:
  assumes "word \<noteq> []" "word \<in> language_auto \<A>_NFA"
  shows "last word = 0"
proof - 
  obtain run where run_acc: "run_accepting run \<A>_NFA word" using assms unfolding language_auto_def by blast
  let ?n = "length run"
  have run: "run_well_defined run \<A>_NFA word \<and> last run = 1" using run_acc unfolding run_accepting_def \<A>_NFA_def by force
  hence "run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence properties: "last run = run ! (?n - 1) \<and> ?n > 1 \<and> run \<noteq> []" using assms run list_properties_not_empty unfolding run_well_defined_def pseudo_run_well_defined_def by force
  have "\<forall> i < ?n - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions \<A>_NFA" using run unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  hence "(run ! (?n - 2), word ! (?n - 2), run ! (?n - 2 + 1)) \<in> transitions \<A>_NFA" using properties by fastforce
  hence "(run ! (?n - 2), word ! (?n - 2), last run) \<in> transitions \<A>_NFA" using simple_math properties by auto
  hence 0: "word ! (?n - 2) = 0" using run unfolding \<A>_NFA_def by force
  have "?n = length word + 1" using run unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  thus ?thesis using 0 list_properties_not_empty assms by fastforce
qed

fun run0 :: "nat \<Rightarrow> nat run" where
  "run0 0 = [1]" |
  "run0 n = 0 # run0 (n - 1)"

value "run0 5"

lemma properties_run0: "run0 n \<noteq> [] \<and> length (run0 n) = n + 1 \<and> (n > 0 \<longrightarrow> (run0 n) ! 0 = 0) \<and> (\<forall> i < n . (run0 n) ! i = 0) \<and> (\<forall> i < n - 1 . (run0 n) ! (i + 1) = 0) \<and> last (run0 n) = 1"
proof - 
  have props: "run0 n \<noteq> [] \<and> length (run0 n) = n + 1 \<and> (n > 0 \<longrightarrow> (run0 n) ! 0 = 0) \<and> last (run0 n) = 1" by (induction n) auto
  have "\<forall> i < n . (run0 n) ! i = 0" apply(induction n) apply simp by (simp add: nth_Cons')
  thus ?thesis using props by force
qed

lemma run0_last_step:
  assumes "word_well_defined word (alphabet \<A>_NFA)" "word \<noteq> []" "last word = 0"
  shows "((run0 (length word)) ! (length (run0 (length word)) - 2), word ! (length (run0 (length word)) - 2), (run0 (length word)) ! ((length (run0 (length word)) - 2) + 1)) \<in> transitions \<A>_NFA"
proof - 
  let ?n = "length word"
  let ?m = "length (run0 ?n)"
  let ?run = "run0 ?n"
  have len_run0: "?n > 0 \<and> ?m = ?n + 1" using properties_run0 assms by blast
  hence last: "?run ! (?n + 1 - 1) = last ?run" using list_properties_not_empty properties_run0 by metis
  have "?run ! (?n + 1 - 1) = ?run ! (?m - 2 + 1)" using len_run0 by auto
  hence second_comp: "?run ! (?m - 2 + 1) = 1" using last properties_run0 unfolding \<A>_NFA_def by force
  have "?m - 2 \<ge> 0" using len_run0 by auto
  hence first_comp: "?run ! (?m - 2) = 0" using properties_run0 len_run0 by auto
  have "word ! (?n - 1) = 0" using assms list_properties_not_empty by metis
  hence "word ! (?m - 2) = 0" using properties_run0 by auto
  thus ?thesis using first_comp second_comp unfolding \<A>_NFA_def by force
qed

lemma run0_i_1_step:
  assumes "word_well_defined word (alphabet \<A>_NFA)" "word \<noteq> []" "last word = 0"
  shows "\<forall> i < length (run0 (length word)) - 2 . ((run0 (length word)) ! i, word ! i, (run0 (length word)) ! (i + 1)) \<in> transitions \<A>_NFA"
proof -
  let ?run = "run0 (length word)"
  have length: "length ?run - 1 = length word" using properties_run0 by auto
  {
    fix j assume assm: "j < length word - 1"
    hence first_comp: "?run ! j = 0" using properties_run0 by force
    have second_comp: "?run ! (j + 1) = 0" using properties_run0 assm by blast
    have "word ! j \<in> alphabet \<A>_NFA" using assms assm unfolding word_well_defined_def by auto
    hence "word ! j = 0 \<or> word ! j = 1" unfolding \<A>_NFA_def by auto
    hence "(?run ! j, word ! j, ?run ! (j + 1)) \<in> transitions \<A>_NFA" using first_comp second_comp unfolding \<A>_NFA_def by auto 
  }
  thus ?thesis using properties_run0 by auto
qed

lemma run0_i_step:
  assumes "word_well_defined word (alphabet \<A>_NFA)" "word \<noteq> []" "last word = 0"
  shows "\<forall> i < length (run0 (length word)) - 1 . ((run0 (length word)) ! i, word ! i, (run0 (length word)) ! (i + 1)) \<in> transitions \<A>_NFA"
proof -
  let ?m = "length (run0 (length word)) - 1"
  let ?run = "run0 (length word)"
  have i_step: "\<forall> i < ?m - 1 . (?run ! i, word ! i, ?run ! (i + 1)) \<in> transitions \<A>_NFA" using run0_i_1_step assms by force
  have "(?run ! (?m - 1), word ! (?m - 1), ?run ! ((?m - 1) + 1)) \<in> transitions \<A>_NFA" using run0_last_step assms properties_run0 by auto
  thus ?thesis using Nat.lessE diff_Suc_1 i_step by metis
qed

lemma run0_accepting:
  assumes "word_well_defined word (alphabet \<A>_NFA)" "word \<noteq> []" "last word = 0"
  shows "run_accepting (run0 (length word)) \<A>_NFA word"
proof - 
  let ?run = "run0 (length word)"
  have initial: "?run ! 0 = initial_state \<A>_NFA \<and> initial_state \<A>_NFA \<in> states \<A>_NFA" using assms properties_run0 unfolding \<A>_NFA_def by auto
  hence "run_well_defined ?run \<A>_NFA word" using assms run0_i_step properties_run0 initial run0_i_step unfolding run_well_defined_def pseudo_run_well_defined_def by blast 
  thus ?thesis using properties_run0 unfolding run_accepting_def \<A>_NFA_def by auto
qed

lemma words_\<A>_NFA_right:
  assumes "word_well_defined word (alphabet \<A>_NFA)" "word \<noteq> []" "last word = 0"
  shows "word \<in> language_auto \<A>_NFA"
  using run0_accepting assms unfolding language_auto_def by blast

theorem words_\<A>_NFA:
  assumes "word_well_defined word (alphabet \<A>_NFA)" "word \<noteq> []"
  shows "last word = 0 \<longleftrightarrow> word \<in> language_auto \<A>_NFA"
  using words_\<A>_NFA_left words_\<A>_NFA_right assms by blast

text \<open>Finally we can prove L(\<A>_A) = L(\<A>_NFA)\<close>
corollary lang_equi_examples: "language_auto \<A>_NFA = language_auto \<A>_A"
proof - 
  have empty_word: "[] \<notin> language_auto \<A>_NFA \<and> [] \<notin> language_auto \<A>_A" using empty_word_\<A>_NFA empty_word_\<A>_A by blast
  have alphas: "alphabet \<A>_NFA = alphabet \<A>_A" unfolding \<A>_NFA_def \<A>_A_def by auto
  {
    fix word assume "word \<in> language_auto \<A>_NFA"
    hence "last word = 0 \<and> word_well_defined word (alphabet \<A>_NFA) \<and> word \<noteq> []" using words_\<A>_NFA empty_word word_in_language_is_well_defined well_def_\<A>_NFA by blast
    hence "last word = 0 \<and> word_well_defined word (alphabet \<A>_A) \<and> word \<noteq> []" using alphas unfolding word_well_defined_def by auto
    hence "word \<in> language_auto \<A>_A" using words_\<A>_A by auto
  }
  hence left: "language_auto \<A>_NFA \<subseteq> language_auto \<A>_A" unfolding language_auto_def by auto
  {
    fix word assume "word \<in> language_auto \<A>_A"
    hence "last word = 0 \<and> word_well_defined word (alphabet \<A>_A) \<and> word \<noteq> []" using words_\<A>_A empty_word word_in_language_is_well_defined well_def_examples by blast
    hence "last word = 0 \<and> word_well_defined word (alphabet \<A>_NFA) \<and> word \<noteq> []" using alphas unfolding word_well_defined_def by auto
    hence "word \<in> language_auto \<A>_NFA" using words_\<A>_NFA by auto
  }
  thus ?thesis using left by auto
qed




text \<open>Example for complementation language\<close>
definition \<A>_E :: "(nat, nat) automaton" where "\<A>_E = Automaton {0, 1} {0, 1} \<delta>_A 0 {0}"
value "accepting_states \<A>_E"

theorem comp_example_equivalence: "\<A>_E = comp_automaton \<A>_A"
  unfolding \<A>_A_def \<A>_E_def comp_automaton_def by auto

theorem well_def_comp_example: "auto_well_defined \<A>_E \<and> DFA_property \<A>_E"
  unfolding auto_well_defined_def DFA_property_def \<A>_E_def comp_automaton_def \<A>_A_def \<delta>_A_def by auto

corollary "language_auto \<A>_E = comp_language (alphabet \<A>_A) (language_auto \<A>_A)"
  using comp_example_equivalence well_def_examples DFA_property_examples comp_automaton_language_correctness unfolding \<A>_A_def \<A>_E_def by metis


text \<open>Example for powerset construction\<close>
definition \<delta>_\<A>_DFA :: "(nat states, nat) transitions" where "\<delta>_\<A>_DFA = {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})}"

lemma powerset_transitions_example: "\<delta>_\<A>_DFA \<subseteq> powerset_transitions \<A>_NFA"
  unfolding \<delta>_\<A>_DFA_def \<A>_NFA_def powerset_transitions_def by force

definition \<A>_DFA :: "(nat states, nat) automaton" where "\<A>_DFA = Automaton {{}, {0}, {1}, {0, 1}} {0, 1} \<delta>_\<A>_DFA {0} {{1}, {0, 1}}"

theorem well_def_\<A>_DFA: "auto_well_defined \<A>_DFA \<and> (\<forall> S \<in> states \<A>_DFA . finite S)"
  unfolding auto_well_defined_def \<A>_DFA_def \<delta>_\<A>_DFA_def by auto

lemma powerset_transitions_example_exhaustive:
  assumes "(S1, a, S2) \<in> powerset_transitions \<A>_NFA"
  shows "(S1, a, S2) \<in> \<delta>_\<A>_DFA"
proof -
  have S1: "S1 \<in> Pow (states \<A>_NFA)" using assms unfolding powerset_transitions_def by auto
  have "states \<A>_NFA = {0, 1}" unfolding \<A>_NFA_def by auto
  hence "Pow (states \<A>_NFA) = {{}, {0}, {1}, {0, 1}}" by auto
  hence cases_S1: "S1 = {} \<or> S1 = {0} \<or> S1 = {1} \<or> S1 = {0, 1}" using S1 by auto
  have a_cases: "a = 0 \<or> a = 1" using assms unfolding powerset_transitions_def \<A>_NFA_def by auto
  have S2: "S2 = {s2 . \<exists> s1 \<in> S1 . (s1, a, s2) \<in> transitions \<A>_NFA}" using assms unfolding powerset_transitions_def by auto
  consider (t1) "S1 = {} \<and> a = 0" | (t2) "S1 = {} \<and> a = 1" | (t3) "S1 = {0} \<and> a = 0" | (t4) "S1 = {0} \<and> a = 1" | (t5) "S1 = {1} \<and> a = 0" | (t6) "S1 = {1} \<and> a = 1" | (t7) "S1 = {0, 1} \<and> a = 0" | (t8) "S1 = {0, 1} \<and> a = 1" using cases_S1 a_cases by argo
  thus ?thesis
  proof cases
    case t1 thus ?thesis using S2 unfolding \<delta>_\<A>_DFA_def by auto
  next
    case t2 thus ?thesis using S2 unfolding \<delta>_\<A>_DFA_def by auto
  next
    case t3 thus ?thesis using S2 unfolding \<delta>_\<A>_DFA_def \<A>_NFA_def by auto
  next
    case t4 thus ?thesis using S2 unfolding \<delta>_\<A>_DFA_def \<A>_NFA_def by auto
  next
    case t5 thus ?thesis using S2 unfolding \<delta>_\<A>_DFA_def \<A>_NFA_def by auto
  next
    case t6 thus ?thesis using S2 unfolding \<delta>_\<A>_DFA_def \<A>_NFA_def by auto
  next
    case t7 thus ?thesis using S2 unfolding \<delta>_\<A>_DFA_def \<A>_NFA_def by auto
  next
    case t8 thus ?thesis using S2 unfolding \<delta>_\<A>_DFA_def \<A>_NFA_def by auto
  qed
qed

lemma powerset_automaton_transition_equivalence: "transitions \<A>_DFA = transitions (powerset_automaton \<A>_NFA)"
  using powerset_transitions_example_exhaustive powerset_transitions_example unfolding \<A>_DFA_def powerset_automaton_def by auto

text \<open>Proof of example powerset automaton equivalence\<close>
theorem powerset_examples_equivalence: "\<A>_DFA = powerset_automaton \<A>_NFA"
  using powerset_automaton_transition_equivalence unfolding \<A>_DFA_def powerset_automaton_def \<A>_NFA_def by auto

corollary "language_auto \<A>_DFA = language_auto \<A>_NFA"
  using powerset_examples_equivalence powerset_automaton_language_correctness well_def_\<A>_NFA by metis




text \<open>Example of product transitions\<close>
definition \<delta>_C :: "((nat \<times> nat), nat) transitions" where "\<delta>_C = {((0, 0), 1, (0, 0)), ((0, 1), 1, (0, 1)), ((0, 0), 0, (1, 1)), ((0, 1), 0, (1, 0)), ((1, 0), 0, (1, 1)), ((1, 1), 0, (1, 0)), ((1, 0), 1, (0, 0)), ((1, 1), 1, (0, 1))}"

lemma \<delta>_C_equality: "\<delta>_C = (product_transitions \<delta>_A \<delta>_B)"
  unfolding product_transitions_def \<delta>_C_def \<delta>_A_def \<delta>_B_def by force

text \<open>Example of product intersection automaton\<close>
definition \<A>_C :: "((nat \<times> nat), nat) automaton" where "\<A>_C = Automaton {(0, 0), (0, 1), (1, 0), (1, 1)} {0, 1} \<delta>_C (0, 0) {(1, 0)}"

theorem well_def_\<A>_C: "auto_well_defined \<A>_C \<and> DFA_property \<A>_C"
  unfolding auto_well_defined_def DFA_property_def \<A>_C_def \<delta>_C_def by auto

text \<open>Proof of example intersection automaton equivalence\<close>
theorem inter_example_equivalence: "\<A>_C = intersection_automaton \<A>_A \<A>_B"
  using \<delta>_C_equality unfolding \<A>_C_def \<A>_A_def \<A>_B_def intersection_automaton_def product_automaton_def by auto

text \<open>Example of product union automaton\<close>
definition \<A>_D :: "((nat \<times> nat), nat) automaton" where "\<A>_D = Automaton {(0, 0), (0, 1), (1, 0), (1, 1)} {0, 1} \<delta>_C (0, 0) {(0, 0), (1, 0), (1, 1)}"

theorem "auto_well_defined \<A>_D \<and> DFA_property \<A>_D"
  unfolding auto_well_defined_def DFA_property_def \<A>_D_def \<delta>_C_def by auto

text \<open>Proof of example union automaton equivalence\<close>
theorem union_example_equivalence: "\<A>_D = union_automaton \<A>_A \<A>_B"
  using \<delta>_C_equality unfolding \<A>_D_def \<A>_A_def \<A>_B_def union_automaton_def product_automaton_def by auto

corollary "language_auto \<A>_C = language_auto \<A>_A \<inter> language_auto \<A>_B"
  using inter_example_equivalence well_def_examples language_intersection_correctness unfolding \<A>_A_def \<A>_B_def by metis

corollary "language_auto \<A>_D = language_auto \<A>_A \<union> language_auto \<A>_B"
proof - 
  have "alphabet \<A>_A = alphabet \<A>_B" unfolding \<A>_A_def \<A>_B_def by auto
  thus ?thesis using union_example_equivalence well_def_examples language_union_correctness DFA_property_examples by metis
qed




text \<open>Examples for isomorphy\<close>
definition \<delta>_1 :: "(nat, nat) transitions" where "\<delta>_1 = {(0, 0, 1), (1, 1, 0)}"
definition \<A>_1 :: "(nat, nat) automaton" where "\<A>_1 = Automaton {0, 1} {0, 1} \<delta>_1 0 {1}"

definition \<delta>_2 :: "(nat, nat) transitions" where "\<delta>_2 = {(2, 2, 3), (3, 3, 2)}"
definition \<A>_2 :: "(nat, nat) automaton" where "\<A>_2 = Automaton {2, 3} {2, 3} \<delta>_2 2 {3}"

definition f_example :: "nat \<Rightarrow> nat" where "f_example s = (if s = 0 then 2 else 3)"

theorem \<A>_1_\<A>_2_well_def: "auto_well_defined \<A>_1 \<and> auto_well_defined \<A>_2"
  unfolding auto_well_defined_def \<A>_1_def \<A>_2_def \<delta>_1_def \<delta>_2_def by auto

theorem \<A>_1_\<A>_2_isomorphic: "isomorphic_automata \<A>_1 \<A>_2"
proof -
  have bij_a: "bij_betw f_example (alphabet \<A>_1) (alphabet \<A>_2)" unfolding \<A>_1_def \<A>_2_def f_example_def bij_betw_def by auto
  have bij_s: "bij_betw f_example (states \<A>_1) (states \<A>_2)" unfolding \<A>_1_def \<A>_2_def f_example_def bij_betw_def by auto
  have init: "f_example (initial_state \<A>_1) = initial_state \<A>_2" unfolding f_example_def \<A>_1_def \<A>_2_def by auto
  have acc: "image f_example (accepting_states \<A>_1) = accepting_states \<A>_2" unfolding f_example_def \<A>_1_def \<A>_2_def by auto
  have "image (\<lambda>(s1, a, s2). (f_example s1, f_example a, f_example s2)) (transitions \<A>_1) = transitions \<A>_2" unfolding f_example_def \<A>_1_def \<A>_2_def \<delta>_1_def \<delta>_2_def by auto
  thus ?thesis using bij_a bij_s init acc unfolding isomorphic_automata_def by auto
qed

text \<open>There exists a bijection for language equivalence\<close>
corollary "\<exists> h . bij_betw h (alphabet \<A>_1) (alphabet \<A>_2) \<and> language_auto \<A>_2 = image (map h) (language_auto \<A>_1)"
  using \<A>_1_\<A>_2_well_def \<A>_1_\<A>_2_isomorphic language_iso_correctness_unfold by metis

proposition language_examples: "language_auto \<A>_2 = image (map f_example) (language_auto \<A>_1)"
proof -
  have well_def: "auto_well_defined \<A>_1 \<and> auto_well_defined \<A>_2" using \<A>_1_\<A>_2_well_def by simp
  have bij_a: "bij_betw f_example (alphabet \<A>_1) (alphabet \<A>_2)" unfolding \<A>_1_def \<A>_2_def f_example_def bij_betw_def by auto
  have bij_s: "bij_betw f_example (states \<A>_1) (states \<A>_2)" unfolding \<A>_1_def \<A>_2_def f_example_def bij_betw_def by auto
  have init: "f_example (initial_state \<A>_1) = initial_state \<A>_2" unfolding f_example_def \<A>_1_def \<A>_2_def by auto
  have acc: "image f_example (accepting_states \<A>_1) = accepting_states \<A>_2" unfolding f_example_def \<A>_1_def \<A>_2_def by auto
  have "image (\<lambda>(s1, a, s2). (f_example s1, f_example a, f_example s2)) (transitions \<A>_1) = transitions \<A>_2" unfolding f_example_def \<A>_1_def \<A>_2_def \<delta>_1_def \<delta>_2_def by auto
  thus ?thesis using well_def bij_a bij_s init acc language_iso_correctness by metis
qed




text \<open>Examples for type conversion over nat numbers\<close>
definition \<A>_F :: "(nat, nat) automaton" where "\<A>_F = Automaton {0, 1, 2, 4} {0, 1} {(0, 1, 0), (1, 1, 1), (0, 0, 4), (1, 0, 2), (2, 0, 4), (4, 0, 2), (2, 1, 0), (4, 1, 1)} 0 {2}"

lemma prod_encode_automaton_transition_equivalence: "transitions \<A>_F = transitions (type_encode_automaton \<A>_C prod_encode id)"
proof -
  let ?\<A> = "type_encode_automaton \<A>_C prod_encode id"
  have trans: "transitions \<A>_C = {((0, 0), 1, (0, 0)), ((0, 1), 1, (0, 1)), ((0, 0), 0, (1, 1)), ((0, 1), 0, (1, 0)), ((1, 0), 0, (1, 1)), ((1, 1), 0, (1, 0)), ((1, 0), 1, (0, 0)), ((1, 1), 1, (0, 1))}" unfolding \<A>_C_def \<delta>_C_def by auto
  have "transitions ?\<A> = image (\<lambda>(s1, a, s2) . (prod_encode s1, id a, prod_encode s2)) (transitions \<A>_C)" unfolding type_encode_automaton_def by auto
  hence equi: "transitions ?\<A> = image (\<lambda>(s1, a, s2) . (prod_encode s1, id a, prod_encode s2)) {((0, 0), 1, (0, 0)), ((0, 1), 1, (0, 1)), ((0, 0), 0, (1, 1)), ((0, 1), 0, (1, 0)), ((1, 0), 0, (1, 1)), ((1, 1), 0, (1, 0)), ((1, 0), 1, (0, 0)), ((1, 1), 1, (0, 1))}" using trans by argo
  have "prod_encode (0, 0) = 0 \<and> prod_encode (0, 1) = 1 \<and> prod_encode (1, 0) = 2 \<and> prod_encode (1, 1) = 4" unfolding prod_encode_def by auto
  hence "image (\<lambda>(s1, a, s2) . (prod_encode s1, id a, prod_encode s2)) {((0, 0), 1, (0, 0)), ((0, 1), 1, (0, 1)), ((0, 0), 0, (1, 1)), ((0, 1), 0, (1, 0)), ((1, 0), 0, (1, 1)), ((1, 1), 0, (1, 0)), ((1, 0), 1, (0, 0)), ((1, 1), 1, (0, 1))} = {(0, 1, 0), (1, 1, 1), (0, 0, 4), (1, 0, 2), (2, 0, 4), (4, 0, 2), (2, 1, 0), (4, 1, 1)}" by simp
  hence "transitions ?\<A> = {(0, 1, 0), (1, 1, 1), (0, 0, 4), (1, 0, 2), (2, 0, 4), (4, 0, 2), (2, 1, 0), (4, 1, 1)}" using equi by metis
  thus ?thesis unfolding \<A>_F_def by simp
qed

theorem prod_encode_examples_equivalence: "\<A>_F = type_encode_automaton \<A>_C prod_encode id"
proof -
  let ?\<A> = "type_encode_automaton \<A>_C prod_encode id"
  have states: "states \<A>_F = states ?\<A>" unfolding \<A>_F_def type_encode_automaton_def \<A>_C_def prod_encode_def by force
  have alphabet: "alphabet \<A>_F = alphabet ?\<A>" unfolding \<A>_F_def type_encode_automaton_def \<A>_C_def by force
  have trans: "transitions \<A>_F = transitions ?\<A>" using prod_encode_automaton_transition_equivalence by auto
  have init: "initial_state \<A>_F = initial_state ?\<A>" unfolding \<A>_F_def type_encode_automaton_def \<A>_C_def prod_encode_def by force
  have acc: "accepting_states \<A>_F = accepting_states ?\<A>" unfolding \<A>_F_def type_encode_automaton_def \<A>_C_def prod_encode_def by force
  thus ?thesis using states alphabet trans init acc by (simp add: automaton.expand)
qed

corollary "language_auto \<A>_F = language_auto \<A>_C"
  using well_def_\<A>_C prod_encode_bij_betw type_encode_preserves_same_language prod_encode_examples_equivalence by metis

definition \<A>_G :: "(nat, nat) automaton" where "\<A>_G = Automaton {0, 1, 2, 3} {0, 1} {(0, 0, 0), (0, 1, 0), (2, 0, 0), (2, 1, 0), (1, 1, 1), (1, 0, 3), (3, 0, 3), (3, 1, 1)} 1 {2, 3}"

lemma set_encode_automaton_transition_equivalence: "transitions \<A>_G = transitions (type_encode_automaton \<A>_DFA set_encode id)"
proof -
  let ?\<A> = "type_encode_automaton \<A>_DFA set_encode id"
  have trans: "transitions \<A>_DFA = {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})}" unfolding \<A>_DFA_def \<delta>_\<A>_DFA_def by auto
  have "transitions ?\<A> = image (\<lambda>(s1, a, s2) . (set_encode s1, id a, set_encode s2)) (transitions \<A>_DFA)" unfolding type_encode_automaton_def by auto
  hence equi: "transitions ?\<A> = image (\<lambda>(s1, a, s2) . (set_encode s1, id a, set_encode s2)) {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})}" using trans by argo
  have set_im: "image (\<lambda>(s1, a, s2) . (set_encode s1, a, set_encode s2)) {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})} = {(set_encode {}, 0, set_encode {}), (set_encode {}, 1, set_encode {}), (set_encode {1}, 0, set_encode {}), (set_encode {1}, 1, set_encode {}), (set_encode {0}, 1, set_encode {0}), (set_encode {0}, 0, set_encode {0,1}), (set_encode {0,1}, 0, set_encode {0,1}), (set_encode {0,1}, 1, set_encode {0})}" by force
  have "set_encode {} = 0 \<and> set_encode {0} = 1 \<and> set_encode {1} = 2 \<and> set_encode {0,1} = 3" unfolding set_encode_def by auto
  hence "{(set_encode {}, 0, set_encode {}), (set_encode {}, 1, set_encode {}), (set_encode {1}, 0, set_encode {}), (set_encode {1}, 1, set_encode {}), (set_encode {0}, 1, set_encode {0}), (set_encode {0}, 0, set_encode {0,1}), (set_encode {0,1}, 0, set_encode {0,1}), (set_encode {0,1}, 1, set_encode {0})} = {(0, 0, 0), (0, 1, 0), (2, 0, 0), (2, 1, 0), (1, 1, 1), (1, 0, 3), (3, 0, 3), (3, 1, 1)}" by presburger
  hence "image (\<lambda>(s1, a, s2) . (set_encode s1, id a, set_encode s2)) {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})} = {(0, 0, 0), (0, 1, 0), (2, 0, 0), (2, 1, 0), (1, 1, 1), (1, 0, 3), (3, 0, 3), (3, 1, 1)}" using set_im by force
  hence "transitions ?\<A> = {(0, 0, 0), (0, 1, 0), (2, 0, 0), (2, 1, 0), (1, 1, 1), (1, 0, 3), (3, 0, 3), (3, 1, 1)}" using equi by metis
  thus ?thesis unfolding \<A>_G_def by simp
qed

theorem set_encode_examples_equivalence: "\<A>_G = type_encode_automaton \<A>_DFA set_encode id"
proof -
  let ?\<A> = "type_encode_automaton \<A>_DFA set_encode id"
  have states: "states \<A>_G = states ?\<A>" unfolding \<A>_G_def type_encode_automaton_def \<A>_DFA_def set_encode_def by force
  have alphabet: "alphabet \<A>_G = alphabet ?\<A>" unfolding \<A>_G_def type_encode_automaton_def \<A>_DFA_def by force
  have trans: "transitions \<A>_G = transitions ?\<A>" using set_encode_automaton_transition_equivalence by auto
  have init: "initial_state \<A>_G = initial_state ?\<A>" unfolding \<A>_G_def type_encode_automaton_def \<A>_DFA_def by fastforce
  have acc: "accepting_states \<A>_G = accepting_states ?\<A>" unfolding \<A>_G_def type_encode_automaton_def \<A>_DFA_def by auto
  thus ?thesis using states alphabet trans init acc by (simp add: automaton.expand)
qed

corollary "language_auto \<A>_G = language_auto \<A>_DFA"
  using well_def_\<A>_DFA set_encode_bij_betw type_encode_preserves_same_language set_encode_examples_equivalence by metis



text \<open>Problem: case when states \<A>1 \<inter> states \<A>2 \<noteq> {}\<close>
proposition "states (concatenation_automaton_helper \<A>_A \<A>_B) = {0, 1}"
  unfolding \<A>_A_def \<A>_B_def concatenation_automaton_helper_def by auto

text \<open>Solution: cross_renaming_iso\<close>
proposition "states (concatenation_automaton \<A>_A \<A>_B) = {(0, 1), (1, 1), (0, 2), (1, 2)}"
  unfolding \<A>_A_def \<A>_B_def concatenation_automaton_def concatenation_automaton_helper_def type_encode_automaton_def cross_renaming_iso_def by force





text \<open>Examples for reachability\<close>
proposition reachable_states_A: "reachable_states \<A>_A = states \<A>_A"
proof -
  have "0 = initial_state \<A>_A" unfolding \<A>_A_def by auto
  hence 0: "reachable_state 0 \<A>_A" using initial_state_is_reachable well_def_examples by metis
  have "auto_well_defined \<A>_A \<and> (0, 0, 1) \<in> transitions \<A>_A" using well_def_examples unfolding \<A>_A_def \<delta>_A_def by auto
  hence "reachable_state 1 \<A>_A" using 0 inheritance_reachable_state by fast
  thus ?thesis using reachable_states_are_states well_def_examples 0 unfolding reachable_states_def \<A>_A_def by fastforce
qed

lemma reachable_states_DFA_example_sub: "{{0}, {0, 1}} \<subseteq> reachable_states \<A>_DFA"
proof -
  have "{0} = initial_state \<A>_DFA" unfolding \<A>_DFA_def by auto
  hence 0: "reachable_state {0} \<A>_DFA" using initial_state_is_reachable well_def_\<A>_DFA  unfolding \<A>_DFA_def by fastforce
  have "auto_well_defined \<A>_DFA \<and> ({0}, 0, {0, 1}) \<in> transitions \<A>_DFA" using well_def_\<A>_DFA unfolding \<A>_DFA_def \<delta>_\<A>_DFA_def by auto
  hence "reachable_state {0, 1} \<A>_DFA" using 0 inheritance_reachable_state by fast
  thus ?thesis using 0 unfolding reachable_states_def by fast
qed

lemma \<A>_DFA_is_DFA: "DFA_property \<A>_DFA"
  using DFA_property_powerset_automaton powerset_examples_equivalence well_def_\<A>_NFA by metis

lemma \<A>_DFA_last: "run_well_defined run \<A>_DFA word \<Longrightarrow> last run = {0} \<or> last run = {0, 1}"
proof(induction word arbitrary: run rule: rev_induct)
  case Nil
  hence "length run = 1 \<and> run ! 0 = initial_state \<A>_DFA" unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence "run = [initial_state \<A>_DFA]" using list_with_one_element by metis
  thus ?case unfolding \<A>_DFA_def by auto
next
  case (snoc a word)
  hence assm: "run_well_defined run \<A>_DFA (word @ [a])" by auto
  hence "run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain run' where "run = run' @ [last run]" using append_butlast_last_id by metis
  hence "run_well_defined run' \<A>_DFA word \<and> (last run', a, last run) \<in> transitions \<A>_DFA" using assm prun_well_defined_extension_snoc well_def_\<A>_DFA unfolding run_well_defined_def by metis
  hence "({0}, a, last run) \<in> transitions \<A>_DFA \<or> ({0, 1}, a, last run) \<in> transitions \<A>_DFA" using snoc by force
  thus ?case unfolding \<A>_DFA_def \<delta>_\<A>_DFA_def using snoc by force
qed

lemma \<A>_DFA_not_reachable1: "\<not> reachable_state {} \<A>_DFA"
proof(rule ccontr)
  assume assm: "\<not> (\<not> reachable_state {} \<A>_DFA)"
  hence "reachable_state {} \<A>_DFA" by auto
  thus False using \<A>_DFA_last unfolding reachable_state_def by blast
qed

lemma \<A>_DFA_not_reachable2: "\<not> reachable_state {1} \<A>_DFA"
proof(rule ccontr)
  assume "\<not> (\<not> reachable_state {1} \<A>_DFA)"
  hence "reachable_state {1} \<A>_DFA" by auto
  thus False using \<A>_DFA_last unfolding reachable_state_def by auto
qed

proposition \<A>_DFA_reachable_states: "{{0}, {0, 1}} = reachable_states \<A>_DFA"
proof - 
  have "reachable_states \<A>_DFA \<subseteq> states \<A>_DFA" using well_def_\<A>_DFA reachable_states_are_states by auto
  hence states: "reachable_states \<A>_DFA \<subseteq> {{}, {0}, {1}, {0, 1}}" unfolding \<A>_DFA_def by auto
  have "{{0}, {0, 1}} \<subseteq> reachable_states \<A>_DFA" using reachable_states_DFA_example_sub by auto
  thus ?thesis using states \<A>_DFA_not_reachable1 \<A>_DFA_not_reachable2 unfolding reachable_states_def by blast
qed

definition \<A>_DFA_reach :: "(nat states, nat) automaton" where "\<A>_DFA_reach = Automaton {{0}, {0,1}} {0,1} {({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})} {0} {{0,1}}"

lemma set_minus: "A \<subseteq> B \<Longrightarrow> (A - {(a, b, c)}) \<subseteq> (B - {(a, b, c)})"
  by blast

lemma trans_set_subset: "\<forall> set_ex :: (nat states, nat) transitions . set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})} \<and> ({}, 0, {}) \<notin> set_ex \<and> ({}, 1, {}) \<notin> set_ex \<and> ({1}, 0, {}) \<notin> set_ex \<and> ({1}, 1, {}) \<notin> set_ex \<longrightarrow> set_ex \<subseteq> {({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})}"
proof -
  {
    fix set_ex assume assm: "(set_ex :: (nat states, nat) transitions) \<subseteq> {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})} \<and> ({}, 0, {}) \<notin> set_ex \<and> ({}, 1, {}) \<notin> set_ex \<and> ({1}, 0, {}) \<notin> set_ex \<and> ({1}, 1, {}) \<notin> set_ex"
    have "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})}" using assm by argo
    hence "(set_ex - {({}, 0, {})}) \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})} - {({}, 0, {})})" using set_minus by metis
    hence "set_ex \<subseteq> {({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})}" using assm by simp
    hence "(set_ex - {({}, 1, {})}) \<subseteq> ({({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})} - {({}, 1, {})})" using set_minus by metis
    hence "set_ex \<subseteq> {({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})}" using assm by simp
    hence "(set_ex - {({1}, 0, {})}) \<subseteq> ({({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})} - {({1}, 0, {})})" using set_minus by metis
    hence "set_ex \<subseteq> {({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})}" using assm by simp
    hence "(set_ex - {({1}, 1, {})}) \<subseteq> ({({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})} - {({1}, 1, {})})" using set_minus by metis
  }
  thus ?thesis by simp
qed

theorem DFA_reach_equi: "reachable_automaton \<A>_DFA = \<A>_DFA_reach"
proof -
  let ?trans_set = "{(s1, a, s2) \<in> transitions \<A>_DFA . reachable_state s1 \<A>_DFA \<and> reachable_state s2 \<A>_DFA}"
  have states: "reachable_states \<A>_DFA = {{0}, {0, 1}}" using \<A>_DFA_reachable_states by argo
  have trans: "transitions \<A>_DFA = {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})}" unfolding \<A>_DFA_def \<delta>_\<A>_DFA_def by auto
  have "?trans_set \<subseteq> transitions \<A>_DFA" by blast
  hence sub: "?trans_set \<subseteq> {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})}" using trans by argo
  have reach: "reachable_state {0} \<A>_DFA \<and> reachable_state {0, 1} \<A>_DFA \<and> \<not> reachable_state {} \<A>_DFA \<and> \<not> reachable_state {1} \<A>_DFA" using states \<A>_DFA_not_reachable1 \<A>_DFA_not_reachable2 unfolding reachable_states_def by blast
  hence "?trans_set \<subseteq> {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})} \<and> ({}, 0, {}) \<notin> ?trans_set \<and> ({}, 1, {}) \<notin> ?trans_set \<and> ({1}, 0, {}) \<notin> ?trans_set \<and> ({1}, 1, {}) \<notin> ?trans_set" using sub by fast
  hence sub_sub: "?trans_set \<subseteq> {({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})}" using trans_set_subset by presburger
  have "({0}, 1, {0}) \<in> ?trans_set \<and> ({0}, 0, {0,1}) \<in> ?trans_set \<and> ({0,1}, 0, {0,1}) \<in> ?trans_set \<and> ({0,1}, 1, {0}) \<in> ?trans_set" using reach trans by force
  hence "?trans_set = {({0}, 1, {0}), ({0}, 0, {0,1}), ({0,1}, 0, {0,1}), ({0,1}, 1, {0})}" using sub_sub by fastforce
  thus ?thesis using states unfolding \<A>_DFA_def \<A>_DFA_reach_def reachable_automaton_def by force
qed

corollary "language_auto \<A>_DFA = language_auto \<A>_DFA_reach"
  using reachable_automaton_language_correctness DFA_reach_equi well_def_\<A>_DFA by metis

text \<open>One can prove L(\<A>_A) = L(\<A>_NFA) in an easy, alternative way using isomorphy and reachability:\<close>
definition f_DFA_reach_A :: "nat states \<Rightarrow> nat" where "f_DFA_reach_A s = (if s = {0} then 0 else 1)"

theorem \<A>_DFA_reach_A_soft_isomorphic: "soft_isomorphic_automata \<A>_DFA_reach \<A>_A"
proof -
  have bij: "bij_betw f_DFA_reach_A (states \<A>_DFA_reach) (states \<A>_A)" unfolding f_DFA_reach_A_def bij_betw_def \<A>_DFA_reach_def \<A>_A_def by force 
  have id: "bij_betw id (alphabet \<A>_DFA_reach) (alphabet \<A>_A)" unfolding \<A>_DFA_reach_def \<A>_A_def by auto
  have init: "f_DFA_reach_A (initial_state \<A>_DFA_reach) = initial_state \<A>_A" unfolding f_DFA_reach_A_def \<A>_DFA_reach_def \<A>_A_def by auto
  have acc: "image f_DFA_reach_A (accepting_states \<A>_DFA_reach) = accepting_states \<A>_A" unfolding f_DFA_reach_A_def \<A>_DFA_reach_def \<A>_A_def by auto
  have "image (\<lambda>(s1, a, s2) . (f_DFA_reach_A s1, id a, f_DFA_reach_A s2)) (transitions \<A>_DFA_reach) = transitions \<A>_A" unfolding f_DFA_reach_A_def \<A>_DFA_reach_def \<A>_A_def \<delta>_A_def by force
  thus ?thesis using bij id init acc unfolding soft_isomorphic_automata_def by blast
qed

lemma well_def_DFA_reach: "auto_well_defined \<A>_DFA_reach"
  using DFA_reach_equi well_def_\<A>_DFA well_def_reachable_automaton by metis

proposition "language_auto \<A>_NFA = language_auto \<A>_A"
proof - 
  have "language_auto \<A>_NFA = language_auto \<A>_DFA" using powerset_automaton_language_correctness powerset_examples_equivalence well_def_\<A>_NFA by metis
  hence "language_auto \<A>_NFA = language_auto \<A>_DFA_reach" using reachable_automaton_language_correctness DFA_reach_equi well_def_\<A>_DFA by metis
  thus ?thesis using \<A>_DFA_reach_A_soft_isomorphic language_soft_iso_correctness well_def_DFA_reach by auto
qed

text \<open>Examples for reachability: iterativ\<close>
proposition "reachable_states_iterativ \<A>_A = reachable_states \<A>_A"
  using reachable_states_A unfolding \<A>_A_def \<delta>_A_def reachable_states_iterativ_def by force

proposition "reachable_states_iterativ \<A>_DFA = reachable_states \<A>_DFA"
proof - 
  have "(card (states \<A>_DFA)) = Suc (Suc (Suc (Suc 0))) \<and> initial_state \<A>_DFA = {0}" unfolding \<A>_DFA_def by auto
  hence "reachable_states_iter (card (states \<A>_DFA) - 1) \<A>_DFA {initial_state \<A>_DFA} = reachable_states_iter (Suc (Suc (Suc 0))) \<A>_DFA {{0}}" by auto
  hence r1: "reachable_states_iter (card (states \<A>_DFA) - 1) \<A>_DFA {initial_state \<A>_DFA} = {{0}} \<union> reachable_states_iter (Suc (Suc 0)) \<A>_DFA {s2 . \<exists> s1 a. s1 \<in> {{0}} \<and> (s1, a, s2) \<in> transitions \<A>_DFA}" by auto
  have "{s2 . \<exists> s1 a. s1 \<in> {{0}} \<and> (s1, a, s2) \<in> transitions \<A>_DFA} = {{0}, {0, 1}}" unfolding \<A>_DFA_def \<delta>_\<A>_DFA_def by auto
  hence "reachable_states_iter (card (states \<A>_DFA) - 1) \<A>_DFA {initial_state \<A>_DFA} = {{0}} \<union> reachable_states_iter (Suc (Suc 0)) \<A>_DFA {{0}, {0, 1}}" using r1 by argo
  hence r2: "reachable_states_iter (card (states \<A>_DFA) - 1) \<A>_DFA {initial_state \<A>_DFA} = {{0}, {0, 1}} \<union> reachable_states_iter (Suc 0) \<A>_DFA {s2 . \<exists> s1 a. s1 \<in> {{0}, {0, 1}} \<and> (s1, a, s2) \<in> transitions \<A>_DFA}" by force
  have equi: "{s2 . \<exists> s1 a. s1 \<in> {{0}, {0, 1}} \<and> (s1, a, s2) \<in> transitions \<A>_DFA} = {s2 . \<exists> s1 a. s1 \<in> {{0}} \<and> (s1, a, s2) \<in> transitions \<A>_DFA} \<union> {s2 . \<exists> s1 a. s1 \<in> {{0, 1}} \<and> (s1, a, s2) \<in> transitions \<A>_DFA}" by auto
  have "{s2 . \<exists> s1 a. s1 \<in> {{0}} \<and> (s1, a, s2) \<in> transitions \<A>_DFA} = {{0}, {0, 1}} \<and> {s2 . \<exists> s1 a. s1 \<in> {{0, 1}} \<and> (s1, a, s2) \<in> transitions \<A>_DFA} = {{0}, {0, 1}}" unfolding \<A>_DFA_def \<delta>_\<A>_DFA_def by force
  hence "{s2 . \<exists> s1 a. s1 \<in> {{0}, {0, 1}} \<and> (s1, a, s2) \<in> transitions \<A>_DFA} = {{0}, {0, 1}}" using equi by auto
  hence "reachable_states_iter (card (states \<A>_DFA) - 1) \<A>_DFA {initial_state \<A>_DFA} = {{0}, {0, 1}}" using r2 by force
  thus ?thesis using \<A>_DFA_reachable_states unfolding reachable_states_iterativ_def by argo
qed





text \<open>Example of an automaton with eps-transitions\<close>
definition \<A>_eps :: "(nat, nat + unit) automaton" where "\<A>_eps = Automaton {0, 1, 2} {Inl 0, Inl 1, Inr()} {(0, Inr(), 2), (0, Inl 0, 1), (1, Inl 1, 0), (1, Inl 0, 2), (2, Inl 0, 2), (2, Inr(), 1)} 0 {2}"

proposition \<A>_eps_well_defined: "auto_well_defined \<A>_eps"
  unfolding \<A>_eps_def auto_well_defined_def by auto

proposition epsi_clos_0: "epsilon_closure 0 \<A>_eps = {0, 1, 2}"
proof -
  have well_def: "auto_well_defined \<A>_eps" using \<A>_eps_well_defined by auto
  have "0 \<in> states \<A>_eps" unfolding \<A>_eps_def by auto
  hence 0: "epsilon_connected 0 \<A>_eps 0" using s_to_s_epsilon_connection by fast
  have "(0, Inr(), 2) \<in> transitions \<A>_eps" unfolding \<A>_eps_def by force
  hence 2: "epsilon_connected 0 \<A>_eps 2" using transitivity_esp_connected well_def 0 by fast
  have "(2, Inr(), 1) \<in> transitions \<A>_eps" unfolding \<A>_eps_def by force 
  hence "epsilon_connected 0 \<A>_eps 1" using transitivity_esp_connected well_def 2 by fast 
  hence sub: "{0, 1, 2} \<subseteq> epsilon_closure 0 \<A>_eps" using 0 2 unfolding epsilon_closure_def by auto
  have "0 \<in> states \<A>_eps \<and> {0, 1, 2} = states \<A>_eps" unfolding \<A>_eps_def by auto
  hence "epsilon_closure 0 \<A>_eps \<subseteq> {0, 1, 2}" using \<A>_eps_well_defined epsilon_closure_sub_states by metis
  thus ?thesis using sub by fast
qed

proposition epsi_clos_1: "epsilon_closure 1 \<A>_eps = {1}"
proof -
  have "1 \<in> states \<A>_eps" unfolding \<A>_eps_def by auto
  hence 1: "1 \<in> epsilon_closure 1 \<A>_eps" using s_to_s_epsilon_connection unfolding epsilon_closure_def by fast
  have 0: "0 \<notin> epsilon_closure 1 \<A>_eps"
  proof(rule ccontr)
    assume "\<not> 0 \<notin> epsilon_closure 1 \<A>_eps"
    hence "0 \<in> epsilon_closure 1 \<A>_eps" by auto
    then obtain run where run: "run ! 0 = 1 \<and> length run > 0 \<and> (\<forall> i < length run - 1 . (run ! i, Inr(), run ! (i + 1)) \<in> transitions \<A>_eps) \<and> last run = 0" unfolding epsilon_closure_def epsilon_connected_def eps_run_well_defined_def by blast
    then consider (case1) "length run = 1" | (case2) "length run > 1" by linarith
    thus False
    proof cases
      case case1
      hence "run = [1]" using run list_with_one_element by fast
      thus ?thesis using run by auto
    next
      case case2
      hence "\<exists> s . (1, Inr(), s) \<in> transitions \<A>_eps \<and> s \<in> states \<A>_eps" using run \<A>_eps_well_defined well_def_trans_components by fastforce
      thus ?thesis unfolding \<A>_eps_def by auto
    qed
  qed
  have 2: "2 \<notin> epsilon_closure 1 \<A>_eps"
  proof(rule ccontr)
    assume "\<not> 2 \<notin> epsilon_closure 1 \<A>_eps"
    hence "2 \<in> epsilon_closure 1 \<A>_eps" by auto
    then obtain run where run: "run ! 0 = 1 \<and> length run > 0 \<and> (\<forall> i < length run - 1 . (run ! i, Inr(), run ! (i + 1)) \<in> transitions \<A>_eps) \<and> last run = 2" unfolding epsilon_closure_def epsilon_connected_def eps_run_well_defined_def by blast
    then consider (case1) "length run = 1" | (case2) "length run > 1" by linarith
    thus False
    proof cases
      case case1
      hence "run = [1]" using run list_with_one_element by metis
      thus ?thesis using run by auto
    next
      case case2
      hence "\<exists> s . (1, Inr(), s) \<in> transitions \<A>_eps \<and> s \<in> states \<A>_eps" using run \<A>_eps_well_defined well_def_trans_components by fastforce
      thus ?thesis unfolding \<A>_eps_def by auto
    qed
  qed
  have "1 \<in> states \<A>_eps \<and> {0, 1, 2} = states \<A>_eps" unfolding \<A>_eps_def by auto
  hence "epsilon_closure 1 \<A>_eps \<subseteq> {0, 1, 2}" using \<A>_eps_well_defined epsilon_closure_sub_states by metis
  thus ?thesis using 0 1 2 by blast
qed

proposition epsi_clos_2: "epsilon_closure 2 \<A>_eps = {1, 2}"
proof -
  have "2 \<in> states \<A>_eps" unfolding \<A>_eps_def by auto
  hence 2: "2 \<in> epsilon_closure 2 \<A>_eps" using s_to_s_epsilon_connection unfolding epsilon_closure_def by fast
  have "[2, 1] ! 0 = 2 \<and> 2 \<in> states \<A>_eps \<and> last [2, 1] = 1 \<and> length [2, 1] > 1 \<and> (\<forall> i < length [2, 1] - 1 . ([2, 1] ! i, Inr(), [2, 1] ! (i + 1)) \<in> transitions \<A>_eps)" unfolding \<A>_eps_def by auto
  hence 1: "1 \<in> epsilon_closure 2 \<A>_eps" unfolding epsilon_connected_def epsilon_closure_def eps_run_well_defined_def by blast
  have 0: "0 \<notin> epsilon_closure 2 \<A>_eps"
  proof(rule ccontr)
    assume "\<not> 0 \<notin> epsilon_closure 2 \<A>_eps"
    hence "0 \<in> epsilon_closure 2 \<A>_eps" by auto
    then obtain run where run: "run ! 0 = 2 \<and> length run > 0 \<and> (\<forall> i < length run - 1 . (run ! i, Inr(), run ! (i + 1)) \<in> transitions \<A>_eps) \<and> last run = 0" unfolding epsilon_closure_def epsilon_connected_def eps_run_well_defined_def by blast
    then consider (case1) "length run = 1" | (case2) "length run > 1" by linarith 
    thus False
    proof cases
      case case1
      hence "run = [2]" using run list_with_one_element by fast
      thus ?thesis using run by auto
    next
      case case2
      hence "run \<noteq> [] \<and> length run > 1" by auto
      hence "\<exists> s . (s, Inr(), 0) \<in> transitions \<A>_eps \<and> s \<in> states \<A>_eps" using run \<A>_eps_well_defined well_def_trans_components list_properties_not_empty less_add_one simple_math by metis
      thus ?thesis unfolding \<A>_eps_def by auto
    qed
  qed
  have "2 \<in> states \<A>_eps \<and> {0, 1, 2} = states \<A>_eps" unfolding \<A>_eps_def by auto
  hence "epsilon_closure 2 \<A>_eps \<subseteq> {0, 1, 2}" using \<A>_eps_well_defined epsilon_closure_sub_states by metis
  thus ?thesis using 0 1 2 by blast
qed

lemma eps_trans_0: "normalize_epsilon_nfa_transitions 0 \<A>_eps = {(0, 1, 0), (0, 0, 1), (0, 0, 2)}"
  using epsi_clos_0 unfolding normalize_epsilon_nfa_transitions_def \<A>_eps_def by auto

lemma eps_trans_1: "normalize_epsilon_nfa_transitions 1 \<A>_eps = {(1, 1, 0), (1, 0, 2)}"
  using epsi_clos_1 unfolding normalize_epsilon_nfa_transitions_def \<A>_eps_def by auto

lemma eps_trans_2: "normalize_epsilon_nfa_transitions 2 \<A>_eps = {(2, 1, 0), (2, 0, 2)}"
  using epsi_clos_2 unfolding normalize_epsilon_nfa_transitions_def \<A>_eps_def by force

definition \<A>_eps_free :: "(nat, nat) automaton" where "\<A>_eps_free = Automaton {0, 1, 2} {0, 1} {(0, 1, 0), (0, 0, 1), (0, 0, 2), (1, 0, 2), (1, 1, 0), (2, 1, 0), (2, 0, 2)} 0 {0, 2}"

theorem normalize_epsilon_examples_equivalence: "\<A>_eps_free = (normalize_epsilon_nfa \<A>_eps)"
proof - 
  let ?\<A> = "normalize_epsilon_nfa \<A>_eps"
  have s: "states \<A>_eps = {0, 1 ,2}" unfolding \<A>_eps_def by auto
  have states: "states \<A>_eps_free = states ?\<A>" unfolding normalize_epsilon_nfa_def \<A>_eps_free_def \<A>_eps_def by force
  have alpha: "alphabet \<A>_eps_free = alphabet ?\<A>" unfolding normalize_epsilon_nfa_def \<A>_eps_free_def \<A>_eps_def original_alphabet_def by force
  have "transitions ?\<A> = (\<Union> s \<in> {0, 1 ,2} . normalize_epsilon_nfa_transitions s \<A>_eps)" using s unfolding normalize_epsilon_nfa_def by force
  hence trans: "transitions ?\<A> = transitions \<A>_eps_free" using eps_trans_0 eps_trans_1 eps_trans_2 unfolding \<A>_eps_free_def by force
  have init: "initial_state \<A>_eps_free = initial_state ?\<A>" unfolding normalize_epsilon_nfa_def \<A>_eps_free_def \<A>_eps_def by force
  have "accepting_states \<A>_eps = {2}" unfolding \<A>_eps_def by force
  hence "accepting_states ?\<A> = {s \<in> {0, 1 ,2} . epsilon_closure s \<A>_eps \<inter> {2} \<noteq> {}}" using s unfolding normalize_epsilon_nfa_def by auto
  hence "accepting_states ?\<A> = accepting_states \<A>_eps_free" using epsi_clos_0 epsi_clos_1 epsi_clos_2 unfolding \<A>_eps_free_def by force
  thus ?thesis using states alpha trans init by (simp add: automaton.expand)
qed

text \<open>Examples for eps-closure: iterativ\<close>
proposition "epsilon_closure_iterativ 0 \<A>_eps = epsilon_closure 0 \<A>_eps"
  using epsi_clos_0 unfolding epsilon_closure_iterativ_def \<A>_eps_def by auto

proposition "epsilon_closure_iterativ 1 \<A>_eps = epsilon_closure 1 \<A>_eps"
  using epsi_clos_1 unfolding epsilon_closure_iterativ_def \<A>_eps_def by force

proposition "epsilon_closure_iterativ 2 \<A>_eps = epsilon_closure 2 \<A>_eps"
  using epsi_clos_2 unfolding epsilon_closure_iterativ_def \<A>_eps_def by force




text \<open>Examples for reversal\<close>
definition \<A>_NFA_rev :: "(nat, nat) nfa_multi" where "\<A>_NFA_rev = NFA_multi {0, 1} {0, 1} {(0, 0, 0), (0, 1, 0), (1, 0, 0)} {1} {0}"

theorem rev_example_equivalence: "\<A>_NFA_rev = reversal_nfa \<A>_NFA"
  unfolding \<A>_NFA_def \<A>_NFA_rev_def reversal_nfa_def by force

text \<open>Example DFA that can be minimized\<close>
definition \<A>_not_minimal :: "(nat, nat) automaton" where "\<A>_not_minimal = Automaton {0, 1, 2} {0, 1} {(0, 0, 2), (0, 1, 0), (1, 0, 2), (1, 1, 0), (2, 0, 2), (2, 1, 0)} 0 {2}"

proposition \<A>_not_minimal_well_def: "auto_well_defined \<A>_not_minimal"
  unfolding auto_well_defined_def \<A>_not_minimal_def by auto

definition \<A>_not_minimal_rev :: "(nat, nat) nfa_multi" where "\<A>_not_minimal_rev = NFA_multi {0, 1, 2} {0, 1} {(2, 0, 0), (0, 1, 0), (2, 0, 1), (0, 1, 1), (2, 0, 2), (0, 1, 2)} {2} {0}"

theorem equi_rev_example: "\<A>_not_minimal_rev = reversal_nfa \<A>_not_minimal"
  unfolding \<A>_not_minimal_def \<A>_not_minimal_rev_def reversal_nfa_def by auto

corollary \<A>_not_minimal_rev_well_def: "auto_well_defined_multi \<A>_not_minimal_rev"
  using \<A>_not_minimal_well_def equi_rev_example reversal_preserves_well_defined by metis

definition \<delta>_\<A>_not_minimal_rev_pow :: "(nat states, nat) transitions" where "\<delta>_\<A>_not_minimal_rev_pow = {({}, 0, {}), ({}, 1, {}), ({0}, 0, {}), ({0}, 1, {0, 1, 2}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}"

definition \<A>_not_minimal_rev_pow :: "(nat states, nat) automaton" where "\<A>_not_minimal_rev_pow = Automaton {{}, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} {0, 1} \<delta>_\<A>_not_minimal_rev_pow {2} {{0}, {0, 1}, {0, 2}, {0, 1, 2}}"

lemma powerset_transitions_multi_example: "\<delta>_\<A>_not_minimal_rev_pow \<subseteq> powerset_transitions_multi \<A>_not_minimal_rev"
  unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def powerset_transitions_multi_def by auto

lemma card_pow_8: "card (Pow {0::nat, 1, 2}) = 8"
proof -
  have "finite {0::nat, 1, 2} \<and> card {0::nat, 1, 2} = 3" by simp
  hence "card (Pow {0::nat, 1, 2}) = 2^3" using card_Pow by metis
  thus ?thesis by auto
qed

lemma card_helper0: "card {{}, {0::nat}, {1::nat}, {2::nat}} = 4"
  by simp

lemma card_helper1: "card {{0::nat, 1::nat}, {0::nat, 2::nat}} = 2"
proof -
  have "{0::nat, 1::nat} \<noteq> {0::nat, 2::nat}" by fastforce
  thus ?thesis by simp
qed

lemma card_helper2: "card {{1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}} = 2"
proof -
  have "{1::nat, 2::nat} \<noteq> {0::nat, 1::nat, 2::nat}" by fastforce
  thus ?thesis by simp
qed

lemma card_helper3: "card {{0::nat, 1::nat}, {0::nat, 2::nat}, {1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}} = 4"
proof -
  have finite: "finite {{0::nat, 1::nat}, {0::nat, 2::nat}} \<and> finite {{1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}}" by simp
  have inter: "{{0::nat, 1::nat}, {0::nat, 2::nat}} \<inter> {{1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}} = {}" by (simp add: insert_eq_iff)
  have "{{0::nat, 1::nat}, {0::nat, 2::nat}, {1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}} = {{0::nat, 1::nat}, {0::nat, 2::nat}} \<union> {{1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}}" by fast
  hence "card {{0::nat, 1::nat}, {0::nat, 2::nat}, {1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}} = card {{0::nat, 1::nat}, {0::nat, 2::nat}} + card {{1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}}" using finite inter card_Un_disjoint by metis 
  thus ?thesis using card_helper1 card_helper2 by presburger
qed

lemma card_states_example_8: "card {{}, {0::nat}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} = 8"
proof - 
  have finite: "finite {{}, {0::nat}, {1::nat}, {2::nat}} \<and> finite {{0::nat, 1::nat}, {0::nat, 2::nat}, {1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}}" by simp
  have inter: "{{}, {0::nat}, {1::nat}, {2::nat}} \<inter> {{0::nat, 1::nat}, {0::nat, 2::nat}, {1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}} = {}" by fastforce
  have "{{}, {0::nat}, {1::nat}, {2::nat}, {0::nat, 1::nat}, {0::nat, 2::nat}, {1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}} = {{}, {0::nat}, {1::nat}, {2::nat}} \<union> {{0::nat, 1::nat}, {0::nat, 2::nat}, {1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}}" by fast
  hence "card {{}, {0::nat}, {1::nat}, {2::nat}, {0::nat, 1::nat}, {0::nat, 2::nat}, {1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}} = card {{}, {0::nat}, {1::nat}, {2::nat}} + card {{0::nat, 1::nat}, {0::nat, 2::nat}, {1::nat, 2::nat}, {0::nat, 1::nat, 2::nat}}" using finite inter card_Un_disjoint by metis 
  thus ?thesis using card_helper0 card_helper3 by presburger
qed  

lemma Pow_set: "Pow {0::nat, 1, 2} = {{}, {0::nat}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}"
proof -
  have sub: "{{}, {0::nat}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} \<subseteq> Pow {0::nat, 1, 2}" by simp
  have card_8: "card {{}, {0::nat}, {1::nat}, {2::nat}, {0::nat, 1}, {0::nat, 2}, {1::nat, 2}, {0::nat, 1, 2}} = 8 \<and> finite {{}, {0::nat}, {1::nat}, {2::nat}, {0::nat, 1}, {0::nat, 2}, {1::nat, 2}, {0::nat, 1, 2}}" using card_states_example_8 by blast
  have "card (Pow {0::nat, 1, 2}) = 8 \<and> finite (Pow {0::nat, 1, 2})" using card_pow_8 by blast
  thus ?thesis using sub card_8 card_subset_eq by metis
qed

lemma powerset_transitions_multi_example_exhaustive:
  assumes "(S1, a, S2) \<in> powerset_transitions_multi \<A>_not_minimal_rev"
  shows "(S1, a, S2) \<in> \<delta>_\<A>_not_minimal_rev_pow"
proof -
  have S1: "S1 \<in> Pow (states_multi \<A>_not_minimal_rev)" using assms unfolding powerset_transitions_multi_def by auto
  have "states_multi \<A>_not_minimal_rev = {0, 1, 2}" unfolding \<A>_not_minimal_rev_def by auto
  hence "Pow (states_multi \<A>_not_minimal_rev) = {{}, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}" using Pow_set by metis
  hence cases_S1: "S1 = {} \<or> S1 = {0} \<or> S1 = {1} \<or> S1 = {2} \<or> S1 = {0, 1} \<or> S1 = {0, 2} \<or> S1 = {1, 2} \<or> S1 = {0, 1 ,2}" using S1 by auto
  have a_cases: "a = 0 \<or> a = 1" using assms unfolding powerset_transitions_multi_def \<A>_not_minimal_rev_def by auto
  have S2: "S2 = {s2 . \<exists> s1 \<in> S1 . (s1, a, s2) \<in> transitions_multi \<A>_not_minimal_rev}" using assms unfolding powerset_transitions_multi_def by auto
  consider (t1) "S1 = {} \<and> a = 0" | (t2) "S1 = {} \<and> a = 1" | (t3) "S1 = {0} \<and> a = 0" | (t4) "S1 = {0} \<and> a = 1" | (t5) "S1 = {1} \<and> a = 0" | (t6) "S1 = {1} \<and> a = 1" | (t7) "S1 = {2} \<and> a = 0" | (t8) "S1 = {2} \<and> a = 1" | (t9) "S1 = {0, 1} \<and> a = 0" | (t10) "S1 = {0, 1} \<and> a = 1" | (t11) "S1 = {0, 2} \<and> a = 0" | (t12) "S1 = {0, 2} \<and> a = 1" | (t13) "S1 = {1, 2} \<and> a = 0" | (t14) "S1 = {1, 2} \<and> a = 1" | (t15) "S1 = {0, 1, 2} \<and> a = 0" | (t16) "S1 = {0, 1, 2} \<and> a = 1" using cases_S1 a_cases by argo
  thus ?thesis
  proof cases
    case t1 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def by auto
  next
    case t2 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def by auto
  next
    case t3 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t4 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t5 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t6 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t7 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t8 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t9 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t10 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t11 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t12 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t13 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t14 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t15 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  next
    case t16 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_def by auto
  qed
qed

lemma powerset_automaton_transition_multi_equivalence: "transitions \<A>_not_minimal_rev_pow = transitions (powerset_automaton_multi \<A>_not_minimal_rev)"
  using powerset_transitions_multi_example_exhaustive powerset_transitions_multi_example unfolding \<A>_not_minimal_rev_pow_def powerset_automaton_multi_def by auto

text \<open>Proof of example powerset automaton equivalence\<close>
theorem powerset_multi_examples_equivalence: "\<A>_not_minimal_rev_pow = powerset_automaton_multi \<A>_not_minimal_rev"
proof -
  have "states_multi \<A>_not_minimal_rev = {0, 1, 2}" unfolding \<A>_not_minimal_rev_def by auto
  hence "Pow (states_multi \<A>_not_minimal_rev) = {{}, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}" using Pow_set by argo
  hence states: "states \<A>_not_minimal_rev_pow = states (powerset_automaton_multi \<A>_not_minimal_rev)" unfolding \<A>_not_minimal_rev_pow_def powerset_automaton_multi_def by auto
  have alphabet: "alphabet \<A>_not_minimal_rev_pow = alphabet (powerset_automaton_multi \<A>_not_minimal_rev)" unfolding \<A>_not_minimal_rev_pow_def powerset_automaton_multi_def \<A>_not_minimal_rev_def by force
  have trans: "transitions \<A>_not_minimal_rev_pow = transitions (powerset_automaton_multi \<A>_not_minimal_rev)" using powerset_automaton_transition_multi_equivalence by auto
  have init: "initial_state \<A>_not_minimal_rev_pow = initial_state (powerset_automaton_multi \<A>_not_minimal_rev)" unfolding \<A>_not_minimal_rev_pow_def powerset_automaton_multi_def \<A>_not_minimal_rev_def by force
  have acc: "accepting_states \<A>_not_minimal_rev_pow = accepting_states (powerset_automaton_multi \<A>_not_minimal_rev)" unfolding \<A>_not_minimal_rev_pow_def powerset_automaton_multi_def \<A>_not_minimal_rev_def by auto
  thus ?thesis using states alphabet trans init acc by (simp add: automaton.expand)
qed

corollary \<A>_not_minimal_rev_pow_well_def: "auto_well_defined \<A>_not_minimal_rev_pow"
  using \<A>_not_minimal_rev_well_def powerset_multi_examples_equivalence well_def_powerset_automaton_multi by metis

lemma card_states_example: "card (states \<A>_not_minimal_rev_pow) = 8"
  using card_states_example_8 unfolding \<A>_not_minimal_rev_pow_def by force

proposition r_s_i_example: "reachable_states_iterativ \<A>_not_minimal_rev_pow = {{2}, {0, 1, 2}, {}}"
proof - 
  have "states \<A>_not_minimal_rev_pow = {{}, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}" unfolding \<A>_not_minimal_rev_pow_def by simp
  have "card (states \<A>_not_minimal_rev_pow) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) \<and> initial_state \<A>_not_minimal_rev_pow = {2}" using card_states_example unfolding \<A>_not_minimal_rev_pow_def by auto 
  hence "reachable_states_iter (card (states \<A>_not_minimal_rev_pow) - 1) \<A>_not_minimal_rev_pow {initial_state \<A>_not_minimal_rev_pow} = reachable_states_iter (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) \<A>_not_minimal_rev_pow {{2}}" by auto
  hence r1: "reachable_states_iter (card (states \<A>_not_minimal_rev_pow) - 1) \<A>_not_minimal_rev_pow {initial_state \<A>_not_minimal_rev_pow} = {{2}} \<union> reachable_states_iter (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) \<A>_not_minimal_rev_pow {s2 . \<exists> s1 a. s1 \<in> {{2}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow}" by simp
  have "{s2 . \<exists> s1 a. s1 \<in> {{2}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow} = {{}, {0, 1, 2}}" unfolding \<A>_not_minimal_rev_pow_def \<delta>_\<A>_not_minimal_rev_pow_def by force
  hence "reachable_states_iter (card (states \<A>_not_minimal_rev_pow) - 1) \<A>_not_minimal_rev_pow {initial_state \<A>_not_minimal_rev_pow} = {{2}} \<union> reachable_states_iter (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) \<A>_not_minimal_rev_pow {{}, {0, 1, 2}}" using r1 by argo
  hence r2: "reachable_states_iter (card (states \<A>_not_minimal_rev_pow) - 1) \<A>_not_minimal_rev_pow {initial_state \<A>_not_minimal_rev_pow} = {{2}, {}, {0, 1, 2}} \<union> reachable_states_iter (Suc (Suc (Suc (Suc (Suc 0))))) \<A>_not_minimal_rev_pow {s2 . \<exists> s1 a. s1 \<in> {{}, {0, 1, 2}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow}" by force
  have equi: "{s2 . \<exists> s1 a. s1 \<in> {{}, {0, 1, 2}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow} = {s2 . \<exists> s1 a. s1 \<in> {{}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow} \<union> {s2 . \<exists> s1 a. s1 \<in> {{0, 1, 2}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow}" by auto
  have "{s2 . \<exists> s1 a. s1 \<in> {{}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow} = {{}} \<and> {s2 . \<exists> s1 a. s1 \<in> {{0, 1, 2}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow} = {{0, 1, 2}}" unfolding \<A>_not_minimal_rev_pow_def \<delta>_\<A>_not_minimal_rev_pow_def by fastforce
  hence "{s2 . \<exists> s1 a. s1 \<in> {{}, {0, 1, 2}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow} = {{}, {0, 1, 2}}" using equi by auto
  hence "reachable_states_iter (card (states \<A>_not_minimal_rev_pow) - 1) \<A>_not_minimal_rev_pow {initial_state \<A>_not_minimal_rev_pow} = {{2}, {}, {0, 1, 2}}" using r2 by force
  thus ?thesis unfolding reachable_states_iterativ_def by force
qed

corollary reachable_states_example: "reachable_states \<A>_not_minimal_rev_pow = {{2}, {0, 1, 2}, {}}"
  using equivalence_of_reachable_states \<A>_not_minimal_rev_pow_well_def r_s_i_example by metis

lemma unreachable_states_example1: "\<not> reachable_state {0} \<A>_not_minimal_rev_pow"
proof(rule ccontr)
  assume "\<not> (\<not> reachable_state {0} \<A>_not_minimal_rev_pow)"
  hence "reachable_state {0} \<A>_not_minimal_rev_pow" by simp
  hence "{0} \<in> reachable_states \<A>_not_minimal_rev_pow" unfolding reachable_states_def by blast
  thus False using reachable_states_example by simp
qed

lemma unreachable_states_example2: "\<not> reachable_state {1} \<A>_not_minimal_rev_pow"
proof(rule ccontr)
  assume "\<not> (\<not> reachable_state {1} \<A>_not_minimal_rev_pow)"
  hence "reachable_state {1} \<A>_not_minimal_rev_pow" by simp
  hence "{1} \<in> reachable_states \<A>_not_minimal_rev_pow" unfolding reachable_states_def by blast
  thus False using reachable_states_example by simp
qed

lemma unreachable_states_example3: "\<not> reachable_state {0, 1} \<A>_not_minimal_rev_pow"
proof(rule ccontr)
  assume "\<not> (\<not> reachable_state {0, 1} \<A>_not_minimal_rev_pow)"
  hence "reachable_state {0, 1} \<A>_not_minimal_rev_pow" by simp
  hence "{0, 1} \<in> reachable_states \<A>_not_minimal_rev_pow" unfolding reachable_states_def by blast
  thus False using reachable_states_example by fastforce
qed

lemma unreachable_states_example4: "\<not> reachable_state {0, 2} \<A>_not_minimal_rev_pow"
proof(rule ccontr)
  assume "\<not> (\<not> reachable_state {0, 2} \<A>_not_minimal_rev_pow)"
  hence "reachable_state {0, 2} \<A>_not_minimal_rev_pow" by simp
  hence "{0, 2} \<in> reachable_states \<A>_not_minimal_rev_pow" unfolding reachable_states_def by blast
  thus False using reachable_states_example by fastforce
qed

lemma unreachable_states_example5: "\<not> reachable_state {1, 2} \<A>_not_minimal_rev_pow"
proof(rule ccontr)
  assume "\<not> (\<not> reachable_state {1, 2} \<A>_not_minimal_rev_pow)"
  hence "reachable_state {1, 2} \<A>_not_minimal_rev_pow" by simp
  hence "{1, 2} \<in> reachable_states \<A>_not_minimal_rev_pow" unfolding reachable_states_def by blast
  thus False using reachable_states_example by fastforce
qed

definition \<A>_not_minimal_rev_pow_reach :: "(nat states, nat) automaton" where "\<A>_not_minimal_rev_pow_reach = Automaton {{2}, {0, 1, 2}, {}} {0, 1} {({}, 0, {}), ({}, 1, {}), ({2}, 1, {}), ({2}, 0, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} {2} {{0, 1, 2}}"

lemma set_equi:
  assumes "A \<subseteq> B" "C \<subseteq> B" "A \<union> C = B" "A \<inter> C = {}"
  shows "B - C = A"
  using assms by auto

lemma set_diff1: "{({}, 0, {}), ({}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0::nat, 1}, 1::nat, {0::nat, 1, 2})} = {({}, 0, {}), ({}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}"
proof -
  let ?A = "{({}, 0, {}), ({}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}"
  let ?B = "{({}, 0, {}), ({}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}"
  let ?C = "{({0::nat, 1}, 1::nat, {0::nat, 1, 2})}"
  have sub_sub: "?A \<subseteq> ?B" by fast
  have sub: "?C \<subseteq> ?B" by fast
  have union: "?A \<union> ?C = ?B" by fastforce
  have "?A \<inter> ?C = {}" by fastforce
  thus ?thesis using sub_sub sub union set_equi by metis
qed

lemma set_diff2: "{({}, 0, {}), ({}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 2}, 1, {0, 1, 2})} = {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}"
proof -
  let ?A = "{({}, 0, {}), ({}, 1, {}), ({2::nat}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}"
  let ?B = "{({}, 0, {}), ({}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}"
  let ?C = "{({0, 2}, 1, {0, 1, 2})}"
  have sub_sub: "?A \<subseteq> ?B" by fast
  have sub: "?C \<subseteq> ?B" by fast
  have union: "?A \<union> ?C = ?B" by fastforce
  have "?A \<inter> ?C = {}" by fastforce
  thus ?thesis using sub_sub sub union set_equi by metis
qed

lemma trans_set_subset_pow: "\<forall> set_ex . set_ex \<subseteq> \<delta>_\<A>_not_minimal_rev_pow \<and> ({0}, 0, {}) \<notin> set_ex \<and> ({0}, 1, {0, 1, 2}) \<notin> set_ex \<and> ({1}, 0, {}) \<notin> set_ex \<and> ({1}, 1, {}) \<notin> set_ex \<and> ({0, 1}, 0, {}) \<notin> set_ex \<and> ({0, 1}, 1, {0, 1, 2}) \<notin> set_ex \<and> ({0, 2}, 0, {0, 1, 2}) \<notin> set_ex \<and> ({0, 2}, 1, {0, 1, 2}) \<notin> set_ex \<and> ({1, 2}, 0, {0, 1, 2}) \<notin> set_ex \<and> ({1, 2}, 1, {}) \<notin> set_ex \<longrightarrow> set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}"
proof -
  {
    fix set_ex assume assm: "set_ex \<subseteq> \<delta>_\<A>_not_minimal_rev_pow \<and> ({0}, 0, {}) \<notin> set_ex \<and> ({0}, 1, {0, 1, 2}) \<notin> set_ex \<and> ({1}, 0, {}) \<notin> set_ex \<and> ({1}, 1, {}) \<notin> set_ex \<and> ({0, 1}, 0, {}) \<notin> set_ex \<and> ({0, 1}, 1, {0, 1, 2}) \<notin> set_ex \<and> ({0, 2}, 0, {0, 1, 2}) \<notin> set_ex \<and> ({0, 2}, 1, {0, 1, 2}) \<notin> set_ex \<and> ({1, 2}, 0, {0, 1, 2}) \<notin> set_ex \<and> ({1, 2}, 1, {}) \<notin> set_ex"
    hence "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({0}, 0, {}), ({0}, 1, {0, 1, 2}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" unfolding \<delta>_\<A>_not_minimal_rev_pow_def by argo
    hence "(set_ex - {({0}, 0, {})}) \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({0}, 0, {}), ({0}, 1, {0, 1, 2}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0}, 0, {})})" using set_minus by metis
    hence 1: "set_ex \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({0}, 0, {}), ({0}, 1, {0, 1, 2}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0}, 0, {})})" using assm by simp
    have "{({}, 0, {}), ({}, 1, {}), ({0}, 0, {}), ({0}, 1, {0, 1, 2}), ({1}, 0, {}), ({1}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0}, 0, {})} = {({}, 0, {}), ({}, 1, {}), ({0}, 1, {0, 1, 2}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" by force
    hence "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({0}, 1, {0, 1, 2}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using 1 by argo
    hence "(set_ex - {({0}, 1, {0, 1, 2})}) \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({0}, 1, {0, 1, 2}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0}, 1, {0, 1, 2})})" using set_minus by metis
    hence 2: "set_ex \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({0}, 1, {0, 1, 2}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0}, 1, {0, 1, 2})})" using assm by auto
    have "{({}, 0, {}), ({}, 1, {}), ({0}, 1, {0, 1, 2}), ({1}, 0, {}), ({1}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0}, 1, {0, 1, 2})} = {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" by force
    hence "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using 2 by argo
    hence "(set_ex - {({1}, 0, {})}) \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({1}, 0, {})})" using set_minus by metis
    hence 3: "set_ex \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({1}, 0, {})})" using assm by auto
    have "{({}, 0, {}), ({}, 1, {}), ({1}, 0, {}), ({1}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({1}, 0, {})} = {({}, 0, {}), ({}, 1, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" by force
    hence "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using 3 by argo
    hence "(set_ex - {({1}, 1, {})}) \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({1}, 1, {})})" using set_minus by metis
    hence 4: "set_ex \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({1}, 1, {})})" using assm by auto
    have "{({}, 0, {}), ({}, 1, {}), ({1}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({1}, 1, {})} = {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" by force
    hence "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using 4 by argo
    hence "(set_ex - {({0, 1}, 0, {})}) \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 1}, 0, {})})" using set_minus by metis
    hence 5: "set_ex \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 1}, 0, {})})" using assm by auto
    have "{({}, 0, {}), ({}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 1}, 0, {})} = {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" by force
    hence "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using 5 by argo
    hence "(set_ex - {({1, 2}, 1, {})}) \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({1, 2}, 1, {})})" using set_minus by metis
    hence 6: "set_ex \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({1, 2}, 1, {})})" using assm by auto
    have "{({}, 0, {}), ({}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({1, 2}, 1, {})} = {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" by force
    hence "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using 6 by argo
    hence "(set_ex - {({0, 2}, 0, {0, 1, 2})}) \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 2}, 0, {0, 1, 2})})" using set_minus by metis
    hence 7: "set_ex \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 2}, 0, {0, 1, 2})})" using assm by auto
    have "{({}, 0, {}), ({}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 2}, 0, {0, 1, 2})} = {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" by fastforce
    hence "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using 7 by argo
    hence "(set_ex - {({1, 2}, 0, {0, 1, 2})}) \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({1, 2}, 0, {0, 1, 2})})" using set_minus by metis
    hence 8: "set_ex \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({1, 2}, 0, {0, 1, 2})})" using assm by auto
    have "{({}, 0, {}), ({}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({1, 2}, 0, {0, 1, 2})} = {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" by fastforce
    hence "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using 8 by argo
    hence "(set_ex - {({0, 1}, 1, {0, 1, 2})}) \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 1}, 1, {0, 1, 2})})" using set_minus by metis
    hence 9: "set_ex \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 1}, 1, {0, 1, 2})})" using assm by auto
    have "{({}, 0, {}), ({}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 1}, 1, {0, 1, 2})} = {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using set_diff1 by blast
    hence "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using 9 by argo
    hence "(set_ex - {({0, 2}, 1, {0, 1, 2})}) \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 2}, 1, {0, 1, 2})})" using set_minus by metis
    hence 10: "set_ex \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 2}, 1, {0, 1, 2})})" using assm by auto
    have "{({}, 0, {}), ({}, 1, {}), ({2::nat}, 0::nat, {0::nat, 1, 2}), ({2}, 1, {}), ({0, 2}, 1, {0, 1, 2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} - {({0, 2}, 1, {0, 1, 2})} = {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using set_diff2 by blast
    hence "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using 10 by argo
  }
  thus ?thesis by simp
qed

theorem equi_reach_example: "reachable_automaton \<A>_not_minimal_rev_pow = \<A>_not_minimal_rev_pow_reach"
proof -
  let ?trans_set = "{(s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow . reachable_state s1 \<A>_not_minimal_rev_pow \<and> reachable_state s2 \<A>_not_minimal_rev_pow}"
  have states: "reachable_states \<A>_not_minimal_rev_pow = {{2}, {0, 1, 2}, {}}" using reachable_states_example by blast
  have trans: "transitions \<A>_not_minimal_rev_pow = {({}, 0, {}), ({}, 1, {}), ({0}, 0, {}), ({0}, 1, {0, 1, 2}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" unfolding \<A>_not_minimal_rev_pow_def \<delta>_\<A>_not_minimal_rev_pow_def by auto
  have "?trans_set \<subseteq> transitions \<A>_not_minimal_rev_pow" by blast
  hence sub: "?trans_set \<subseteq> {({}, 0, {}), ({}, 1, {}), ({0}, 0, {}), ({0}, 1, {0, 1, 2}), ({1}, 0, {}), ({1}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1}, 0, {}), ({0, 1}, 1, {0, 1, 2}), ({0, 2}, 0, {0, 1, 2}), ({0, 2}, 1, {0, 1, 2}), ({1, 2}, 0, {0, 1, 2}), ({1, 2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using trans by argo
  have reach: "reachable_state {} \<A>_not_minimal_rev_pow \<and> reachable_state {2} \<A>_not_minimal_rev_pow \<and> reachable_state {0, 1, 2} \<A>_not_minimal_rev_pow \<and> \<not> reachable_state {0} \<A>_not_minimal_rev_pow \<and> \<not> reachable_state {1} \<A>_not_minimal_rev_pow \<and> \<not> reachable_state {0, 1} \<A>_not_minimal_rev_pow \<and> \<not> reachable_state {0, 2} \<A>_not_minimal_rev_pow \<and> \<not> reachable_state {1, 2} \<A>_not_minimal_rev_pow" using states unreachable_states_example1 unreachable_states_example2 unreachable_states_example3 unreachable_states_example4 unreachable_states_example5 unfolding reachable_states_def by blast
  hence "?trans_set \<subseteq> \<delta>_\<A>_not_minimal_rev_pow \<and> ({0}, 0, {}) \<notin> ?trans_set \<and> ({0}, 1, {0, 1, 2}) \<notin> ?trans_set \<and> ({1}, 0, {}) \<notin> ?trans_set \<and> ({1}, 1, {}) \<notin> ?trans_set \<and> ({0, 1}, 0, {}) \<notin> ?trans_set \<and> ({0, 1}, 1, {0, 1, 2}) \<notin> ?trans_set \<and> ({0, 2}, 0, {0, 1, 2}) \<notin> ?trans_set \<and> ({0, 2}, 1, {0, 1, 2}) \<notin> ?trans_set \<and> ({1, 2}, 0, {0, 1, 2}) \<notin> ?trans_set \<and> ({1, 2}, 1, {}) \<notin> ?trans_set" using sub unfolding \<delta>_\<A>_not_minimal_rev_pow_def by fast
  hence sub_sub: "?trans_set \<subseteq> {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using trans_set_subset_pow by presburger
  have "({}, 0, {}) \<in> ?trans_set \<and> ({}, 1, {}) \<in> ?trans_set \<and> ({2}, 0, {0, 1, 2}) \<in> ?trans_set \<and> ({2}, 1, {}) \<in> ?trans_set \<and> ({0, 1, 2}, 0, {0, 1, 2}) \<in> ?trans_set \<and> ({0, 1, 2}, 1, {0, 1, 2}) \<in> ?trans_set" using reach trans by simp
  hence "?trans_set = {({}, 0, {}), ({}, 1, {}), ({2}, 0, {0, 1, 2}), ({2}, 1, {}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})}" using sub_sub by fastforce
  thus ?thesis using states unfolding \<A>_not_minimal_rev_pow_def \<A>_not_minimal_rev_pow_reach_def reachable_automaton_def by force
qed

corollary \<A>_not_minimal_rev_pow_reach_well_def: "auto_well_defined \<A>_not_minimal_rev_pow_reach"
  using \<A>_not_minimal_rev_pow_well_def equi_reach_example well_def_reachable_automaton by metis

definition \<A>_not_minimal_rev_pow_reach_rev :: "(nat states, nat) nfa_multi" where "\<A>_not_minimal_rev_pow_reach_rev = NFA_multi {{2}, {0, 1, 2}, {}} {0, 1} {({}, 0, {}), ({}, 1, {}), ({}, 1, {2}), ({0, 1, 2}, 0, {2}), ({0, 1, 2}, 0, {0, 1, 2}), ({0, 1, 2}, 1, {0, 1, 2})} {{0, 1, 2}} {{2}}"

theorem equi_rev_example_pow: "\<A>_not_minimal_rev_pow_reach_rev = reversal_nfa \<A>_not_minimal_rev_pow_reach"
proof - 
  have states: "states_multi \<A>_not_minimal_rev_pow_reach_rev = states_multi (reversal_nfa \<A>_not_minimal_rev_pow_reach)" unfolding \<A>_not_minimal_rev_pow_reach_rev_def \<A>_not_minimal_rev_pow_reach_def reversal_nfa_def by force
  have acc: "accepting_states_multi \<A>_not_minimal_rev_pow_reach_rev = accepting_states_multi (reversal_nfa \<A>_not_minimal_rev_pow_reach)" unfolding \<A>_not_minimal_rev_pow_reach_rev_def \<A>_not_minimal_rev_pow_reach_def reversal_nfa_def by force
  have init: "initial_states_multi \<A>_not_minimal_rev_pow_reach_rev = initial_states_multi (reversal_nfa \<A>_not_minimal_rev_pow_reach)" unfolding \<A>_not_minimal_rev_pow_reach_rev_def \<A>_not_minimal_rev_pow_reach_def reversal_nfa_def by force
  have alpha: "alphabet_multi \<A>_not_minimal_rev_pow_reach_rev = alphabet_multi (reversal_nfa \<A>_not_minimal_rev_pow_reach)" unfolding \<A>_not_minimal_rev_pow_reach_rev_def \<A>_not_minimal_rev_pow_reach_def reversal_nfa_def by force
  have left: "transitions_multi \<A>_not_minimal_rev_pow_reach_rev \<subseteq> transitions_multi (reversal_nfa \<A>_not_minimal_rev_pow_reach)" unfolding \<A>_not_minimal_rev_pow_reach_rev_def \<A>_not_minimal_rev_pow_reach_def reversal_nfa_def by simp
  have "transitions_multi (reversal_nfa \<A>_not_minimal_rev_pow_reach) \<subseteq> transitions_multi \<A>_not_minimal_rev_pow_reach_rev" unfolding \<A>_not_minimal_rev_pow_reach_rev_def \<A>_not_minimal_rev_pow_reach_def reversal_nfa_def by auto
  hence "transitions_multi \<A>_not_minimal_rev_pow_reach_rev = transitions_multi (reversal_nfa \<A>_not_minimal_rev_pow_reach)" using left by blast
  thus ?thesis using states alpha init acc by (simp add: nfa_multi.expand)
qed

corollary \<A>_not_minimal_rev_pow_reach_rev_well_def: "auto_well_defined_multi \<A>_not_minimal_rev_pow_reach_rev"
  using \<A>_not_minimal_rev_pow_reach_well_def equi_rev_example_pow reversal_preserves_well_defined by metis

definition \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow :: "((nat states) states, nat) transitions" where "\<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow = {({}, 0, {}), ({}, 1, {}), ({{2}}, 0, {}), ({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}"

definition \<A>_not_minimal_rev_pow_reach_rev_pow :: "((nat states) states, nat) automaton" where "\<A>_not_minimal_rev_pow_reach_rev_pow = Automaton {{}, {{}}, {{2}}, {{0, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}} {0, 1} \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow {{0, 1, 2}} {{{2}}, {{}, {2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}}"

lemma powerset_transitions_multi_example_pow: "\<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow \<subseteq> powerset_transitions_multi \<A>_not_minimal_rev_pow_reach_rev"
  unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def powerset_transitions_multi_def by auto

lemma card_pow_8_pow: "card (Pow {{2::nat}, {0, 1, 2}, {}}) = 8"
proof -
  have "finite {{2::nat}, {0, 1, 2}, {}} \<and> card {{2::nat}, {0, 1, 2}, {}} = 3" by simp
  hence "card (Pow {{2::nat}, {0, 1, 2}, {}}) = 2^3" using card_Pow by metis
  thus ?thesis by auto
qed

lemma card_helper0_pow: "card {{}, {{}}, {{2::nat}}, {{0, 1, 2}}} = 4"
  by simp

lemma card_helper1_pow: "card {{{}, {2::nat}}, {{}, {0::nat, 1, 2}}} = 2"
proof -
  have "{2::nat} \<noteq> {0::nat, 1, 2}" by simp
  hence "{{}, {2::nat}} \<noteq> {{}, {0::nat, 1, 2}}" by blast
  thus ?thesis by simp
qed

lemma card_helper2_pow: "card {{{2::nat}, {0, 1, 2}}, {{}, {2::nat}, {0, 1, 2}}} = 2"
proof -
  have "{{2::nat}, {0, 1, 2}} \<noteq> {{}, {2::nat}, {0, 1, 2}}" by blast
  thus ?thesis by simp
qed

lemma card_helper3_pow: "card {{{}, {2::nat}}, {{}, {0::nat, 1, 2}}, {{2::nat}, {0, 1, 2}}, {{}, {2::nat}, {0, 1, 2}}} = 4"
proof -
  have finite: "finite {{{}, {2::nat}}, {{}, {0::nat, 1, 2}}} \<and> finite {{{2::nat}, {0, 1, 2}}, {{}, {2::nat}, {0, 1, 2}}}" by simp
  have inter: "{{{}, {2::nat}}, {{}, {0::nat, 1, 2}}} \<inter> {{{2::nat}, {0, 1, 2}}, {{}, {2::nat}, {0, 1, 2}}} = {}" by (simp add: insert_eq_iff)
  have "{{{}, {2::nat}}, {{}, {0::nat, 1, 2}}, {{2::nat}, {0, 1, 2}}, {{}, {2::nat}, {0, 1, 2}}} = {{{}, {2::nat}}, {{}, {0::nat, 1, 2}}} \<union> {{{2::nat}, {0, 1, 2}}, {{}, {2::nat}, {0, 1, 2}}}" by auto
  hence "card {{{}, {2::nat}}, {{}, {0::nat, 1, 2}}, {{2::nat}, {0, 1, 2}}, {{}, {2::nat}, {0, 1, 2}}} = card {{{}, {2::nat}}, {{}, {0::nat, 1, 2}}} + card {{{2::nat}, {0, 1, 2}}, {{}, {2::nat}, {0, 1, 2}}}" using finite inter card_Un_disjoint by metis 
  thus ?thesis using card_helper1_pow card_helper2_pow by presburger
qed

lemma card_states_example_8_pow: "card {{}, {{}}, {{2}}, {{0::nat, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}} = 8"
proof - 
  have finite: "finite {{}, {{}}, {{2::nat}}, {{0, 1, 2}}} \<and> finite {{{}, {2::nat}}, {{}, {0::nat, 1, 2}}, {{2::nat}, {0, 1, 2}}, {{}, {2::nat}, {0, 1, 2}}}" by simp
  have inter: "{{}, {{}}, {{2::nat}}, {{0, 1, 2}}} \<inter> {{{}, {2::nat}}, {{}, {0::nat, 1, 2}}, {{2::nat}, {0, 1, 2}}, {{}, {2::nat}, {0, 1, 2}}} = {}" by force
  have "{{}, {{}}, {{2}}, {{0, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}} = {{}, {{}}, {{2::nat}}, {{0, 1, 2}}} \<union> {{{}, {2::nat}}, {{}, {0::nat, 1, 2}}, {{2::nat}, {0, 1, 2}}, {{}, {2::nat}, {0, 1, 2}}}" by fast
  hence "card {{}, {{}}, {{2}}, {{0::nat, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}} = card {{}, {{}}, {{2::nat}}, {{0, 1, 2}}} + card {{{}, {2::nat}}, {{}, {0::nat, 1, 2}}, {{2::nat}, {0, 1, 2}}, {{}, {2::nat}, {0, 1, 2}}}" using finite inter card_Un_disjoint by metis 
  thus ?thesis using card_helper0_pow card_helper3_pow by presburger
qed  

lemma Pow_set_pow: "Pow {{2::nat}, {0, 1, 2}, {}} = {{}, {{}}, {{2}}, {{0::nat, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}}"
proof -
  have sub: "{{}, {{}}, {{2}}, {{0::nat, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}} \<subseteq> Pow {{2::nat}, {0, 1, 2}, {}}" by simp
  have card_8: "card {{}, {{}}, {{2}}, {{0::nat, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}} = 8 \<and> finite {{}, {{}}, {{2}}, {{0::nat, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}}" using card_states_example_8_pow by blast
  have "card (Pow {{2::nat}, {0, 1, 2}, {}}) = 8 \<and> finite (Pow {{2::nat}, {0, 1, 2}, {}})" using card_pow_8_pow by blast
  thus ?thesis using sub card_8 card_subset_eq by metis
qed

lemma powerset_transitions_multi_example_exhaustive_pow:
  assumes "(S1, a, S2) \<in> powerset_transitions_multi \<A>_not_minimal_rev_pow_reach_rev"
  shows "(S1, a, S2) \<in> \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow"
proof -
  have S1: "S1 \<in> Pow (states_multi \<A>_not_minimal_rev_pow_reach_rev)" using assms unfolding powerset_transitions_multi_def by auto
  have "states_multi \<A>_not_minimal_rev_pow_reach_rev = {{2}, {0, 1, 2}, {}}" unfolding \<A>_not_minimal_rev_pow_reach_rev_def by auto
  hence "Pow (states_multi \<A>_not_minimal_rev_pow_reach_rev) = {{}, {{}}, {{2}}, {{0::nat, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}}" using Pow_set_pow by metis
  hence cases_S1: "S1 = {} \<or> S1 = {{}} \<or> S1 = {{2}} \<or> S1 = {{0, 1, 2}} \<or> S1 = {{}, {2}} \<or> S1 = {{}, {0, 1, 2}} \<or> S1 = {{2}, {0, 1, 2}} \<or> S1 = {{}, {2}, {0, 1, 2}}" using S1 by auto
  have a_cases: "a = 0 \<or> a = 1" using assms unfolding powerset_transitions_multi_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  have S2: "S2 = {s2 . \<exists> s1 \<in> S1 . (s1, a, s2) \<in> transitions_multi \<A>_not_minimal_rev_pow_reach_rev}" using assms unfolding powerset_transitions_multi_def by auto
  consider (t1) "S1 = {} \<and> a = 0" | (t2) "S1 = {} \<and> a = 1" | (t3) "S1 = {{}} \<and> a = 0" | (t4) "S1 = {{}} \<and> a = 1" | (t5) "S1 = {{2}} \<and> a = 0" | (t6) "S1 = {{2}} \<and> a = 1" | (t7) "S1 = {{}, {2}} \<and> a = 0" | (t8) "S1 = {{}, {2}} \<and> a = 1" | (t9) "S1 = {{}, {0, 1, 2}} \<and> a = 0" | (t10) "S1 = {{}, {0, 1, 2}} \<and> a = 1" | (t11) "S1 = {{0, 1, 2}} \<and> a = 0" | (t12) "S1 = {{0, 1, 2}} \<and> a = 1" | (t13) "S1 = {{2}, {0, 1, 2}} \<and> a = 0" | (t14) "S1 = {{2}, {0, 1, 2}} \<and> a = 1" | (t15) "S1 = {{}, {2}, {0, 1, 2}} \<and> a = 0" | (t16) "S1 = {{}, {2}, {0, 1, 2}} \<and> a = 1" using cases_S1 a_cases by argo
  thus ?thesis
  proof cases
    case t1 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def by auto
  next
    case t2 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def by auto
  next
    case t3 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t4 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t5 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t6 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t7 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t8 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t9 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t10 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t11 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t12 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t13 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t14 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t15 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  next
    case t16 thus ?thesis using S2 unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def by auto
  qed
qed

lemma powerset_automaton_transition_multi_equivalence_pow: "transitions \<A>_not_minimal_rev_pow_reach_rev_pow = transitions (powerset_automaton_multi \<A>_not_minimal_rev_pow_reach_rev)"
  using powerset_transitions_multi_example_exhaustive_pow powerset_transitions_multi_example_pow unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def powerset_automaton_multi_def by auto

text \<open>Proof of example powerset automaton equivalence\<close>
theorem powerset_multi_examples_equivalence_pow: "\<A>_not_minimal_rev_pow_reach_rev_pow = powerset_automaton_multi \<A>_not_minimal_rev_pow_reach_rev"
proof -
  have "states_multi \<A>_not_minimal_rev_pow_reach_rev = {{2}, {0, 1, 2}, {}}" unfolding \<A>_not_minimal_rev_pow_reach_rev_def by auto
  hence pow_states: "Pow (states_multi \<A>_not_minimal_rev_pow_reach_rev) = {{}, {{}}, {{2}}, {{0, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}}" using Pow_set_pow by argo
  hence states: "states \<A>_not_minimal_rev_pow_reach_rev_pow = states (powerset_automaton_multi \<A>_not_minimal_rev_pow_reach_rev)" unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def powerset_automaton_multi_def by auto
  have alphabet: "alphabet \<A>_not_minimal_rev_pow_reach_rev_pow = alphabet (powerset_automaton_multi \<A>_not_minimal_rev_pow_reach_rev)" unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def powerset_automaton_multi_def \<A>_not_minimal_rev_pow_reach_rev_def by force
  have trans: "transitions \<A>_not_minimal_rev_pow_reach_rev_pow = transitions (powerset_automaton_multi \<A>_not_minimal_rev_pow_reach_rev)" using powerset_automaton_transition_multi_equivalence_pow by auto
  have init: "initial_state \<A>_not_minimal_rev_pow_reach_rev_pow = initial_state (powerset_automaton_multi \<A>_not_minimal_rev_pow_reach_rev)" unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def powerset_automaton_multi_def \<A>_not_minimal_rev_pow_reach_rev_def by force
  have sub: "accepting_states \<A>_not_minimal_rev_pow_reach_rev_pow \<subseteq> accepting_states (powerset_automaton_multi \<A>_not_minimal_rev_pow_reach_rev)" unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_def powerset_automaton_multi_def by fastforce
  have "accepting_states_multi \<A>_not_minimal_rev_pow_reach_rev = {{2}} \<and> Pow (states_multi \<A>_not_minimal_rev_pow_reach_rev) = {{}, {{}}, {{2}}, {{0, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}}" using pow_states unfolding \<A>_not_minimal_rev_pow_reach_rev_def by simp
  hence equi: "accepting_states (powerset_automaton_multi \<A>_not_minimal_rev_pow_reach_rev) = {S \<in> {{}, {{}}, {{2}}, {{0::nat, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}} . S \<inter> {{2::nat}} \<noteq> {}}" unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def powerset_automaton_multi_def by force
  hence "{S \<in> {{}, {{}}, {{2}}, {{0::nat, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}} . S \<inter> {{2::nat}} \<noteq> {}} \<subseteq> {{{2::nat}}, {{}, {2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}}" by fast
  hence "accepting_states (powerset_automaton_multi \<A>_not_minimal_rev_pow_reach_rev) \<subseteq> {{{2::nat}}, {{}, {2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}}" using equi by presburger
  hence "accepting_states (powerset_automaton_multi \<A>_not_minimal_rev_pow_reach_rev) \<subseteq> accepting_states \<A>_not_minimal_rev_pow_reach_rev_pow" unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def by simp
  hence acc: "accepting_states \<A>_not_minimal_rev_pow_reach_rev_pow = accepting_states (powerset_automaton_multi \<A>_not_minimal_rev_pow_reach_rev)" using sub by blast 
  thus ?thesis using states alphabet trans init acc by (simp add: automaton.expand)
qed

corollary \<A>_not_minimal_rev_pow_reach_rev_pow_well_def: "auto_well_defined \<A>_not_minimal_rev_pow_reach_rev_pow"
  using \<A>_not_minimal_rev_pow_reach_rev_well_def powerset_multi_examples_equivalence_pow well_def_powerset_automaton_multi by metis

lemma card_states_example_pow: "card (states \<A>_not_minimal_rev_pow_reach_rev_pow) = 8"
  using card_states_example_8_pow unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def by force

lemma neighbourhood_equi: "{s2 . \<exists> s1 a. s1 \<in> {{{2::nat}, {0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {{{2}, {0, 1, 2}}, {{0, 1, 2}}}"
proof -
  have "transitions \<A>_not_minimal_rev_pow_reach_rev_pow = \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow" unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def by simp
  hence trans: "transitions \<A>_not_minimal_rev_pow_reach_rev_pow = {({}, 0, {}), ({}, 1, {}), ({{2}}, 0, {}), ({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def by blast
  have states: "states \<A>_not_minimal_rev_pow_reach_rev_pow = {{}, {{}}, {{2}}, {{0, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}}" unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def by simp
  have "{s2 . \<exists> s1 a. s1 \<in> {{{2::nat}, {0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {s2 . \<exists> s1 a. s1 = {{2::nat}, {0, 1, 2}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow}" by simp
  hence equi: "{s2 . \<exists> s1 a. s1 \<in> {{{2::nat}, {0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {s2 . \<exists> a. ({{2::nat}, {0, 1, 2}}, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow}" by presburger
  have "\<forall> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow . a = 0 \<or> a = 1" using trans by force
  hence "{s2 . \<exists> s1 a. s1 \<in> {{{2::nat}, {0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {s2 . ({{2::nat}, {0, 1, 2}}, 0, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow \<or> ({{2::nat}, {0, 1, 2}}, 1, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow}" using equi by auto
  hence "{s2 . \<exists> s1 a. s1 \<in> {{{2::nat}, {0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {s2 . ({{2::nat}, {0, 1, 2}}, 0, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} \<union> {s2 . ({{2::nat}, {0, 1, 2}}, 1, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow}" by force
  hence equi2: "{s2 . \<exists> s1 a. s1 \<in> {{{2::nat}, {0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . ({{2::nat}, {0, 1, 2}}, 0, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} \<union> {s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . ({{2::nat}, {0, 1, 2}}, 1, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow}" using \<A>_not_minimal_rev_pow_reach_rev_pow_well_def well_def_trans_components by force  
  {
    fix S2 assume "S2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow"
    then consider (t1) "S2 = {}" | (t2) "S2 = {{}}" | (t3) "S2 = {{2}}" | (t4) "S2 = {{0, 1, 2}}" | (t5) "S2 = {{}, {2}}" | (t6) "S2 = {{0, 1, 2}, {}}" | (t7) "S2 = {{2}, {0, 1, 2}}" | (t8) "S2 = {{}, {2}, {0, 1, 2}}" using states by force
    hence "({{2::nat}, {0, 1, 2}}, 0, S2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow \<longrightarrow> S2 = {{2}, {0, 1, 2}}"
    proof cases
      case t1 thus ?thesis using trans by simp
    next
      case t2 thus ?thesis using trans apply simp by blast
    next
      case t3 thus ?thesis using trans by simp
    next
      case t4 thus ?thesis using trans by simp
    next
      case t5 thus ?thesis using trans by simp
    next
      case t6 thus ?thesis using trans by simp
    next
      case t7 thus ?thesis using trans by simp
    next
      case t8 thus ?thesis using trans by simp
    qed
  }
  hence left: "\<forall> s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . ({{2::nat}, {0, 1, 2}}, 0, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow \<longrightarrow> s2 = {{2}, {0, 1, 2}}" by simp
  have "\<forall> s2 . s2 = {{2}, {0, 1, 2}} \<longrightarrow> s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow \<and> ({{2::nat}, {0, 1, 2}}, 0, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow" using trans states by simp
  hence "\<forall> s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . ({{2::nat}, {0, 1, 2}}, 0, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow \<longleftrightarrow> s2 = {{2}, {0, 1, 2}}" using left by fastforce
  hence equi_left: "{s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . ({{2::nat}, {0, 1, 2}}, 0, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . s2 = {{2}, {0, 1, 2}}}" by fastforce
  have "{s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . s2 = {{2}, {0, 1, 2}}} = {{{2}, {0, 1, 2}}}" using states by auto
  hence leftleft: "{s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . ({{2::nat}, {0, 1, 2}}, 0, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {{{2}, {0, 1, 2}}}" using equi_left by presburger
  {
    fix S2 assume "S2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow"
    then consider (t1) "S2 = {}" | (t2) "S2 = {{}}" | (t3) "S2 = {{2}}" | (t4) "S2 = {{0, 1, 2}}" | (t5) "S2 = {{}, {2::nat}}" | (t6) "S2 = {{}, {0::nat, 1, 2}}" | (t7) "S2 = {{2}, {0, 1, 2}}" | (t8) "S2 = {{}, {2}, {0, 1, 2}}" using states by force
    hence "({{2::nat}, {0, 1, 2}}, 1, S2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow \<longrightarrow> S2 = {{0::nat, 1, 2}}"
    proof cases
      case t1 thus ?thesis using trans by simp
    next
      case t2 thus ?thesis using trans by simp
    next
      case t3 thus ?thesis using trans by simp
    next
      case t4 thus ?thesis using trans by simp
    next
      case t5 
      hence "({{2::nat}, {0, 1, 2}}, 1, S2) \<notin> transitions \<A>_not_minimal_rev_pow_reach_rev_pow" using trans by (simp add: doubleton_eq_iff)
      thus ?thesis by auto
    next
      case t6
      hence "({{2::nat}, {0, 1, 2}}, 1, S2) \<notin> transitions \<A>_not_minimal_rev_pow_reach_rev_pow" using trans by (simp add: doubleton_eq_iff)
      thus ?thesis by auto
    next
      case t7 thus ?thesis using trans apply simp by blast
    next
      case t8 thus ?thesis using trans apply simp by blast
    qed
  }
  hence right: "\<forall> s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . ({{2::nat}, {0, 1, 2}}, 1, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow \<longrightarrow> s2 = {{0, 1, 2}}" by simp
  have "\<forall> s2 . s2 = {{0, 1, 2}} \<longrightarrow> s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow \<and> ({{2::nat}, {0, 1, 2}}, 1, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow" using trans states by simp
  hence "\<forall> s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . ({{2::nat}, {0, 1, 2}}, 1, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow \<longleftrightarrow> s2 = {{0, 1, 2}}" using right by fastforce
  hence equi_right: "{s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . ({{2::nat}, {0, 1, 2}}, 1, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . s2 = {{0, 1, 2}}}" by fastforce
  have "{s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . s2 = {{0, 1, 2}}} = {{{0, 1, 2}}}" using states by auto
  hence rightright: "{s2 \<in> states \<A>_not_minimal_rev_pow_reach_rev_pow . ({{2::nat}, {0, 1, 2}}, 1, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {{{0, 1, 2}}}" using equi_right by presburger
  thus ?thesis using equi2 leftleft right right by auto
qed

proposition r_s_i_example_pow: "reachable_states_iterativ \<A>_not_minimal_rev_pow_reach_rev_pow = {{{0, 1, 2}}, {{2}, {0, 1, 2}}}"
proof - 
  have "states \<A>_not_minimal_rev_pow_reach_rev_pow = {{}, {{}}, {{2}}, {{0, 1, 2}}, {{}, {2}}, {{}, {0, 1, 2}}, {{2}, {0, 1, 2}}, {{}, {2}, {0, 1, 2}}}" unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def by simp
  have "card (states \<A>_not_minimal_rev_pow_reach_rev_pow) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) \<and> initial_state \<A>_not_minimal_rev_pow_reach_rev_pow = {{0, 1, 2}}" using card_states_example_pow unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def by auto 
  hence "reachable_states_iter (card (states \<A>_not_minimal_rev_pow_reach_rev_pow) - 1) \<A>_not_minimal_rev_pow_reach_rev_pow {initial_state \<A>_not_minimal_rev_pow_reach_rev_pow} = reachable_states_iter (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) \<A>_not_minimal_rev_pow_reach_rev_pow {{{0, 1, 2}}}" by auto
  hence r1: "reachable_states_iter (card (states \<A>_not_minimal_rev_pow_reach_rev_pow) - 1) \<A>_not_minimal_rev_pow_reach_rev_pow {initial_state \<A>_not_minimal_rev_pow_reach_rev_pow} = {{{0, 1, 2}}} \<union> reachable_states_iter (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) \<A>_not_minimal_rev_pow_reach_rev_pow {s2 . \<exists> s1 a. s1 \<in> {{{0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow}" by simp
  have neigh: "{s2 . \<exists> s1 a. s1 \<in> {{{0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {{{0, 1, 2}}, {{2}, {0, 1, 2}}}" unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def by force
  hence "reachable_states_iter (card (states \<A>_not_minimal_rev_pow_reach_rev_pow) - 1) \<A>_not_minimal_rev_pow_reach_rev_pow {initial_state \<A>_not_minimal_rev_pow_reach_rev_pow} = {{{0, 1, 2}}} \<union> reachable_states_iter (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) \<A>_not_minimal_rev_pow_reach_rev_pow {{{0, 1, 2}}, {{2}, {0, 1, 2}}}" using r1 by argo
  hence r2: "reachable_states_iter (card (states \<A>_not_minimal_rev_pow_reach_rev_pow) - 1) \<A>_not_minimal_rev_pow_reach_rev_pow {initial_state \<A>_not_minimal_rev_pow_reach_rev_pow} = {{{0, 1, 2}}, {{2}, {0, 1, 2}}} \<union> reachable_states_iter (Suc (Suc (Suc (Suc (Suc 0))))) \<A>_not_minimal_rev_pow_reach_rev_pow {s2 . \<exists> s1 a. s1 \<in> {{{0, 1, 2}}, {{2}, {0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow}" by force
  have equi: "{s2 . \<exists> s1 a. s1 \<in> {{{0, 1, 2}}, {{2}, {0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {s2 . \<exists> s1 a. s1 \<in> {{{0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} \<union> {s2 . \<exists> s1 a. s1 \<in> {{{2}, {0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow}" by auto
  have "{s2 . \<exists> s1 a. s1 \<in> {{{0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {{{0, 1, 2}}, {{2}, {0, 1, 2}}} \<and> {s2 . \<exists> s1 a. s1 \<in> {{{2}, {0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {{{2}, {0, 1, 2}}, {{0, 1, 2}}}" using neigh neighbourhood_equi by blast
  hence "{s2 . \<exists> s1 a. s1 \<in> {{{0, 1, 2}}, {{2}, {0, 1, 2}}} \<and> (s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow} = {{{0, 1, 2}}, {{2}, {0, 1, 2}}}" using equi by auto
  hence "reachable_states_iter (card (states \<A>_not_minimal_rev_pow_reach_rev_pow) - 1) \<A>_not_minimal_rev_pow_reach_rev_pow {initial_state \<A>_not_minimal_rev_pow_reach_rev_pow} = {{{0, 1, 2}}, {{2}, {0, 1, 2}}}" using r2 by force
  thus ?thesis unfolding reachable_states_iterativ_def by force
qed

corollary reachable_states_example_pow: "reachable_states \<A>_not_minimal_rev_pow_reach_rev_pow = {{{0, 1, 2}}, {{2}, {0, 1, 2}}}"
  using equivalence_of_reachable_states \<A>_not_minimal_rev_pow_reach_rev_pow_well_def r_s_i_example_pow by metis

lemma unreachable_states_example1_pow: "\<not> reachable_state {} \<A>_not_minimal_rev_pow_reach_rev_pow"
proof(rule ccontr)
  assume "\<not> (\<not> reachable_state {} \<A>_not_minimal_rev_pow_reach_rev_pow)"
  hence "reachable_state {} \<A>_not_minimal_rev_pow_reach_rev_pow" by simp
  hence "{} \<in> reachable_states \<A>_not_minimal_rev_pow_reach_rev_pow" unfolding reachable_states_def by blast
  thus False using reachable_states_example_pow by simp
qed

lemma unreachable_states_example2_pow: "\<not> reachable_state {{}} \<A>_not_minimal_rev_pow_reach_rev_pow"
proof(rule ccontr)
  assume "\<not> (\<not> reachable_state {{}} \<A>_not_minimal_rev_pow_reach_rev_pow)"
  hence "reachable_state {{}} \<A>_not_minimal_rev_pow_reach_rev_pow" by simp
  hence "{{}} \<in> reachable_states \<A>_not_minimal_rev_pow_reach_rev_pow" unfolding reachable_states_def by blast
  thus False using reachable_states_example_pow by simp
qed

lemma unreachable_states_example3_pow: "\<not> reachable_state {{2}} \<A>_not_minimal_rev_pow_reach_rev_pow"
proof(rule ccontr)
  assume "\<not> (\<not> reachable_state {{2}} \<A>_not_minimal_rev_pow_reach_rev_pow)"
  hence "reachable_state {{2}} \<A>_not_minimal_rev_pow_reach_rev_pow" by simp
  hence "{{2}} \<in> reachable_states \<A>_not_minimal_rev_pow_reach_rev_pow" unfolding reachable_states_def by blast
  thus False using reachable_states_example_pow by fastforce
qed

lemma unreachable_states_example4_pow: "\<not> reachable_state {{}, {2}} \<A>_not_minimal_rev_pow_reach_rev_pow"
proof(rule ccontr)
  assume "\<not> (\<not> reachable_state {{}, {2}} \<A>_not_minimal_rev_pow_reach_rev_pow)"
  hence "reachable_state {{}, {2}} \<A>_not_minimal_rev_pow_reach_rev_pow" by simp
  hence "{{}, {2}} \<in> reachable_states \<A>_not_minimal_rev_pow_reach_rev_pow" unfolding reachable_states_def by blast
  thus False using reachable_states_example_pow by auto
qed

lemma unreachable_states_example5_pow: "\<not> reachable_state {{}, {0, 1, 2}} \<A>_not_minimal_rev_pow_reach_rev_pow"
proof(rule ccontr)
  assume "\<not> (\<not> reachable_state {{}, {0, 1, 2}} \<A>_not_minimal_rev_pow_reach_rev_pow)"
  hence "reachable_state {{}, {0, 1, 2}} \<A>_not_minimal_rev_pow_reach_rev_pow" by simp
  hence "{{}, {0, 1, 2}} \<in> reachable_states \<A>_not_minimal_rev_pow_reach_rev_pow" unfolding reachable_states_def by blast
  thus False using reachable_states_example_pow by auto
qed

lemma unreachable_states_example6_pow: "\<not> reachable_state {{}, {2}, {0, 1, 2}} \<A>_not_minimal_rev_pow_reach_rev_pow"
proof(rule ccontr)
  assume "\<not> (\<not> reachable_state {{}, {2}, {0, 1, 2}} \<A>_not_minimal_rev_pow_reach_rev_pow)"
  hence "reachable_state {{}, {2}, {0, 1, 2}} \<A>_not_minimal_rev_pow_reach_rev_pow" by simp
  hence "{{}, {2}, {0, 1, 2}} \<in> reachable_states \<A>_not_minimal_rev_pow_reach_rev_pow" unfolding reachable_states_def by blast
  thus False using reachable_states_example_pow by auto
qed

definition \<A>_not_minimal_rev_pow_reach_rev_pow_reach :: "((nat states) states, nat) automaton" where "\<A>_not_minimal_rev_pow_reach_rev_pow_reach = Automaton {{{0, 1, 2}}, {{2}, {0, 1, 2}}} {0, 1} {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}})} {{0, 1, 2}} {{{2}, {0, 1, 2}}}"

lemma set_diff1_pow: "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2::nat}}, 1::nat, {{}, {2::nat}})} = {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}"
proof -
  let ?A = "{({{0::nat, 1, 2}}, 0::nat, {{2::nat}, {0::nat, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}"
  let ?B = "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}"
  let ?C = "{({{}, {2::nat}}, 1::nat, {{}, {2::nat}})}"
  have sub_sub: "?A \<subseteq> ?B" by fast
  have sub: "?C \<subseteq> ?B" by fast
  have union: "?A \<union> ?C = ?B" by fastforce
  have "?A \<inter> ?C = {}" by (simp add: insert_eq_iff)
  thus ?thesis using sub_sub sub union set_equi by metis
qed

lemma set_diff2_pow: "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {0::nat, 1, 2}}, 0::nat, {{}, {2::nat}, {0::nat, 1, 2}})} = {({{0::nat, 1, 2}}, 0::nat, {{2::nat}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}"
proof -
  let ?A = "{({{0::nat, 1, 2}}, 0::nat, {{2::nat}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}"
  let ?B = "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}"
  let ?C = "{({{}, {0::nat, 1, 2}}, 0::nat, {{}, {2::nat}, {0::nat, 1, 2}})}"
  have sub_sub: "?A \<subseteq> ?B" by fast
  have sub: "?C \<subseteq> ?B" by fast
  have union: "?A \<union> ?C = ?B" by fastforce
  have "?A \<inter> ?C = {}" by (simp add: insert_eq_iff)
  thus ?thesis using sub_sub sub union set_equi by metis
qed

lemma set_diff3_pow: "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {0::nat, 1, 2}}, 1::nat, {{}, {2::nat}, {0::nat, 1, 2}})} = {({{0::nat, 1, 2}}, 0::nat, {{2::nat}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}"
proof -
  let ?A = "{({{0::nat, 1, 2}}, 0::nat, {{2::nat}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}"
  let ?B = "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}"
  let ?C = "{({{}, {0::nat, 1, 2}}, 1::nat, {{}, {2::nat}, {0::nat, 1, 2}})}"
  have sub_sub: "?A \<subseteq> ?B" by fast
  have sub: "?C \<subseteq> ?B" by fast
  have union: "?A \<union> ?C = ?B" by fastforce
  have "?A \<inter> ?C = {}" by (simp add: insert_eq_iff)
  thus ?thesis using sub_sub sub union set_equi by metis
qed

lemma trans_set_subset_pow_pow: "\<forall> set_ex . set_ex \<subseteq> \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow \<and> ({}, 0, {}) \<notin> set_ex \<and> ({}, 1, {}) \<notin> set_ex \<and> ({{2}}, 0, {}) \<notin> set_ex \<and> ({{2}}, 1, {}) \<notin> set_ex \<and> ({{}}, 0, {{}}) \<notin> set_ex \<and> ({{}}, 1, {{}, {2}}) \<notin> set_ex \<and> ({{}, {2}}, 0, {{}}) \<notin> set_ex \<and> ({{}, {2}}, 1, {{}, {2}}) \<notin> set_ex \<and> ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}) \<notin> set_ex \<and> ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}) \<notin> set_ex \<and> ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}) \<notin> set_ex \<and> ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}) \<notin> set_ex \<longrightarrow> set_ex \<subseteq> {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}})}"
proof -
  {
    fix set_ex assume assm: "set_ex \<subseteq> \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow \<and> ({}, 0, {}) \<notin> set_ex \<and> ({}, 1, {}) \<notin> set_ex \<and> ({{2}}, 0, {}) \<notin> set_ex \<and> ({{2}}, 1, {}) \<notin> set_ex \<and> ({{}}, 0, {{}}) \<notin> set_ex \<and> ({{}}, 1, {{}, {2}}) \<notin> set_ex \<and> ({{}, {2}}, 0, {{}}) \<notin> set_ex \<and> ({{}, {2}}, 1, {{}, {2}}) \<notin> set_ex \<and> ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}) \<notin> set_ex \<and> ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}) \<notin> set_ex \<and> ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}) \<notin> set_ex \<and> ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}) \<notin> set_ex"
    hence "set_ex \<subseteq> {({}, 0, {}), ({}, 1, {}), ({{2}}, 0, {}), ({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def by argo
    hence "(set_ex - {({}, 0, {})}) \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({{2}}, 0, {}), ({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({}, 0, {})})" using set_minus by metis
    hence 1: "set_ex \<subseteq> ({({}, 0, {}), ({}, 1, {}), ({{2}}, 0, {}), ({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({}, 0, {})})" using assm by auto
    have "{({}, 0, {}), ({}, 1, {}), ({{2}}, 0, {}), ({{2}}, 1, {}), ({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({}, 0, {})} = {({}, 1, {}), ({{2}}, 0, {}), ({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" by force
    hence "set_ex \<subseteq> {({}, 1, {}), ({{2}}, 0, {}), ({{2}}, 1, {}), ({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using 1 by simp
    hence "(set_ex - {({}, 1, {})}) \<subseteq> ({({}, 1, {}), ({{2}}, 0, {}), ({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({}, 1, {})})" using set_minus by metis
    hence 2: "set_ex \<subseteq> ({({{2}}, 0, {}), ({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({}, 0, {})})" using assm by auto
    have "{({}, 1, {}), ({{2}}, 0, {}), ({{2}}, 1, {}), ({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({}, 1, {})} = {({{2}}, 0, {}), ({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" by force
    hence "set_ex \<subseteq> {({{2}}, 0, {}), ({{2}}, 1, {}), ({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using 2 by simp
    hence "(set_ex - {({{2}}, 0, {})}) \<subseteq> ({({{2}}, 0, {}), ({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{2}}, 0, {})})" using set_minus by metis
    hence 3: "set_ex \<subseteq> ({({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{2}}, 0, {})})" using assm by auto
    have "{({{2}}, 0, {}), ({{2}}, 1, {}), ({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{2}}, 0, {})} = {({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" by force
    hence "set_ex \<subseteq> {({{2}}, 1, {}), ({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using 3 by simp
    hence "(set_ex - {({{2}}, 1, {})}) \<subseteq> ({({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{2}}, 1, {})})" using set_minus by metis
    hence 4: "set_ex \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{2}}, 0, {})})" using assm by auto
    have "{({{2}}, 1, {}), ({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{2}}, 1, {})} = {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" by force
    hence "set_ex \<subseteq> {({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using 4 by simp
    hence "(set_ex - {({{}}, 0, {{}})}) \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}}, 0, {{}})})" using set_minus by metis
    hence 5: "set_ex \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}}, 0, {{}})})" using assm by auto
    have "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}}, 0, {{}})} = {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" by force
    hence "set_ex \<subseteq> {({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using 5 by metis
    hence "(set_ex - {({{}}, 1, {{}, {2}})}) \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}}, 1, {{}, {2}})})" using set_minus by metis
    hence 6: "set_ex \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}}, 1, {{}, {2}})})" using assm by auto
    have "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}}, 1, {{}, {2}})} = {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" by force
    hence "set_ex \<subseteq> {({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using 6 by metis
    hence "(set_ex - {({{}, {2}}, 0, {{}})}) \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2}}, 0, {{}})})" using set_minus by metis
    hence 7: "set_ex \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2}}, 0, {{}})})" using assm by auto
    have "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2}}, 0, {{}})} = {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" by force
    hence "set_ex \<subseteq> {({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using 7 by metis
    hence "(set_ex - {({{}, {2}}, 1, {{}, {2}})}) \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2}}, 1, {{}, {2}})})" using set_minus by metis
    hence 8: "set_ex \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2}}, 1, {{}, {2}})})" using assm by auto
    have "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2::nat}}, 1::nat, {{}, {2::nat}})} = {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using set_diff1_pow by blast
    hence "set_ex \<subseteq> {({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using 8 by argo
    hence "(set_ex - {({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}})}) \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}})})" using set_minus by metis
    hence 9: "set_ex \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}})})" using assm by auto
    have "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {0::nat, 1, 2}}, 0::nat, {{}, {2::nat}, {0::nat, 1, 2}})} = {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using set_diff2_pow by blast
    hence "set_ex \<subseteq> {({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using 9 by argo  
    hence "(set_ex - {({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}) \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})})" using set_minus by metis
    hence 10: "set_ex \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})})" using assm by auto
    have "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {0::nat, 1, 2}}, 1::nat, {{}, {2::nat}, {0::nat, 1, 2}})} = {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using set_diff3_pow by blast
    hence "set_ex \<subseteq> {({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using 10 by argo
    hence "(set_ex - {({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}})}) \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}})})" using set_minus by metis
    hence 11: "set_ex \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}})})" using assm by auto
    have "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2}, {0, 1, 2}}, 0::nat, {{}, {2}, {0, 1, 2}})} = {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" by auto
    hence "set_ex \<subseteq> {({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using 11 by metis
    hence "(set_ex - {({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}) \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})})" using set_minus by metis
    hence 12: "set_ex \<subseteq> ({({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})})" using assm by auto
    have "{({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})} - {({{}, {2}, {0, 1, 2}}, 1::nat, {{}, {2}, {0, 1, 2}})} = {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}})}" by force
    hence "set_ex \<subseteq> {({{0::nat, 1, 2}}, 0::nat, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}})}" using 12 by metis
  }
  thus ?thesis by simp
qed

theorem equi_reach_example_pow: "reachable_automaton \<A>_not_minimal_rev_pow_reach_rev_pow = \<A>_not_minimal_rev_pow_reach_rev_pow_reach"
proof -
  let ?trans_set = "{(s1, a, s2) \<in> transitions \<A>_not_minimal_rev_pow_reach_rev_pow . reachable_state s1 \<A>_not_minimal_rev_pow_reach_rev_pow \<and> reachable_state s2 \<A>_not_minimal_rev_pow_reach_rev_pow}"
  have states: "reachable_states \<A>_not_minimal_rev_pow_reach_rev_pow = {{{0, 1, 2}}, {{2}, {0, 1, 2}}}" using reachable_states_example_pow by blast
  have trans: "transitions \<A>_not_minimal_rev_pow_reach_rev_pow = {({}, 0, {}), ({}, 1, {}), ({{2}}, 0, {}), ({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def by auto
  have "?trans_set \<subseteq> transitions \<A>_not_minimal_rev_pow_reach_rev_pow" by blast
  hence sub: "?trans_set \<subseteq> {({}, 0, {}), ({}, 1, {}), ({{2}}, 0, {}), ({{2}}, 1, {}), ({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{}}, 0, {{}}), ({{}}, 1, {{}, {2}}), ({{}, {2}}, 0, {{}}), ({{}, {2}}, 1, {{}, {2}}), ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}), ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}})}" using trans by argo
  have reach: "reachable_state {{0, 1, 2}} \<A>_not_minimal_rev_pow_reach_rev_pow \<and> reachable_state {{2}, {0, 1, 2}} \<A>_not_minimal_rev_pow_reach_rev_pow \<and> \<not> reachable_state {} \<A>_not_minimal_rev_pow_reach_rev_pow \<and> \<not> reachable_state {{}} \<A>_not_minimal_rev_pow_reach_rev_pow \<and> \<not> reachable_state {{2}} \<A>_not_minimal_rev_pow_reach_rev_pow \<and> \<not> reachable_state {{}, {2}} \<A>_not_minimal_rev_pow_reach_rev_pow \<and> \<not> reachable_state {{}, {0, 1, 2}} \<A>_not_minimal_rev_pow_reach_rev_pow \<and> \<not> reachable_state {{}, {2}, {0, 1, 2}} \<A>_not_minimal_rev_pow_reach_rev_pow" using states unreachable_states_example1_pow unreachable_states_example2_pow unreachable_states_example3_pow unreachable_states_example4_pow unreachable_states_example5_pow unreachable_states_example6_pow unfolding reachable_states_def by blast
  hence "?trans_set \<subseteq> \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow \<and> ({}, 0, {}) \<notin> ?trans_set \<and> ({}, 1, {}) \<notin> ?trans_set \<and> ({{2}}, 0, {}) \<notin> ?trans_set \<and> ({{2}}, 1, {}) \<notin> ?trans_set \<and> ({{}}, 0, {{}}) \<notin> ?trans_set \<and> ({{}}, 1, {{}, {2}}) \<notin> ?trans_set \<and> ({{}, {2}}, 0, {{}}) \<notin> ?trans_set \<and> ({{}, {2}}, 1, {{}, {2}}) \<notin> ?trans_set \<and> ({{}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}) \<notin> ?trans_set \<and> ({{}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}) \<notin> ?trans_set \<and> ({{}, {2}, {0, 1, 2}}, 0, {{}, {2}, {0, 1, 2}}) \<notin> ?trans_set \<and> ({{}, {2}, {0, 1, 2}}, 1, {{}, {2}, {0, 1, 2}}) \<notin> ?trans_set" using sub unfolding \<delta>_\<A>_not_minimal_rev_pow_reach_rev_pow_def by fast
  hence sub_sub: "?trans_set \<subseteq> {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}})}" using trans_set_subset_pow_pow by presburger
  have "({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}) \<in> ?trans_set \<and> ({{0, 1, 2}}, 1, {{0, 1, 2}}) \<in> ?trans_set \<and> ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}) \<in> ?trans_set \<and> ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}}) \<in> ?trans_set" using reach trans by simp
  hence "?trans_set = {({{0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{0, 1, 2}}, 1, {{0, 1, 2}}), ({{2}, {0, 1, 2}}, 0, {{2}, {0, 1, 2}}), ({{2}, {0, 1, 2}}, 1, {{0, 1, 2}})}" using sub_sub by fast
  thus ?thesis using states unfolding \<A>_not_minimal_rev_pow_reach_rev_pow_def \<A>_not_minimal_rev_pow_reach_rev_pow_reach_def reachable_automaton_def by force
qed

theorem equivalence_minimal_DFA_brz: "minimal_DFA_brz \<A>_not_minimal = \<A>_not_minimal_rev_pow_reach_rev_pow_reach"
  using equi_reach_example_pow powerset_multi_examples_equivalence_pow equi_rev_example_pow equi_reach_example powerset_multi_examples_equivalence equi_rev_example unfolding minimal_DFA_brz_def by simp

corollary well_def_example_pow: "auto_well_defined \<A>_not_minimal_rev_pow_reach_rev_pow_reach"
  using equivalence_minimal_DFA_brz minimal_preserves_well_defined \<A>_not_minimal_well_def by metis

definition f_min_A :: "nat \<Rightarrow> ((nat states) states)" where "f_min_A s = (if s = 0 then {{0, 1, 2}} else {{2}, {0, 1, 2}})"

theorem minimal_ex_soft_isomorphic: "soft_isomorphic_automata \<A>_A \<A>_not_minimal_rev_pow_reach_rev_pow_reach"
proof -
  have bij: "bij_betw f_min_A (states \<A>_A) (states \<A>_not_minimal_rev_pow_reach_rev_pow_reach)" unfolding f_min_A_def bij_betw_def \<A>_A_def \<A>_not_minimal_rev_pow_reach_rev_pow_reach_def by auto
  have alpha: "bij_betw id (alphabet \<A>_A) (alphabet \<A>_not_minimal_rev_pow_reach_rev_pow_reach)" unfolding \<A>_A_def \<A>_not_minimal_rev_pow_reach_rev_pow_reach_def by auto
  have init: "f_min_A (initial_state \<A>_A) = initial_state \<A>_not_minimal_rev_pow_reach_rev_pow_reach" unfolding f_min_A_def \<A>_A_def \<A>_not_minimal_rev_pow_reach_rev_pow_reach_def by auto
  have acc: "image f_min_A (accepting_states \<A>_A) = accepting_states \<A>_not_minimal_rev_pow_reach_rev_pow_reach" unfolding f_min_A_def \<A>_A_def \<A>_not_minimal_rev_pow_reach_rev_pow_reach_def by auto
  have left: "image (\<lambda>(s1, a, s2) . (f_min_A s1, id a, f_min_A s2)) (transitions \<A>_A) \<subseteq>  transitions \<A>_not_minimal_rev_pow_reach_rev_pow_reach" unfolding \<A>_A_def \<delta>_A_def \<A>_not_minimal_rev_pow_reach_rev_pow_reach_def f_min_A_def by simp
  have "transitions \<A>_not_minimal_rev_pow_reach_rev_pow_reach \<subseteq> image (\<lambda>(s1, a, s2) . (f_min_A s1, id a, f_min_A s2)) (transitions \<A>_A)" unfolding \<A>_A_def \<delta>_A_def \<A>_not_minimal_rev_pow_reach_rev_pow_reach_def f_min_A_def by simp
  hence "image (\<lambda>(s1, a, s2) . (f_min_A s1, id a, f_min_A s2)) (transitions \<A>_A) = transitions \<A>_not_minimal_rev_pow_reach_rev_pow_reach" using left by blast
  thus ?thesis unfolding soft_isomorphic_automata_def using bij alpha init acc by blast
qed

corollary minimal_DFA_ex_soft_isomorphic: "soft_isomorphic_automata \<A>_A (minimal_DFA_brz \<A>_not_minimal)"
  using minimal_ex_soft_isomorphic equivalence_minimal_DFA_brz by simp

corollary language_examples_soft_minimal: "language_auto \<A>_A = language_auto (minimal_DFA_brz \<A>_not_minimal)"
  using minimal_DFA_ex_soft_isomorphic language_soft_iso_correctness well_def_examples by auto

theorem language_equi_example_minimality: "language_auto \<A>_A = language_auto \<A>_not_minimal"
  using language_examples_soft_minimal \<A>_not_minimal_well_def minimal_DFA_language_correctness by blast

proposition example_is_not_minimal: "\<not> minimal_DFA_property \<A>_not_minimal"
proof - 
  have card: "card (states \<A>_A) < card (states \<A>_not_minimal)" unfolding \<A>_not_minimal_def \<A>_A_def by auto
  have dfa: "DFA_property \<A>_A" using DFA_property_examples by blast
  have well_def: "auto_well_defined \<A>_A" using well_def_examples by auto
  have alpha: "alphabet \<A>_A = alphabet \<A>_not_minimal" unfolding \<A>_not_minimal_def \<A>_A_def by auto 
  have "language_auto \<A>_A = language_auto \<A>_not_minimal" using language_equi_example_minimality by blast
  thus ?thesis using card dfa well_def alpha unfolding minimal_DFA_property_def by blast
qed

proposition well_def_implies_not_empty_auto:
  assumes "auto_well_defined \<A>"
  shows "card (states \<A>) \<noteq> 0"
  using assms unfolding auto_well_defined_def by auto

proposition one_state_implies_initial_state:
  assumes "auto_well_defined \<A>" "card (states \<A>) = 1"
  shows "states \<A> = {initial_state \<A>}"
  using assms card_1_singletonE unfolding auto_well_defined_def by force

lemma non_existence_of_smaller_auto_example: "\<nexists> \<A>_minimal :: (nat, nat) automaton . auto_well_defined \<A>_minimal \<and> alphabet \<A>_minimal = alphabet \<A>_A \<and> DFA_property \<A>_minimal \<and> language_auto \<A>_minimal = language_auto \<A>_A \<and> card (states \<A>_minimal) < card (states \<A>_A)"
proof(rule ccontr)
  assume "\<not> (\<nexists> \<A>_minimal :: (nat, nat) automaton . auto_well_defined \<A>_minimal \<and> alphabet \<A>_minimal = alphabet \<A>_A \<and> DFA_property \<A>_minimal \<and> language_auto \<A>_minimal = language_auto \<A>_A \<and> card (states \<A>_minimal) < card (states \<A>_A))"
  hence "\<exists> \<A>_minimal :: (nat, nat) automaton . auto_well_defined \<A>_minimal \<and> alphabet \<A>_minimal = alphabet \<A>_A \<and> DFA_property \<A>_minimal \<and> language_auto \<A>_minimal = language_auto \<A>_A \<and> card (states \<A>_minimal) < card (states \<A>_A)" by blast
  then obtain \<A>_minimal :: "(nat, nat) automaton" where A_mini: "auto_well_defined \<A>_minimal \<and> alphabet \<A>_minimal = alphabet \<A>_A \<and> DFA_property \<A>_minimal \<and> language_auto \<A>_minimal = language_auto \<A>_A \<and> card (states \<A>_minimal) < card (states \<A>_A)" by blast
  hence "card (states \<A>_minimal) = 1" using well_def_implies_not_empty_auto unfolding \<A>_A_def by fastforce
  hence states: "states \<A>_minimal = {initial_state \<A>_minimal}" using one_state_implies_initial_state A_mini by blast
  consider (case1) "initial_state \<A>_minimal \<notin> accepting_states \<A>_minimal" | (case2) "initial_state \<A>_minimal \<in> accepting_states \<A>_minimal" by blast
  thus False
  proof cases
    case case1
    hence "accepting_states \<A>_minimal = {}" using A_mini states unfolding auto_well_defined_def by auto
    hence "language_auto \<A>_minimal = {}" using no_acc_states by blast
    thus ?thesis using run_accepting_example A_mini unfolding language_auto_def by blast
  next
    case case2
    hence "initial_state \<A>_minimal \<in> accepting_states \<A>_minimal \<and> initial_state \<A>_minimal \<in> states \<A>_minimal" using A_mini unfolding auto_well_defined_def by blast
    hence "run_accepting [initial_state \<A>_minimal] \<A>_minimal []" unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by simp
    hence "[] \<in> language_auto \<A>_minimal" unfolding language_auto_def by blast
    thus ?thesis using empty_word_\<A>_A A_mini by blast
  qed
qed

theorem \<A>_A_is_minimal_DFA: "minimal_DFA_property \<A>_A"
  using non_existence_of_smaller_auto_example DFA_property_examples well_def_examples unfolding minimal_DFA_property_def by blast

text \<open>Same result with two different proofs\<close>
corollary "minimal_DFA_property (minimal_DFA_brz \<A>_not_minimal)"
  using soft_implies_isomorphic minimal_DFA_ex_soft_isomorphic \<A>_A_is_minimal_DFA isomorphic_auto_is_minimal_DFA by blast

corollary "minimal_DFA_property (minimal_DFA_brz \<A>_not_minimal)"
  using \<A>_not_minimal_well_def brz_algo_correctness by blast


text \<open>Examples: Regular Expressions and sugar coating\<close> 
definition RE_example_A :: "nat regular_expression" where "RE_example_A = Concatenation (Kleene_star (Concatenation (Kleene_star (Singleton 1)) (Kleene_star (Singleton 0)))) (Singleton 0)"

notation Concatenation (infixl "\<sqdot>" 65)
notation Alternation (infixl "\<parallel>" 60)
notation Kleene_star ("(_)*" [101] 100)
syntax "regular_expression_singleton" :: "'a \<Rightarrow> 'a regular_expression" ("\<langle>_\<rangle>")
translations "\<langle>a\<rangle>" == "CONST Singleton a"

definition RE_example_B :: "nat regular_expression" where "RE_example_B = (\<langle>1\<rangle>* \<sqdot> \<langle>0\<rangle>*)* \<sqdot> \<langle>0\<rangle>"

theorem "RE_example_A = RE_example_B"
  unfolding RE_example_A_def RE_example_B_def by blast

proposition alphabet_RE_example_B: "alphabet_RE RE_example_B = {0, 1}"
  unfolding RE_example_B_def by simp

lemma language_RE_example_B: "language_reg_exp RE_example_B = {word1 @ word2 | word1 word2 . word1 \<in> kleene_star_language (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) \<and> word2 \<in> {[0]}}"
proof -
  have "language_reg_exp RE_example_B = concatenation_language (kleene_star_language (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]}))) {[0]}" unfolding RE_example_B_def by simp
  thus ?thesis unfolding concatenation_language_def by blast
qed

corollary empty_word_not_in_lang_RE_example_B: "[] \<notin> language_reg_exp RE_example_B"
  using language_RE_example_B by blast

proposition word00_in_lang_RE_example_B: "[0, 0] \<in> language_reg_exp RE_example_B"
proof - 
  have "[0] \<in> kleene_star_language {[0]}" using kleene_star_lang_1 unfolding kleene_star_language_def by blast
  hence "[] \<in> kleene_star_language {[1]} \<and> [0] \<in> kleene_star_language {[0]}" using  empty_string_in_kleene_star_lang by blast
  hence "[0] \<in> concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})" unfolding concatenation_language_def by blast
  hence "[0] \<in> kleene_star_language (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) \<and> [0] \<in> {[0]}" using kleene_star_lang_1 unfolding kleene_star_language_def by blast
  hence "[0] @ [0] \<in> {word1 @ word2 | word1 word2 . word1 \<in> kleene_star_language (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) \<and> word2 \<in> {[0]}}" by fast
  hence "[0, 0] \<in> {word1 @ word2 | word1 word2 . word1 \<in> kleene_star_language (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) \<and> word2 \<in> {[0]}}" by force
  thus ?thesis using language_RE_example_B by blast
qed

proposition word10_in_lang_RE_example_B: "[1, 0] \<in> language_reg_exp RE_example_B"
proof - 
  have "[1] \<in> kleene_star_language {[1]}" using kleene_star_lang_1 unfolding kleene_star_language_def by blast
  hence "[] \<in> kleene_star_language {[0]} \<and> [1] \<in> kleene_star_language {[1]}" using  empty_string_in_kleene_star_lang by blast
  hence "[1] \<in> concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})" unfolding concatenation_language_def by blast
  hence "[1] \<in> kleene_star_language (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) \<and> [0] \<in> {[0]}" using kleene_star_lang_1 unfolding kleene_star_language_def by blast
  hence "[1] @ [0] \<in> {word1 @ word2 | word1 word2 . word1 \<in> kleene_star_language (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) \<and> word2 \<in> {[0]}}" by fast
  hence "[1, 0] \<in> {word1 @ word2 | word1 word2 . word1 \<in> kleene_star_language (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) \<and> word2 \<in> {[0]}}" by force
  thus ?thesis using language_RE_example_B by blast
qed

lemma words_RE_example_B_left:
  assumes "word \<in> language_reg_exp RE_example_B"
  shows "last word = 0"
  using assms language_RE_example_B by force

lemma word0_in_concat_lang:
  assumes "n \<noteq> 0"
  shows "[0] \<in> concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})"
proof - 
  have "[0] \<in> kleene_star_language {[0]}" using kleene_star_lang_1 unfolding kleene_star_language_def by blast
  hence "[] \<in> kleene_star_language {[1]} \<and> [0] \<in> kleene_star_language {[0]}" using  empty_string_in_kleene_star_lang by blast
  hence "[0] \<in> concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})" unfolding concatenation_language_def by blast
  thus ?thesis by blast
qed

lemma word1_in_concat_lang:
  assumes "n \<noteq> 0"
  shows "[1] \<in> concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})"
proof - 
  have "[1] \<in> kleene_star_language {[1]}" using kleene_star_lang_1 unfolding kleene_star_language_def by blast
  hence "[] \<in> kleene_star_language {[0]} \<and> [1] \<in> kleene_star_language {[1]}" using  empty_string_in_kleene_star_lang by blast
  hence "[1] \<in> concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})" unfolding concatenation_language_def by blast
  thus ?thesis by blast
qed

lemma words_RE_example_B_right: "word_well_defined word (alphabet_RE RE_example_B) \<and> word \<noteq> [] \<and> last word = 0 \<Longrightarrow> word \<in> language_reg_exp RE_example_B"
proof(induction word)
  case Nil thus ?case by blast
next
  case (Cons a word)
  consider (case1) "word = []" | (case2) "word \<noteq> []" by blast
  thus ?case
  proof cases
    case case1
    hence a: "a = 0 \<and> (a # word) = [a]" using Cons by auto
    hence word_equi: "(a # word) = [] @ [a]" by blast
    have "[] \<in> kleene_star_language (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) \<and> [a] \<in> {[0]}" using a empty_string_in_kleene_star_lang by fast
    thus ?thesis using word_equi language_RE_example_B by blast
  next
    case case2
    hence props: "a \<in> {0, 1} \<and> word_well_defined word (alphabet_RE RE_example_B) \<and> word \<noteq> [] \<and> last word = 0" using Cons case2 word_well_def_cons alphabet_RE_example_B by force
    hence word: "word \<in> language_reg_exp RE_example_B" using Cons by blast
    then obtain word' where word': "word = (word' @ [0])" using props append_butlast_last_id by metis
    hence "word' \<in> kleene_star_language (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]}))" using word language_RE_example_B by blast
    then obtain n where n: "word' \<in> kleene_star_language_helper (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) n" unfolding kleene_star_language_def by blast
    thus ?thesis 
    proof(cases n)
      case 0
      hence "word' = []" using n by simp
      hence "(a # word) = [0, 0] \<or> (a # word) = [1, 0]" using word' props by auto
      thus ?thesis using word00_in_lang_RE_example_B word10_in_lang_RE_example_B by fast
    next
      case (Suc nat)
      hence "[a] \<in> concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})" using props word0_in_concat_lang  word1_in_concat_lang by blast
      hence "[a] @ word' \<in> concatenation_language (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) (kleene_star_language_helper (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) n)" using n unfolding concatenation_language_def by blast
      hence "[a] @ word' \<in> kleene_star_language_helper (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) (Suc n)" using kleene_star_cons by fast
      hence "(a # word') \<in> kleene_star_language_helper (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]})) (Suc n)" by simp
      hence "(a # word') \<in> kleene_star_language (concatenation_language (kleene_star_language {[1]}) (kleene_star_language {[0]}))" unfolding kleene_star_language_def by fast
      hence "(a # word') @ [0] \<in> language_reg_exp RE_example_B" using language_RE_example_B by blast
      thus ?thesis using word' by simp
    qed
  qed
qed

theorem words_RE_example_B:
  assumes "word_well_defined word (alphabet_RE RE_example_B)" "word \<noteq> []"
  shows "last word = 0 \<longleftrightarrow> word \<in> language_reg_exp RE_example_B"
  using words_RE_example_B_left words_RE_example_B_right assms by blast

corollary equivalence_lang_RE_auto_A: "language_reg_exp RE_example_B = language_auto \<A>_A"
proof - 
  have empty_word: "[] \<notin> language_reg_exp RE_example_B \<and> [] \<notin> language_auto \<A>_A" using empty_word_not_in_lang_RE_example_B empty_word_\<A>_A by blast
  have alphas: "alphabet_RE RE_example_B = alphabet \<A>_A" using alphabet_RE_example_B unfolding \<A>_A_def by auto
  {
    fix word assume "word \<in> language_reg_exp RE_example_B"
    hence "last word = 0 \<and> word_well_defined word (alphabet_RE RE_example_B) \<and> word \<noteq> []" using words_RE_example_B empty_word word_in_language_re_is_well_defined by blast 
    hence "last word = 0 \<and> word_well_defined word (alphabet \<A>_A) \<and> word \<noteq> []" using alphas unfolding word_well_defined_def by auto
    hence "word \<in> language_auto \<A>_A" using words_\<A>_A by auto
  }
  hence left: "language_reg_exp RE_example_B \<subseteq> language_auto \<A>_A" unfolding language_auto_def by auto
  {
    fix word assume "word \<in> language_auto \<A>_A"
    hence "last word = 0 \<and> word_well_defined word (alphabet \<A>_A) \<and> word \<noteq> []" using words_\<A>_A empty_word word_in_language_is_well_defined well_def_examples by blast
    hence "last word = 0 \<and> word_well_defined word (alphabet_RE RE_example_B) \<and> word \<noteq> []" using alphas unfolding word_well_defined_def by auto
    hence "word \<in> language_reg_exp RE_example_B" using words_RE_example_B by auto
  }
  thus ?thesis using left by auto
qed





text \<open>Examples: Regular Grammar and sugar coating\<close> 
syntax
  "_rule_right" :: "'s non_terminal \<Rightarrow> 'a symbol \<Rightarrow> 's non_terminal \<Rightarrow> logic" ("_ \<rightarrow>R _ _" [51, 51, 51] 50)
  "_rule_left" :: "'s non_terminal \<Rightarrow> 'a symbol \<Rightarrow> 's non_terminal \<Rightarrow> logic" ("_ \<rightarrow>L _ _" [51, 51, 51] 50)
  "_rule_terminal" :: "'s non_terminal \<Rightarrow> 'a symbol \<Rightarrow> logic" ("_ \<rightarrow> _" [51, 51] 50)
  "_rule_epsilon" :: "'s non_terminal \<Rightarrow> logic" ("_ \<rightarrow> \<epsilon>" [51] 50)

translations
  "_rule_right A a B" == "(CONST Inl A, CONST Inl a, CONST Inl B)"
  "_rule_left A B a" == "(CONST Inl A, CONST Inl a, CONST Inl B)"
  "_rule_terminal A a" == "(CONST Inl A, CONST Inl a, CONST Inr ())"
  "_rule_epsilon A" == "(CONST Inl A, CONST Inr (), CONST Inr ())"

definition G_example1 :: "(string, nat) regular_grammar" where "G_example1 = Grammar {Inl ''S'', Inr()} {Inl 0, Inl 1} {(Inl ''S'', Inl 0, Inl ''S''), (Inl ''S'', Inl 1, Inl ''S''), (Inl ''S'', Inl 0, Inr ())} (Inl ''S'')"

definition G_example2 :: "(string, nat) regular_grammar" where
  "G_example2 = Grammar {Inl ''S'', Inr()} {Inl 0, Inl 1} {''S'' \<rightarrow>R 0 ''S'', ''S'' \<rightarrow>R 1 ''S'', ''S'' \<rightarrow> 0} (Inl ''S'')"

theorem "G_example1 = G_example2"
  unfolding G_example1_def G_example2_def by blast

theorem well_def_G_example1: "grammar_well_defined G_example1"
  unfolding G_example1_def grammar_well_defined_def by force

definition G_example1_auto :: "(string + unit, nat + unit) automaton" where "G_example1_auto = Automaton {Inl ''S'', Inr()} {Inl 0, Inl 1} {(Inl ''S'', Inl 0, Inl ''S''), (Inl ''S'', Inl 1, Inl ''S''), (Inl ''S'', Inl 0, Inr ())} (Inl ''S'') {Inr()}"

theorem G_example1_auto_equi: "G_example1_auto = grammar_to_eps_auto G_example1"
  unfolding G_example1_auto_def grammar_to_eps_auto_def G_example1_def by force

theorem well_def_G_example1_auto: "auto_well_defined G_example1_auto"
  using well_def_G_example1 G_example1_auto_equi well_def_grammar_implies_well_def_eps_auto by force

definition f_bij_G_ex :: "nat \<Rightarrow> (string + unit)" where "f_bij_G_ex n = (if n = 0 then Inl ''S'' else Inr())"

proposition isomorphic_props: "bij_betw f_bij_G_ex (states \<A>_NFA) (states G_example1_auto) \<and> bij_betw Inl (alphabet \<A>_NFA) (alphabet G_example1_auto) \<and> f_bij_G_ex (initial_state \<A>_NFA) = initial_state G_example1_auto \<and> image f_bij_G_ex (accepting_states \<A>_NFA) = accepting_states G_example1_auto \<and> image (\<lambda>(s1, a, s2) . (f_bij_G_ex s1, Inl a, f_bij_G_ex s2)) (transitions \<A>_NFA) = transitions G_example1_auto"
  unfolding f_bij_G_ex_def \<A>_NFA_def G_example1_auto_def bij_betw_def by auto

corollary "isomorphic_automata \<A>_NFA G_example1_auto"
  using isomorphic_props unfolding isomorphic_automata_def by auto

lemma iso_language_examples: "language_auto G_example1_auto = image (map Inl) (language_auto \<A>_NFA)"
  using well_def_\<A>_NFA well_def_G_example1_auto isomorphic_props language_iso_correctness by metis

theorem lang_G_example1_auto_equi: "eps_free_language (language_auto G_example1_auto) = language_auto \<A>_NFA"
proof - 
  {
    fix word assume "word \<in> eps_free_language (language_auto G_example1_auto)"
    then obtain word' where word: "word = evaluate_eps_word word' \<and> word' \<in> language_auto G_example1_auto" unfolding eps_free_language_def by blast
    then obtain word'' where "map Inl word'' = word' \<and> word'' \<in> language_auto \<A>_NFA" using iso_language_examples by auto
    hence "word = evaluate_eps_word (map Inl word'') \<and> word'' \<in> language_auto \<A>_NFA" using word by blast
    hence "word \<in> language_auto \<A>_NFA" using inverse_evaluate_eps by metis
  }
  hence sub: "eps_free_language (language_auto G_example1_auto) \<subseteq> language_auto \<A>_NFA" by blast
  {
    fix word assume "word \<in> language_auto \<A>_NFA"
    hence "map Inl word \<in> language_auto G_example1_auto" using iso_language_examples by blast
    hence "evaluate_eps_word (map Inl word) \<in> eps_free_language (language_auto G_example1_auto)" unfolding eps_free_language_def by blast
    hence "word \<in> eps_free_language (language_auto G_example1_auto)" using inverse_evaluate_eps by metis
  }
  thus ?thesis using sub by blast
qed

corollary grammar_lang_G_example1: "right_grammar_language G_example1 = language_auto \<A>_NFA"
  using well_def_G_example1 G_example1_auto_equi lang_G_example1_auto_equi grammar_to_eps_auto_language_correctness by metis

corollary "right_grammar_language G_example1 = language_reg_exp RE_example_B"
  using grammar_lang_G_example1 equivalence_lang_RE_auto_A lang_equi_examples by auto

definition Grammar_\<A>_A :: "(nat, nat) regular_grammar" where "Grammar_\<A>_A = Grammar {Inl 0, Inl 1, Inr()} {Inl 0, Inl 1, Inr()} {(Inl 0, Inl 0, Inl 1), (Inl 0, Inl 1, Inl 0), (Inl 1, Inl 0, Inl 1), (Inl 1, Inl 1, Inl 0), (Inl 1, Inr(), Inr())} (Inl 0)"

proposition well_def_grammar_A: "grammar_well_defined Grammar_\<A>_A"
  unfolding Grammar_\<A>_A_def grammar_well_defined_def by force

theorem grammar_A_auto_to_grammar: "Grammar_\<A>_A = auto_to_grammar \<A>_A"
  unfolding Grammar_\<A>_A_def auto_to_grammar_def \<A>_A_def \<delta>_A_def by force

corollary "right_grammar_language Grammar_\<A>_A = language_auto \<A>_A"
  using well_def_examples auto_to_grammarlanguage_correctness grammar_A_auto_to_grammar by metis

end