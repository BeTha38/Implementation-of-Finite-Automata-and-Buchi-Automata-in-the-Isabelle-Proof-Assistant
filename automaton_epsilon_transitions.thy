theory automaton_epsilon_transitions

imports Main automaton_nfa_multis

begin

text \<open>Author: Benno Thalmann, last update: 20.10.2025, Addition to masterarbeit_benno_thalmann\<close>

text \<open>Definition of the epsilon free language, Inr() = epsilon\<close>
fun evaluate_eps_word :: "('a + unit) word \<Rightarrow> 'a word" where
  "evaluate_eps_word [] = []" |
  "evaluate_eps_word (Inl a # word) = a # evaluate_eps_word word" |
  "evaluate_eps_word (Inr() # word) = evaluate_eps_word word"

proposition evaluate_eps_word_snoc: "evaluate_eps_word (word1 @ word2) = evaluate_eps_word word1 @ evaluate_eps_word word2"
proof(induction word1 arbitrary: word2 rule: rev_induct)
  case Nil thus ?case by auto
next
  case (snoc x xs)
  hence "evaluate_eps_word ((xs @ [x]) @ word2) = evaluate_eps_word (xs @ (x # word2))" by force
  hence split: "evaluate_eps_word ((xs @ [x]) @ word2) = evaluate_eps_word xs @ evaluate_eps_word (x # word2)" using snoc by auto
  consider (case1) "x = Inr()" | (case2) "x \<noteq> Inr()" by auto
  thus ?case
  proof cases
    case case1 thus ?thesis using snoc by auto
  next
    case case2
    then obtain y where y: "Inl y = x" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    hence "evaluate_eps_word ((xs @ [x]) @ word2) = evaluate_eps_word xs @ [y] @ evaluate_eps_word word2" using split by auto
    hence "evaluate_eps_word ((xs @ [x]) @ word2) = evaluate_eps_word xs @ evaluate_eps_word [x] @ evaluate_eps_word word2" using y by auto
    thus ?thesis using snoc by force
  qed
qed

definition eps_free_language :: "('a + unit) language \<Rightarrow> 'a language" where "eps_free_language L = {evaluate_eps_word word | word . word \<in> L}"

definition original_alphabet :: "('a + unit) alphabet \<Rightarrow> 'a alphabet" where "original_alphabet \<Sigma> = {a . Inl a \<in> \<Sigma>}"

lemma word_well_def_inheritance: "word_well_defined word' \<Sigma> \<and> word = evaluate_eps_word word' \<Longrightarrow> word_well_defined word (original_alphabet \<Sigma>)"
proof(induction word' arbitrary: word)
  case Nil thus ?case unfolding word_well_defined_def by simp
next
  case (Cons a word')
  consider (case1) "a = Inr()" | (case2) "a \<noteq> Inr()" by auto
  thus ?case
  proof cases
    case case1 thus ?thesis using Cons word_well_def_cons by fastforce
  next
    case case2
    hence props: "word_well_defined word' \<Sigma> \<and> a \<in> \<Sigma> \<and> word = evaluate_eps_word (a # word')" using Cons word_well_def_cons by metis
    obtain b where b: "a = Inl b" using case2 old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    hence word: "b \<in> {a . Inl a \<in> \<Sigma>} \<and> word = b # evaluate_eps_word word'" using props by simp
    then obtain word'' where word'': "word = b # word''" by blast
    hence "word_well_defined word' \<Sigma> \<and> b \<in> {a . Inl a \<in> \<Sigma>} \<and> word'' = evaluate_eps_word word' "using props word by blast
    thus ?thesis using Cons word_well_def_cons word'' unfolding original_alphabet_def by fast
  qed
qed

proposition eps_free_language_well_defined:
  assumes "language_well_defined L \<Sigma>"
  shows "language_well_defined (eps_free_language L) (original_alphabet \<Sigma>)"
  using assms word_well_def_inheritance unfolding language_well_defined_def eps_free_language_def by blast

definition NFA_to_epsi :: "('s, 'a) automaton \<Rightarrow> ('s, 'a + unit) automaton" where
  "NFA_to_epsi \<A> = Automaton
    (states \<A>)
    (image Inl (alphabet \<A>))
    (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions \<A>))
    (initial_state \<A>)
    (accepting_states \<A>)"

proposition NFA_to_epsi_auto_well_defined:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (NFA_to_epsi \<A>)"
  using assms unfolding auto_well_defined_def NFA_to_epsi_def by auto

corollary language_well_def_NFA_to_epsi:
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (language_auto (NFA_to_epsi \<A>)) (alphabet (NFA_to_epsi \<A>))"
  using NFA_to_epsi_auto_well_defined assms automata_language_are_well_defined by blast

lemma eps_free_language_NFA_to_epsi:
  assumes "auto_well_defined \<A>" "word \<in> language_auto (NFA_to_epsi \<A>)"
  shows "Inr() \<notin> set word"
  using assms language_well_def_NFA_to_epsi unfolding language_well_defined_def word_well_defined_def NFA_to_epsi_def by auto

lemma NFA_to_epsi_alphabet:
  assumes "auto_well_defined \<A>"
  shows "alphabet \<A> = original_alphabet (alphabet (NFA_to_epsi \<A>))"
  unfolding NFA_to_epsi_def original_alphabet_def by auto

lemma inverse_evaluate_eps: "evaluate_eps_word (map Inl word) = word"
  by (induction word) auto

lemma inverse_Inl_eps: "Inr() \<notin> set word \<Longrightarrow> map Inl (evaluate_eps_word word) = word"
proof(induction word)
  case Nil thus ?case by simp
next
  case (Cons a word)
  hence no_inr: "Inr() \<notin> set word \<and> a \<noteq> Inr()" by force
  then obtain b where b: "a = Inl b" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
  have "a # word = [a] @ word" by simp
  hence "evaluate_eps_word (a # word) = evaluate_eps_word [a] @ evaluate_eps_word word" using evaluate_eps_word_snoc by metis
  hence "map Inl (evaluate_eps_word (a # word)) = (map Inl (evaluate_eps_word [a])) @ (map Inl (evaluate_eps_word word))" by simp
  hence "map Inl (evaluate_eps_word (a # word)) = (map Inl [b]) @ word" using no_inr Cons b by auto
  thus ?case using b by simp
qed

proposition prun_on_NFA_to_epsi: "pseudo_run_well_defined run \<A> s word \<longleftrightarrow> pseudo_run_well_defined run (NFA_to_epsi \<A>) s (map Inl word)"
  unfolding NFA_to_epsi_def pseudo_run_well_defined_def by force

text \<open>Main result for NFA_to_epsi\<close>
theorem NFA_to_epsi_language_correctness:
  assumes "auto_well_defined \<A>"
  shows "language_auto \<A> = eps_free_language (language_auto (NFA_to_epsi \<A>))"
proof -
  {
    fix word assume "word \<in> language_auto \<A>"
    then obtain run where "pseudo_run_well_defined run \<A> (initial_state \<A>) word \<and> last run \<in> accepting_states \<A>" unfolding language_auto_def run_accepting_def run_well_defined_def by blast
    hence "pseudo_run_well_defined run (NFA_to_epsi \<A>) (initial_state (NFA_to_epsi \<A>)) (map Inl word) \<and> last run \<in> accepting_states (NFA_to_epsi \<A>)" using prun_on_NFA_to_epsi unfolding NFA_to_epsi_def by force
    hence "(map Inl word) \<in> language_auto (NFA_to_epsi \<A>)" unfolding pseudo_run_well_defined_def run_well_defined_def run_accepting_def language_auto_def by auto
    hence "evaluate_eps_word (map Inl word) \<in> eps_free_language (language_auto (NFA_to_epsi \<A>))" unfolding eps_free_language_def by fast
    hence "word \<in> eps_free_language (language_auto (NFA_to_epsi \<A>))" using inverse_evaluate_eps by metis
  }
  hence sub: "language_auto \<A> \<subseteq> eps_free_language (language_auto (NFA_to_epsi \<A>))" by blast
  {
    fix word assume "word \<in> eps_free_language (language_auto (NFA_to_epsi \<A>))"
    then obtain word' where word': "word = evaluate_eps_word word' \<and> word' \<in> language_auto (NFA_to_epsi \<A>)" unfolding eps_free_language_def by fast
    hence "Inr() \<notin> set word' \<and> word' \<in> language_auto (NFA_to_epsi \<A>)" using assms eps_free_language_NFA_to_epsi by blast
    hence "map Inl word = word' \<and> word' \<in> language_auto (NFA_to_epsi \<A>)" using inverse_Inl_eps word' by blast
    then obtain run where "pseudo_run_well_defined run (NFA_to_epsi \<A>) (initial_state (NFA_to_epsi \<A>)) (map Inl word) \<and> last run \<in> accepting_states (NFA_to_epsi \<A>)" unfolding language_auto_def run_accepting_def run_well_defined_def by blast
    hence "pseudo_run_well_defined run \<A> (initial_state \<A>) word \<and> last run \<in> accepting_states \<A>" using prun_on_NFA_to_epsi unfolding NFA_to_epsi_def by fastforce    
    hence "word \<in> language_auto \<A>" unfolding run_well_defined_def run_accepting_def language_auto_def by blast
  }
  thus ?thesis using sub by blast
qed

corollary existence_of_NFA_to_epsi:
  assumes "auto_well_defined (NFA_\<A> :: ('s, 'a) automaton)"
  shows "\<exists> NFA_epsi_\<A> :: ('s, 'a + unit) automaton . auto_well_defined NFA_epsi_\<A> \<and> alphabet NFA_\<A> = original_alphabet (alphabet NFA_epsi_\<A>) \<and> language_auto NFA_\<A> = eps_free_language (language_auto NFA_epsi_\<A>)"
  using assms NFA_to_epsi_language_correctness NFA_to_epsi_auto_well_defined NFA_to_epsi_alphabet by fastforce


text \<open>Generalization of finite automata with epsilon-transitions\<close>
definition eps_run_well_defined :: "'s run \<Rightarrow> ('s, 'a + unit) automaton \<Rightarrow> 's state \<Rightarrow> bool" where
  "eps_run_well_defined eps_run \<A> s =
    (length eps_run > 0 \<and>
    (eps_run ! 0) = s \<and> s \<in> states \<A> \<and>
    (\<forall> i < length eps_run - 1 . (eps_run ! i, Inr(), eps_run ! (i + 1)) \<in> transitions \<A>))"

proposition eps_run_states:
  assumes "auto_well_defined \<A>" "eps_run_well_defined eps_run \<A> s"
  shows "prun_states eps_run \<A>"
proof - 
  consider (case1) "length eps_run = 1" | (case2) "length eps_run > 1" using assms unfolding eps_run_well_defined_def by linarith
  thus ?thesis
  proof cases
    case case1
    hence "eps_run = [s] \<and> s \<in> states \<A>" using assms list_with_one_element unfolding eps_run_well_defined_def by metis
    thus ?thesis using prun_states_equivalence by force
  next
    let ?n = "length eps_run"
    case case2
    have eps_run_i: "\<forall> i < ?n - 1 . eps_run ! i \<in> states \<A>" using well_def_trans_components assms unfolding eps_run_well_defined_def by fast
    have "\<forall> i < ?n - 1 . eps_run ! (i + 1) \<in> states \<A>" using well_def_trans_components assms unfolding eps_run_well_defined_def by fast
    hence "eps_run ! (?n - 1) \<in> states \<A>" using case2 simple_math less_add_one by metis
    hence "\<forall> i < ?n . eps_run ! i \<in> states \<A>" using eps_run_i merge_one_more by simp
    thus ?thesis using prun_states_equivalence in_set_conv_nth by metis
  qed
qed

lemma eps_run_well_defined_induction:
  assumes "auto_well_defined \<A>" "eps_run_well_defined eps_run \<A> s" "(last eps_run, Inr(), s') \<in> transitions \<A>"
  shows "eps_run_well_defined (eps_run @ [s']) \<A> s \<and> length (eps_run @ [s']) > 1"
proof -
  let ?n = "length eps_run"
  let ?eps_run = "eps_run @ [s']"
  have properties: "?n > 0 \<and> eps_run \<noteq> [] \<and> eps_run ! 0 = s \<and> s \<in> states \<A>" using assms unfolding eps_run_well_defined_def by fast
  hence snoc_transition_step: "\<forall> i < ?n - 1 . (?eps_run ! i, Inr(), ?eps_run ! (i + 1)) \<in> transitions \<A>" using assms list_properties_length unfolding eps_run_well_defined_def by metis
  have more_props: "length ?eps_run > 1 \<and> ?eps_run ! 0 = s \<and> s \<in> states \<A>" using properties list_properties_not_empty by force
  have "?eps_run ! (?n - 1) = last eps_run \<and> ?eps_run ! ?n = s'" using properties list_properties_not_empty nth_append_length by fast
  hence "(?eps_run ! (?n - 1), Inr(), ?eps_run ! ((?n - 1) + 1)) \<in> transitions \<A>" using properties assms by auto
  hence "\<forall> i < length ?eps_run - 1 . (?eps_run ! i, Inr(), ?eps_run ! (i + 1)) \<in> transitions \<A>" using snoc_transition_step merge_one_more by simp
  thus ?thesis using properties list_properties_not_empty more_props unfolding eps_run_well_defined_def by blast
qed

lemma no_last_transition_eps:
  assumes "auto_well_defined \<A>" "eps_run_well_defined (eps_run @ [s']) \<A> s" "length (eps_run @ [s']) = 1"
  shows "s = s'"
  using assms unfolding eps_run_well_defined_def by auto

lemma last_transition_eps:
  assumes "auto_well_defined \<A>" "eps_run_well_defined (eps_run @ [s']) \<A> s" "length (eps_run @ [s']) > 1"
  shows "(last eps_run, Inr(), s') \<in> transitions \<A>"
proof - 
  let ?n = "length (eps_run @ [s'])"
  let ?eps_run = "eps_run @ [s']"
  have properties: "eps_run \<noteq> [] \<and> ?n > 1" using assms unfolding eps_run_well_defined_def by auto
  have "\<forall> i < ?n - 1 . (?eps_run ! i, Inr(), ?eps_run ! (i + 1)) \<in> transitions \<A>" using assms unfolding eps_run_well_defined_def by argo
  hence trans: "(?eps_run ! (?n - 2), Inr(), ?eps_run ! (?n - 2 + 1)) \<in> transitions \<A>" using properties simple_math less_add_one by metis
  have last: "?eps_run ! (length ?eps_run - 2) = last eps_run" using list_properties_not_empty properties by fastforce
  have "eps_run \<noteq> []" using properties by auto
  hence "?eps_run ! (?n - 2 + 1) = s'" by auto
  thus ?thesis using last trans by argo
qed

lemma eps_run_well_defined_snoc:
  assumes "auto_well_defined \<A>" "eps_run_well_defined (eps_run @ [s']) \<A> s" "length (eps_run @ [s']) > 1"
  shows "eps_run_well_defined eps_run \<A> s \<and> (last eps_run, Inr(), s') \<in> transitions \<A>"
proof -
  let ?n = "length eps_run"
  let ?eps_run = "eps_run @ [s']"
  have properties: "?eps_run ! 0 = s \<and> eps_run \<noteq> [] \<and> s \<in> states \<A>" using assms unfolding eps_run_well_defined_def by fastforce
  hence initial_state: "eps_run ! 0 = s \<and> ?n > 0" using list_properties_not_empty by fast
  have "\<forall> i < ?n - 1 . (?eps_run ! i, Inr(), ?eps_run ! (i + 1)) \<in> transitions \<A>" using assms unfolding eps_run_well_defined_def by auto
  hence "\<forall> i < ?n - 1 . (eps_run ! i, Inr(), eps_run ! (i + 1)) \<in> transitions \<A>" using properties list_properties_length by metis
  thus ?thesis using properties initial_state assms last_transition_eps unfolding eps_run_well_defined_def by metis
qed

proposition eps_run_well_defined_extension:
  assumes "auto_well_defined \<A>"
  shows "eps_run_well_defined (eps_run @ [s']) \<A> s \<and> length (eps_run @ [s']) > 1 \<longleftrightarrow> eps_run_well_defined eps_run \<A> s \<and> (last eps_run, Inr(), s') \<in> transitions \<A>"
  using assms eps_run_well_defined_snoc eps_run_well_defined_induction by metis

definition epsilon_connected :: "'s state \<Rightarrow> ('s, 'a + unit) automaton \<Rightarrow> 's state \<Rightarrow> bool" where "epsilon_connected s1 \<A> s2 = (\<exists> eps_run . eps_run_well_defined eps_run \<A> s1 \<and> last eps_run = s2)"

lemma s_to_s_epsilon_connection:
  assumes "s \<in> states \<A>"
  shows "epsilon_connected s \<A> s" 
proof -
  have props: "[s] ! 0 = s \<and> s \<in> states \<A> \<and> last [s] = s \<and> length [s] > 0 \<and> (\<forall> i < length [s] - 1 . ([s] ! i, Inr(), [s] ! (i + 1)) \<in> transitions \<A>)" using assms by auto
  hence "eps_run_well_defined [s] \<A> s" unfolding eps_run_well_defined_def by auto
  thus ?thesis using props unfolding epsilon_connected_def by blast
qed

definition epsilon_closure :: "'s state \<Rightarrow> ('s, 'a + unit) automaton \<Rightarrow> 's states" where "epsilon_closure s \<A> = {states . epsilon_connected s \<A> states}"

proposition epsilon_closure_sub_states:
  assumes "auto_well_defined \<A>"
  shows "epsilon_closure s \<A> \<subseteq> states \<A>"
proof - 
  {
    fix s' assume "s' \<in> epsilon_closure s \<A>"
    then obtain eps_run where eps_run: "eps_run ! 0 = s \<and> s \<in> states \<A> \<and> length eps_run > 0 \<and> (\<forall> i < length eps_run - 1 . (eps_run ! i, Inr(), eps_run ! (i + 1)) \<in> transitions \<A>) \<and> last eps_run = s'" unfolding epsilon_closure_def epsilon_connected_def eps_run_well_defined_def by blast
    then consider (case1) "length eps_run = 1" | (case2) "length eps_run > 1" by linarith
    hence "s' \<in> states \<A>"
    proof cases
      case case1
      hence "eps_run = [s]" using eps_run list_with_one_element by metis
      hence "s' = s" using eps_run by auto
      thus ?thesis using assms eps_run by auto
    next
      case case2
      hence "eps_run \<noteq> []" by auto
      hence "s' = eps_run ! (length eps_run - 1)" using eps_run list_properties_not_empty by metis
      hence "(eps_run ! (length eps_run - 2), Inr(), s') \<in> transitions \<A>" using eps_run case2 simple_math less_add_one by metis
      thus ?thesis using assms well_def_trans_components by fast
    qed
  }
  thus ?thesis by auto
qed

lemma transitivity_esp_connected:
  assumes "auto_well_defined \<A>" "epsilon_connected s1 \<A> s2" "(s2, Inr(), s) \<in> transitions \<A>"
  shows "epsilon_connected s1 \<A> s"
proof - 
  obtain eps_run where eps_run: "eps_run_well_defined eps_run \<A> s1 \<and> last eps_run = s2" using assms unfolding epsilon_connected_def eps_run_well_defined_def by blast
  hence "eps_run_well_defined (eps_run @ [s]) \<A> s1" using eps_run_well_defined_extension assms by fast
  thus ?thesis unfolding epsilon_connected_def by auto
qed

definition normalize_epsilon_nfa_transitions :: "'s state \<Rightarrow> ('s, 'a + unit) automaton \<Rightarrow> ('s, 'a) transitions" where "normalize_epsilon_nfa_transitions s \<A> = {(s, a, s2) | s1 s2 a . s1 \<in> epsilon_closure s \<A> \<and> (s1, Inl a, s2) \<in> transitions \<A>}"

lemma trivial_normalize_transitions:
  assumes "auto_well_defined \<A>" "(s, Inl b, s') \<in> transitions \<A>"
  shows "(s, b, s') \<in> normalize_epsilon_nfa_transitions s \<A>"
proof -
  have "s \<in> states \<A>" using assms well_def_trans_components by fast
  hence "s \<in> epsilon_closure s \<A>" using s_to_s_epsilon_connection unfolding epsilon_closure_def by fast
  thus ?thesis using assms unfolding normalize_epsilon_nfa_transitions_def by auto
qed

proposition normalize_epsilon_sub_set:
  assumes "auto_well_defined \<A>" "s \<in> states \<A>"
  shows "normalize_epsilon_nfa_transitions s \<A> \<subseteq> {(s1, a, s2) . s1 = s \<and> s2 \<in> states \<A> \<and> Inl a \<in> alphabet \<A>}"
proof - 
  have "epsilon_closure s \<A> \<subseteq> states \<A>" using assms epsilon_closure_sub_states by fast
  hence "normalize_epsilon_nfa_transitions s \<A> \<subseteq> {(s, a, s2) | s1 s2 a . s1 \<in> states \<A> \<and> (s1, Inl a, s2) \<in> transitions \<A>}" unfolding normalize_epsilon_nfa_transitions_def by blast
  thus ?thesis using assms well_def_trans_components unfolding normalize_epsilon_nfa_transitions_def by fast
qed

corollary normalize_epsilon_nfa_transitions_characteristic:
  assumes "auto_well_defined \<A>"
  shows "(\<Union> s \<in> states \<A> . normalize_epsilon_nfa_transitions s \<A>) \<subseteq> {(s1, a, s2) . s1 \<in> states \<A> \<and> s2 \<in> states \<A> \<and> Inl a \<in> alphabet \<A>}"
  using assms normalize_epsilon_sub_set by fast

text \<open>Transformation of finite epsilon-automata to an epsilon-free-NFA\<close>
definition normalize_epsilon_nfa :: "('s, 'a + unit) automaton \<Rightarrow> ('s, 'a) automaton" where
  "normalize_epsilon_nfa \<A> = Automaton
    (states \<A>)
    (original_alphabet (alphabet \<A>))
    (\<Union> s \<in> states \<A> . normalize_epsilon_nfa_transitions s \<A>)
    (initial_state \<A>)
    {s \<in> states \<A> . epsilon_closure s \<A> \<inter> accepting_states \<A> \<noteq> {}}"

proposition normalize_epsilon_nfa_alphabet: "alphabet (normalize_epsilon_nfa \<A>) = original_alphabet (alphabet \<A>)"
  unfolding normalize_epsilon_nfa_def by simp

proposition normalize_epsilon_nfa_well_def:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (normalize_epsilon_nfa \<A>)"
proof - 
  have fin_states: "finite (states \<A>)" using assms unfolding auto_well_defined_def by auto
  have "finite (alphabet \<A>)" using assms unfolding auto_well_defined_def by auto
  hence fin_alphabet: "finite {a . Inl a \<in> alphabet \<A>}" using finite_vimageI inj_Inl vimage_def by metis
  have initi: "initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by auto
  have trans: "\<forall> (s1, a, s2) \<in> (\<Union> s \<in> states \<A> . normalize_epsilon_nfa_transitions s \<A>) . s1 \<in> states \<A> \<and> s2 \<in> states \<A> \<and> a \<in> {a . Inl a \<in> alphabet \<A>}" using assms normalize_epsilon_nfa_transitions_characteristic by auto
  have acc_states: "{s \<in> states \<A> . epsilon_closure s \<A> \<inter> accepting_states \<A> \<noteq> {}} \<subseteq> states \<A>" by auto
  thus ?thesis using fin_states fin_alphabet initi trans acc_states unfolding auto_well_defined_def normalize_epsilon_nfa_def original_alphabet_def by force
qed

corollary language_well_def_normalize_epsilon_auto:
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (language_auto (normalize_epsilon_nfa \<A>)) (alphabet (normalize_epsilon_nfa \<A>))"
  using normalize_epsilon_nfa_well_def assms automata_language_are_well_defined by blast




fun cut_epsilon_run_helper :: "'s run \<Rightarrow> ('a + unit) word \<Rightarrow> 's run" where
  "cut_epsilon_run_helper _ [] = []" |
  "cut_epsilon_run_helper [] _ = []" |
  "cut_epsilon_run_helper (s # run) (Inr() # word) = cut_epsilon_run_helper run word" |
  "cut_epsilon_run_helper (s # run) (Inl a # word) = s # cut_epsilon_run_helper run word"

definition cut_epsilon_run :: "'s run \<Rightarrow> ('a + unit) word \<Rightarrow> 's run" where "cut_epsilon_run run word = (hd run) # cut_epsilon_run_helper (tl run) word"

lemma min_length_cerh: "length (cut_epsilon_run_helper run word) \<le> min (length run) (length word)"
proof(induction word arbitrary: run)
  case Nil thus ?case by auto
next
  case (Cons a word)
  consider (case1) "run = []" | (case2) "run \<noteq> []" by auto
  thus ?case
  proof cases
    case case1 thus ?thesis by force
  next
    case case2
    hence len: "length run > 0" by auto
    consider (case3) "a = Inr()" | (case4) "a \<noteq> Inr()" by auto
    thus ?thesis
    proof cases
      case case3
      hence equi: "cut_epsilon_run_helper run (a # word) = cut_epsilon_run_helper (tl run) word" using case2 list.collapse cut_epsilon_run_helper.simps(3) by metis
      have "length (cut_epsilon_run_helper (tl run) word) \<le> min (length (tl run)) (length word)" using Cons by metis
      thus ?thesis using equi by force
    next
      case case4
      then obtain b where b: "a = Inl b" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
      hence equi: "cut_epsilon_run_helper run (a # word) = (hd run) # cut_epsilon_run_helper (tl run) word" using case2 list.collapse cut_epsilon_run_helper.simps(4) by metis
      have estimation: "length (cut_epsilon_run_helper (tl run) word) \<le> min (length (tl run)) (length word)" using Cons by metis
      have "length (cut_epsilon_run_helper run (a # word)) = 1 + length (cut_epsilon_run_helper (tl run) word)" using equi by auto
      hence step: "length (cut_epsilon_run_helper run (a # word)) \<le> 1 + min (length (tl run)) (length word)" using estimation by auto
      have "1 + length (tl run) = length run \<and> 1 + length word = length (a # word)" using case2 by auto
      thus ?thesis using step by linarith
    qed
  qed
qed

lemma less_length_cer:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word" 
  shows "length (cut_epsilon_run run word) \<le> length run"
  using assms min_length_cerh unfolding pseudo_run_well_defined_def run_well_defined_def cut_epsilon_run_def by fastforce

lemma not_empty_cut_epsilon_run: "length (cut_epsilon_run run word) > 0"
  unfolding cut_epsilon_run_def by auto

proposition cut_epsilon_run_snoc: "length run1 = length word1 + 1 \<and> length run2 = length word2 \<Longrightarrow> cut_epsilon_run (run1 @ run2) (word1 @ word2) = cut_epsilon_run run1 word1 @ cut_epsilon_run_helper run2 word2"
proof(induction word1 arbitrary: run1 run2 word2 rule: rev_induct)
  case Nil
  hence "length run1 = 1" by auto
  hence run1: "run1 = [last run1]" using list_with_one_element by metis
  hence cer: "cut_epsilon_run ((last run1) # run2) word2 = (last run1) # cut_epsilon_run_helper run2 word2" unfolding cut_epsilon_run_def by auto
  have "cut_epsilon_run [last run1] [] @ cut_epsilon_run_helper run2 word2 = (last run1) # cut_epsilon_run_helper run2 word2" unfolding cut_epsilon_run_def by auto
  hence "cut_epsilon_run run1 [] @ cut_epsilon_run_helper run2 word2 = (last run1) # cut_epsilon_run_helper run2 word2" using run1 by auto
  hence equi: "cut_epsilon_run run1 [] @ cut_epsilon_run_helper run2 word2 = cut_epsilon_run ((last run1) # run2) word2" using cer by auto
  have "((last run1) # run2) = run1 @ run2 \<and> word2 = [] @ word2" using run1 by auto
  thus ?case using Nil equi by metis
next
  case (snoc a word)
  hence len: "length run1 = length (word @ [a]) + 1" by blast
  hence "run1 \<noteq> []" by auto
  then obtain run' where run: "run1 = run' @ [last run1]" using append_butlast_last_id by metis
  hence "length (run' @ [last run1]) = length (word @ [a]) + 1" using len by auto
  hence length: "length run' = length word + 1" by auto
  have "cut_epsilon_run (run1 @ run2) ((word @ [a]) @ word2) = cut_epsilon_run ((run' @ [last run1]) @ run2) ((word @ [a]) @ word2)" using run by auto
  hence "cut_epsilon_run (run1 @ run2) ((word @ [a]) @ word2) = cut_epsilon_run (run' @ ([last run1] @ run2)) (word @ ([a] @ word2))" by auto
  hence equi: "cut_epsilon_run (run1 @ run2) ((word @ [a]) @ word2) = cut_epsilon_run run' word @ cut_epsilon_run_helper ([last run1] @ run2) ([a] @ word2)" using snoc length by force
  consider (case1) "a = Inr()" | (case2) "a \<noteq> Inr()" by blast
  hence ultimo: "cut_epsilon_run (run1 @ run2) ((word @ [a]) @ word2) = cut_epsilon_run run' word @ cut_epsilon_run_helper [last run1] [a] @ cut_epsilon_run_helper run2 word2"
  proof cases
    case case1
    hence "cut_epsilon_run_helper [last run1] [a] = []" by auto
    hence "cut_epsilon_run_helper ([last run1] @ run2) ([a] @ word2) = cut_epsilon_run_helper [last run1] [a] @ cut_epsilon_run_helper run2 word2" using case1 by auto 
    thus ?thesis using equi by auto
  next
    case case2
    then obtain b where b: "a = Inl b" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    hence "cut_epsilon_run_helper [last run1] [a] = [last run1]" by auto
    hence "cut_epsilon_run_helper ([last run1] @ run2) ([a] @ word2) = cut_epsilon_run_helper [last run1] [a] @ cut_epsilon_run_helper run2 word2" using case2 b by auto
    thus ?thesis using equi by force
  qed
  have "length [last run1] = length [a]" by auto
  hence "cut_epsilon_run run' word @ cut_epsilon_run_helper [last run1] [a] = cut_epsilon_run (run' @ [last run1]) (word @ [a])" using snoc length by auto
  thus ?case using ultimo run by auto
qed

value "evaluate_eps_word [Inr(), Inr(), Inl (1 :: nat)]"
value "cut_epsilon_run [0 :: nat, 2, 1, 0] [Inr(), Inr(), Inl (1 :: nat)]"
value "evaluate_eps_word [Inr(), Inr(), Inl (1 :: nat), Inr()]"
value "cut_epsilon_run [0 :: nat, 2, 1, 0, 2] [Inr(), Inr(), Inl (1 :: nat), Inr()]"

lemma length_cut_eva: "length run = length word + 1 \<Longrightarrow> length (cut_epsilon_run run word) = length (evaluate_eps_word word) + 1"
proof(induction word arbitrary: run)
  case Nil thus ?case unfolding cut_epsilon_run_def by auto
next
  case (Cons a word)
  hence "run \<noteq> []" by force
  then obtain run' where run: "run = (hd run # run') \<and> length run = length (a # word) + 1" using Cons list.collapse by metis
  hence "length run' = length run - 1" using length_tl list.sel(3) by metis
  hence len: "length run' = length word + 1" using run by auto
  hence ind_step: "length (cut_epsilon_run run' word) = length (evaluate_eps_word word) + 1" using Cons by blast
  consider (case1) "a = Inr()" | (case2) "a \<noteq> Inr()" by blast
  thus ?case
  proof cases
    case case1
    hence len_eva: "length (evaluate_eps_word (a # word)) = length (evaluate_eps_word word)" by auto
    have "cut_epsilon_run run (a # word) = (hd run) # cut_epsilon_run_helper run' (a # word)" using run list.sel(3) unfolding cut_epsilon_run_def by metis
    hence len_cut_run: "cut_epsilon_run run (a # word) = (hd run) # cut_epsilon_run_helper (tl run') word" using cut_epsilon_run_helper.simps(1, 2, 3) case1 Nil_tl list.exhaust_sel by metis
    have "cut_epsilon_run run' word = (hd run') # cut_epsilon_run_helper (tl run') word" unfolding cut_epsilon_run_def by auto
    hence "length (cut_epsilon_run run (a # word)) = length (cut_epsilon_run run' word)" using len_cut_run by auto
    thus ?thesis using len_eva ind_step by auto
  next
    case case2
    then obtain b where b: "a = Inl b" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    hence "evaluate_eps_word (a # word) = b # evaluate_eps_word word" by auto
    hence len_eva: "length (evaluate_eps_word (a # word)) = length (evaluate_eps_word word) + 1" by auto
    have not_empty: "run' \<noteq> []" using len by auto
    have "cut_epsilon_run run (a # word) = (hd run) # cut_epsilon_run_helper run' (a # word)" using run list.sel(3) unfolding cut_epsilon_run_def by metis
    hence len_cut_run: "cut_epsilon_run run (a # word) = (hd run) # ((hd run') # cut_epsilon_run_helper (tl run') word)" using cut_epsilon_run_helper.simps(4) case2 not_empty list.collapse b by metis
    have "cut_epsilon_run run' word = (hd run') # cut_epsilon_run_helper (tl run') word" unfolding cut_epsilon_run_def by auto
    hence "length (cut_epsilon_run run (a # word)) = length (cut_epsilon_run run' word) + 1" using len_cut_run by auto
    thus ?thesis using len_eva ind_step by auto
  qed
qed

lemma cut_init:
  assumes "run_well_defined run \<A> word"
  shows "(cut_epsilon_run run word) ! 0 = initial_state \<A>"
proof - 
  have "(run ! 0) = initial_state \<A> \<and> length run = length word + 1" using assms unfolding pseudo_run_well_defined_def run_well_defined_def by argo
  hence "(run ! 0) = initial_state \<A> \<and> run \<noteq> []" by auto
  thus ?thesis unfolding cut_epsilon_run_def by (simp add: hd_conv_nth)
qed

lemma last_element_of_cut_epsilon_run:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined (run @ [s]) \<A> word \<Longrightarrow> last (cut_epsilon_run (run @ [s]) word) = s \<or> epsilon_connected (last (cut_epsilon_run (run @ [s]) word)) \<A> s"
proof(induction word arbitrary: run s rule: rev_induct)
  case Nil
  hence "length (run @ [s]) = length [] + 1" unfolding pseudo_run_well_defined_def run_well_defined_def by auto
  hence "(run @ [s]) = [s]" by auto
  thus ?case unfolding cut_epsilon_run_def by auto
next
  case (snoc a word)
  hence "length run = length word + 1" unfolding pseudo_run_well_defined_def run_well_defined_def by force
  hence equi: "cut_epsilon_run (run @ [s]) (word @ [a]) = cut_epsilon_run run word @ cut_epsilon_run_helper [s] [a]" using cut_epsilon_run_snoc by force
  consider (case1) "a \<noteq> Inr()" | (case2) "a = Inr()" by argo
  thus ?case 
  proof cases
    case case1
    then obtain b where b: "a = Inl b" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    thus ?thesis using equi by auto
  next
    case case2
    hence equi2: "cut_epsilon_run (run @ [s]) (word @ [a]) = cut_epsilon_run run word" using equi by auto
    then obtain s' where s': "last (cut_epsilon_run run word) = s'" using not_empty_cut_epsilon_run by auto
    consider (case3) "s = s'" | (case4) "s \<noteq> s'" by fast
    thus ?thesis
    proof cases
      case case3 thus ?thesis using equi2 s' by argo
    next
      case case4
      have "run \<noteq> []" using snoc unfolding pseudo_run_well_defined_def run_well_defined_def by force
      then obtain run' where run: "run = run' @ [last run]" using append_butlast_last_id by metis
      hence well_def: "run_well_defined (run' @ [last run]) \<A> word \<and> (last run, a, s) \<in> transitions \<A>" using snoc prun_well_defined_extension_snoc assms unfolding run_well_defined_def by metis
      hence "length (run' @ [last run]) = length word + 1" using snoc run unfolding run_well_defined_def pseudo_run_well_defined_def by blast
      hence "last (cut_epsilon_run (run' @ [last run]) word) = last run \<or> epsilon_connected (last (cut_epsilon_run (run' @ [last run]) word)) \<A> (last run)" using snoc well_def by blast 
      thus ?thesis using assms well_def well_def_trans_components transitivity_esp_connected case2 equi2 s_to_s_epsilon_connection run by metis
    qed
  qed
qed

lemma run_states_cut_eps:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined run \<A> word \<Longrightarrow> prun_states (cut_epsilon_run run word) \<A>"
proof(induction word arbitrary: run rule: rev_induct)
  case Nil
  hence one_element: "cut_epsilon_run run [] = [hd run]" unfolding cut_epsilon_run_def by auto
  hence "prun_states run \<A> \<and> run \<noteq> []" using assms Nil well_def_implies_prun_states unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce
  hence hd: "hd run \<in> states \<A>" unfolding prun_states_def by auto
  hence "\<forall> s \<in> set (cut_epsilon_run run []) . s \<in> states \<A>" by (simp add: one_element)
  thus ?case using prun_states_equivalence by auto
next
  case (snoc a word)
  hence well_def_run: "run_well_defined run \<A> (word @ [a])" using assms by auto
  hence len: "length run = length (word @ [a]) + 1 \<and> run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain run' where run: "run = (run' @ [last run])" using append_butlast_last_id by metis
  hence run': "run_well_defined run' \<A> word" using prun_well_defined_extension_snoc well_def_run assms unfolding run_well_defined_def by metis 
  hence IH: "prun_states (cut_epsilon_run run' word) \<A>" using snoc by auto
  have "length (run' @ [last run]) = length (word @ [a]) + 1" using run len by argo
  hence "length run' = length word + 1 \<and> length [last run] = length [a]" by auto
  hence equi: "cut_epsilon_run (run' @ [last run]) (word @ [a]) = cut_epsilon_run run' word @ cut_epsilon_run_helper [last run] [a]" using cut_epsilon_run_snoc by blast
  have last_run: "last run \<in> states \<A>" using well_def_run assms last_of_prun_is_state unfolding run_well_defined_def by fast
  consider (case1) "a \<noteq> Inr()" | (case2) "a = Inr()" by auto
  hence "cut_epsilon_run_helper [last run] [a] = [last run] \<or> cut_epsilon_run_helper [last run] [a] = []"
  proof cases
    case case1
    then obtain b where b: "a = Inl b" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    thus ?thesis by auto
  next
    case case2 thus ?thesis by auto
  qed
  hence "prun_states (cut_epsilon_run_helper [last run] [a]) \<A>" using last_run unfolding prun_states_def by auto
  hence "(\<forall> s \<in> set (cut_epsilon_run_helper [last run] [a]) . s \<in> states \<A>) \<and> (\<forall> s \<in> set (cut_epsilon_run run' word) . s \<in> states \<A>)" using IH prun_states_equivalence by fast
  hence "\<forall> s \<in> set (cut_epsilon_run (run' @ [last run]) (word @ [a])) . s \<in> states \<A>" using equi by auto
  thus ?case using run prun_states_equivalence by auto
qed

lemma cut_i_step:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined run \<A> word \<Longrightarrow> \<forall> i < length (cut_epsilon_run run word) - 1 . (cut_epsilon_run run word ! i, evaluate_eps_word word ! i, cut_epsilon_run run word ! (i + 1)) \<in> transitions (normalize_epsilon_nfa \<A>)"
proof(induction word arbitrary: run rule: rev_induct)
  case Nil thus ?case unfolding cut_epsilon_run_def by auto
next
  case (snoc a word)
  hence well_def_run: "run_well_defined run \<A> (word @ [a])" using assms by blast
  hence len: "length run = length (word @ [a]) + 1 \<and> run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain run' where run: "run = (run' @ [last run])" using append_butlast_last_id by metis
  hence run': "run_well_defined run' \<A> word \<and> (last run', a, last run) \<in> transitions \<A>" using prun_well_defined_extension_snoc well_def_run assms unfolding run_well_defined_def by metis
  hence i_step: "\<forall> i < length (cut_epsilon_run run' word) - 1 . (cut_epsilon_run run' word ! i, evaluate_eps_word word ! i, cut_epsilon_run run' word ! (i + 1)) \<in> transitions (normalize_epsilon_nfa \<A>) \<and> (last run', a, last run) \<in> transitions \<A>" using snoc by blast
  consider (case1) "a = Inr()" | (case2) "a \<noteq> Inr()" by auto
  thus ?case
  proof cases
    case case1
    hence eva: "evaluate_eps_word (word @ [a]) = evaluate_eps_word word" by (simp add: evaluate_eps_word_snoc)
    have "length run' = length word + 1 \<and> length [last run] = length [a]" using run' unfolding run_well_defined_def pseudo_run_well_defined_def by force
    hence "cut_epsilon_run run (word @ [a]) = cut_epsilon_run run' word @ cut_epsilon_run_helper [last run] [a]" using cut_epsilon_run_snoc run by metis
    hence "cut_epsilon_run run (word @ [a]) = cut_epsilon_run run' word" using case1 by auto
    thus ?thesis using i_step eva by presburger
  next
    case case2
    let ?run = "cut_epsilon_run run (word @ [a])"
    let ?word = "evaluate_eps_word (word @ [a])"
    let ?n = "length (cut_epsilon_run run' word)"
    obtain b where b: "a = Inl b" using case2 old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    hence eva: "?word = evaluate_eps_word word @ [b]" by (simp add: evaluate_eps_word_snoc)
    have len_eva: "?n = length (evaluate_eps_word word) + 1" using run' length_cut_eva unfolding run_well_defined_def pseudo_run_well_defined_def by blast
    hence equi_eva: "\<forall> i < ?n - 1 . evaluate_eps_word word ! i = ?word ! i" using eva by (simp add: nth_append)
    have "length run' = length word + 1 \<and> length [last run] = length [a]" using run' unfolding run_well_defined_def pseudo_run_well_defined_def by auto
    hence "?run = cut_epsilon_run run' word @ cut_epsilon_run_helper [last run] [a]" using cut_epsilon_run_snoc run by metis
    hence equi: "?run = cut_epsilon_run run' word @ [last run]" using case2 b by auto
    hence "\<forall> i < ?n - 1 . cut_epsilon_run run' word ! i = ?run ! i \<and> cut_epsilon_run run' word ! (i + 1) = ?run ! (i + 1)" using equi list_properties_length by metis
    hence first_i: "\<forall> i < ?n - 1 . (?run ! i, ?word ! i, ?run ! (i + 1)) \<in> transitions (normalize_epsilon_nfa \<A>)" using i_step equi_eva by auto
    hence last_trans: "(last run', a, last run) \<in> transitions \<A> \<and> last run' \<in> states \<A>" using assms well_def_trans_components run' by fast
    have "prun_states ?run \<A>" using assms well_def_run run_states_cut_eps by blast
    hence "\<forall> s \<in> set ?run . s \<in> states \<A>" using prun_states_equivalence by fast
    hence "\<forall> i < length ?run . ?run ! i \<in> states \<A>" by auto
    hence in_states: "(?run ! (?n - 1)) \<in> states \<A>" using equi by auto
    have "run_well_defined run' \<A> word \<and> run' \<noteq> []" using run' unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce
    then obtain run'' where "run' = (run'' @ [last run'])" using append_butlast_last_id by metis
    hence last_element_eps: "last (cut_epsilon_run run' word) = last run' \<or> epsilon_connected (last (cut_epsilon_run run' word)) \<A> (last run')" using assms last_element_of_cut_epsilon_run run' by metis
    have "?run ! (?n - 1) = last (cut_epsilon_run run' word)" using equi length_greater_0_conv list_properties_not_empty not_empty_cut_epsilon_run by metis
    hence "(?run ! (?n - 1)) = last run' \<or> epsilon_connected (?run ! (?n - 1)) \<A> (last run')" using last_element_eps by argo
    hence i: "(last run') \<in> epsilon_closure (?run ! (?n - 1)) \<A> \<and> (?run ! (?n - 1)) \<in> states \<A>" using in_states s_to_s_epsilon_connection unfolding epsilon_closure_def by auto
    have i1: "?run ! ?n = last run" using equi by auto
    have "?word ! (?n - 1) = b" using b eva len_eva by auto
    hence "(?run ! (?n - 1), ?word ! (?n - 1), ?run ! ((?n - 1) + 1)) \<in> transitions (normalize_epsilon_nfa \<A>)" using i i1 last_trans b len_eva unfolding normalize_epsilon_nfa_def normalize_epsilon_nfa_transitions_def by auto 
    hence "\<forall> i < ?n . (?run ! i, ?word ! i, ?run ! (i + 1)) \<in> transitions (normalize_epsilon_nfa \<A>)" using first_i merge_one_more by simp
    thus ?thesis using equi by auto
  qed
qed

lemma normalize_epsilon_run_left:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word"
  shows "\<exists> run' . run_well_defined run' (normalize_epsilon_nfa \<A>) (evaluate_eps_word word) \<and> epsilon_connected (last run') \<A> (last run)"
proof - 
  have "run \<noteq> []" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  then obtain run' where "run = run' @ [last run]" using append_butlast_last_id by metis
  hence last: "last (cut_epsilon_run run word) = last run \<or> epsilon_connected (last (cut_epsilon_run run word)) \<A> (last run)" using assms last_element_of_cut_epsilon_run by metis
  have len: "length (cut_epsilon_run run word) = length (evaluate_eps_word word) + 1" using assms length_cut_eva unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  have "(cut_epsilon_run run word) ! 0 = initial_state \<A>" using assms cut_init by auto
  hence "(cut_epsilon_run run word) ! 0 = initial_state (normalize_epsilon_nfa \<A>)" unfolding normalize_epsilon_nfa_def by auto
  hence init: "(cut_epsilon_run run word) ! 0 = initial_state (normalize_epsilon_nfa \<A>) \<and> initial_state (normalize_epsilon_nfa \<A>) \<in> states (normalize_epsilon_nfa \<A>)" using assms normalize_epsilon_nfa_well_def unfolding auto_well_defined_def by blast
  have i_step: "\<forall> i < length (cut_epsilon_run run word) - 1 . (cut_epsilon_run run word ! i, evaluate_eps_word word ! i, cut_epsilon_run run word ! (i + 1)) \<in> transitions (normalize_epsilon_nfa \<A>)" using assms cut_i_step by blast
  hence "run_well_defined (cut_epsilon_run run word) (normalize_epsilon_nfa \<A>) (evaluate_eps_word word)" using len init i_step unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  hence "run_well_defined (cut_epsilon_run run word) (normalize_epsilon_nfa \<A>) (evaluate_eps_word word) \<and> last run \<in> states \<A>" using assms normalize_epsilon_nfa_well_def last_of_prun_is_state unfolding run_well_defined_def by fast
  thus ?thesis using last s_to_s_epsilon_connection assms by metis
qed

lemma normalize_epsilon_language_left:
  assumes "auto_well_defined \<A>"
  shows "eps_free_language (language_auto \<A>) \<subseteq> language_auto (normalize_epsilon_nfa \<A>)"
proof -
  let ?\<A> = "normalize_epsilon_nfa \<A>"
  {
    fix word assume "word \<in> eps_free_language (language_auto \<A>)"
    then obtain word' where word': "word' \<in> language_auto \<A> \<and> word = evaluate_eps_word word'" unfolding eps_free_language_def by auto
    then obtain run where "run_accepting run \<A> word'" unfolding language_auto_def by blast
    hence acc: "run_well_defined run \<A> word' \<and> last run \<in> accepting_states \<A>" unfolding run_accepting_def by auto
    then obtain run' where run': "run_well_defined run' ?\<A> word \<and> epsilon_connected (last run') \<A> (last run)" using assms normalize_epsilon_run_left word' by blast
    hence closure: "last run \<in> accepting_states \<A> \<and> last run \<in> epsilon_closure (last run') \<A>" using acc unfolding epsilon_closure_def by auto
    have not_empty: "run' \<noteq> []" using run' unfolding run_well_defined_def pseudo_run_well_defined_def by force
    have "prun_states run' ?\<A>" using assms run' well_def_implies_prun_states normalize_epsilon_nfa_well_def unfolding run_well_defined_def by fast
    hence "last run' \<in> states ?\<A>" using prun_states_equivalence not_empty by force
    hence "last run' \<in> accepting_states ?\<A>" using closure unfolding normalize_epsilon_nfa_def by auto
    hence "word \<in> language_auto ?\<A>" using run' unfolding run_accepting_def language_auto_def by blast
  }
  thus ?thesis by blast
qed

fun only_eps_word :: "nat \<Rightarrow> ('a + unit) word" where
  "only_eps_word 0 = []" |
  "only_eps_word (Suc n) = Inr() # only_eps_word n"

lemma only_eps_pos: "\<forall> i < n . only_eps_word n ! i = Inr()"
  using less_Suc_eq_0_disj by (induction n) auto

lemma only_eps_length: "length (only_eps_word n) = n"
  by (induction n) auto

lemma eva_only_eps: "evaluate_eps_word (only_eps_word n) = []"
  by (induction n) auto

lemma normalize_epsilon_run_i_step:
  assumes "auto_well_defined \<A>" "run_well_defined run' \<A> word' \<and> last run' = last run \<and> evaluate_eps_word word' = word \<and> eps_run ! 0 = last run \<and> length eps_run > 0 \<and> (\<forall> i < length eps_run - 1 . (eps_run ! i, Inr(), eps_run ! (i + 1)) \<in> transitions \<A>)"
  shows "\<forall> i < length (run' @ (tl eps_run)) - 1 . ((run' @ (tl eps_run)) ! i, (word' @ (only_eps_word (length (tl (eps_run))))) ! i, (run' @ (tl eps_run)) ! (i + 1)) \<in> transitions \<A>"
proof -
  have pseudo_0: "eps_run ! 0 = last run' \<and> length eps_run > 0" using assms by argo
  let ?run = "run' @ (tl eps_run)"
  let ?word = "word' @ (only_eps_word (length (tl (eps_run))))"
  have len: "length run' = length word' + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  hence length: "length ?run = length ?word + 1" by (simp add: only_eps_length)
  have not_empty: "run' \<noteq> []" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "?run! 0 = run' ! 0" by (simp add: nth_append)
  hence init: "?run ! 0 = initial_state \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  have run_i: "\<forall> i < length run' - 1 . (run' ! i, word' ! i, run' ! (i + 1)) \<in> transitions \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  consider (case1) "length eps_run = 1" | (case2) "length eps_run > 1" using assms by linarith
  thus ?thesis
  proof cases
    case case1
    have "tl eps_run = []" using list_with_one_element case1 by fast
    hence "?run = run'" by auto
    thus ?thesis using run_i by auto
  next
    case case2
    {
      fix k assume assm: "k < length ?run - 1"
      consider (case3) "k < length run' - 1" | (case4) "k = length run' - 1" | (case5) "k > length run' - 1" by fastforce
      hence "(?run ! k, ?word ! k, ?run ! (k + 1)) \<in> transitions \<A>"
      proof cases
        case case3 thus ?thesis using run_i len by (simp add: nth_append)
      next
        case case4
        have tl_len: "length (tl eps_run) = length eps_run - 1" by auto
        hence "\<forall> i < length eps_run - 1 . only_eps_word (length (tl (eps_run))) ! i = Inr()" using only_eps_pos by auto 
        hence pseudo_i: "\<forall> i < length eps_run - 1 . (eps_run ! i, only_eps_word (length (tl (eps_run))) ! i, eps_run ! (i + 1)) \<in> transitions \<A>" using assms by metis
        hence trans: "(last run', only_eps_word (length (tl (eps_run))) ! 0, eps_run ! 1) \<in> transitions \<A>" using pseudo_0 case2 by fastforce
        have "run' ! k = last run'" using not_empty case4 list_properties_not_empty by fast
        hence kth: "?run ! k = last run'" using not_empty case4 by (simp add: nth_append)
        have "?run ! (k + 1) = (tl eps_run) ! 0" using not_empty case4 by (simp add: nth_append)
        hence k1th: "?run ! (k + 1) = eps_run ! 1" using case2 by (simp add: nth_tl)
        have "?word ! k = only_eps_word (length (tl (eps_run))) ! 0" using case4 len by (simp add: nth_append)
        thus ?thesis using trans kth k1th by presburger
      next
        case case5
        have tl_len: "length (tl eps_run) = length eps_run - 1" by auto
        hence "\<forall> i < length eps_run - 1 . only_eps_word (length (tl (eps_run))) ! i = Inr()" using only_eps_pos by auto 
        hence pseudo_i: "\<forall> i < length eps_run - 1 . (eps_run ! i, only_eps_word (length (tl (eps_run))) ! i, eps_run ! (i + 1)) \<in> transitions \<A>" using assms by metis
        obtain j where j: "j = k - length run'" by auto
        hence "j + 1 < length eps_run - 1" using assm case5 by force
        hence trans: "(eps_run ! (j + 1), only_eps_word (length (tl (eps_run))) ! (j + 1), eps_run ! (j + 1 + 1)) \<in> transitions \<A>" using pseudo_i by blast
        have "?run ! k = (tl eps_run) ! j" using j case5 len by (simp add: nth_append)
        hence kth: "?run ! k = eps_run ! (j + 1)" using case2 j assm by (simp add: nth_tl)
        have "?run ! (k + 1) = (tl eps_run) ! (j + 1)" using j assm case5 nth_list_append1 by blast
        hence k1th: "?run ! (k + 1) = eps_run ! (j + 2)" using j assm case5 by (simp add: nth_tl)
        have "?word ! k = only_eps_word (length (tl (eps_run))) ! (j + 1)" using case5 len length assm j nth_list_append2 by metis
        thus ?thesis using trans kth k1th by force
      qed
    }
    thus ?thesis by auto
  qed
qed

lemma normalize_epsilon_run_right:
  assumes "auto_well_defined \<A>" 
  shows "run_well_defined run (normalize_epsilon_nfa \<A>) word \<Longrightarrow> \<exists> run' word' . run_well_defined run' \<A> word' \<and> last run' = last run \<and> evaluate_eps_word word' = word"
proof(induction word arbitrary: run rule: rev_induct)
  let ?\<A> = "normalize_epsilon_nfa \<A>"
  case Nil
  hence "length run = 1 \<and> run ! 0 = initial_state ?\<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "last run = initial_state ?\<A>" using list_with_one_element by fast
  hence "last run = initial_state \<A>" unfolding normalize_epsilon_nfa_def by force
  hence "last run = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by auto
  hence "run_well_defined [initial_state \<A>] \<A> [] \<and> last [initial_state \<A>] = last run \<and> evaluate_eps_word [] = []" unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  thus ?case by blast
next
  let ?\<A> = "normalize_epsilon_nfa \<A>"
  have well_def: "auto_well_defined ?\<A>" using assms normalize_epsilon_nfa_well_def by auto
  case (snoc a word)
  hence "run \<noteq>[]" unfolding run_well_defined_def pseudo_run_well_defined_def by force 
  then obtain run' where "run = (run' @ [last run])" using append_butlast_last_id by metis
  hence "run_well_defined run' ?\<A> word \<and> (last run', a, last run) \<in> transitions ?\<A>" using prun_well_defined_extension_snoc snoc well_def unfolding run_well_defined_def by metis
  then obtain run_eps word_eps where run_word_eps: "run_well_defined run_eps \<A> word_eps \<and> last run_eps = last run' \<and> evaluate_eps_word word_eps = word \<and> (last run', a, last run) \<in> transitions ?\<A>" using snoc by blast
  then obtain s where s: "s \<in> epsilon_closure (last run') \<A> \<and> (s, Inl a, last run) \<in> transitions \<A>" unfolding normalize_epsilon_nfa_def normalize_epsilon_nfa_transitions_def by auto
  hence "epsilon_connected (last run') \<A> s \<and> (s, Inl a, last run) \<in> transitions \<A>" unfolding epsilon_closure_def by auto
  then obtain eps_run where eps_run: "eps_run ! 0 = last run' \<and> length eps_run > 0 \<and> (\<forall> i < length eps_run - 1 . (eps_run ! i, Inr(), eps_run ! (i + 1)) \<in> transitions \<A>) \<and> last eps_run = s" unfolding epsilon_connected_def eps_run_well_defined_def by blast
  let ?run = "run_eps @ (tl eps_run) @ [last run]"
  let ?word = "word_eps @ (only_eps_word (length (tl eps_run))) @ [Inl a]"
  have last: "last ?run = last run" by auto
  have "evaluate_eps_word ?word = evaluate_eps_word word_eps @ evaluate_eps_word (only_eps_word (length (tl eps_run))) @ evaluate_eps_word [Inl a] " using evaluate_eps_word_snoc by metis
  hence eva_word: "evaluate_eps_word ?word = (word @ [a])" using eva_only_eps run_word_eps by auto
  have len: "length run_eps = length word_eps + 1" using run_word_eps unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence length: "length ?run = length ?word + 1" by (simp add: only_eps_length)
  have "run_eps \<noteq> []" using run_word_eps unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "?run! 0 = run_eps ! 0" by (simp add: nth_append)
  hence "?run ! 0 = initial_state \<A>" using run_word_eps unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence init: "?run ! 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by argo
  have len_run: "length ?run = length (run_eps @ (tl eps_run)) + 1" by auto
  hence equi_run: "\<forall> i < length (run_eps @ (tl eps_run)) - 1 . (run_eps @ (tl eps_run)) ! i = ?run ! i \<and> (run_eps @ (tl eps_run)) ! (i + 1) = ?run ! (i + 1)" using append_assoc list_properties_length by metis
  have "length (word_eps @ (only_eps_word (length (tl eps_run)))) = length (run_eps @ (tl eps_run)) - 1" using length by auto
  hence equi_word: "\<forall> i < length (run_eps @ (tl eps_run)) - 1 . ((word_eps @ (only_eps_word (length (tl eps_run))))) ! i = ?word ! i" using list_properties_length append_assoc by metis 
  have "\<forall> i < length (run_eps @ (tl eps_run)) - 1 . ((run_eps @ (tl eps_run)) ! i, ((word_eps @ (only_eps_word (length (tl eps_run))))) ! i, (run_eps @ (tl eps_run)) ! (i + 1)) \<in> transitions \<A>" using assms eps_run run_word_eps normalize_epsilon_run_i_step by blast
  hence first_i: "\<forall> i < length (run_eps @ (tl eps_run)) - 1 . (?run ! i, ?word ! i, ?run ! (i + 1)) \<in> transitions \<A>" using equi_run equi_word by metis
  consider (case1) "length eps_run = 1" | (case2) "length eps_run > 1" using eps_run by linarith
  hence "(?run ! (length (run_eps @ (tl eps_run)) - 1), ?word ! (length (run_eps @ (tl eps_run)) - 1), ?run ! ((length (run_eps @ (tl eps_run)) - 1) + 1)) \<in> transitions \<A>"
  proof cases
    case case1
    let ?k = "length (run_eps @ (tl eps_run)) - 1"
    have not_empty: "run_eps \<noteq> []" using run_word_eps unfolding run_well_defined_def pseudo_run_well_defined_def by auto
    hence kth: "?run ! ?k = last run'" using case1 run_word_eps by (simp add: last_conv_nth nth_append)
    have k1th: "?run ! (?k + 1) = last run" using not_empty case1 by (simp add: nth_append)
    have kword: "?word ! ?k = Inl a" using case1 len by (simp add: nth_append)
    have "eps_run ! 0 = s" using eps_run case1 list_with_one_element by metis
    hence "s = last run'" using eps_run by blast
    thus ?thesis using kth k1th kword s by argo
  next
    case case2
    let ?k = "length (run_eps @ (tl eps_run)) - 1"
    have not_empty: "(run_eps @ (tl eps_run)) \<noteq> []" using run_word_eps unfolding run_well_defined_def pseudo_run_well_defined_def by auto
    have "length (tl eps_run) > 0" using case2 by auto
    hence not_empty_tl: "(tl eps_run) \<noteq> []" by blast
    hence "?run ! ?k = last (tl eps_run)" using not_empty list_properties_not_empty append_assoc last_appendR by metis
    hence kth: "?run ! ?k = s" using case2 last_tl not_empty_tl eps_run by metis
    have "?run \<noteq> [] \<and> (?k + 1) = length ?run - 1" using length by auto
    hence k1th: "?run ! (?k + 1) = last run" using last list_properties_not_empty by metis
    have "?word \<noteq> [] \<and> ?k = length ?word - 1" using length by force
    hence kword: "?word ! ?k = Inl a" by (simp add: nth_append)
    thus ?thesis using kth k1th kword s by argo
  qed
  hence "\<forall> i < length (run_eps @ (tl eps_run)) . (?run ! i, ?word ! i, ?run ! (i + 1)) \<in> transitions \<A>" using first_i merge_one_more by simp
  hence i_step: "\<forall> i < length ?run - 1 . (?run ! i, ?word ! i, ?run ! (i + 1)) \<in> transitions \<A>" using len_run by auto
  have "run_well_defined ?run \<A> ?word \<and> last ?run = last run \<and> evaluate_eps_word ?word = (word @ [a])" using i_step init length eva_word last unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  thus ?case by blast
qed

lemma normalize_epsilon_run_right_accepting:
  assumes "auto_well_defined \<A>" "run_accepting run (normalize_epsilon_nfa \<A>) word"
  shows "\<exists> run' word' . run_accepting run' \<A> word' \<and> evaluate_eps_word word' = word"
proof -
  let ?\<A> = "normalize_epsilon_nfa \<A>"
  have props: "run_well_defined run ?\<A> word \<and> last run \<in> accepting_states ?\<A>" using assms unfolding run_accepting_def by auto
  hence "epsilon_closure (last run) \<A> \<inter> accepting_states \<A> \<noteq> {}" unfolding normalize_epsilon_nfa_def by auto
  hence "\<exists> s . epsilon_connected (last run) \<A> s \<and> s \<in> accepting_states \<A>" unfolding epsilon_closure_def by auto
  then obtain s where s: "epsilon_connected (last run) \<A> s \<and> s \<in> accepting_states \<A>" by auto
  then obtain eps_run where eps_run: "eps_run ! 0 = last run \<and> length eps_run > 0 \<and> (\<forall> i < length eps_run - 1 . (eps_run ! i, Inr(), eps_run ! (i + 1)) \<in> transitions \<A>) \<and> last eps_run = s" unfolding epsilon_connected_def eps_run_well_defined_def by blast
  obtain run' word' where run': "run_well_defined run' \<A> word' \<and> last run' = last run \<and> evaluate_eps_word word' = word" using props assms normalize_epsilon_run_right by blast
  hence pseudo_0: "eps_run ! 0 = last run' \<and> length eps_run > 0" using eps_run by argo
  let ?run = "run' @ (tl eps_run)"
  let ?word = "word' @ (only_eps_word (length (tl (eps_run))))"
  have len: "length run' = length word' + 1" using run' unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  hence length: "length ?run = length ?word + 1" by (simp add: only_eps_length)
  have "run' \<noteq> []" using run' unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence "?run! 0 = run' ! 0" by (simp add: nth_append)
  hence "?run ! 0 = initial_state \<A>" using run' unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  hence init: "?run ! 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  hence i_step: "\<forall> i < length ?run - 1 . (?run ! i, ?word ! i, ?run ! (i + 1)) \<in> transitions \<A>" using assms s eps_run run' normalize_epsilon_run_i_step by blast
  consider (case1) "length eps_run = 1" | (case2) "length eps_run > 1" using eps_run by linarith
  hence last: "last ?run = s"
  proof cases
    case case1
    hence equi: "last run = s" using eps_run list_with_one_element by metis
    have "tl eps_run = []" using list_with_one_element case1 by fast
    hence "last ?run = last run'" by auto
    thus ?thesis using equi run' by argo
  next
    case case2
    hence not_empty: "tl eps_run \<noteq> []" using tl_more_elements by auto
    hence "last ?run = last (tl eps_run)" by auto
    thus ?thesis using eps_run not_empty by (simp add: last_tl)
  qed
  have eva: "evaluate_eps_word ?word = word" using run' by (simp add: eva_only_eps evaluate_eps_word_snoc)
  have "run_well_defined ?run \<A> ?word \<and> last ?run = s \<and> evaluate_eps_word ?word = word" using last eva init length i_step unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  thus ?thesis using s unfolding run_accepting_def by blast
qed

lemma normalize_epsilon_language_right:
  assumes "auto_well_defined \<A>"
  shows "language_auto (normalize_epsilon_nfa \<A>) \<subseteq> eps_free_language (language_auto \<A>)"
proof -
  let ?\<A> = "normalize_epsilon_nfa \<A>"
  {
    fix word assume "word \<in> language_auto ?\<A>"
    then obtain run where "run_accepting run ?\<A> word" unfolding language_auto_def by blast
    then obtain run' word' where run': "run_accepting run' \<A> word' \<and> evaluate_eps_word word' = word" using assms normalize_epsilon_run_right_accepting by blast
    hence "word' \<in> language_auto \<A>" unfolding language_auto_def by auto
    hence "word \<in> eps_free_language (language_auto \<A>)" using run' unfolding eps_free_language_def by auto
  }
  thus ?thesis by auto
qed

text \<open>Main result for the normalize_epsilon automaton: language equivalence\<close>
theorem normalize_epsilon_language_correctness:
  assumes "auto_well_defined \<A>"
  shows "language_auto (normalize_epsilon_nfa \<A>) = eps_free_language (language_auto \<A>)"
  using assms normalize_epsilon_language_left normalize_epsilon_language_right by auto

theorem eps_main:
  assumes "auto_well_defined (\<A> :: ('s, 'a + unit) automaton)"
  shows "\<exists> eps_free_\<A> :: ('s, 'a) automaton . auto_well_defined eps_free_\<A> \<and> alphabet eps_free_\<A> = original_alphabet (alphabet \<A>) \<and> language_auto eps_free_\<A> = eps_free_language (language_auto \<A>)"
  using assms normalize_epsilon_language_correctness normalize_epsilon_nfa_well_def normalize_epsilon_nfa_alphabet by fast

theorem expressive_power_eps_nfa_main: "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> \<Sigma> = alphabet NFA_\<A> \<and> L = language_auto NFA_\<A>} = {eps_free_language L | L . \<exists> (NFA_\<A>_eps :: ('s, 'a + unit) automaton) . auto_well_defined NFA_\<A>_eps \<and> \<Sigma> = original_alphabet (alphabet NFA_\<A>_eps) \<and> L = language_auto NFA_\<A>_eps}"
proof -
  have "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> \<Sigma> = alphabet NFA_\<A> \<and> L = language_auto NFA_\<A>} \<subseteq> {eps_free_language L | L . \<exists> (NFA_\<A>_eps :: ('s, 'a + unit) automaton) . auto_well_defined NFA_\<A>_eps \<and> \<Sigma> = original_alphabet (alphabet NFA_\<A>_eps) \<and> L = language_auto NFA_\<A>_eps}" using existence_of_NFA_to_epsi by fast
  thus ?thesis using eps_main by fast
qed


text \<open>Since we now studied eps-trans automata, we can use them to have another normalization of nfa_multi's\<close>
text \<open>Transformation of finite automata with multiple initial states to a eps-NFA with only one initial state\<close>
definition normalize_nfa_eps :: "('s, 'a) nfa_multi \<Rightarrow> (('s + unit), ('a + unit)) automaton" where
  "normalize_nfa_eps \<A> = Automaton
    ((image Inl (states_multi \<A>)) \<union> {Inr()})
    (image Inl (alphabet_multi \<A>) \<union> {Inr()})
    ((image (\<lambda>(s1, a, s2) . (Inl s1, Inl a, Inl s2)) (transitions_multi \<A>)) \<union> {(Inr(), Inr(), Inl s) | s . s \<in> initial_states_multi \<A>})
    (Inr())
    (image Inl (accepting_states_multi \<A>))"

proposition normalize_preserves_well_defined_eps:
  assumes "auto_well_defined_multi \<A>"
  shows "auto_well_defined (normalize_nfa_eps \<A>)"
  using assms unfolding normalize_nfa_eps_def auto_well_defined_multi_def auto_well_defined_def by auto

corollary language_well_def_normalize_eps_multi_auto:
  assumes "auto_well_defined_multi \<A>"
  shows "language_well_defined (language_auto (normalize_nfa_eps \<A>)) (alphabet (normalize_nfa_eps \<A>))"
  using normalize_preserves_well_defined_eps assms automata_language_are_well_defined by blast

definition run_transformation_eps :: "'s run \<Rightarrow> ('s + unit) run" where "run_transformation_eps run = Inr() # map Inl run"

definition word_transformation_eps :: "'a word \<Rightarrow> ('a + unit) word" where "word_transformation_eps word = Inr() # map Inl word"

lemma word_transformation_snoc: "word_transformation_eps word = word' \<Longrightarrow> word_transformation_eps (word @ [a]) = word' @ [Inl a]"
  unfolding word_transformation_eps_def by (induction word) auto

lemma run_transformation_eps_i:
  assumes "i > 0 \<and> i < length run"
  shows "(run_transformation_eps run) ! i = Inl (run ! (i - 1)) \<and> (run_transformation_eps run) ! (i + 1) = Inl (run ! i)"
proof - 
  have len: "length (run_transformation_eps run) = length run + 1" using assms unfolding run_transformation_eps_def by auto
  thus ?thesis using assms unfolding run_transformation_eps_def by force
qed

lemma run_transformation_eps_i_spezial:
  assumes "i < length run"
  shows "(run_transformation_eps run) ! (i + 1) = Inl (run ! i)"
proof - 
  have len: "length (run_transformation_eps run) = length run + 1" using assms unfolding run_transformation_eps_def by auto
  thus ?thesis using assms unfolding run_transformation_eps_def by force
qed

lemma word_transformation_eps_i:
  assumes "i > 0 \<and> i < length word + 1"
  shows "(word_transformation_eps word) ! i = Inl (word ! (i - 1))"
proof - 
  have len: "length (word_transformation_eps word) = length word + 1" using assms unfolding word_transformation_eps_def by auto
  thus ?thesis using assms unfolding word_transformation_eps_def by force
qed

proposition run_transformation_eps_left:
  assumes "auto_well_defined_multi \<A>" "run_well_defined_multi run \<A> word"
  shows "run_well_defined (run_transformation_eps run) (normalize_nfa_eps \<A>) (word_transformation_eps word)"
proof - 
  have "length run > 0 \<and> length run = length word + 1" using assms unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by force
  hence length: "length (run_transformation_eps run) = length run + 1 \<and> length (run_transformation_eps run) = length (word_transformation_eps word) + 1" unfolding run_transformation_eps_def word_transformation_eps_def by auto
  have "(run_transformation_eps run) ! 0 = initial_state (normalize_nfa_eps \<A>)" using assms unfolding run_transformation_eps_def normalize_nfa_eps_def by auto
  hence init: "(run_transformation_eps run) ! 0 = initial_state (normalize_nfa_eps \<A>) \<and> initial_state (normalize_nfa_eps \<A>) \<in> states (normalize_nfa_eps \<A>)" using assms normalize_preserves_well_defined_eps unfolding auto_well_defined_def by blast
  have "(\<forall> i < length (run_transformation_eps run) - 1 . ((run_transformation_eps run) ! i, (word_transformation_eps word) ! i, (run_transformation_eps run) ! (i + 1)) \<in> transitions (normalize_nfa_eps \<A>))"
  proof -
    {
      fix i assume assm: "i < length (run_transformation_eps run) - 1"

      hence "((run_transformation_eps run) ! i, (word_transformation_eps word) ! i, (run_transformation_eps run) ! (i + 1)) \<in> transitions (normalize_nfa_eps \<A>)"
      proof(cases i)
        case 0
        hence len: "i < length run" using assm length by auto
        have init: "run ! 0 \<in> initial_states_multi \<A>" using assms unfolding run_well_defined_multi_def by auto
        have word: "(word_transformation_eps word) ! 0 = Inr()" unfolding word_transformation_eps_def by auto
        have "(run_transformation_eps run) ! 0 = Inr()" unfolding run_transformation_eps_def by auto
        hence "(run_transformation_eps run) ! 0 = Inr() \<and> (run_transformation_eps run) ! 1 = Inl (run ! 0)" using len 0 run_transformation_eps_i_spezial by auto
        thus ?thesis using init 0 word unfolding normalize_nfa_eps_def by auto
      next
        case (Suc nat)
        hence len: "i < length run" using assm length by auto
        hence equi: "(run_transformation_eps run) ! i = Inl (run ! (i - 1)) \<and> (run_transformation_eps run) ! (i + 1) = Inl (run ! i)" using Suc run_transformation_eps_i by blast 
        have "length run = length word + 1" using assms unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by blast
        hence "i < length word + 1" using len by auto
        hence word: "(word_transformation_eps word) ! i = Inl (word ! (i - 1))" using Suc word_transformation_eps_i by blast
        obtain j where j_def: "j = i - 1" using Suc by auto
        hence j: "j < length run - 1" using len Suc by linarith
        have "\<forall> j < length run - 1 . (run ! j, word ! j, run ! (j + 1)) \<in> transitions_multi \<A>" using assms unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by blast
        hence "(run ! j, word ! j, run ! (j + 1)) \<in> transitions_multi \<A>" using j by blast
        hence "(Inl (run ! j), Inl (word ! j), Inl (run ! (j + 1))) \<in> transitions (normalize_nfa_eps \<A>)" unfolding normalize_nfa_eps_def by force
        thus ?thesis using equi word j_def Suc by fastforce
      qed
    }
    thus ?thesis using length by argo
  qed
  thus ?thesis using length init assms unfolding run_well_defined_def pseudo_run_well_defined_def by fast
qed

lemma nfa_multi_run_eps_left_i:
  assumes "auto_well_defined_multi \<A>" "run_well_defined_multi run \<A> word"
  shows "run_well_defined (run_transformation_eps run) (normalize_nfa_eps \<A>) (word_transformation_eps word) \<and> Inl (last run) = last (run_transformation_eps run)"
proof - 
  have well_def: "run_well_defined (run_transformation_eps run) (normalize_nfa_eps \<A>) (word_transformation_eps word)" using assms run_transformation_eps_left by auto
  have len: "length run > 0" using assms unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by simp
  have len_equi: "length run + 1 = length (run_transformation_eps run)" unfolding run_transformation_eps_def by auto
  hence ge1: "length (run_transformation_eps run) > 1" using len by linarith
  hence "length (run_transformation_eps run) - 1 = length run" using len_equi by auto
  hence len_equi2: "length (run_transformation_eps run) - 2 = length run - 1" by force
  hence "length (run_transformation_eps run) - 2 < length run" using ge1 len_equi by linarith
  hence "(run_transformation_eps run) ! (length (run_transformation_eps run) - 2 + 1) = Inl (run ! (length (run_transformation_eps run) - 2))" using run_transformation_eps_i_spezial by blast
  hence "(run_transformation_eps run) ! (length (run_transformation_eps run) - 1) = Inl (run ! (length (run_transformation_eps run) - 2))" using ge1 simple_math by metis
  hence equi: "(run_transformation_eps run) ! (length (run_transformation_eps run) - 1) = Inl (run ! (length run - 1))" using len_equi2 by argo
  have "run \<noteq> [] \<and> run_transformation_eps run \<noteq> []" using len ge1 by force
  hence "last run = run ! (length run - 1) \<and> last (run_transformation_eps run) = (run_transformation_eps run) ! (length (run_transformation_eps run) - 1)" using list_properties_not_empty len by metis
  hence "Inl (last run) = last (run_transformation_eps run)" using equi by argo
  thus ?thesis using well_def assms by auto
qed

lemma nfa_multi_language_eps_left:
  assumes "auto_well_defined_multi \<A>"
  shows "image word_transformation_eps (language_auto_multi \<A>) \<subseteq> language_auto (normalize_nfa_eps \<A>)"
proof -
  let ?\<A> = "normalize_nfa_eps \<A>"
  {
    fix word assume "word \<in> language_auto_multi \<A>"
    then obtain run where "run_accepting_multi run \<A> word" unfolding language_auto_multi_def by auto
    hence run: "run_well_defined_multi run \<A> word \<and> last run \<in> accepting_states_multi \<A>" unfolding run_accepting_multi_def by auto
    have len: "length run \<ge> 1" using run unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by auto
    hence "\<exists> Run . run_well_defined Run ?\<A> (word_transformation_eps word) \<and> last Run \<in> accepting_states ?\<A>"
    proof - 
      have well_def: "run_well_defined (run_transformation_eps run) ?\<A> (word_transformation_eps word) \<and> Inl (last run) = last (run_transformation_eps run)" using run assms nfa_multi_run_eps_left_i by auto
      have "Inl (last run) \<in> accepting_states ?\<A>" using run unfolding normalize_nfa_eps_def by auto
      thus ?thesis using well_def by auto
    qed
    hence "(word_transformation_eps word) \<in> language_auto ?\<A>" unfolding language_auto_def run_accepting_def by auto
  }
  thus ?thesis by auto
qed

lemma nfa_multi_run_eps_eval_tl:
  assumes "auto_well_defined_multi \<A>" "run_well_defined run (normalize_nfa_eps \<A>) word"
  shows "Inr() \<notin> set (tl run)"
proof(rule ccontr)
  assume "\<not> Inr() \<notin> set (tl run)"
  hence "Inr() \<in> set (tl run)" by auto
  then obtain j where "(tl run) ! j = Inr() \<and> j < length (tl run)" using assms in_set_conv_nth by metis
  hence "(tl run) ! j = Inr() \<and> j < length run - 1" by auto
  hence j: "run ! (j + 1) = Inr() \<and> j < length run - 1" using j_pos_tl by metis
  have "\<forall> i < length run - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions (normalize_nfa_eps \<A>)" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  hence "(run ! j, word ! j, Inr()) \<in> transitions (normalize_nfa_eps \<A>)" using j by metis
  thus False unfolding normalize_nfa_eps_def by auto
qed

lemma nfa_multi_word_eps_eval_tl:
  assumes "auto_well_defined_multi \<A>" "run_well_defined run (normalize_nfa_eps \<A>) word"
  shows "Inr() \<notin> set (tl word)"
proof(rule ccontr)
  assume "\<not> Inr() \<notin> set (tl word)"
  hence not_in_set: "Inr() \<in> set (tl word)" by auto
  have len: "length word + 1 = length run" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  then obtain j where "(tl word) ! j = Inr() \<and> j < length (tl word)" using assms not_in_set in_set_conv_nth by metis
  hence "(tl word) ! j = Inr() \<and> j < length word - 1" by force
  hence j: "word ! (j + 1) = Inr() \<and> j < length word - 1" using j_pos_tl by metis
  hence j_le: "j < length run - 1 - 1" using len by force
  hence j_le2: "j < length run - 1" by linarith
  have "\<forall> i < length run - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions (normalize_nfa_eps \<A>)" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence "(run ! (j + 1), Inr(), run ! (j + 1 + 1)) \<in> transitions (normalize_nfa_eps \<A>)" using j_le j less_diff_conv by metis
  hence "run ! (j + 1) = Inr()" unfolding normalize_nfa_eps_def by auto
  hence "(tl run) ! j = Inr()" using j_pos_tl len j_le2 by metis
  hence "Inr() \<in> set (tl run)" using j_le2 length_tl nth_mem by metis
  thus False using assms nfa_multi_run_eps_eval_tl by blast
qed

proposition run_transformation_eps_right_base:
  assumes "auto_well_defined_multi \<A>" "run_well_defined run (normalize_nfa_eps \<A>) []" 
  shows "last run \<notin> accepting_states (normalize_nfa_eps \<A>)"
proof - 
  let ?\<A> = "normalize_nfa_eps \<A>"
  have "length run = 1 \<and> run ! 0 = Inr()" using assms unfolding run_well_defined_def pseudo_run_well_defined_def normalize_nfa_eps_def by auto
  hence "run = [Inr()]" using list_with_one_element by metis
  thus ?thesis unfolding normalize_nfa_eps_def by auto
qed

proposition run_transformation_eps_right:
  assumes "auto_well_defined_multi \<A>"
  shows "run_well_defined run (normalize_nfa_eps \<A>) (word @ [a]) \<Longrightarrow> \<exists> run' word' . run_well_defined_multi run' \<A> word' \<and> Inl (last run') = last run \<and> word_transformation_eps word' = word @ [a]"
proof(induction word arbitrary: run a rule: rev_induct)
  case Nil
  let ?\<A> = "normalize_nfa_eps \<A>"
  have well_def: "auto_well_defined ?\<A>" using assms normalize_preserves_well_defined_eps by auto
  hence init: "run ! 0 = Inr()" using Nil unfolding run_well_defined_def pseudo_run_well_defined_def normalize_nfa_eps_def by force
  have "(run ! 0, [a] ! 0, run ! 1) \<in> transitions ?\<A>" using Nil unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce
  hence trans: "(Inr(), [a] ! 0, run ! 1) \<in> transitions ?\<A>" using init by auto
  hence a: "a = Inr()" unfolding normalize_nfa_eps_def by auto
  hence "\<exists> s . s \<in> initial_states_multi \<A> \<and> (Inr(), Inr(), Inl s) \<in> transitions ?\<A> \<and> (run ! 1) = Inl s" using trans unfolding normalize_nfa_eps_def by auto
  then obtain s where "s \<in> initial_states_multi \<A> \<and> (Inr(), Inr(), Inl s) \<in> transitions ?\<A> \<and> (run ! 1) = Inl s" by blast
  hence "s \<in> initial_states_multi \<A> \<and> (Inr(), Inr(), Inl s) \<in> transitions ?\<A> \<and> (run ! 1) = Inl s \<and> s \<in> states_multi \<A>" using assms unfolding auto_well_defined_multi_def by fast
  hence run: "run_well_defined_multi [s] \<A> [] \<and> (run ! 1) = Inl (last [s])" unfolding run_well_defined_multi_def pseudo_run_well_defined_multi_def by auto
  have word: "word_transformation_eps [] = [Inr()]" unfolding word_transformation_eps_def by auto
  have "length run = 2 \<and> run \<noteq> []" using Nil unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence "last run = run ! 1" using list_properties_not_empty by fastforce
  hence "run_well_defined_multi [s] \<A> [] \<and> last run = Inl (last [s]) \<and> word_transformation_eps [] = [a]" using run word a by auto
  thus ?case using Nil by force
next
  let ?\<A> = "normalize_nfa_eps \<A>"
  have well_def: "auto_well_defined ?\<A>" using assms normalize_preserves_well_defined_eps by auto
  case (snoc a' word)
  hence "run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain run' where "run = run' @ [last run]" using append_butlast_last_id by metis
  hence trans: "run_well_defined run' ?\<A> (word @ [a']) \<and> (last run', a, last run) \<in> transitions ?\<A>" using prun_well_defined_extension_snoc snoc well_def unfolding run_well_defined_def by metis
  hence "\<exists>run'' word'' . run_well_defined_multi run'' \<A> word'' \<and> Inl (last run'') = last run' \<and> word_transformation_eps word'' = word @ [a']" using snoc by blast
  then obtain run'' word'' where obtained_run: "run_well_defined_multi run'' \<A> word'' \<and> Inl (last run'') = last run' \<and> word_transformation_eps word'' = word @ [a'] \<and> (last run', a, last run) \<in> transitions ?\<A>" using trans by blast
  hence "\<exists> s' . Inl s' = last run" unfolding normalize_nfa_eps_def by auto
  then obtain s' where s': "Inl s' = last run" by auto
  have "Inr() \<notin> set (tl ((word @ [a']) @ [a]))" using assms snoc nfa_multi_word_eps_eval_tl by blast
  hence "a \<noteq> Inr()" using a_in_set_tl by fast
  then obtain b where b: "Inl b = a" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
  hence "run_well_defined_multi run'' \<A> word'' \<and> (last run'', b, s') \<in> transitions_multi \<A>" using s' obtained_run unfolding normalize_nfa_eps_def by auto
  hence existence: "run_well_defined_multi (run'' @ [s']) \<A> (word'' @ [b]) \<and> Inl s' = last run" using s' run_well_defined_extension_snoc_multi assms by fast
  have "word_transformation_eps word'' = word @ [a']" using obtained_run by auto
  hence "word_transformation_eps (word'' @ [b]) = (word @ [a']) @ [a]" using b word_transformation_snoc by fast
  thus ?case using existence by force
qed

lemma nfa_multi_language_eps_right:
  assumes "auto_well_defined_multi \<A>"
  shows "language_auto (normalize_nfa_eps \<A>) \<subseteq> image word_transformation_eps (language_auto_multi \<A>)"
proof -
  let ?\<A> = "normalize_nfa_eps \<A>"
  {
    fix word assume "word \<in> language_auto ?\<A>"
    then obtain run where "run_accepting run ?\<A> word" unfolding language_auto_def by auto
    hence run: "run_well_defined run ?\<A> word \<and> last run \<in> accepting_states ?\<A>" unfolding run_accepting_def by blast
    hence "word \<noteq> []" using assms run_transformation_eps_right_base by auto
    then obtain word'' where "word = word'' @ [last word]" using append_butlast_last_id by metis
    then obtain run' word' where obtained_runs: "run_well_defined_multi run' \<A> word' \<and> Inl (last run') = last run \<and> word_transformation_eps word' = word" using assms run_transformation_eps_right run by metis
    hence "run_well_defined_multi run' \<A> word' \<and> Inl (last run') \<in> accepting_states ?\<A> \<and> word_transformation_eps word' = word" using run by auto
    hence "\<exists> run' . run_well_defined_multi run' \<A> word' \<and> last run' \<in> accepting_states_multi \<A> \<and> word_transformation_eps word' = word" unfolding normalize_nfa_eps_def by auto
    hence "word' \<in> language_auto_multi \<A> \<and> word_transformation_eps word' = word" unfolding language_auto_multi_def run_accepting_multi_def by fast
    hence "word \<in> image word_transformation_eps (language_auto_multi \<A>)" by auto
  }
  thus ?thesis by auto
qed

text \<open>Main result for the normalize_nfa_eps automaton: language equivalence\<close>
theorem normalize_nfa_eps_language_correctness:
  assumes "auto_well_defined_multi \<A>"
  shows "language_auto (normalize_nfa_eps \<A>) = image word_transformation_eps (language_auto_multi \<A>)"
  using assms nfa_multi_language_eps_left nfa_multi_language_eps_right by fast

text \<open>Now we can combine the normalize_nfa_eps with normalize_epsilon_nfa automaton:\<close>
lemma image_composition_language:
  assumes "auto_well_defined_multi \<A>"
  shows "language_auto_multi \<A> = image evaluate_eps_word (image word_transformation_eps (language_auto_multi \<A>))"
proof - 
  {
    fix word assume assm: "word \<in> language_auto_multi \<A>"
    hence "word_transformation_eps word = Inr() # map Inl word" unfolding word_transformation_eps_def by auto
    hence "evaluate_eps_word (word_transformation_eps word) = evaluate_eps_word (Inr() # map Inl word)" by auto
    hence "evaluate_eps_word (word_transformation_eps word) = evaluate_eps_word (map Inl word)" by auto
    hence equi: "evaluate_eps_word (word_transformation_eps word) = word" using inverse_evaluate_eps by auto
    have "evaluate_eps_word (word_transformation_eps word) \<in> image evaluate_eps_word (image word_transformation_eps (language_auto_multi \<A>))" using assm by blast
    hence "word \<in> image evaluate_eps_word (image word_transformation_eps (language_auto_multi \<A>))" using equi by argo
  }
  hence left: "language_auto_multi \<A> \<subseteq> image evaluate_eps_word (image word_transformation_eps (language_auto_multi \<A>))" by fast
  {
    fix word assume assm: "word \<in> image evaluate_eps_word (image word_transformation_eps (language_auto_multi \<A>))"
    then obtain word' where word': "word = evaluate_eps_word word' \<and> word' \<in> image word_transformation_eps (language_auto_multi \<A>)" by fast
    then obtain word'' where word'': "word' = word_transformation_eps word'' \<and> word'' \<in> language_auto_multi \<A>" by fast
    hence "word' = Inr() # map Inl word''" unfolding word_transformation_eps_def by auto
    hence "word = evaluate_eps_word (Inr() # map Inl word'')" using word' by auto
    hence "word = evaluate_eps_word (map Inl word'')" by auto
    hence "word = word''" using inverse_evaluate_eps by auto
    hence "word \<in> language_auto_multi \<A>" using word'' by auto 
  }
  hence right: "image evaluate_eps_word (image word_transformation_eps (language_auto_multi \<A>)) \<subseteq> language_auto_multi \<A> " by blast
  thus ?thesis using left right by fast
qed

corollary normalize_nfa_eps_free_language_correctness:
  assumes "auto_well_defined_multi \<A>"
  shows "eps_free_language (language_auto (normalize_nfa_eps \<A>)) = language_auto_multi \<A>"
  using assms normalize_nfa_eps_language_correctness image_composition_language unfolding eps_free_language_def by fast

text \<open>Main result for the normalize_nfa_eps combined with normalize_epsilon_nfa automaton: language equivalence\<close>
theorem word_transformation_eps_free_language:
  assumes "auto_well_defined_multi \<A>"
  shows "language_auto (normalize_epsilon_nfa (normalize_nfa_eps \<A>)) = language_auto_multi \<A>"
proof -
  {
    fix word assume "word \<in> language_auto (normalize_epsilon_nfa (normalize_nfa_eps \<A>))"
    hence "word \<in> eps_free_language (language_auto (normalize_nfa_eps \<A>))" using assms normalize_preserves_well_defined_eps normalize_epsilon_language_correctness by auto
    then obtain word' where "word = evaluate_eps_word word' \<and> word' \<in> language_auto (normalize_nfa_eps \<A>)" unfolding eps_free_language_def by blast
    hence "word = evaluate_eps_word word' \<and> word' \<in> image word_transformation_eps (language_auto_multi \<A>)" using assms normalize_nfa_eps_language_correctness by auto
    hence "word \<in> image evaluate_eps_word (image word_transformation_eps (language_auto_multi \<A>))" by auto
    hence "word \<in> language_auto_multi \<A>" using assms image_composition_language by blast
  }
  hence left: "language_auto (normalize_epsilon_nfa (normalize_nfa_eps \<A>)) \<subseteq> language_auto_multi \<A>" by auto
  {
    fix word assume "word \<in> language_auto_multi \<A>"
    hence "word \<in> image evaluate_eps_word (image word_transformation_eps (language_auto_multi \<A>))" using assms image_composition_language by blast
    then obtain word' where "word = evaluate_eps_word word' \<and> word' \<in> image word_transformation_eps (language_auto_multi \<A>)" by blast
    hence "word = evaluate_eps_word word' \<and> word' \<in> language_auto (normalize_nfa_eps \<A>)" using assms normalize_nfa_eps_language_correctness by fast
    hence "word \<in> eps_free_language (language_auto (normalize_nfa_eps \<A>))" unfolding eps_free_language_def by fast
    hence "word \<in> language_auto (normalize_epsilon_nfa (normalize_nfa_eps \<A>))" using assms normalize_preserves_well_defined_eps normalize_epsilon_language_correctness by fast
  }
  hence right: "language_auto_multi \<A> \<subseteq> language_auto (normalize_epsilon_nfa (normalize_nfa_eps \<A>))" by auto
  thus ?thesis using left right by blast
qed

end