theory omega_automata_concatenation

imports Main omega_automata_multi_union_inter_compDBA

begin

text \<open>Author: Benno Thalmann, last update: 11.2.2026, Addition to masterarbeit_benno_thalmann\<close>

text \<open>Concatenation omega_language\<close>
definition concatenation_omega_language :: "'a language \<Rightarrow> 'a omega_language \<Rightarrow> 'a omega_language" where "concatenation_omega_language L1 L2 = {merge_lists_fun word omega_word | word omega_word . word \<in> L1 \<and> omega_word \<in> L2}"

lemma merge_merge_list_fun: "merge_lists_fun list1 (merge_lists_fun list2 fun) = merge_lists_fun (list1 @ list2) fun"
proof -
  {
    fix i
    consider (case1) "i < length list1" | (case2) "i \<ge> length list1 \<and> i < length (list1 @ list2)" | (case3) "i \<ge> length (list1 @ list2)" by linarith
    hence "(merge_lists_fun (list1 @ list2) fun) i = (merge_lists_fun list1 (merge_lists_fun list2 fun)) i"
    proof cases
      case case1
      hence not_empty: "list1 \<noteq> []" by auto
      have ml: "(merge_lists_fun list1 (merge_lists_fun list2 fun)) i = list1 ! i" using case1 unfolding merge_lists_fun_def by simp
      have "(list1 @ list2) ! i = list1 ! i \<and> i < length (list1 @ list2)" using not_empty case1 by(simp add: nth_append)
      hence "(merge_lists_fun (list1 @ list2) fun) i = list1 ! i" unfolding merge_lists_fun_def by auto
      thus ?thesis using ml by auto
    next
      case case2
      hence "merge_lists_fun (list1 @ list2) fun i = (list1 @ list2) ! i" unfolding merge_lists_fun_def by auto
      hence ml: "merge_lists_fun (list1 @ list2) fun i = list2 ! (i - length list1)" using case2 by (simp add: nth_append)
      have "(merge_lists_fun list1 (merge_lists_fun list2 fun)) i = (merge_lists_fun list2 fun) (i - length list1)" using case2 unfolding merge_lists_fun_def by auto
      hence "(merge_lists_fun list1 (merge_lists_fun list2 fun)) i = list2 ! (i - length list1)" using case2 unfolding merge_lists_fun_def by auto
      thus ?thesis using ml by auto
    next
      case case3 thus ?thesis unfolding merge_lists_fun_def by force
    qed
  }
  thus ?thesis by auto
qed

lemma conc_conc_omega_language: "concatenation_omega_language L1 (concatenation_omega_language L2 L3) = {merge_lists_fun (word1 @ word2) omega_word | word1 word2 omega_word . word1 \<in> L1 \<and> word2 \<in> L2 \<and> omega_word \<in> L3}"
proof -
  {
    fix omega_word assume "omega_word \<in> concatenation_omega_language L1 (concatenation_omega_language L2 L3)"
    then obtain word1 word2 where word: "omega_word = merge_lists_fun word1 word2 \<and> word1 \<in> L1 \<and> word2 \<in> concatenation_omega_language L2 L3" unfolding concatenation_omega_language_def by blast
    then obtain word3 word4 where "word2 = merge_lists_fun word3 word4 \<and> word3 \<in> L2 \<and> word4 \<in> L3" unfolding concatenation_omega_language_def by blast
    hence "omega_word \<in> {merge_lists_fun (word1 @ word2) omega_word | word1 word2 omega_word . word1 \<in> L1 \<and> word2 \<in> L2 \<and> omega_word \<in> L3}" using word merge_merge_list_fun by fast
  }
  hence sub: "concatenation_omega_language L1 (concatenation_omega_language L2 L3) \<subseteq> {merge_lists_fun (word1 @ word2) omega_word | word1 word2 omega_word . word1 \<in> L1 \<and> word2 \<in> L2 \<and> omega_word \<in> L3}" by blast
  {
    fix omega_word assume "omega_word \<in> {merge_lists_fun (word1 @ word2) omega_word | word1 word2 omega_word . word1 \<in> L1 \<and> word2 \<in> L2 \<and> omega_word \<in> L3}"
    then obtain word1 word2 word3 where word: "omega_word = merge_lists_fun (word1 @ word2) word3 \<and> word1 \<in> L1 \<and> word2 \<in> L2 \<and> word3 \<in> L3" by blast
    hence "omega_word = merge_lists_fun word1 (merge_lists_fun word2 word3)" using merge_merge_list_fun by metis
    hence "omega_word \<in> concatenation_omega_language L1 (concatenation_omega_language L2 L3)" using word unfolding concatenation_omega_language_def by blast
  }  
  thus ?thesis using sub by fast
qed

lemma merge_list_well_def:
  assumes "word_well_defined word \<Sigma>1" "omega_word_well_defined omega_word \<Sigma>2"
  shows "omega_word_well_defined (merge_lists_fun word omega_word) (\<Sigma>1 \<union> \<Sigma>2)"
  using assms unfolding word_well_defined_def omega_word_well_defined_def merge_lists_fun_def by auto

proposition conc_omega_language_well_defined:
  assumes "language_well_defined L1 \<Sigma>1" "omega_language_well_defined L2 \<Sigma>2"
  shows "omega_language_well_defined (concatenation_omega_language L1 L2) (\<Sigma>1 \<union> \<Sigma>2)"
  using assms merge_list_well_def unfolding language_well_defined_def omega_language_well_defined_def concatenation_omega_language_def by blast




text \<open>Concatenation omega automaton of two automata\<close>
definition concatenation_omega_automaton :: "('s, 'a) automaton \<Rightarrow> ('s, 'a) automaton \<Rightarrow> ('s \<times> nat, 'a) nfa_multi" where
  "concatenation_omega_automaton \<A>1 \<A>2 = NFA_multi
    ({(s, 1) | s . s \<in> states \<A>1} \<union> {(s, 2) | s . s \<in> states \<A>2})
    (alphabet \<A>1 \<union> alphabet \<A>2)
    ({((s1, 1), a, (s2, 1)) | s1 s2 a . (s1, a, s2) \<in> transitions \<A>1} \<union> {((s1, 2), a, (s2, 2)) | s1 s2 a . (s1, a, s2) \<in> transitions \<A>2} \<union> {((s1, 1), a, (initial_state \<A>2, 2)) | s1 s2 a . (s1, a, s2) \<in> transitions \<A>1 \<and> s2 \<in> accepting_states \<A>1})
    (if (initial_state \<A>1 \<notin> accepting_states \<A>1) then {(initial_state \<A>1, 1)} else {(initial_state \<A>1, 1), (initial_state \<A>2, 2)})
    {(s, 2) | s . s \<in> accepting_states \<A>2}"

lemma initial_state_of_conc_omega_auto:
  assumes "s \<in> initial_states_multi (concatenation_omega_automaton \<A>1 \<A>2)"
  shows "s = (initial_state \<A>1, 1) \<or> s = (initial_state \<A>2, 2)"
proof - 
  consider (case1) "initial_state \<A>1 \<notin> accepting_states \<A>1" | (case2) "initial_state \<A>1 \<in> accepting_states \<A>1" by blast
  thus ?thesis
  proof cases
    case case1 thus ?thesis using assms unfolding concatenation_omega_automaton_def by auto
  next
    case case2 thus ?thesis using assms unfolding concatenation_omega_automaton_def by auto
  qed
qed

proposition concatenation_omega_alphabet: "alphabet_multi (concatenation_omega_automaton \<A>1 \<A>2) = alphabet \<A>1 \<union> alphabet \<A>2"
  unfolding concatenation_omega_automaton_def by force

proposition concatenation_omega_automaton_auto_well_defined:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "auto_well_defined_multi (concatenation_omega_automaton \<A>1 \<A>2)"
proof -
  let ?\<A> = "(concatenation_omega_automaton \<A>1 \<A>2)"
  have fin_s: "finite (states_multi ?\<A>)" using assms unfolding concatenation_omega_automaton_def auto_well_defined_def by auto
  have fin_a: "finite (alphabet_multi ?\<A>)" using assms unfolding concatenation_omega_automaton_def auto_well_defined_def by simp
  have init: "initial_states_multi ?\<A> \<subseteq> states_multi ?\<A>" using assms unfolding concatenation_omega_automaton_def auto_well_defined_def by auto
  have trans: "\<forall> (s1, a, s2) \<in> transitions_multi ?\<A> . s1 \<in> states_multi ?\<A> \<and> a \<in> alphabet_multi ?\<A> \<and> s2 \<in> states_multi ?\<A>" using assms unfolding concatenation_omega_automaton_def auto_well_defined_def by fastforce
  have "accepting_states_multi ?\<A> \<subseteq> states_multi ?\<A>" using assms unfolding concatenation_omega_automaton_def auto_well_defined_def by fastforce
  thus ?thesis using fin_s fin_a init trans unfolding auto_well_defined_multi_def by blast
qed

corollary language_well_def_cont_omega_auto:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "omega_language_well_defined (omega_language_auto_multi (concatenation_omega_automaton \<A>1 \<A>2)) (alphabet_multi (concatenation_omega_automaton \<A>1 \<A>2))"
  using concatenation_omega_automaton_auto_well_defined assms automata_omega_language_are_well_defined_multi by blast

theorem merged_run_is_accepting:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "run_accepting run \<A>1 word" "omega_run_accepting omega_run \<A>2 omega_word"
  shows "omega_run_accepting_multi (merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) (concatenation_omega_automaton \<A>1 \<A>2) (merge_lists_fun word omega_word)"
proof(cases word)
  case Nil
  hence "run = [initial_state \<A>1] \<and> last run \<in> accepting_states \<A>1" using assms list_with_one_element unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by fastforce
  hence props: "initial_state \<A>1 \<in> accepting_states \<A>1 \<and> butlast run = []" by auto
  hence equi: "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) = (cross_renaming_iso 2) \<circ> omega_run" unfolding merge_lists_fun_def by force
  have start: "(initial_state \<A>2, 2) \<in> initial_states_multi (concatenation_omega_automaton \<A>1 \<A>2)"using props unfolding concatenation_omega_automaton_def by force
  have "omega_run 0 = initial_state \<A>2" using assms unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
  hence init: "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) 0 = (initial_state \<A>2, 2) \<and> (initial_state \<A>2, 2) \<in> initial_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using equi start unfolding cross_renaming_iso_def concatenation_omega_automaton_def by simp
  have "auto_well_defined_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms concatenation_omega_automaton_auto_well_defined by blast
  hence in_states: "(initial_state \<A>2, 2) \<in> states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using start unfolding auto_well_defined_multi_def by fast
  have word_merge: "(merge_lists_fun word omega_word) = omega_word" using Nil unfolding merge_lists_fun_def by simp
  {
    fix i
    have "(omega_run i, omega_word i, omega_run (i + 1)) \<in> transitions \<A>2" using assms unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
    hence "(((cross_renaming_iso 2) \<circ> omega_run) i, omega_word i, ((cross_renaming_iso 2) \<circ> omega_run) (i + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" unfolding cross_renaming_iso_def concatenation_omega_automaton_def by simp
  }
  hence "\<forall> i . (((cross_renaming_iso 2) \<circ> omega_run) i, omega_word i, ((cross_renaming_iso 2) \<circ> omega_run) (i + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" by blast
  hence omega_run: "omega_run_well_defined_multi (merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) (concatenation_omega_automaton \<A>1 \<A>2) (merge_lists_fun word omega_word)" using word_merge equi init in_states unfolding omega_pseudo_run_well_defined_multi_def omega_run_well_defined_multi_def by presburger
  have "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>2" using assms unfolding omega_run_accepting_def by blast
  hence "\<forall> n . \<exists> N > n . ((cross_renaming_iso 2) \<circ> omega_run) N \<in> accepting_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" unfolding cross_renaming_iso_def concatenation_omega_automaton_def by simp
  hence "\<forall> n . \<exists> N > n . (merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) N \<in> accepting_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using equi by simp
  thus ?thesis using omega_run unfolding omega_run_accepting_multi_def by blast
next
  case (Cons a as)
  hence not_empty: "word \<noteq> []" by blast
  have le: "run ! 0 = initial_state \<A>1 \<and> length run = length word + 1" using assms unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by blast
  hence len: "run ! 0 = initial_state \<A>1 \<and> length run > 1" using not_empty by simp
  hence "butlast run ! 0 = initial_state \<A>1" using length_butlast nth_butlast zero_less_diff by metis
  hence run0: "butlast run ! 0 = initial_state \<A>1 \<and> initial_state \<A>1 \<in> states \<A>1" using assms unfolding auto_well_defined_def by blast
  have not_empty_butlast: "length (butlast run) > 0" using len by simp
  hence "(map (cross_renaming_iso 1) (butlast run)) ! 0 = (initial_state \<A>1, 1)" using run0 nth_map unfolding cross_renaming_iso_def by metis
  hence "(map (cross_renaming_iso 1) (butlast run)) ! 0 = (initial_state \<A>1, 1) \<and> (initial_state \<A>1, 1) \<in> initial_states_multi (concatenation_omega_automaton \<A>1 \<A>2) \<and> (initial_state \<A>1, 1) \<in> states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using run0 unfolding concatenation_omega_automaton_def cross_renaming_iso_def by force
  hence init: "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) 0 = (initial_state \<A>1, 1) \<and> (initial_state \<A>1, 1) \<in> initial_states_multi (concatenation_omega_automaton \<A>1 \<A>2) \<and> (initial_state \<A>1, 1) \<in> states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using not_empty_butlast unfolding merge_lists_fun_def by auto
  have length: "length (butlast run) = length word" using le by simp
  {
    fix i
    consider (case1) "i < length (butlast run) - 1" | (case2) "i = length (butlast run) - 1" | (case3) "i > length (butlast run) - 1" by linarith
    hence "((merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) i, (merge_lists_fun word omega_word) i, (merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) (i + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)"
    proof cases
      case case1
      hence equi_i: "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) i = (map (cross_renaming_iso 1) (butlast run)) ! i" unfolding merge_lists_fun_def by force
      have equi_i1: "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) (i + 1) = (map (cross_renaming_iso 1) (butlast run)) ! (i + 1)" using case1 unfolding merge_lists_fun_def by force
      have equi_w: "(merge_lists_fun word omega_word) i = word ! i" using length case1 unfolding merge_lists_fun_def by auto
      have equi_ri: "run ! i = (butlast run) ! i" using case1 add_lessD1 less_diff_conv nth_butlast by metis
      have equi_ri1: "run ! (i + 1) = (butlast run) ! (i + 1)" using case1 add_lessD1 less_diff_conv nth_butlast by metis
      have "(run ! i, word ! i, run ! (i + 1)) \<in> transitions \<A>1" using assms case1 unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by simp
      hence "((butlast run) ! i, word ! i, (butlast run) ! (i + 1)) \<in> transitions \<A>1" using equi_ri equi_ri1 by simp
      hence "(((butlast run) ! i, 1), word ! i, ((butlast run) ! (i + 1), 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" unfolding concatenation_omega_automaton_def by force
      thus ?thesis using equi_i equi_i1 equi_w nth_map case1 unfolding cross_renaming_iso_def by force
    next
      case case2
      hence le_i: "i < length run - 1" using len le by simp
      hence trans: "(run ! i, word ! i, run ! (i + 1)) \<in> transitions \<A>1 \<and> last run \<in> accepting_states \<A>1" using assms unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by blast
      have "run \<noteq> []" using le by force
      hence "last run = run ! (length run - 1)" using list_properties_not_empty by metis
      hence last: "run ! (i + 1) = last run" using case2 len le by simp
      have "run ! i = (butlast run) ! i" using nth_butlast le_i by force
      hence "((butlast run) ! i, word ! i, last run) \<in> transitions \<A>1 \<and> last run \<in> accepting_states \<A>1" using trans last by simp
      hence spez_trans: "(((butlast run) ! i, 1), word ! i, (initial_state \<A>2, 2)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" unfolding concatenation_omega_automaton_def by auto
      have "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) i = (map (cross_renaming_iso 1) (butlast run)) ! i" using le len case2 unfolding merge_lists_fun_def by auto
      hence equi_i: "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) i = ((butlast run) ! i, 1)" using nth_map case2 not_empty_butlast unfolding cross_renaming_iso_def by auto
      have "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) (i + 1) = ((cross_renaming_iso 2) \<circ> omega_run) 0" using le len case2 unfolding merge_lists_fun_def by auto
      hence equi_i1: "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) (i + 1) = (initial_state \<A>2, 2)" using assms unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def cross_renaming_iso_def by simp
      have "(merge_lists_fun word omega_word) i = word ! i" using length case2 le_i unfolding merge_lists_fun_def by auto     
      thus ?thesis using spez_trans equi_i equi_i1 by auto
    next
      case case3
      hence equi_i: "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) i = ((cross_renaming_iso 2) \<circ> omega_run) (i - length (butlast run))" unfolding merge_lists_fun_def by fastforce
      have ge: "i + 1 - length (butlast run) = i - length (butlast run) + 1" using Nat.diff_add_assoc2 add_leD2 case3 discrete le_add_diff_inverse2 not_empty_butlast by metis
      have "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) (i + 1) = ((cross_renaming_iso 2) \<circ> omega_run) (i + 1 - length (butlast run))" using case3 unfolding merge_lists_fun_def by auto
      hence equi_i1: "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) (i + 1) = ((cross_renaming_iso 2) \<circ> omega_run) (i - length (butlast run) + 1)" using ge by presburger
      have equi_w: "(merge_lists_fun word omega_word) i = omega_word (i - length (butlast run))" using length case3 unfolding merge_lists_fun_def by force
      hence "(omega_run (i - length (butlast run)), omega_word  (i - length (butlast run)), omega_run (i - length (butlast run) + 1)) \<in> transitions \<A>2" using assms case3 unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by simp
      hence "((omega_run (i - length (butlast run)), 2), omega_word  (i - length (butlast run)), (omega_run (i - length (butlast run) + 1), 2)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" unfolding concatenation_omega_automaton_def by force
      thus ?thesis using equi_i equi_i1 equi_w unfolding cross_renaming_iso_def by force
    qed
  }
  hence "\<forall> i . ((merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) i, (merge_lists_fun word omega_word) i, (merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) (i + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" by blast
  hence omega_run: "omega_run_well_defined_multi (merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) (concatenation_omega_automaton \<A>1 \<A>2) (merge_lists_fun word omega_word)" using init unfolding omega_pseudo_run_well_defined_multi_def omega_run_well_defined_multi_def by presburger
  have "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>2" using assms unfolding omega_run_accepting_def by blast
  hence acc: "\<forall> n . \<exists> N > n . ((cross_renaming_iso 2) \<circ> omega_run) N \<in> accepting_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" unfolding cross_renaming_iso_def concatenation_omega_automaton_def by simp
  {
    fix n
    obtain n' where n': "n' = n + length (butlast run)" by simp
    then obtain N where N: "N > n' \<and> ((cross_renaming_iso 2) \<circ> omega_run) N \<in> accepting_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using acc by blast
    hence "N > n + length (butlast run) \<and> ((cross_renaming_iso 2) \<circ> omega_run) N \<in> accepting_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using n' by blast
    then obtain k where k: "N = k - length (butlast run)" using diff_add_inverse by metis
    hence "k > n \<and> k > length (butlast run) \<and> ((cross_renaming_iso 2) \<circ> omega_run) N \<in> accepting_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using N n' by linarith
    hence props: "k > n \<and> k > length (butlast run) \<and> ((cross_renaming_iso 2) \<circ> omega_run) (k - length (butlast run)) \<in> accepting_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using k by blast
    hence "(merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) k = ((cross_renaming_iso 2) \<circ> omega_run) (k - length (butlast run))" unfolding merge_lists_fun_def by simp
    hence "\<exists> N > n . (merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run)) N \<in> accepting_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using props by metis
  }
  thus ?thesis using omega_run unfolding omega_run_accepting_multi_def by blast
qed

lemma init_in_acc:
  assumes "(initial_state \<A>2, 2) \<in> initial_states_multi (concatenation_omega_automaton \<A>1 \<A>2)"
  shows "initial_state \<A>1 \<in> accepting_states \<A>1"
proof(rule ccontr)
  assume "initial_state \<A>1 \<notin> accepting_states \<A>1"
  hence "initial_states_multi (concatenation_omega_automaton \<A>1 \<A>2) = {(initial_state \<A>1, 1)}" unfolding concatenation_omega_automaton_def by auto
  thus False using assms by simp
qed

definition proj_omega_run :: "('s \<times> nat) omega_run \<Rightarrow> 's omega_run" where "proj_omega_run omega_run = (\<lambda>n . fst (omega_run n))"

lemma inverse_cross_proj:
  assumes "omega_run_accepting_multi omega_run (concatenation_omega_automaton \<A>1 \<A>2) omega_word"
  shows "omega_run n = (s, 2) \<and> i \<ge> n \<Longrightarrow> ((cross_renaming_iso 2) \<circ> (proj_omega_run omega_run)) i = omega_run i"
proof(induction "i - n" arbitrary: i)
  case 0 thus ?case unfolding cross_renaming_iso_def proj_omega_run_def by force
next
  case (Suc x)
  hence "x = (i - 1) - n \<and> (i - 1) \<ge> n" by auto
  hence "((cross_renaming_iso 2) \<circ> (proj_omega_run omega_run)) (i - 1) = omega_run (i - 1)" using Suc by blast
  then obtain s1 where s1: "(s1, 2) = omega_run (i - 1)" using comp_apply unfolding proj_omega_run_def cross_renaming_iso_def by auto
  have "i - 1 + 1 = i" using Suc by force
  hence "(omega_run (i - 1), omega_word (i - 1), omega_run i) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_run_accepting_multi_def omega_run_well_defined_multi_def omega_pseudo_run_well_defined_multi_def by metis
  then obtain s2 where "omega_run i = (s2, 2)" using s1 unfolding concatenation_omega_automaton_def by force
  thus ?case unfolding cross_renaming_iso_def proj_omega_run_def by simp
qed

corollary inverse_0_cross_proj:
  assumes "omega_run_accepting_multi omega_run (concatenation_omega_automaton \<A>1 \<A>2) omega_word" "omega_run 0 = (s, 2)"
  shows "((cross_renaming_iso 2) \<circ> (proj_omega_run omega_run)) i = omega_run i"
proof - 
  have "\<forall> i :: nat . i \<ge> 0" by simp
  thus ?thesis using assms inverse_cross_proj by metis
qed

lemma existence_of_s2:
  assumes "omega_run_accepting_multi omega_run (concatenation_omega_automaton \<A>1 \<A>2) omega_word"
  shows "\<exists> i s . omega_run i = (s, 2)"
proof(rule ccontr)
  assume "\<not> (\<exists> i s . omega_run i = (s, 2))"
  hence forall: "\<forall> i s . omega_run i \<noteq> (s, 2)" by blast
  have acc: "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_run_accepting_multi_def by blast
  {
    fix n
    obtain N where "omega_run N \<in> accepting_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using acc by blast
    then obtain s where "omega_run N = (s, 2)" unfolding concatenation_omega_automaton_def by auto
    hence "\<exists> N s . omega_run N = (s, 2)" by blast
  }
  thus False using forall by blast
qed

theorem omega_run_implies_pre_run_well_def_multi:
  assumes "omega_pseudo_run_well_defined_multi omega_run \<A> s omega_word"
  shows "pseudo_run_well_defined_multi (pre_omega_run omega_run n) \<A> s (pre_omega_word omega_word n) \<and> last (pre_omega_run omega_run n) = omega_run n"
proof -
  have len: "length (pre_omega_run omega_run n) = length (pre_omega_word omega_word n) + 1" using pre_omega_run_length pre_omega_word_length Suc_eq_plus1 by metis
  hence "pre_omega_run omega_run n \<noteq> []" by force
  hence last: "last (pre_omega_run omega_run n) = (pre_omega_run omega_run n) ! (length (pre_omega_run omega_run n) - 1)" using list_properties_not_empty by metis
  have "length (pre_omega_run omega_run n) - 1 = n" by (simp add: pre_omega_run_length)
  hence last_last: "last (pre_omega_run omega_run n) = omega_run n" using last pre_omega_run_nth by auto
  have "omega_run 0 = s \<and> s \<in> states_multi \<A>" using assms unfolding omega_pseudo_run_well_defined_multi_def by simp
  hence init: "(pre_omega_run omega_run n) ! 0 = s \<and> s \<in> states_multi \<A>" using pre_omega_run_nth by blast
  have len_run: "length (pre_omega_run omega_run n) = Suc n" using pre_omega_run_length by blast
  hence i: "\<forall> i < length (pre_omega_run omega_run n) - 1 . (pre_omega_run omega_run n) ! i = omega_run i" by (simp add: pre_omega_run_nth)
  have i1: "\<forall> i < length (pre_omega_run omega_run n) - 1 . (pre_omega_run omega_run n) ! (i + 1) = omega_run (i + 1)" using len_run by (simp add: pre_omega_run_nth)
  have "\<forall> i < length (pre_omega_run omega_run n) - 1 . (pre_omega_word omega_word n) ! i = omega_word i" using len_run by (simp add: pre_omega_word_nth)
  hence "\<forall> i < length (pre_omega_run omega_run n) - 1 . ((pre_omega_run omega_run n) ! i, (pre_omega_word omega_word n) ! i, (pre_omega_run omega_run n) ! (i + 1)) \<in> transitions_multi \<A>" using assms i i1 unfolding omega_pseudo_run_well_defined_multi_def by auto
  thus ?thesis using len init last_last unfolding pseudo_run_well_defined_multi_def by blast
qed

lemma last_butlast:
  assumes "length (butlast run) > 0"
  shows "run ! (length run - 2) = last (butlast run)"
proof - 
  have "(butlast run) \<noteq> []" using assms by blast
  hence last: "last (butlast run) = (butlast run) ! (length (butlast run) - 1)" using list_properties_not_empty by metis
  have "length (butlast run) + 1 = length run" using assms by simp
  hence len: "length (butlast run) - 1 = length run - 2" using assms by linarith
  hence "last (butlast run) = (butlast run) ! (length run - 2)" using last by argo
  thus ?thesis using assms len diff_less nth_butlast zero_less_one by metis
qed

lemma merge_lists_omega_word:
  assumes "word = pre_omega_word omega_word i" "omega_word_de = (\<lambda>n . (omega_word (n + i)))"
  shows "omega_word = merge_lists_fun word omega_word_de"
  using assms unfolding merge_lists_fun_def pre_omega_word_def by force

theorem de_merged_run_is_accepting:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "omega_run_accepting_multi omega_run (concatenation_omega_automaton \<A>1 \<A>2) omega_word"
  shows "\<exists> word omega_word_de run omega_run_de . run_accepting run \<A>1 word \<and> omega_run_accepting omega_run_de \<A>2 omega_word_de \<and> omega_run = merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run_de) \<and> omega_word = merge_lists_fun word omega_word_de"
proof -
  have ini: "omega_run 0 \<in> initial_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_run_accepting_multi_def omega_run_well_defined_multi_def omega_pseudo_run_well_defined_multi_def by blast
  then consider (case1) "omega_run 0 = (initial_state \<A>1, 1)" | (case2) "omega_run 0 = (initial_state \<A>2, 2)" using initial_state_of_conc_omega_auto by blast
  thus ?thesis
  proof cases
    case case1
    obtain i where i: "i = (LEAST n . \<exists> s . omega_run n = (s, 2))" by simp
    have "\<exists> n . \<exists> s . omega_run n = (s, 2)" using assms existence_of_s2 by blast
    hence ex: "\<exists> s . omega_run (LEAST n . \<exists> s . omega_run n = (s, 2)) = (s, 2)" by (rule LeastI_ex) 
    hence ig0: "i > 0" using case1 gr0I i by fastforce
    obtain s_i where s_i: "omega_run i = (s_i, 2)" using i ex by blast
    have le_i: "\<forall> n < i . \<nexists> s . omega_run n = (s, 2)" using i not_less_Least by auto
    define run' where "run' = pre_omega_run omega_run i"
    define word where "word = pre_omega_word omega_word i"
    have len_Suc: "length run' = Suc i" using pre_omega_run_length unfolding run'_def by blast
    hence length_run_i: "length run' - 1 = i" by simp
    have length_word: "length word > 0" using ig0 pre_omega_word_length unfolding word_def by metis
    have pr: "pseudo_run_well_defined_multi run' (concatenation_omega_automaton \<A>1 \<A>2) (initial_state \<A>1, 1) word \<and> last run' = omega_run i" using omega_run_implies_pre_run_well_def_multi assms case1 unfolding omega_run_accepting_multi_def omega_run_well_defined_multi_def run'_def word_def by metis
    hence len_equi: "length run' = length word + 1" unfolding pseudo_run_well_defined_multi_def by blast
    hence len_run: "length run' > 1" using length_word by auto
    hence len_butlast: "length (butlast run') > 0 \<and> run' \<noteq> []" by auto
    hence equi: "run' ! (length run' - 2) = last (butlast run') \<and> run' ! (length run' - 1) = last run'" using last_butlast list_properties_not_empty by metis
    have last: "last run' = omega_run i \<and> run' ! (length run' - 1) = last run'" using equi length_run_i unfolding run'_def by (simp add: pre_omega_run_nth)
    have "auto_well_defined_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms concatenation_omega_automaton_auto_well_defined by blast
    hence in_states: "\<forall> i . omega_run i \<in> states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms well_def_implies_omega_prun_states_multi unfolding omega_run_accepting_multi_def omega_run_well_defined_multi_def omega_prun_states_multi_def by fast
    hence n_le_i: "\<forall> n < i . \<exists> s . omega_run n = (s, 1)" using le_i unfolding concatenation_omega_automaton_def by auto
    have partial_equi: "\<forall> i < length run' . run' ! i = omega_run i" using length_run_i unfolding run'_def by (simp add: pre_omega_run_nth)
    hence "\<forall> i < length run' - 1 . run' ! i \<in> states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using in_states by simp
    hence existence_s1: "\<forall> i < length run' - 1 . \<exists> s \<in> states \<A>1 . run' ! i = (s, 1)" using partial_equi length_run_i le_i unfolding concatenation_omega_automaton_def by auto
    then obtain s where s: "s \<in> states \<A>1 \<and> run' ! (length run' - 2) = (s, 1)" using len_run length_run_i len_Suc ig0 Suc_1 Suc_diff_1 diff_Suc_Suc lessI by metis
    have trans: "\<forall> i < length run' - 1 . (run' ! i, word ! i, run' ! (i + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" using pr unfolding pseudo_run_well_defined_multi_def by blast
    hence "(run' ! (length run' - 2), word ! (length run' - 2), run' ! ((length run' - 2) + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" using len_run by simp
    hence "(run' ! (length run' - 2), word ! (length run' - 2), run' ! (length run' - 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" using len_run simple_math by metis
    hence "((s, 1), word ! (length run' - 2), (s_i, 2)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" using s s_i equi last by argo
    hence s_i_init:"s_i = initial_state \<A>2 \<and> (\<exists> s_acc . (s, word ! (length run' - 2), s_acc) \<in> transitions \<A>1 \<and> s_acc \<in> accepting_states \<A>1)" unfolding concatenation_omega_automaton_def by force
    then obtain s_acc where s_acc: "(s, word ! (length run' - 2), s_acc) \<in> transitions \<A>1 \<and> s_acc \<in> accepting_states \<A>1" by blast
    {
      fix n assume "n < length run' - 2"
      hence assm: "n < length run' - 1 \<and> (n + 1) < length run' - 1" by linarith
      then obtain s1 s2 where s1s2: "run' ! n = (s1, 1) \<and> run' ! (n + 1) = (s2, 1)" using existence_s1 by blast
      hence "((s1, 1), word ! n, (s2, 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assm trans by metis
      hence "(s1, word ! n, s2) \<in> transitions \<A>1" unfolding concatenation_omega_automaton_def by force
      hence "(fst (run' ! n), word ! n, fst (run' ! (n + 1))) \<in> transitions \<A>1" using s1s2 by auto
    }
    hence fst_in_trans: "\<forall> i < length run' - 2 . (fst (run' ! i), word ! i, fst (run' ! (i + 1))) \<in> transitions \<A>1" by blast
    define run where "run = (map fst (butlast run')) @ [s_acc]"
    have "run ! 0 = (map fst (butlast run')) ! 0" using len_butlast length_map nth_append unfolding run_def by metis
    hence "run ! 0 = fst (run' ! 0)" using len_butlast nth_butlast nth_map by metis
    hence "run ! 0 = initial_state \<A>1" using partial_equi case1 by (simp add: ig0 len_Suc)
    hence init: "run ! 0 = initial_state \<A>1 \<and> initial_state \<A>1 \<in> states \<A>1" using assms unfolding auto_well_defined_def by blast
    have last: "last run \<in> accepting_states \<A>1" using s_acc unfolding run_def by auto
    have length: "length run = length word + 1" using len_equi unfolding run_def word_def by auto
    {
      fix n assume assm: "n < length run - 1"
      then consider (case3) "n < length run - 2" | (case4) "n = length run - 2" by linarith
      hence "(run ! n, word ! n, run ! (n + 1)) \<in> transitions \<A>1"
      proof cases
        case case3
        hence "n < length run' - 2" using len_equi length by fastforce
        hence n_trans: "(fst (run' ! n), word ! n, fst (run' ! (n + 1))) \<in> transitions \<A>1" using fst_in_trans by blast
        have "run ! n = (map fst (butlast run')) ! n" using case3 len_butlast assm len_equi length length_butlast length_map nth_append unfolding run_def by metis
        hence "run ! n = fst (butlast run' ! n)" using assm len_equi length by auto
        hence run_n: "run ! n = fst (run' ! n)" using assm nth_butlast unfolding run_def by fastforce
        have "length run = length run'" by (simp add: len_Suc run_def)
        hence n_less: "n < length (butlast run') - 1" using case3 by simp
        hence "run ! (n + 1) = (map fst (butlast run')) ! (n + 1)" using case3 length_map list_append_position4 unfolding run_def by metis
        hence "run ! (n + 1) = fst (butlast run' ! (n + 1))" using case3 assm len_equi length by simp
        hence "run ! (n + 1) = fst (run' ! (n + 1))" using less_diff_conv n_less nth_butlast by metis
        thus ?thesis using run_n n_trans by force
      next
        case case4
        hence "n = length run' - 2" using len_equi length by simp
        hence word_n: "word ! n = word ! (length run' - 2)" by blast
        have "run \<noteq> []" unfolding run_def by simp
        hence "run ! (n + 1) = last run" using list_properties_not_empty case4 simple_math len_equi len_run length by metis
        hence run_n1: "run ! (n + 1) = s_acc" unfolding run_def by simp
        have "length (map fst (butlast run')) > 0" using len_butlast by simp
        hence "length (butlast run) > 0" unfolding run_def by auto
        hence "run ! n = last (butlast run)" using last_butlast case4 by fast
        hence "run ! n = last (map fst (butlast run'))" unfolding run_def by simp
        hence "run ! n = s" using s equi fst_eqD last_map len_butlast length_greater_0_conv by metis
        thus ?thesis using s_acc word_n run_n1 by argo
      qed
    }
    hence run_acc: "run_accepting run \<A>1 word" using init last length unfolding pseudo_run_well_defined_def run_well_defined_def run_accepting_def by blast
    define omega_run_de where "omega_run_de = proj_omega_run (\<lambda>n . omega_run (n + i))"
    define omega_word_de where "omega_word_de = (\<lambda>n . omega_word (n + i))"
    {
      fix n
      have "n \<ge> i \<Longrightarrow> \<exists> s . omega_run n = (s, 2)"
      proof(induction "n - i" arbitrary: n)
        case 0 thus ?case using i s_i by simp
      next
        case (Suc x)
        then obtain t where t: "omega_run (n - 1) = (t, 2)" by fastforce
        obtain k where k: "k = n - 1" by simp
        have "(omega_run k, omega_word k, omega_run (k + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_run_accepting_multi_def omega_run_well_defined_multi_def omega_pseudo_run_well_defined_multi_def by blast
        hence "((t, 2), omega_word k, omega_run (k + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" using t k by argo
        hence "\<exists> t2 . omega_run (k + 1) = (t2, 2)" unfolding concatenation_omega_automaton_def by force
        thus ?case using k Suc ig0 by force
      qed
    }
    hence stay_2: "\<forall> n \<ge> i . \<exists> s . omega_run n = (s, 2)" by blast
    have "omega_run_de 0 = initial_state \<A>2" using s_i s_i_init unfolding omega_run_de_def proj_omega_run_def by simp
    hence init: "omega_run_de 0 = initial_state \<A>2 \<and> initial_state \<A>2 \<in> states \<A>2" using assms unfolding auto_well_defined_def by blast
    {
      fix n
      obtain t1 t2 where t1t2: "omega_run (n + i) = (t1, 2) \<and> omega_run (n + i + 1) = (t2, 2)" using stay_2 by force
      have equis: "omega_run_de n = fst (omega_run (n + i)) \<and> omega_word_de n = omega_word (n + i) \<and> omega_run_de (n + 1) = fst (omega_run (n + i + 1))" unfolding omega_run_de_def proj_omega_run_def omega_word_de_def by simp
      have "\<forall> n . (omega_run n, omega_word n, omega_run (n + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_run_accepting_multi_def omega_run_well_defined_multi_def omega_pseudo_run_well_defined_multi_def by blast
      hence "(omega_run (n + i), omega_word (n + i), omega_run (n + i + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" by blast
      hence "(omega_run_de n, omega_word_de n, omega_run_de (n + 1)) \<in> transitions \<A>2" using t1t2 equis unfolding concatenation_omega_automaton_def by simp
    }
    hence omega_run: "omega_run_well_defined omega_run_de \<A>2 omega_word_de" using init unfolding omega_pseudo_run_well_defined_def omega_run_well_defined_def by blast
    {
      fix n
      obtain k where k: "k = n + i + 1" by auto
      obtain N where N: "N > k \<and> omega_run N \<in> accepting_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_run_accepting_multi_def by blast
      hence "omega_run_de (N - i) = fst (omega_run N)" using k unfolding omega_run_de_def proj_omega_run_def by force
      hence "omega_run_de (N - i) \<in> accepting_states \<A>2" using N unfolding concatenation_omega_automaton_def by fastforce
      hence "\<exists> N > n . omega_run_de N \<in> accepting_states \<A>2" using k N add_lessD1 less_diff_conv by metis
    }
    hence "\<forall> n . \<exists> N > n . omega_run_de N \<in> accepting_states \<A>2" by blast
    hence omega_run_acc: "omega_run_accepting omega_run_de \<A>2 omega_word_de" using omega_run unfolding omega_run_accepting_def by blast
    have or_w: "omega_word = merge_lists_fun word omega_word_de" using merge_lists_omega_word unfolding word_def omega_word_de_def by force
    have length_but: "length (map (cross_renaming_iso 1) (butlast run)) = i" using len_equi length length_run_i by auto
    {
      fix n assume assm: "n < i"
      hence equi_n: "\<forall> n < i + 1 . run' ! n = omega_run n" using partial_equi length_run_i by auto
      have "length (butlast run') = length run' - 1" using length_butlast by blast
      hence len_b: "length (butlast run') = i" using length_run_i by auto
      hence "\<forall> n < i . (butlast run') ! n = run' ! n" using nth_butlast by blast
      hence eqiu: "\<forall> n < i . (butlast run') ! n = omega_run n" using equi_n by auto
      then obtain t where t: "(butlast run') ! n = (t, 1)" using n_le_i assm by auto
      have "butlast run = (map fst (butlast run'))" unfolding run_def by simp
      hence "butlast run ! n = t" using t len_b assm by simp
      hence "(cross_renaming_iso 1) ((butlast run) ! n) = (t, 1)" unfolding cross_renaming_iso_def by simp
      hence "(cross_renaming_iso 1) ((butlast run) ! n) = omega_run n" using t assm eqiu by auto
      hence "map (cross_renaming_iso 1) (butlast run) ! n = omega_run n" using len_b assm unfolding run_def by auto
    }
    hence run_b_equi: "\<forall> n < i . (map (cross_renaming_iso 1) (butlast run)) ! n = omega_run n" by blast
    have "\<forall> n \<ge> i . ((cross_renaming_iso 2) \<circ> (proj_omega_run omega_run)) n = omega_run n" using assms s_i inverse_cross_proj by metis
    hence "\<forall> n . ((cross_renaming_iso 2) \<circ> (proj_omega_run omega_run)) (n + i) = omega_run (n + i)" by simp
    hence "\<forall> n . ((cross_renaming_iso 2) \<circ> omega_run_de) n = omega_run (n + i)" unfolding cross_renaming_iso_def proj_omega_run_def omega_run_de_def by simp
    hence or_de: "omega_run = merge_lists_fun (map (cross_renaming_iso 1) (butlast run)) ((cross_renaming_iso 2) \<circ> omega_run_de)" using run_b_equi length_but unfolding merge_lists_fun_def by auto
    thus ?thesis using omega_run_acc run_acc or_de or_w by blast
  next
    case case2
    hence in_acc: "initial_state \<A>1 \<in> accepting_states \<A>1" using ini init_in_acc by auto
    have "initial_state \<A>1 \<in> states \<A>1" using assms unfolding auto_well_defined_def by blast
    hence run: "run_accepting [initial_state \<A>1] \<A>1 []" using in_acc unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by auto
    have init: "proj_omega_run omega_run 0 = initial_state \<A>2 \<and> initial_state \<A>2 \<in> states \<A>2" using case2 assms unfolding auto_well_defined_def proj_omega_run_def by auto
    {
      fix i
      have "\<exists> s . omega_run i = (s, 2) \<and> (proj_omega_run omega_run i, omega_word i, proj_omega_run omega_run (i + 1)) \<in> transitions \<A>2"
      proof(induction i)
        case 0
        have trans: "(omega_run 0, omega_word 0, omega_run (0 + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_run_accepting_multi_def omega_run_well_defined_multi_def omega_pseudo_run_well_defined_multi_def by blast
        then obtain s where "omega_run 1 = (s, 2) \<and> (initial_state \<A>2, omega_word 0, s) \<in> transitions \<A>2" using case2 unfolding concatenation_omega_automaton_def by auto
        thus ?case using trans case2 unfolding proj_omega_run_def by simp
      next
        case (Suc i)
        then obtain s1 where s1: "(s1, 2) = omega_run i \<and> (proj_omega_run omega_run i, omega_word i, proj_omega_run omega_run (i + 1)) \<in> transitions \<A>2" by auto
        have trans: "(omega_run i, omega_word i, omega_run (i + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_run_accepting_multi_def omega_run_well_defined_multi_def omega_pseudo_run_well_defined_multi_def by blast
        then obtain s2 where "omega_run (i + 1) = (s2, 2) \<and> (s1, omega_word i, s2) \<in> transitions \<A>2" using s1 unfolding concatenation_omega_automaton_def by force
        hence s2: "omega_run (Suc i) = (s2, 2) \<and> (s1, omega_word i, s2) \<in> transitions \<A>2" by simp
        have trans_suc: "(omega_run (Suc i), omega_word (Suc i), omega_run ((Suc i) + 1)) \<in> transitions_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_run_accepting_multi_def omega_run_well_defined_multi_def omega_pseudo_run_well_defined_multi_def by blast
        then obtain s3 where "omega_run ((Suc i) + 1) = (s3, 2) \<and> (s2, omega_word (Suc i), s3) \<in> transitions \<A>2" using s2 unfolding concatenation_omega_automaton_def by force
        thus ?case using trans_suc s2 unfolding proj_omega_run_def by simp
      qed
    }
    hence "\<forall> i . (proj_omega_run omega_run i, omega_word i, proj_omega_run omega_run (i + 1)) \<in> transitions \<A>2" by blast
    hence omega_run: "omega_run_well_defined (proj_omega_run omega_run) \<A>2 omega_word" using init unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
    have "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states_multi (concatenation_omega_automaton \<A>1 \<A>2)" using assms unfolding omega_run_accepting_multi_def by blast
    hence acc: "\<forall> n . \<exists> N > n . (proj_omega_run omega_run) N \<in> accepting_states \<A>2" unfolding proj_omega_run_def concatenation_omega_automaton_def by fastforce
    have or_de: "omega_run = merge_lists_fun (map (cross_renaming_iso 1) (butlast [initial_state \<A>1])) ((cross_renaming_iso 2) \<circ> (proj_omega_run omega_run))" using assms case2 inverse_0_cross_proj unfolding merge_lists_fun_def by fastforce
    have or_w: "omega_word = merge_lists_fun [] omega_word" unfolding merge_lists_fun_def by force    
    thus ?thesis using acc omega_run run or_de or_w unfolding omega_run_accepting_def by blast
  qed
qed

text \<open>Main result for the concatenation_omega_automaton: omega_language equivalence\<close>
theorem concatenation_omega_language_correctness:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "omega_language_auto_multi (concatenation_omega_automaton \<A>1 \<A>2) = concatenation_omega_language (language_auto \<A>1) (omega_language_auto \<A>2)"
proof - 
  {
    fix omega_word assume "omega_word \<in> omega_language_auto_multi (concatenation_omega_automaton \<A>1 \<A>2)"
    hence "omega_word \<in> concatenation_omega_language (language_auto \<A>1) (omega_language_auto \<A>2)" using assms de_merged_run_is_accepting unfolding omega_language_auto_multi_def concatenation_omega_language_def language_auto_def omega_language_auto_def by fast
  }
  hence "omega_language_auto_multi (concatenation_omega_automaton \<A>1 \<A>2) \<subseteq> concatenation_omega_language (language_auto \<A>1) (omega_language_auto \<A>2)" by blast
  thus ?thesis using merged_run_is_accepting assms unfolding omega_language_auto_multi_def concatenation_omega_language_def language_auto_def omega_language_auto_def by fast
qed

theorem conc_omega_main:
  assumes "auto_well_defined (\<A>1 :: ('r, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> conc_\<A> :: ('s \<times> nat, 'a) nfa_multi . auto_well_defined_multi conc_\<A> \<and> alphabet_multi conc_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> omega_language_auto_multi conc_\<A> = concatenation_omega_language (language_auto \<A>1) (omega_language_auto \<A>2)"
proof - 
  obtain \<A>3 :: "('s, 'a) automaton" where A3: "auto_well_defined \<A>3 \<and> alphabet \<A>3 = alphabet \<A>2 \<and> omega_language_auto \<A>3 = omega_language_auto \<A>2" using assms existence_soft_iso_auto_omega_lang by blast
  obtain \<A>4 :: "('s, 'a) automaton" where "auto_well_defined \<A>4 \<and> alphabet \<A>4 = alphabet \<A>1 \<and> language_auto \<A>4 = language_auto \<A>1" using assms existence_soft_iso_auto_lang by blast
  thus ?thesis using A3 concatenation_omega_language_correctness concatenation_omega_automaton_auto_well_defined concatenation_omega_alphabet by metis
qed

theorem existence_of_omega_conc_same_type:
  assumes "auto_well_defined (\<A>1 :: ('r, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> conc_\<A> :: ('s, 'a) automaton . auto_well_defined conc_\<A> \<and> alphabet conc_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> omega_language_auto conc_\<A> = concatenation_omega_language (language_auto \<A>1) (omega_language_auto \<A>2)"
proof - 
  have inf: "infinite (UNIV :: ('s \<times> nat) set)" using assms by (simp add: finite_prod)
  obtain conc_\<A> :: "('s \<times> nat, 'a) nfa_multi" where A: "auto_well_defined_multi conc_\<A> \<and> alphabet_multi conc_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> omega_language_auto_multi conc_\<A> = concatenation_omega_language (language_auto \<A>1) (omega_language_auto \<A>2)" using assms conc_omega_main by blast
  hence "\<exists> NFA_\<A> :: ('s \<times> nat, 'a) automaton . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = alphabet_multi conc_\<A> \<and> omega_language_auto NFA_\<A> = omega_language_auto_multi conc_\<A>" using inf existence_of_omega_nfa_same_type by blast
  thus ?thesis using assms existence_soft_iso_auto_omega_lang A by metis
qed

end