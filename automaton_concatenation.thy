theory automaton_concatenation

imports Main automaton_epsilon_transitions

begin

text \<open>Author: Benno Thalmann, last update: 12.1.2026, Addition to masterarbeit_benno_thalmann\<close>

text \<open>Concatenation language\<close>
definition concatenation_language :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where "concatenation_language L1 L2 = {word1 @ word2 | word1 word2 . word1 \<in> L1 \<and> word2 \<in> L2}"

lemma conc_conc_language: "concatenation_language (concatenation_language L1 L2) L3 = {word1 @ word2 @ word3 | word1 word2 word3 . word1 \<in> L1 \<and> word2 \<in> L2 \<and> word3 \<in> L3}"
proof -
  {
    fix word assume "word \<in> concatenation_language (concatenation_language L1 L2) L3"
    then obtain word4 word3 where word: "word = word4 @ word3 \<and> word4 \<in> {word1 @ word2 | word1 word2 . word1 \<in> L1 \<and> word2 \<in> L2} \<and> word3 \<in> L3" unfolding concatenation_language_def by blast
    then obtain word1 word2 where "word4 = word1 @ word2 \<and> word1 \<in> L1 \<and> word2 \<in> L2" by blast
    hence "word = word1 @ word2 @ word3 \<and>  word1 \<in> L1 \<and> word2 \<in> L2 \<and> word3 \<in> L3" using word by auto
    hence "word \<in> {word1 @ word2 @ word3 | word1 word2 word3 . word1 \<in> L1 \<and> word2 \<in> L2 \<and> word3 \<in> L3}" by blast
  }
  hence sub: "concatenation_language (concatenation_language L1 L2) L3 \<subseteq> {word1 @ word2 @ word3 | word1 word2 word3 . word1 \<in> L1 \<and> word2 \<in> L2 \<and> word3 \<in> L3}" by blast
  {
    fix word assume "word \<in> {word1 @ word2 @ word3 | word1 word2 word3 . word1 \<in> L1 \<and> word2 \<in> L2 \<and> word3 \<in> L3}"
    then obtain word1 word2 word3 where word: "word = word1 @ word2 @ word3 \<and> word1 \<in> L1 \<and> word2 \<in> L2 \<and> word3 \<in> L3" by blast
    then obtain word4 where "word4 = word1 @ word2 \<and> word4 \<in> concatenation_language L1 L2" unfolding concatenation_language_def by fast
    hence "word = word4 @ word3 \<and> word4 \<in> concatenation_language L1 L2 \<and> word3 \<in> L3" using word by auto
    hence "word \<in> concatenation_language (concatenation_language L1 L2) L3" unfolding concatenation_language_def by blast
  }  
  thus ?thesis using sub by fast
qed

corollary conc_language_assoziative: "concatenation_language (concatenation_language L1 L2) L3 = concatenation_language L1 (concatenation_language L2 L3)"
proof -
  have "concatenation_language (concatenation_language L1 L2) L3 = {word1 @ word2 @ word3 | word1 word2 word3 . word1 \<in> L1 \<and> word2 \<in> L2 \<and> word3 \<in> L3}" using conc_conc_language by blast
  hence "concatenation_language (concatenation_language L1 L2) L3 = {word1 @ word2 | word1 word2 . word1 \<in> L1 \<and> word2 \<in> concatenation_language L2 L3}" unfolding concatenation_language_def by auto
  thus ?thesis unfolding concatenation_language_def by argo
qed

proposition conc_language_well_defined:
  assumes "language_well_defined L1 \<Sigma>1" "language_well_defined L2 \<Sigma>2"
  shows "language_well_defined (concatenation_language L1 L2) (\<Sigma>1 \<union> \<Sigma>2)"
  using assms unfolding language_well_defined_def concatenation_language_def word_well_defined_def by fastforce




text \<open>Concatenation automaton of two automata\<close>
definition concatenation_automaton_helper :: "('s, 'a) automaton \<Rightarrow> ('s, 'a) automaton \<Rightarrow> ('s , 'a + unit) automaton" where
  "concatenation_automaton_helper \<A>1 \<A>2 = Automaton
    (states \<A>1 \<union> states \<A>2)
    ((image Inl (alphabet \<A>1 \<union> alphabet \<A>2)) \<union> {Inr()})
    ((image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions \<A>1)) \<union> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions \<A>2)) \<union> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states \<A>1 \<and> s2 = initial_state \<A>2})
    (initial_state \<A>1)
    (accepting_states \<A>2)"

lemma spezial_trans_concat_auto: "s1 \<in> accepting_states \<A>1 \<and> s2 = initial_state \<A>2 \<longleftrightarrow> (s1, Inr(), s2) \<in> transitions (concatenation_automaton_helper \<A>1 \<A>2)"
  unfolding concatenation_automaton_helper_def by auto

proposition concatenation_helper_auto_well_defined:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "auto_well_defined (concatenation_automaton_helper \<A>1 \<A>2)"
  using assms unfolding concatenation_automaton_helper_def auto_well_defined_def by auto

corollary language_well_def_concat_helper_multi_auto:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "language_well_defined (language_auto (concatenation_automaton_helper \<A>1 \<A>2)) (alphabet (concatenation_automaton_helper \<A>1 \<A>2))"
  using concatenation_helper_auto_well_defined assms automata_language_are_well_defined by blast

definition concatenation_automaton :: "('s, 'a) automaton \<Rightarrow> ('s, 'a) automaton \<Rightarrow> ('s \<times> nat , 'a + unit) automaton" where "concatenation_automaton \<A>1 \<A>2 = concatenation_automaton_helper (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"

proposition concatenation_alphabet: "alphabet (concatenation_automaton \<A>1 \<A>2) = (image Inl (alphabet \<A>1 \<union> alphabet \<A>2)) \<union> {Inr()}"
  unfolding concatenation_automaton_def concatenation_automaton_helper_def type_encode_automaton_def by force

proposition concatenation_auto_well_defined:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "auto_well_defined (concatenation_automaton \<A>1 \<A>2)"
  using assms cross_renaming_iso_automaton_auto_well_defined concatenation_helper_auto_well_defined unfolding concatenation_automaton_def by metis

corollary language_well_def_concatenation_auto:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "language_well_defined (language_auto (concatenation_automaton \<A>1 \<A>2)) (alphabet (concatenation_automaton \<A>1 \<A>2))"
  using concatenation_auto_well_defined assms automata_language_are_well_defined by blast

lemma normal_trans_concat_auto_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions (concatenation_automaton \<A>1 \<A>2)" "s1 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" "a \<noteq> Inr()"
  shows "s2 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
proof(rule ccontr)
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  assume "\<not> s2 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
  hence assm: "s2 \<notin> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" by auto
  have "auto_well_defined ?\<A>" using assms concatenation_auto_well_defined by auto
  hence "s2 \<in> states ?\<A>" using assms well_def_trans_components by fast
  hence in_states2: "s2 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assm unfolding concatenation_automaton_def concatenation_automaton_helper_def by force
  have well_def: "auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  have "transitions ?\<A> = (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))) \<union> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))) \<union> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)}" unfolding concatenation_automaton_def concatenation_automaton_helper_def by auto
  hence "(s1, a, s2) \<in> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))) \<union> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))) \<union> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)}" using assms by argo
  then consider (case1) "(s1, a, s2) \<in> image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))" | (case2) "(s1, a, s2) \<in> image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" | (case3) "(s1, a, s2) \<in> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)}" by blast
  thus False
  proof cases
    case case1 thus ?thesis using well_def well_def_trans_components assm by fast
  next
    case case2 thus ?thesis using well_def well_def_trans_components assms cross_renaming_intersection_empty by fast
  next
    case case3 thus ?thesis using assms by auto
  qed
qed

corollary normal_trans_concat_auto_A1_inv:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions (concatenation_automaton \<A>1 \<A>2)" "s1 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" "a \<noteq> Inr()" "Inl b = a"
  shows "(s1, b, s2) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
proof -
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  have well_def: "auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  have trans: "transitions ?\<A> = (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))) \<union> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))) \<union> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)}" unfolding concatenation_automaton_def concatenation_automaton_helper_def by auto
  have props: "s1 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> a \<noteq> Inr() \<and> s2 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms normal_trans_concat_auto_A1 by blast
  then obtain b where b: "Inl b = a" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
  hence "(s1, a, s2) \<in> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))) \<union> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))) \<union> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)}" using assms trans by argo
  then consider (case1) "(s1, a, s2) \<in> image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))" | (case2) "(s1, a, s2) \<in> image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" | (case3) "(s1, a, s2) \<in> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)}" by blast
  hence "(s1, a, s2) \<in> image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))"
  proof cases
    case case1 thus ?thesis using props by blast
  next
    case case2 thus ?thesis using well_def well_def_trans_components assms cross_renaming_intersection_empty by fast
  next
    case case3 thus ?thesis using props by auto
  qed
  thus ?thesis using b assms by fast
qed

lemma normal_trans_concat_auto_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions (concatenation_automaton \<A>1 \<A>2)" "s1 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  shows "s2 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
proof(rule ccontr)
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  assume "\<not> s2 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
  hence assm: "s2 \<notin> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" by auto
  have "auto_well_defined ?\<A>" using assms concatenation_auto_well_defined by auto
  hence "s2 \<in> states ?\<A>" using assms well_def_trans_components by fast
  hence in_states2: "s2 \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assm unfolding concatenation_automaton_def concatenation_automaton_helper_def by auto
  have well_def: "auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  have "transitions ?\<A> = (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))) \<union> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))) \<union> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)}" unfolding concatenation_automaton_def concatenation_automaton_helper_def by force
  hence "(s1, a, s2) \<in> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))) \<union> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))) \<union> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)}" using assms by argo
  then consider (case1) "(s1, a, s2) \<in> image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))" | (case2) "(s1, a, s2) \<in> image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" | (case3) "(s1, a, s2) \<in> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)}" by blast
  thus False
  proof cases
    case case1 thus ?thesis using well_def well_def_trans_components assms cross_renaming_intersection_empty by fast
  next
    case case2 thus ?thesis using well_def well_def_trans_components assm by fast
  next
  case case3 thus ?thesis using well_def assm unfolding auto_well_defined_def by blast
  qed
qed

corollary normal_trans_concat_auto_A2_inv:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "(s1, a, s2) \<in> transitions (concatenation_automaton \<A>1 \<A>2)" "s1 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" "a \<noteq> Inr()" "Inl b = a"
  shows "(s1, b, s2) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
proof -
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  have well_def: "auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  have trans: "transitions ?\<A> = (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))) \<union> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))) \<union> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)}" unfolding concatenation_automaton_def concatenation_automaton_helper_def by auto
  have props: "s1 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<and> a \<noteq> Inr() \<and> s2 \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms normal_trans_concat_auto_A2 by blast
  then obtain b where b: "Inl b = a" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
  hence "(s1, a, s2) \<in> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))) \<union> (image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))) \<union> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)}" using assms trans by argo
  then consider (case1) "(s1, a, s2) \<in> image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id))" | (case2) "(s1, a, s2) \<in> image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" | (case3) "(s1, a, s2) \<in> {(s1, Inr(), s2) | s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)}" by blast
  hence "(s1, a, s2) \<in> image (\<lambda>(s1, a, s2) . (s1, Inl a, s2)) (transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))"
  proof cases
    case case1 thus ?thesis using well_def well_def_trans_components assms cross_renaming_intersection_empty by fast
  next
    case case2 thus ?thesis using props by blast
  next
    case case3 thus ?thesis using props by blast
  qed
  thus ?thesis using b assms by fast
qed

definition run_cross_renaming_iso :: "nat \<Rightarrow> 's run \<Rightarrow> ('s \<times> nat) run" where "run_cross_renaming_iso n run = map (cross_renaming_iso n) run"

lemma last_run_cross_renaming_iso:
  assumes "run \<noteq> []"
  shows "(cross_renaming_iso n) (last run) = last (run_cross_renaming_iso n run)"
  using assms unfolding run_cross_renaming_iso_def by (simp add: last_map)

theorem concate_run_correct_left:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "run_accepting run1 \<A>1 word1" "run_accepting run2 \<A>2 word2"
  shows "run_accepting ((run_cross_renaming_iso 1 run1) @ (run_cross_renaming_iso 2 run2)) (concatenation_automaton \<A>1 \<A>2) ((map Inl word1) @ [Inr()] @ (map Inl word2))"
proof - 
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  let ?run1 = "run_cross_renaming_iso 1 run1"
  let ?run2 = "run_cross_renaming_iso 2 run2"
  let ?subword1 = "map Inl word1"
  let ?subword2 = "[Inr()] @ (map Inl word2)"
  have "length run1 = length word1 + 1 \<and> length run2 = length word2 + 1" using assms unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by blast
  hence len: "length ?run1 = length word1 + 1 \<and> length ?run2 = length word2 + 1" unfolding run_cross_renaming_iso_def by auto
  hence length: "length (?run1 @ ?run2) = length (?subword1 @ ?subword2) + 1 \<and> length ?run2 = length ?subword2" by auto
  have "run1 \<noteq> [] \<and> run1 ! 0 = initial_state \<A>1" using assms unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by fastforce
  hence "?run1 \<noteq> [] \<and> ?run1 ! 0 = (initial_state \<A>1, 1)" unfolding run_cross_renaming_iso_def cross_renaming_iso_def by auto
  hence "?run1 \<noteq> [] \<and> ?run1 ! 0 = initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" unfolding type_encode_automaton_def concatenation_automaton_helper_def cross_renaming_iso_def by auto
  hence "(?run1 @ ?run2) ! 0 = initial_state ?\<A>" using list_properties_not_empty unfolding concatenation_automaton_def concatenation_automaton_helper_def by fastforce
  hence init: "(?run1 @ ?run2) ! 0 = initial_state ?\<A> \<and> initial_state ?\<A> \<in> states ?\<A>" using assms concatenation_auto_well_defined unfolding auto_well_defined_def by auto
  have not_empty_original: "run1 \<noteq> [] \<and> run2 \<noteq> [] \<and> run2 ! 0 = initial_state \<A>2 \<and> last run1 \<in> accepting_states \<A>1" using assms unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by force
  hence "?run2 \<noteq> [] \<and> ?run2 ! 0 = (initial_state \<A>2, 2) \<and> last ?run1 = (cross_renaming_iso 1) (last run1) \<and> last run1 \<in> accepting_states \<A>1" using last_run_cross_renaming_iso unfolding run_cross_renaming_iso_def cross_renaming_iso_def by fastforce
  hence not_empty: "?run2 \<noteq> [] \<and> ?run2 ! 0 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<and> last ?run1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" unfolding type_encode_automaton_def concatenation_automaton_helper_def cross_renaming_iso_def by auto
  have impl: "(\<forall> s1 s2 a . (s1, a, s2) \<in> transitions \<A>1 \<longrightarrow> (cross_renaming_iso 1 s1, a, cross_renaming_iso 1 s2) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)) \<and> (\<forall> s1 s2 a . (s1, a, s2) \<in> transitions \<A>2 \<longrightarrow> (cross_renaming_iso 2 s1, a, cross_renaming_iso 2 s2) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id))" unfolding type_encode_automaton_def by force
  have "(\<forall> s1 s2 a . (s1, a, s2) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<longrightarrow> (s1, Inl a, s2) \<in> transitions ?\<A>) \<and> (\<forall> s1 s2 a . (s1, a, s2) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<longrightarrow> (s1, Inl a, s2) \<in> transitions ?\<A>)" unfolding concatenation_automaton_def concatenation_automaton_helper_def by force
  hence trans_impl: "(\<forall> s1 s2 a . (s1, a, s2) \<in> transitions \<A>1 \<longrightarrow> (cross_renaming_iso 1 s1, Inl a, cross_renaming_iso 1 s2) \<in> transitions ?\<A>) \<and> (\<forall> s1 s2 a . (s1, a, s2) \<in> transitions \<A>2 \<longrightarrow> (cross_renaming_iso 2 s1, Inl a, cross_renaming_iso 2 s2) \<in> transitions ?\<A>)" using impl by presburger
  {
    fix i assume assm: "i < length (?run1 @ ?run2) - 1"
    consider (case1) "i < length ?run1 - 1" | (case2) "i = length ?run1 - 1" | (case3) "i > length ?run1 - 1" by linarith
    hence "((?run1 @ ?run2) ! i, ((map Inl word1) @ [Inr()] @ (map Inl word2)) ! i, (?run1 @ ?run2) ! (i + 1)) \<in> transitions ?\<A>"
    proof cases
      case case1 
      hence case1_run: "i < length run1 - 1" unfolding run_cross_renaming_iso_def by auto
      have equi: "(?run1 @ ?run2) ! i = ?run1 ! i \<and> (?run1 @ ?run2) ! (i + 1) = ?run1 ! (i + 1) \<and> (?subword1 @ ?subword2) ! i = ?subword1 ! i" using case1 list_append_position1 length by blast
      have "(run1 ! i, word1 ! i, run1 ! (i + 1)) \<in> transitions \<A>1" using assms case1_run unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by blast
      hence "(?run1 ! i, (map Inl word1) ! i, ?run1 ! (i + 1)) \<in> transitions ?\<A>" using case1 len trans_impl unfolding run_cross_renaming_iso_def by force 
      thus ?thesis using equi by argo
    next
      case case2
      hence case2_run: "i = length run1 - 1" unfolding run_cross_renaming_iso_def by auto
      have equi: "(?run1 @ ?run2) ! i = last ?run1 \<and> (?run1 @ ?run2) ! (i + 1) = ?run2 ! 0 \<and> (?subword1 @ ?subword2) ! i = ?subword2 ! 0" using case2 list_append_position2 length by blast
      have "\<forall> s1 s2 . s1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> s2 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<longrightarrow> (s1, Inr(), s2) \<in> transitions ?\<A>" using spezial_trans_concat_auto unfolding concatenation_automaton_def by fast
      hence "(last ?run1, Inr(), ?run2 ! 0) \<in> transitions ?\<A>" using not_empty by blast
      thus ?thesis using equi by auto
    next
      case case3
      hence case3_run: "length run1 = length ?run1 \<and> length run2 = length ?run2" unfolding run_cross_renaming_iso_def by auto
      have "(?run1 @ ?run2) ! i = ?run2 ! (i - length ?run1) \<and> (?run1 @ ?run2) ! (i + 1) = ?run2 ! (i + 1 - length ?run1) \<and> (?subword1 @ ?subword2) ! i = ?subword2 ! (i + 1 - length ?run1)" using assm case3 list_append_position3 length by blast
      hence equi: "(?run1 @ ?run2) ! i = ?run2 ! (i - length ?run1) \<and> (?run1 @ ?run2) ! (i + 1) = ?run2 ! (i + 1 - length ?run1) \<and> (?subword1 @ ?subword2) ! i = (map Inl word2) ! (i - length ?run1)" using case3 by force
      have "(i - length ?run1) < length ?run2 - 1" using case3 assm length by force
      then obtain k where k: "k = i - length ?run1 \<and> k < length ?run2 - 1" by blast
      have "\<forall> i < length run2 - 1 . (run2 ! i, word2 ! i, run2 ! (i + 1)) \<in> transitions \<A>2" using assms unfolding pseudo_run_well_defined_def run_well_defined_def run_accepting_def by blast
      hence "(run2 ! k, word2 ! k, run2 ! (k + 1)) \<in> transitions \<A>2" using k case3_run by metis 
      hence "(?run2 ! k, (map Inl word2) ! k, ?run2 ! (k + 1)) \<in> transitions ?\<A>" using case3 len k trans_impl unfolding run_cross_renaming_iso_def by auto
      hence trans: "(?run2 ! (i - length ?run1), (map Inl word2) ! (i - length ?run1), ?run2 ! (i - length ?run1 + 1)) \<in> transitions ?\<A>" using k by blast
      have "i - length ?run1 + 1 = i + 1 - length ?run1" using case3 by force
      hence "(?run2 ! (i - length ?run1), (map Inl word2) ! (i - length ?run1), ?run2 ! (i + 1 - length ?run1)) \<in> transitions ?\<A>" using trans by argo
      thus ?thesis using equi by argo
    qed
  }
  hence "\<forall> i < length (?run1 @ ?run2) - 1 . ((?run1 @ ?run2) ! i, ((map Inl word1) @ [Inr()] @ (map Inl word2)) ! i, (?run1 @ ?run2) ! (i + 1)) \<in> transitions ?\<A>" by blast
  hence well_def: "run_well_defined (?run1 @ ?run2) ?\<A> ((map Inl word1) @ [Inr()] @ (map Inl word2))" using length init unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  have "last run2 \<in> accepting_states \<A>2" using assms unfolding run_accepting_def by auto
  hence "last ?run2 = (cross_renaming_iso 2) (last run2) \<and> last run2 \<in> accepting_states \<A>2" using not_empty_original last_run_cross_renaming_iso by metis
  hence "last ?run2 \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" unfolding type_encode_automaton_def by auto
  hence acc: "last ?run2 \<in> accepting_states ?\<A>" unfolding concatenation_automaton_def concatenation_automaton_helper_def by auto
  have "last ?run2 = last (?run1 @ ?run2)" using not_empty by auto
  thus ?thesis using acc well_def unfolding run_accepting_def by argo
qed

theorem concate_language_left:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "concatenation_language (language_auto \<A>1) (language_auto \<A>2) \<subseteq> eps_free_language (language_auto (concatenation_automaton \<A>1 \<A>2))"
proof -
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  {
    fix word assume "word \<in> concatenation_language (language_auto \<A>1) (language_auto \<A>2)"
    then obtain word1 word2 where words: "word1 \<in> language_auto \<A>1 \<and> word2 \<in> language_auto \<A>2 \<and> word = word1 @ word2" unfolding concatenation_language_def by blast
    then obtain run1 run2 where "run_accepting run1 \<A>1 word1 \<and> run_accepting run2 \<A>2 word2" unfolding language_auto_def by auto
    hence "run_accepting ((run_cross_renaming_iso 1 run1) @ (run_cross_renaming_iso 2 run2)) ?\<A> ((map Inl word1) @ [Inr()] @ (map Inl word2))" using assms concate_run_correct_left by blast
    hence "(map Inl word1) @ [Inr()] @ (map Inl word2) \<in> language_auto ?\<A>" unfolding language_auto_def by auto
    hence eps_free_lan: "evaluate_eps_word ((map Inl word1) @ [Inr()] @ (map Inl word2)) \<in> eps_free_language (language_auto ?\<A>)" unfolding eps_free_language_def by auto
    have "evaluate_eps_word ((map Inl word1) @ [Inr()] @ (map Inl word2)) = evaluate_eps_word (map Inl word1) @ evaluate_eps_word [Inr()] @ evaluate_eps_word (map Inl word2)" using evaluate_eps_word_snoc by metis
    hence "evaluate_eps_word ((map Inl word1) @ [Inr()] @ (map Inl word2)) = word1 @ word2" by (simp add: inverse_evaluate_eps)
    hence "word \<in> eps_free_language (language_auto ?\<A>)" using eps_free_lan words by auto
  }
  thus ?thesis by auto
qed

lemma concatenation_automaton_run_states_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "run_well_defined run (concatenation_automaton \<A>1 \<A>2) word \<and> Inr() \<notin> set word \<Longrightarrow> prun_states run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)"
proof(induction word arbitrary: run rule: rev_induct)
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  case Nil
  hence run: "run = [initial_state ?\<A>]" using list_with_one_element unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce
  have "?\<A> = concatenation_automaton_helper (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" unfolding concatenation_automaton_def by auto
  hence equi: "initial_state ?\<A> = initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" unfolding concatenation_automaton_helper_def by auto
  have "initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms cross_renaming_iso_automaton_auto_well_defined unfolding auto_well_defined_def by auto
  thus ?case using equi run unfolding prun_states_def by auto
next
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  case (snoc a word)
  hence "run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain run' where run': "run = run' @ [last run]" using append_butlast_last_id by metis
  hence trans: "run_well_defined run' ?\<A> word \<and> (last run', a, last run) \<in> transitions ?\<A>" using prun_well_defined_extension_snoc snoc unfolding run_well_defined_def by metis
  hence run_states: "prun_states run' (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> run' \<noteq> []" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce
  hence "last run' \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> a \<noteq> Inr()" using snoc unfolding prun_states_def by auto
  hence "last run \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using trans assms normal_trans_concat_auto_A1 by blast 
  thus ?case using prun_states_snoc run_states run' by metis
qed

lemma concatenation_automaton_run_states_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "run_well_defined run (concatenation_automaton \<A>1 \<A>2) word \<and> word ! i = Inr() \<and> i < length run - 1 \<Longrightarrow> \<forall> k . i < k \<and> k < length run \<longrightarrow> run ! k \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
proof(induction word arbitrary: run rule: rev_induct)
  case Nil thus ?case unfolding run_well_defined_def pseudo_run_well_defined_def by auto
next
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  let ?\<A>2 = "type_encode_automaton \<A>2 (cross_renaming_iso 2) id"
  case (snoc a word) 
  hence "run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain run' where run': "run = run' @ [last run]" using append_butlast_last_id by metis
  hence trans: "run_well_defined run' ?\<A> word \<and> (last run', a, last run) \<in> transitions ?\<A>" using prun_well_defined_extension_snoc snoc unfolding run_well_defined_def by metis
  hence not_empty: "length run' > 0" unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence len: "length run' = length run - 1" using run' butlast_snoc length_butlast by metis
  then consider (case1) "i = length run' - 1" | (case2) "i < length run' - 1" using snoc by linarith
  hence IH: "\<forall> k . i < k \<and> k < length run' \<longrightarrow> run' ! k \<in> states ?\<A>2"
  proof cases
    case case1 thus ?thesis by linarith
  next
    case case2
    have "length (word @ [a]) + 1 = length run" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by argo
    hence length: "length word + 1 = length run'" using len by auto
    hence "(word @ [a]) ! i = Inr() \<and> i < length word" using snoc case2 by auto
    hence "word ! i = Inr()" using nth_append by metis
    thus ?thesis using snoc trans case2 by blast
  qed
  have "\<forall> k < length run' . run ! k = run' ! k" using list_properties_length run' by metis
  hence ks: "\<forall> k . i < k \<and> k < length run - 1 \<longrightarrow> run ! k \<in> states ?\<A>2" using IH len by presburger
  consider (case1) "i = length run - 2" | (case2) "i < length run - 2" using snoc len by linarith 
  hence "run ! (length run - 1) \<in> states ?\<A>2"
  proof cases
    case case1
    have run_props: "length run = length (word @ [a]) + 1 \<and> (\<forall> j < length run - 1 . (run ! j, (word @ [a]) ! j, run ! (j + 1)) \<in> transitions ?\<A>)" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by blast
    hence "i < length run - 1" using snoc by argo
    hence "(run ! i, (word @ [a]) ! i, run ! (i + 1)) \<in> transitions ?\<A>" using run_props assms by blast
    hence "(run ! i, Inr(), run ! (i + 1)) \<in> transitions ?\<A>" using snoc by argo
    hence "run ! (i + 1) = initial_state ?\<A>2" using spezial_trans_concat_auto unfolding concatenation_automaton_def by fast
    hence "run ! (i + 1) \<in> states ?\<A>2" using assms cross_renaming_iso_automaton_auto_well_defined unfolding auto_well_defined_def by auto
    hence run_pos: "run ! (length run - 2 + 1) \<in> states ?\<A>2" using case1 by auto
    have "length run > 1" using not_empty len by auto
    thus ?thesis using simple_math run_pos by presburger
  next
    case case2
    hence run_2: "run ! (length run - 2) \<in> states ?\<A>2" using ks by auto
    have run_props: "\<forall> j < length run - 1 . (run ! j, (word @ [a]) ! j, run ! (j + 1)) \<in> transitions ?\<A>" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by argo
    hence "(run ! (length run - 2), (word @ [a]) ! (length run - 2), run ! ((length run - 2) + 1)) \<in> transitions ?\<A>" using not_empty len by auto
    hence run_pos: "run ! ((length run - 2) + 1) \<in> states ?\<A>2" using run_2 normal_trans_concat_auto_A2 assms unfolding concatenation_automaton_def by blast
    have "length run > 1" using not_empty len by auto
    thus ?thesis using simple_math run_pos by presburger
    qed
  thus ?case using ks Nat.lessE diff_Suc_1 by metis
qed

lemma concatenation_automaton_uniqueness_Inr:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "run_accepting run (concatenation_automaton \<A>1 \<A>2) word" "i < length word \<and> word ! i = Inr() \<and> j < length word \<and> word ! j = Inr() \<and> i < j"
  shows "False"
proof - 
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  have run_well_def: "run_well_defined run ?\<A> word" using assms unfolding run_accepting_def by auto
  hence run_props: "length run = length word + 1 \<and> (\<forall> i < length run - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions ?\<A>)" unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence i: "i < length run - 1 \<and> j < length run - 1" using assms by auto
  hence "\<forall> k . i < k \<and> k < length run \<longrightarrow> run ! k \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms run_well_def concatenation_automaton_run_states_A2 by blast
  hence run_j: "run ! j \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms i by fastforce
  have "(run ! j, word ! j, run ! (j + 1)) \<in> transitions ?\<A>" using i run_props assms by blast
  hence "(run ! j, Inr(), run ! (j + 1)) \<in> transitions ?\<A>" using assms by argo
  hence "run ! j \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using spezial_trans_concat_auto unfolding concatenation_automaton_def by fast
  hence "run ! j \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms cross_renaming_iso_automaton_auto_well_defined unfolding auto_well_defined_def by auto
  thus ?thesis using run_j cross_renaming_intersection_empty by auto
qed

proposition concatenation_automaton_unique_existence_Inr:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "run_accepting run (concatenation_automaton \<A>1 \<A>2) word"
  shows "\<exists>! k . k < length word \<and> word ! k = Inr()"
proof - 
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  have "run_well_defined run ?\<A> word \<and> last run \<in> accepting_states ?\<A>" using assms unfolding run_accepting_def by auto
  hence props: "run_well_defined run ?\<A> word \<and> last run \<in> accepting_states ?\<A> \<and> run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce
  have "?\<A> = concatenation_automaton_helper (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" unfolding concatenation_automaton_def by auto
  hence "last run \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using props unfolding concatenation_automaton_helper_def by auto
  hence "last run \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined unfolding auto_well_defined_def by auto
  hence "last run \<notin> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using cross_renaming_intersection_empty by auto
  hence "\<not> prun_states run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using props unfolding prun_states_def by force
  hence "Inr() \<in> set word" using assms concatenation_automaton_run_states_A1 props by blast
  hence existence: "\<exists> k < length word . word ! k = Inr()" by (simp add: in_set_conv_nth)
  {
    fix i j assume ij: "i < length word \<and> word ! i = Inr() \<and> j < length word \<and> word ! j = Inr()"
    consider (case1) "i < j" | (case2) "i = j" | (case3) "i > j" by linarith
    hence "i = j"
    proof cases
      case case1 thus ?thesis using ij assms concatenation_automaton_uniqueness_Inr by blast
    next
      case case2 thus ?thesis by auto
    next
      case case3 thus ?thesis using ij assms concatenation_automaton_uniqueness_Inr by blast
    qed
  }
  thus ?thesis using existence by blast
qed

lemma concate_run_correct_right_A1:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" 
  shows "run_well_defined run (concatenation_automaton \<A>1 \<A>2) word \<and> Inr() \<notin> set word \<Longrightarrow> run_well_defined run (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (evaluate_eps_word word)"
proof(induction word arbitrary: run rule: rev_induct)
  case Nil
  hence "run = [initial_state (concatenation_automaton \<A>1 \<A>2)]" using list_with_one_element unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "run = [initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)]" unfolding concatenation_automaton_def concatenation_automaton_helper_def by auto
  hence "run = [initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)] \<and> initial_state (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms cross_renaming_iso_automaton_auto_well_defined unfolding auto_well_defined_def by fast
  thus ?case unfolding run_well_defined_def pseudo_run_well_defined_def by auto
next
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  have well_def: "auto_well_defined (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  case (snoc a word)
  hence "run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain run' where run': "run = run' @ [last run]" using append_butlast_last_id by metis
  hence trans: "run_well_defined run' ?\<A> word \<and> (last run', a, last run) \<in> transitions ?\<A>" using prun_well_defined_extension_snoc snoc unfolding run_well_defined_def by metis
  have "Inr() \<notin> set word" using snoc by simp
  hence run_well_def: "run_well_defined run' (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (evaluate_eps_word word) \<and> (last run', a, last run) \<in> transitions ?\<A> \<and> Inr() \<notin> set word" using trans snoc by blast
  hence last: "last run' \<in> states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using well_def last_of_prun_is_state unfolding run_well_defined_def by fast
  have a: "a \<noteq> Inr()" using snoc by auto
  then obtain b where b: "Inl b = a" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
  hence trans_ins_cross: "(last run', b, last run) \<in> transitions (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using assms trans last a normal_trans_concat_auto_A1_inv by fast
  have "evaluate_eps_word (word @ [a]) = evaluate_eps_word word @ evaluate_eps_word [a]" using evaluate_eps_word_snoc by auto
  hence "evaluate_eps_word (word @ [a]) = evaluate_eps_word word @ [b]" using a b by auto
  thus ?case using trans_ins_cross run_well_def prun_well_defined_extension_snoc run' unfolding run_well_defined_def by metis
qed

lemma concate_run_correct_right_A2:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" 
  shows "run ! 0 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) \<and> Inr() \<notin> set word \<and> length run = length word + 1 \<and> (\<forall> j < length run - 1 . (run ! j, word ! j, run ! (j + 1)) \<in> transitions (concatenation_automaton \<A>1 \<A>2)) \<Longrightarrow> run_well_defined run (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (evaluate_eps_word word) \<and> last run \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)"
proof(induction word arbitrary: run rule: rev_induct)
  case Nil
  have well_def: "auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  have run: "run = [initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)]" using list_with_one_element Nil by fastforce
  hence "last run = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" by auto
  hence "last run \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using well_def unfolding auto_well_defined_def by argo
  thus ?case using run unfolding run_well_defined_def pseudo_run_well_defined_def by force
next
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  have well_def: "auto_well_defined (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms cross_renaming_iso_automaton_auto_well_defined by auto
  case (snoc a word)
  hence "run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence not_empty: "run \<noteq> []" by auto
  then obtain run' where run': "run = run' @ [last run]" using append_butlast_last_id by metis
  hence "length run = length (run' @ [last run])" by auto
  hence "length run = length run' + length [last run]" by simp
  hence len_plus_1: "length run = length run' + 1" by auto
  have len_word: "length run = length (word @ [a]) + 1" using snoc by force
  hence "length run = length word + 1 + 1" by auto
  hence length: "length run' = length word + 1 \<and> Inr() \<notin> set word" using len_plus_1 snoc by auto
  hence not_empty': "run' \<noteq> []" by auto
  hence init: "run' ! 0 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using snoc list_properties_not_empty run' by metis
  have not_empty_word: "word @ [a] \<noteq> []" by auto
  have "\<forall> j < length word . (word @ [a]) ! j = word ! j" using list_properties_length by metis
  hence word_equi: "\<forall> j < length run' - 1 . (word @ [a]) ! j = word ! j" using length by auto
  have run_equi: "\<forall> j < length run' . run ! j = run' ! j" using list_properties_length run' by metis
  have "(\<forall> j < length run - 1 - 1 . (run ! j, (word @ [a]) ! j, run ! (j + 1)) \<in> transitions ?\<A>) \<and> (run ! (length run - 2), (word @ [a]) ! (length run - 2), run ! (length run - 2 + 1)) \<in> transitions ?\<A>" using snoc by force
  hence "(\<forall> j < length run' - 1 . (run' ! j, word ! j, run' ! (j + 1)) \<in> transitions ?\<A>) \<and> (run ! (length run - 2), (word @ [a]) ! (length run - 2), run ! (length run - 2 + 1)) \<in> transitions ?\<A>" using len_plus_1 word_equi run_equi by auto
  hence "(\<forall> j < length run' - 1 . (run' ! j, word ! j, run' ! (j + 1)) \<in> transitions ?\<A>) \<and> (run' ! (length run' - 1), (word @ [a]) ! (length (word @ [a]) - 1), run ! (length run - 1)) \<in> transitions ?\<A>" using simple_math len_word len_plus_1 run_equi len_word by force
  hence "(\<forall> j < length run' - 1 . (run' ! j, word ! j, run' ! (j + 1)) \<in> transitions ?\<A>) \<and> (last run', last (word @ [a]), last run) \<in> transitions ?\<A>" using not_empty not_empty' list_properties_not_empty not_empty_word by metis
  hence trans: "(\<forall> j < length run' - 1 . (run' ! j, word ! j, run' ! (j + 1)) \<in> transitions ?\<A>) \<and> (last run', a, last run) \<in> transitions ?\<A>" by auto
  hence run_well_def: "run_well_defined run' (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (evaluate_eps_word word) \<and> last run' \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using init length snoc by blast
  have a: "a \<noteq> Inr()" using snoc by auto
  then obtain b where b: "Inl b = a" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
  hence trans_ins_cross: "(last run', b, last run) \<in> transitions (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using assms run_well_def trans normal_trans_concat_auto_A2_inv a by metis 
  hence last: "last run \<in> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using well_def well_def_trans_components by fast
  have "evaluate_eps_word (word @ [a]) = evaluate_eps_word word @ evaluate_eps_word [a]" using evaluate_eps_word_snoc by auto
  hence "evaluate_eps_word (word @ [a]) = evaluate_eps_word word @ [b]" using a b by auto
  thus ?case using trans_ins_cross run_well_def prun_well_defined_extension_snoc run' last unfolding run_well_defined_def by metis
qed

theorem concate_run_correct_right:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2" "run_accepting run (concatenation_automaton \<A>1 \<A>2) word" 
  shows "\<exists> run1 run2 word1 word2 . run_accepting run1 (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) word1 \<and> run_accepting run2 (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) word2 \<and> word = ((map Inl word1) @ [Inr()] @ (map Inl word2))"
proof - 
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  have "run_well_defined run ?\<A> word \<and> last run \<in> accepting_states ?\<A>" using assms unfolding run_accepting_def by auto
  hence run_props: "run_well_defined run ?\<A> word \<and> last run \<in> accepting_states ?\<A> \<and> run \<noteq> [] \<and> length run = length word + 1 \<and> (\<forall> i < length run - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions ?\<A>) \<and> run ! 0 = initial_state ?\<A>" unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce
  obtain k where k: "k < length word \<and> word ! k = Inr()" using assms concatenation_automaton_unique_existence_Inr by blast
  let ?subrun1 = "take (Suc k) run"
  let ?subword1 = "take k word"
  have length1: "length ?subrun1 = length ?subword1 + 1 \<and> k = length ?subrun1 - 1" using run_props k by force
  hence not_empty1: "?subrun1 \<noteq> []" by fastforce
  have no_inr1: "\<forall> i . i \<noteq> k \<and> i < length word \<longrightarrow> word ! i \<noteq> Inr()" using assms k concatenation_automaton_unique_existence_Inr by blast
  hence no_inr_set1: "Inr() \<notin> set ?subword1" using k by (simp add: no_inr1 in_set_conv_nth) 
  have "\<forall> i < k . (?subrun1 ! i, ?subword1 ! i, ?subrun1 ! (i + 1)) \<in> transitions ?\<A>" using run_props k by force
  hence "run_well_defined ?subrun1 ?\<A> ?subword1" using length1 run_props unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence run1: "run_well_defined ?subrun1 (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (evaluate_eps_word ?subword1)" using no_inr_set1 assms concate_run_correct_right_A1 by blast
  have "(run ! k, word ! k, run ! (k + 1)) \<in> transitions ?\<A>" using k run_props by fastforce
  hence "(run ! k, Inr(), run ! (k + 1)) \<in> transitions ?\<A>" using k by auto
  hence spezial_states: "run ! k \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<and> run ! (k + 1) = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using spezial_trans_concat_auto unfolding concatenation_automaton_def by fast
  have equi1: "last ?subrun1 = ?subrun1 ! (length ?subrun1 - 1)" using not_empty1 list_properties_not_empty by metis
  have "length ?subrun1 = k + 1" using k length1 by auto
  hence "last ?subrun1 = ?subrun1 ! k" using equi1 by simp
  hence "last ?subrun1 \<in> accepting_states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id)" using spezial_states by auto
  hence run1acc: "run_accepting ?subrun1 (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) (evaluate_eps_word ?subword1)" using run1 unfolding run_accepting_def by blast
  let ?subrun2 = "sublist (Suc k) (length run) run"
  let ?subword2 = "sublist (Suc k) (length word) word"
  have len_k: "k < length word \<and> length run = length word + 1" using run_props k by blast
  hence length2: "length ?subrun2 = length ?subword2 + 1" unfolding sublist_def by fastforce
  hence not_empty2: "?subrun2 \<noteq> []" by auto
  hence no_inr_set2: "Inr() \<notin> set ?subword2" using k unfolding sublist_def by (simp add: no_inr1 in_set_conv_nth) 
  have "?subrun2 ! 0 = run ! (k + 1)" using len_k unfolding sublist_def by auto
  hence init2: "?subrun2 ! 0 = initial_state (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using spezial_states by auto
  {
    fix i assume assm: "k < i \<and> i < length run - 1"
    have app_run: "?subrun1 @ ?subrun2 = run \<and> length ?subrun1 = k + 1" using k length1 unfolding sublist_def by auto
    hence "i > length ?subrun1 - 1 \<and> i < length (?subrun1 @ ?subrun2) - 1 \<and> length ?subrun1 > 0" using assm not_empty1 by simp
    hence "(?subrun1 @ ?subrun2) ! i = ?subrun2 ! (i - length ?subrun1) \<and> (?subrun1 @ ?subrun2) ! (i + 1) = ?subrun2 ! (i + 1 - length ?subrun1)" using list_append_position6 by blast
    hence equi: "run ! i = ?subrun2 ! (i - length ?subrun1) \<and> run ! (i + 1) = ?subrun2 ! (i + 1 - length ?subrun1)" using app_run by argo
    have "i < length word" using assm run_props by auto
    hence word_equi: "word ! i = ?subword2 ! (i - length ?subrun1)" using assm length1  unfolding sublist_def by auto
    have "(run ! i, word ! i, run ! (i + 1)) \<in> transitions ?\<A>" using assm run_props by blast
    hence trans2: "(?subrun2 ! (i - length ?subrun1), ?subword2 ! (i - length ?subrun1), ?subrun2 ! (i + 1 - length ?subrun1)) \<in> transitions ?\<A>" using word_equi equi by argo
  }
  hence i_trans: "\<forall> i . k < i \<and> i < length run - 1 \<longrightarrow> (?subrun2 ! (i - length ?subrun1), ?subword2 ! (i - length ?subrun1), ?subrun2 ! (i + 1 - length ?subrun1)) \<in> transitions ?\<A>" by blast
  {
    fix j assume assm: "j < length ?subrun2 - 1 \<and> j \<ge> 0"
    have "?subrun1 @ ?subrun2 = run \<and> length ?subrun1 = k + 1 \<and> length ?subrun2 > 0" using k length1 not_empty2 unfolding sublist_def by auto
    hence "length ?subrun1 + length ?subrun2 = length run \<and> length ?subrun1 = k + 1 \<and> length ?subrun2 > 0" using length_append by metis
    hence "j + length ?subrun1 \<ge> k + 1 \<and> j + length ?subrun1 < length run - 1" using assm by linarith
    hence "k < j + length ?subrun1 \<and> j + length ?subrun1 < length run - 1" by auto
    hence "(?subrun2 ! j, ?subword2 ! j, ?subrun2 ! (j + 1)) \<in> transitions ?\<A>" using i_trans assm by auto
  }
  hence "\<forall> j < length ?subrun2 - 1 . (?subrun2 ! j, ?subword2 ! j, ?subrun2 ! (j + 1)) \<in> transitions ?\<A>" by blast
  hence run2: "run_well_defined ?subrun2 (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (evaluate_eps_word ?subword2)" using assms init2 no_inr_set2 length2 concate_run_correct_right_A2 by blast
  have "last run \<in> accepting_states ?\<A>" using run_props by blast
  hence spezial_states2: "last run \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" unfolding concatenation_automaton_def concatenation_automaton_helper_def by simp
  have app_run: "?subrun1 @ ?subrun2 = run" unfolding sublist_def by force
  hence "last ?subrun2 = last run" using not_empty2 last_appendR by metis
  hence "last ?subrun2 \<in> accepting_states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id)" using spezial_states2 by auto
  hence run2acc: "run_accepting ?subrun2 (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) (evaluate_eps_word ?subword2)" using run2 unfolding run_accepting_def by blast
  have "Inr() \<notin> set ?subword1 \<and> Inr() \<notin> set ?subword2" using no_inr_set1 no_inr_set2 by blast
  hence map_inv: "map Inl (evaluate_eps_word ?subword1) = ?subword1 \<and> map Inl (evaluate_eps_word ?subword2) = ?subword2" using inverse_Inl_eps by blast
  have "word = ?subword1 @ [Inr()] @ ?subword2" using k Cons_nth_drop_Suc unfolding sublist_def by force
  hence "word = ((map Inl (evaluate_eps_word ?subword1)) @ [Inr()] @ (map Inl (evaluate_eps_word ?subword2)))" using map_inv by argo
  thus ?thesis using run1acc run2acc by blast
qed

theorem concate_language_right:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "eps_free_language (language_auto (concatenation_automaton \<A>1 \<A>2)) \<subseteq> concatenation_language (language_auto \<A>1) (language_auto \<A>2)"
proof -
  let ?\<A> = "concatenation_automaton \<A>1 \<A>2"
  let ?\<A>1 = "type_encode_automaton \<A>1 (cross_renaming_iso 1) id"
  let ?\<A>2 = "type_encode_automaton \<A>2 (cross_renaming_iso 2) id"
  {
    fix word assume "word \<in> eps_free_language (language_auto ?\<A>)"
    then obtain word' where word': "evaluate_eps_word word' = word \<and> word' \<in> language_auto ?\<A>" unfolding eps_free_language_def by blast
    then obtain run1 run2 word1 word2 where obtained_words: "run_accepting run1 ?\<A>1 word1 \<and> run_accepting run2 ?\<A>2 word2 \<and> word' = ((map Inl word1) @ [Inr()] @ (map Inl word2))" using concate_run_correct_right assms unfolding language_auto_def by blast
    hence "word1 \<in> language_auto ?\<A>1 \<and> word2 \<in> language_auto ?\<A>2" unfolding language_auto_def by fast
    hence "word1 \<in> language_auto \<A>1 \<and> word2 \<in> language_auto \<A>2" using assms cross_renaming_iso_automaton_same_language by auto
    hence con_lan: "word1 @ word2 \<in> concatenation_language (language_auto \<A>1) (language_auto \<A>2)" unfolding concatenation_language_def by auto
    have "evaluate_eps_word ((map Inl word1) @ [Inr()] @ (map Inl word2)) = evaluate_eps_word (map Inl word1) @ evaluate_eps_word [Inr()] @ evaluate_eps_word (map Inl word2)" using evaluate_eps_word_snoc by metis
    hence "evaluate_eps_word ((map Inl word1) @ [Inr()] @ (map Inl word2)) = word1 @ word2" by (simp add: inverse_evaluate_eps)
    hence "word \<in> concatenation_language (language_auto \<A>1) (language_auto \<A>2)" using con_lan obtained_words word' by argo
  }
  thus ?thesis by auto
qed

text \<open>Main result for the concatenation_automaton: language equivalence\<close>
theorem concatenation_language_correctness:
  assumes "auto_well_defined \<A>1" "auto_well_defined \<A>2"
  shows "eps_free_language (language_auto (concatenation_automaton \<A>1 \<A>2)) = concatenation_language (language_auto \<A>1) (language_auto \<A>2)"
  using concate_language_right concate_language_left assms by blast

theorem conc_main:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> conc_\<A> :: ('s \<times> nat , 'a + unit) automaton . auto_well_defined conc_\<A> \<and> alphabet conc_\<A> = (image Inl (alphabet \<A>1 \<union> alphabet \<A>2)) \<union> {Inr()} \<and> eps_free_language (language_auto conc_\<A>) = concatenation_language (language_auto \<A>1) (language_auto \<A>2)"
  using concatenation_language_correctness concatenation_auto_well_defined concatenation_alphabet existence_soft_iso_auto_lang assms by metis

proposition conc_alpha_and_eps_alpha: "{a . Inl a \<in> ((image Inl (alphabet \<A>1 \<union> alphabet \<A>2)) \<union> {Inr()})} = alphabet \<A>1 \<union> alphabet \<A>2"
  by blast

theorem existence_of_conc_same_type:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> conc_\<A> :: ('s, 'a) automaton . auto_well_defined conc_\<A> \<and> alphabet conc_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> language_auto conc_\<A> = concatenation_language (language_auto \<A>1) (language_auto \<A>2)"
proof -
  have "\<exists> conc_\<A> :: ('s \<times> nat , 'a + unit) automaton . auto_well_defined conc_\<A> \<and> alphabet conc_\<A> = (image Inl (alphabet \<A>1 \<union> alphabet \<A>2)) \<union> {Inr()} \<and> eps_free_language (language_auto conc_\<A>) = concatenation_language (language_auto \<A>1) (language_auto \<A>2)" using assms conc_main by blast
  hence "\<exists> eps_free_\<A> :: ('s \<times> nat, 'a) automaton . auto_well_defined eps_free_\<A> \<and> alphabet eps_free_\<A> = {a . Inl a \<in> ((image Inl (alphabet \<A>1 \<union> alphabet \<A>2)) \<union> {Inr()})} \<and> language_auto eps_free_\<A> = concatenation_language (language_auto \<A>1) (language_auto \<A>2)" using eps_main unfolding original_alphabet_def by metis
  thus ?thesis using assms existence_soft_iso_auto_lang conc_alpha_and_eps_alpha by metis
qed

end