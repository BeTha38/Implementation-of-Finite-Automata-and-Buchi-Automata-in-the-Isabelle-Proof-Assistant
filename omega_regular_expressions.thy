theory omega_regular_expressions

imports Main omega_automata_omega_power

begin

text \<open>Author: Benno Thalmann, last update: 11.2.2026, Addition to masterarbeit_benno_thalmann\<close>

datatype 'a omega_regular_expression =  Omega_power "'a regular_expression" | Left_concatenation "'a regular_expression" "'a omega_regular_expression" | Omega_alternation "'a omega_regular_expression" "'a omega_regular_expression"

fun alphabet_omega_RE :: "'a omega_regular_expression \<Rightarrow> 'a set" where
  "alphabet_omega_RE (Omega_power re) = alphabet_RE re" |
  "alphabet_omega_RE (Left_concatenation re r) = alphabet_RE re \<union> alphabet_omega_RE r" |
  "alphabet_omega_RE (Omega_alternation r1 r2) = alphabet_omega_RE r1 \<union> alphabet_omega_RE r2"

lemma finite_alphabet_omega_RE: "finite (alphabet_omega_RE r)"
  using finite_alphabet_RE by (induction r) auto

definition omega_RE_well_defined :: "'a omega_regular_expression \<Rightarrow> 'a alphabet \<Rightarrow> bool" where "omega_RE_well_defined r \<Sigma> = (alphabet_omega_RE r \<subseteq> \<Sigma> \<and> finite \<Sigma>)"

theorem "omega_RE_well_defined r (alphabet_omega_RE r)"
  using finite_alphabet_omega_RE unfolding omega_RE_well_defined_def by auto

lemma omega_inheritance_omega_power_well_def_r:
  assumes "RE_well_defined re \<Sigma>"
  shows "omega_RE_well_defined (Omega_power re) \<Sigma>"
  using assms unfolding omega_RE_well_defined_def RE_well_defined_def by simp

lemma omega_inheritance_omega_power_well_def_l:
  assumes "omega_RE_well_defined (Omega_power re) \<Sigma>"
  shows "RE_well_defined re \<Sigma>"
  using assms unfolding omega_RE_well_defined_def RE_well_defined_def by simp

proposition omega_inheritance_omega_power_well_def: "omega_RE_well_defined (Omega_power re) \<Sigma> \<longleftrightarrow> RE_well_defined re \<Sigma>"
  using omega_inheritance_omega_power_well_def_r omega_inheritance_omega_power_well_def_l by blast

lemma omega_inheritance_concatenation_well_def_r:
  assumes "RE_well_defined re \<Sigma>" "omega_RE_well_defined r \<Sigma>"
  shows "omega_RE_well_defined (Left_concatenation re r) \<Sigma>"
  using assms unfolding omega_RE_well_defined_def RE_well_defined_def by simp

lemma omega_inheritance_concatenation_well_def_l:
  assumes "omega_RE_well_defined (Left_concatenation re r) \<Sigma>"
  shows "RE_well_defined re \<Sigma> \<and> omega_RE_well_defined r \<Sigma>"
  using assms unfolding omega_RE_well_defined_def RE_well_defined_def by simp

proposition omega_inheritance_concatenation_well_def: "omega_RE_well_defined (Left_concatenation re r) \<Sigma> \<longleftrightarrow> RE_well_defined re \<Sigma> \<and> omega_RE_well_defined r \<Sigma>"
  using omega_inheritance_concatenation_well_def_r omega_inheritance_concatenation_well_def_l by blast

lemma omega_inheritance_alternation_well_def_r:
  assumes "omega_RE_well_defined r1 \<Sigma>" "omega_RE_well_defined r2 \<Sigma>"
  shows "omega_RE_well_defined (Omega_alternation r1 r2) \<Sigma>"
  using assms unfolding omega_RE_well_defined_def by simp

lemma omega_inheritance_alternation_well_def_l:
  assumes "omega_RE_well_defined (Omega_alternation r1 r2) \<Sigma>"
  shows "omega_RE_well_defined r1 \<Sigma> \<and> omega_RE_well_defined r2 \<Sigma>"
  using assms unfolding omega_RE_well_defined_def by simp

proposition omega_inheritance_alternation_well_def: "omega_RE_well_defined (Omega_alternation r1 r2) \<Sigma> \<longleftrightarrow> omega_RE_well_defined r1 \<Sigma> \<and> omega_RE_well_defined r2 \<Sigma>"
  using omega_inheritance_alternation_well_def_r omega_inheritance_alternation_well_def_l by blast



fun language_omega_reg_exp :: "'a omega_regular_expression \<Rightarrow> 'a omega_language" where
  "language_omega_reg_exp (Omega_power re) = omega_power_language (language_reg_exp re)" |
  "language_omega_reg_exp (Left_concatenation re r) = concatenation_omega_language (language_reg_exp re) (language_omega_reg_exp r)" |
  "language_omega_reg_exp (Omega_alternation r1 r2) = language_omega_reg_exp r1 \<union> language_omega_reg_exp r2"

proposition omega_word_in_omega_language_reg_is_well_defined: "omega_word \<in> language_omega_reg_exp r \<and> omega_RE_well_defined r \<Sigma> \<Longrightarrow> omega_word_well_defined omega_word \<Sigma>"
proof(induction r arbitrary: omega_word)
  case (Omega_power re)
  hence "RE_well_defined re \<Sigma>" using omega_inheritance_omega_power_well_def by force
  hence "language_well_defined (language_reg_exp re) \<Sigma>" using word_in_language_reg_is_well_defined unfolding language_well_defined_def by blast
  thus ?case using Omega_power omega_power_well_defined unfolding omega_language_well_defined_def by auto
next
  case (Left_concatenation re r)
  hence "omega_word \<in> concatenation_omega_language (language_reg_exp re) (language_omega_reg_exp r)" by auto
  hence "omega_word \<in> {merge_lists_fun word omega_word | word omega_word . word \<in> (language_reg_exp re) \<and> omega_word \<in> (language_omega_reg_exp r)}" unfolding concatenation_omega_language_def by blast
  then obtain word1 word2 where word: "omega_word = merge_lists_fun word1 word2 \<and> word1 \<in> (language_reg_exp re) \<and> word2 \<in> (language_omega_reg_exp r)" by blast
  hence "word_well_defined word1 \<Sigma> \<and> omega_word_well_defined word2 \<Sigma>" using Left_concatenation omega_inheritance_concatenation_well_def word_in_language_reg_is_well_defined by blast
  thus ?case using word merge_list_well_def by fastforce
next
  case (Omega_alternation r1 r2) thus ?case using omega_inheritance_alternation_well_def by fastforce
qed

corollary omega_word_in_omega_language_re_is_well_defined: "omega_word \<in> language_omega_reg_exp r \<Longrightarrow> omega_word_well_defined omega_word (alphabet_omega_RE r)"
  using omega_word_in_omega_language_reg_is_well_defined finite_alphabet_omega_RE unfolding omega_RE_well_defined_def by blast

proposition well_def_omega_REs_omega_language_is_well_def: "omega_RE_well_defined r \<Sigma> \<Longrightarrow> omega_language_well_defined (language_omega_reg_exp r) \<Sigma>"
  using omega_word_in_omega_language_reg_is_well_defined unfolding omega_language_well_defined_def by blast

corollary omega_lang_well_def_of_omega_RE: "omega_language_well_defined (language_omega_reg_exp r) (alphabet_omega_RE r)"
  using omega_word_in_omega_language_re_is_well_defined unfolding omega_language_well_defined_def by blast

text \<open>Key result for showing equivalence of expressive power between omega_RE and NBA: omega_RE --> NBA\<close>
theorem omega_regular_expression_implies_existence_of_auto:
  assumes "infinite (UNIV :: 's set)"
  shows "omega_RE_well_defined (r :: 'a omega_regular_expression) \<Sigma> \<Longrightarrow> \<exists> \<A> :: ('s, 'a) automaton . auto_well_defined \<A> \<and> alphabet \<A> = \<Sigma> \<and> omega_language_auto \<A> = language_omega_reg_exp r"
proof(induction r)
  case (Omega_power re)
  hence well_def: "RE_well_defined re \<Sigma>" using omega_inheritance_omega_power_well_def by blast
  then obtain \<A> :: "('s, 'a) automaton" where A: "auto_well_defined \<A> \<and> alphabet \<A> = \<Sigma> \<and> language_auto \<A> = language_reg_exp re" using assms regular_expression_implies_existence_of_auto by blast
  then obtain \<A>' :: "('s, 'a) automaton" where "auto_well_defined \<A>' \<and> alphabet \<A>' = alphabet \<A> \<and> omega_language_auto \<A>' = omega_power_language (language_auto \<A>)" using assms existence_of_omega_power_same_type by blast
  thus ?case using A by auto
next
  case (Left_concatenation re r)
  hence well_def: "RE_well_defined re \<Sigma> \<and> omega_RE_well_defined r \<Sigma>" using omega_inheritance_concatenation_well_def by blast
  then obtain \<A>1 :: "('s, 'a) automaton" where A1: "auto_well_defined \<A>1 \<and> alphabet \<A>1 = \<Sigma> \<and> language_auto \<A>1 = language_reg_exp re" using assms regular_expression_implies_existence_of_auto by blast
  obtain \<A>2 :: "('s, 'a) automaton" where A2: "auto_well_defined \<A>2 \<and> alphabet \<A>2 = \<Sigma> \<and> omega_language_auto \<A>2 = language_omega_reg_exp r" using Left_concatenation well_def by blast
  then obtain conc_\<A> :: "('s, 'a) automaton" where "auto_well_defined conc_\<A> \<and> alphabet conc_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> omega_language_auto conc_\<A> = concatenation_omega_language (language_auto \<A>1) (omega_language_auto \<A>2)" using A1 assms existence_of_omega_conc_same_type by metis 
  thus ?case using A1 A2 by auto
next
  case (Omega_alternation r1 r2)
  hence well_def: "omega_RE_well_defined r1 \<Sigma> \<and> omega_RE_well_defined r2 \<Sigma>" using omega_inheritance_alternation_well_def by metis
  then obtain \<A>1 :: "('s, 'a) automaton" where A1: "auto_well_defined \<A>1 \<and> alphabet \<A>1 = \<Sigma> \<and> omega_language_auto \<A>1 = language_omega_reg_exp r1" using Omega_alternation by blast
  obtain \<A>2 :: "('s, 'a) automaton" where A2: "auto_well_defined \<A>2 \<and> alphabet \<A>2 = \<Sigma> \<and> omega_language_auto \<A>2 = language_omega_reg_exp r2" using Omega_alternation well_def by blast  
  then obtain union_\<A> :: "('s, 'a) automaton" where "auto_well_defined union_\<A> \<and> alphabet union_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> omega_language_auto union_\<A> = omega_language_auto \<A>1 \<union> omega_language_auto \<A>2" using A1 assms existence_of_omega_union_same_type by metis
  thus ?case using A1 A2 by auto
qed







definition sub_automaton :: "('s, 'a) automaton \<Rightarrow> 's state \<Rightarrow> 's state \<Rightarrow> ('s, 'a) automaton" where
  "sub_automaton \<A> s1 s2 = Automaton
    (states \<A>)
    (alphabet \<A>)
    (transitions \<A>)
    (s1)
    ({s2})"

lemma alphabet_sub_automaton: "alphabet \<A> = alphabet (sub_automaton \<A> s1 s2)"
  unfolding sub_automaton_def by auto

lemma inheritance_pseudo_run_sub_automaton:
  assumes "pseudo_run_well_defined run \<A> s word"
  shows "pseudo_run_well_defined run (sub_automaton \<A> s1 s2) s word"
  using assms unfolding pseudo_run_well_defined_def sub_automaton_def by force

proposition sub_automaton_alphabet: "alphabet (sub_automaton \<A> s1 s2) = alphabet \<A>" unfolding sub_automaton_def by auto

proposition sub_automaton_well_defined:
  assumes "auto_well_defined \<A>" "s1 \<in> states \<A>" "s2 \<in> states \<A>"
  shows "auto_well_defined (sub_automaton \<A> s1 s2)"
  using assms unfolding auto_well_defined_def sub_automaton_def by auto

corollary language_well_def_sub_automaton:
  assumes "auto_well_defined \<A>" "s1 \<in> states \<A>" "s2 \<in> states \<A>"
  shows "omega_language_well_defined (omega_language_auto (sub_automaton \<A> s1 s2)) (alphabet (sub_automaton \<A> s1 s2))"
  using assms sub_automaton_well_defined automata_omega_language_are_well_defined by fast

theorem omega_power_omega_power_auto_in_omega_lang:
  assumes "auto_well_defined \<A>" "s' \<in> states \<A>"
  shows "omega_power_language (language_auto (sub_automaton \<A> s' s')) \<subseteq> omega_language_auto (sub_automaton \<A> s' s')"
proof - 
  let ?\<A> = "sub_automaton \<A> s' s'"
  {
    fix omega_word assume "omega_word \<in> omega_power_language (language_auto ?\<A>)"
    then obtain inf_word_list where inf_word_list: "\<forall> n . inf_word_list n \<in> language_auto ?\<A> \<and> inf_word_list n \<noteq> [] \<and> (\<forall> k . k < length (inf_word_list n) \<longrightarrow> omega_word (length (prefix_concat inf_word_list n) + k) = (inf_word_list n) ! k)" unfolding omega_power_language_def by blast
    {
      fix n 
      have "inf_word_list n \<in> language_auto ?\<A> \<and> inf_word_list n \<noteq> []" using inf_word_list by blast
      hence "\<exists> run . run_accepting run ?\<A> (inf_word_list n) \<and> inf_word_list n \<noteq> []" unfolding language_auto_def by blast
      then obtain run where run: "run_accepting run ?\<A> (inf_word_list n) \<and> inf_word_list n \<noteq> []" by blast
      hence "length run > 1" unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by auto
      hence "length (butlast run) > 0" by simp
      hence "butlast run \<noteq> []" by blast
      hence "\<exists> run . run_accepting run ?\<A> (inf_word_list n) \<and> butlast run \<noteq> []"  using run by blast 
    }    
    hence existence: "\<forall> n . \<exists> run . run_accepting run ?\<A> (inf_word_list n) \<and> butlast run \<noteq> []" unfolding language_auto_def by blast
    hence ex_0: "\<exists> run . run_accepting run ?\<A> (inf_word_list 0) \<and> butlast run \<noteq> []" by blast
    define inf_run_list where "inf_run_list = (\<lambda>n . (butlast (SOME run . run_accepting run ?\<A> (inf_word_list n) \<and> butlast run \<noteq> [])))"
    hence not_empty: "\<forall> n . inf_run_list n \<noteq> []" using existence tfl_some unfolding inf_run_list_def by (metis (mono_tags, lifting))
    hence unique: "\<forall> i . \<exists>! n . \<exists>! k . i = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n)" by (rule exists_unique_decomposition_forall)
    define omega_run where "omega_run = (\<lambda>n . omega_run_from_blocks inf_run_list n)"
    obtain s where s: "s = (THE s . \<exists> n k . 0 = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k)" using unique by blast
    have "\<exists>! s. \<exists> n k . 0 = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k" using add_diff_cancel_left' unique by metis
    hence "\<exists> n k . 0 = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k" using s the1_equality by blast
    then obtain k n where kn: "0 = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k" by metis
    hence "k = 0 \<and> length (prefix_concat inf_run_list n) = 0" using zero_eq_add_iff_both_eq_0 by force
    hence "k = 0 \<and> n = 0" using length_greater_0_conv not_empty length_prefix_concat by auto
    hence "s = (inf_run_list 0) ! 0" using kn by blast
    hence equi_0: "omega_run 0 = (inf_run_list 0) ! 0" using s unfolding omega_run_def omega_run_from_blocks_def by auto
    have "run_accepting (SOME run. run_accepting run ?\<A> (inf_word_list 0) \<and> butlast run \<noteq> []) ?\<A> (inf_word_list 0)" using tfl_some ex_0 by (metis (mono_tags, lifting))
    hence "(SOME run. run_accepting run ?\<A> (inf_word_list 0) \<and> butlast run \<noteq> []) ! 0 = initial_state ?\<A>" unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by blast
    hence "(inf_run_list 0) ! 0 = initial_state ?\<A>" using Eps_cong length_greater_0_conv not_empty nth_butlast unfolding inf_run_list_def by (metis (no_types, lifting))
    hence start: "omega_run 0 = initial_state ?\<A>" using equi_0 by simp
    have "auto_well_defined ?\<A>" using assms sub_automaton_well_defined by fast
    hence init: "omega_run 0 = initial_state ?\<A> \<and> initial_state ?\<A> \<in> states ?\<A>" using start unfolding auto_well_defined_def by blast
    {
      fix i
      have "run_accepting (SOME run. run_accepting run ?\<A> (inf_word_list i) \<and> butlast run \<noteq> []) ?\<A> (inf_word_list i)" using tfl_some existence by (metis (mono_tags, lifting))
      hence "length (SOME run. run_accepting run ?\<A> (inf_word_list i) \<and> butlast run \<noteq> []) = length (inf_word_list i) + 1" unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by blast
      hence "length (inf_word_list i) = length (inf_run_list i)" unfolding inf_run_list_def by force
    }
    hence length: "\<forall> i . length (inf_word_list i) = length (inf_run_list i)" by blast   
    {
      fix i
      obtain s where s: "s = (THE s . \<exists> n k . i = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k)" using unique by blast
      have "\<exists>! s . \<exists> n k . i = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k" using add_diff_cancel_left' unique by metis
      hence "\<exists> n k . i = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k" using s the1_equality by blast
      then obtain k n where kn: "i = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k" by metis
      hence equi_run: "omega_run i = (inf_run_list n) ! k" using s unfolding omega_run_def omega_run_from_blocks_def by auto
      have "run_accepting (SOME run. run_accepting run ?\<A> (inf_word_list i) \<and> butlast run \<noteq> []) ?\<A> (inf_word_list i)" using tfl_some existence by (metis (mono_tags, lifting))
      hence "length (SOME run. run_accepting run ?\<A> (inf_word_list i) \<and> butlast run \<noteq> []) = length (inf_word_list i) + 1" unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by blast
      hence "length (inf_word_list i) = length (inf_run_list i)" unfolding inf_run_list_def by force
      hence equi_word: "omega_word i = (inf_word_list n) ! k" using inf_word_list kn length length_prefix_concat_equi by metis
      let ?run_n = "(SOME run. run_accepting run ?\<A> (inf_word_list n) \<and> butlast run \<noteq> [])"
      have run_acc: "run_accepting ?run_n ?\<A> (inf_word_list n)" using tfl_some existence by (metis (mono_tags, lifting))
      hence "pseudo_run_well_defined ?run_n ?\<A> (initial_state ?\<A>) (inf_word_list n)" unfolding run_accepting_def run_well_defined_def by blast
      hence prun: "\<forall> i < length ?run_n - 1 . (?run_n ! i, (inf_word_list n) ! i, ?run_n ! (i + 1)) \<in> transitions ?\<A>" unfolding pseudo_run_well_defined_def by auto
      hence "\<forall> i < length (butlast ?run_n) - 1 . (?run_n ! i, (inf_word_list n) ! i, ?run_n ! (i + 1)) \<in> transitions ?\<A>" by auto
      hence trans_i: "\<forall> i < length (butlast ?run_n) - 1 . ((butlast ?run_n) ! i, (inf_word_list n) ! i, (butlast ?run_n) ! (i + 1)) \<in> transitions ?\<A>" by (simp add: nth_butlast)
      have inf_run_list_n: "inf_run_list n = butlast ?run_n" unfolding inf_run_list_def by blast
      hence trans: "\<forall> i < length (butlast ?run_n) - 1 . ((inf_run_list n) ! i, (inf_word_list n) ! i, (inf_run_list n) ! (i + 1)) \<in> transitions ?\<A>" using trans_i by presburger
      hence "(omega_run i, omega_word i, omega_run (i + 1)) \<in> transitions ?\<A>"
      proof (cases "k < length (inf_run_list n) - 1")
        case True
        obtain s1 where s1: "s1 = (THE s1 . \<exists> n1 k1 . (i + 1) = length (prefix_concat inf_run_list n1) + k1 \<and> k1 < length (inf_run_list n1) \<and> s1 = (inf_run_list n1) ! k1)" using unique by blast
        have "\<exists>! s1 . \<exists> n1 k1 . (i + 1) = length (prefix_concat inf_run_list n1) + k1 \<and> k1 < length (inf_run_list n1) \<and> s1 = (inf_run_list n1) ! k1" using add_diff_cancel_left' unique by metis
        hence "\<exists> n1 k1 . (i + 1) = length (prefix_concat inf_run_list n1) + k1 \<and> k1 < length (inf_run_list n1) \<and> s1 = (inf_run_list n1) ! k1" using s1 the1_equality by blast
        then obtain k1 n1 where kn1: "(i + 1) = length (prefix_concat inf_run_list n1) + k1 \<and> k1 < length (inf_run_list n1) \<and> s1 = (inf_run_list n1) ! k1" by metis
        hence equi_run1: "omega_run (i + 1) = (inf_run_list n1) ! k1" using s1 unfolding omega_run_def omega_run_from_blocks_def by auto
        have unique1: "\<exists>! n . \<exists>! k . (i + 1) = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n)" using unique by auto
        have "k + 1 < length (inf_run_list n) \<and> i + 1 = length (prefix_concat inf_run_list n) + (k + 1)" using True kn by force
        hence nk_equi: "n1 = n \<and> (k + 1) = k1" using kn1 unique1 add_diff_cancel_left' by metis
        hence run_i1: "omega_run (i + 1) = (inf_run_list n) ! (k + 1)" using equi_run1 by blast
        have "k < length ?run_n - 1" using True inf_run_list_n by auto
        hence "((inf_run_list n) ! k, (inf_word_list n) ! k, (inf_run_list n) ! (k + 1)) \<in> transitions ?\<A>" using trans True inf_run_list_n by force
        thus ?thesis using equi_run run_i1 equi_word by auto
      next
        case False
        hence kend: "k = length (inf_run_list n) - 1" using kn by linarith
        hence kless: "k < length (inf_run_list n)" using kn by linarith
        have last: "last ?run_n = s'" using run_acc unfolding run_accepting_def sub_automaton_def by simp
        have "length (butlast ?run_n) > 0" using inf_run_list_n not_empty by force
        hence ge1: "length ?run_n > 1" using length_butlast by simp
        hence "?run_n \<noteq> []" by force
        hence last_s': "?run_n ! (length ?run_n - 1) = s'" using list_properties_not_empty last by fastforce
        have k_len: "k = length ?run_n - 2" using kend unfolding inf_run_list_n by force
        hence equi_k: "(inf_run_list n) ! k = ?run_n ! (length ?run_n - 2)" using inf_run_list_n kless by (simp add: nth_butlast)
        have "length ?run_n - 1 = length ?run_n - 2 + 1" using ge1 simple_math by force
        hence "(?run_n ! (length ?run_n - 2), (inf_word_list n) ! (length ?run_n - 2), ?run_n ! (length ?run_n - 1)) \<in> transitions ?\<A>" using prun less_add_one by force
        hence trans: "((inf_run_list n) ! k, (inf_word_list n) ! k, s') \<in> transitions ?\<A>" using k_len equi_k last_s' by argo
        have "run_accepting (SOME run. run_accepting run ?\<A> (inf_word_list (n + 1)) \<and> butlast run \<noteq> []) ?\<A> (inf_word_list (n + 1))" using tfl_some existence by (metis (mono_tags, lifting))
        hence "(SOME run. run_accepting run ?\<A> (inf_word_list (n + 1)) \<and> butlast run \<noteq> []) ! 0 = initial_state ?\<A>" unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by blast
        hence "(inf_run_list (n + 1)) ! 0 = initial_state ?\<A>" using Eps_cong length_greater_0_conv not_empty nth_butlast unfolding inf_run_list_def by (metis (no_types, lifting))
        hence sucn_s': "(inf_run_list (n + 1)) ! 0 = s'" unfolding sub_automaton_def by auto
        have "length (prefix_concat inf_run_list (n + 1)) = length (prefix_concat inf_run_list n) + length (inf_run_list n)" by simp
        hence i_suc: "i + 1 = length (prefix_concat inf_run_list (n + 1))" using kn kend by linarith
        obtain s where s: "s = (THE s . \<exists> n k . i + 1 = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k)" using unique by blast
        have "\<exists>! s. \<exists> n k . i + 1 = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k" using add_diff_cancel_left' unique by metis
        hence "\<exists> n k . i + 1 = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k" using s the1_equality by blast
        then obtain k1 n1 where kn1: "i + 1 = length (prefix_concat inf_run_list n1) + k1 \<and> k1 < length (inf_run_list n1) \<and> s = (inf_run_list n1) ! k1" by metis
        have cand: "i + 1 = length (prefix_concat inf_run_list (n + 1)) + 0 \<and> 0 < length (inf_run_list (n + 1))" using i_suc not_empty by simp
        have "\<exists>! n . \<exists>! k . i + 1 = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n)" using unique by simp
        hence n_eq_m: "n1 = (n + 1) \<and> k1 = 0" using kn1 cand add_left_cancel by metis
        have "omega_run (i + 1) = s" using s unfolding omega_run_def omega_run_from_blocks_def by blast
        hence equi_i: "omega_run (i + 1) = (inf_run_list (n + 1)) ! 0" using kn1 n_eq_m s by blast
        hence "omega_run (i + 1) = s'" using sucn_s' by simp
        thus ?thesis using trans equi_run equi_word by argo
      qed
    }
    hence step: "\<forall> i . (omega_run i, omega_word i, omega_run (i + 1)) \<in> transitions ?\<A>" by blast
    {
      fix l
      obtain m where m: "length (prefix_concat inf_run_list m) > l" using assms Suc_le_lessD exists_unique_block_index not_empty unfolding return_index_start_def by metis
      let ?i = "length (prefix_concat inf_run_list m)"
      obtain s where s: "s = (THE s . \<exists> n k . ?i = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k)" using unique by blast
      have "\<exists>! s. \<exists> n k . ?i = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k" using add_diff_cancel_left' unique by metis
      hence "\<exists> n k . ?i = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k" using s the1_equality by blast
      then obtain k n where kn: "?i = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k" by metis
      have cand: "?i = length (prefix_concat inf_run_list m) + 0 \<and> 0 < length (inf_run_list m)" using not_empty by simp
      have "\<exists>! n . \<exists>! k . ?i = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n)" using unique by simp
      hence n_eq_m: "n = m \<and> k = 0" using kn cand add_left_cancel by metis
      have "omega_run ?i = s" using s unfolding omega_run_def omega_run_from_blocks_def by blast
      hence equi_i: "omega_run ?i = (inf_run_list m) ! 0" using kn n_eq_m s by blast
      have "run_accepting (SOME run. run_accepting run ?\<A> (inf_word_list m) \<and> butlast run \<noteq> []) ?\<A> (inf_word_list m)" using tfl_some existence by (metis (mono_tags, lifting))
      hence "(SOME run. run_accepting run ?\<A> (inf_word_list m) \<and> butlast run \<noteq> []) ! 0 = initial_state ?\<A>" unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by blast
      hence "(inf_run_list m) ! 0 = initial_state ?\<A>" using length_greater_0_conv not_empty nth_butlast unfolding inf_run_list_def by (metis (no_types, lifting))
      hence "omega_run ?i = initial_state ?\<A>" using equi_i by simp
      hence "omega_run ?i \<in> accepting_states ?\<A>" unfolding sub_automaton_def by force
      hence "\<exists> N > l . omega_run N \<in> accepting_states ?\<A>" using m by blast 
    }
    hence "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states ?\<A>" by argo
    hence "omega_run_accepting omega_run ?\<A> omega_word" using init step unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
    hence "omega_word \<in> omega_language_auto ?\<A>" unfolding omega_language_auto_def by blast
  }
  thus ?thesis by blast
qed

fun cut_omega_run_sub :: "'s omega_run \<Rightarrow> 's state \<Rightarrow> nat \<Rightarrow> nat" where
  "cut_omega_run_sub omega_run s' 0 = 0" |
  "cut_omega_run_sub omega_run s' (Suc n) = (LEAST i . i > cut_omega_run_sub omega_run s' n \<and> omega_run i = s')"

lemma cut_hits_s':
  assumes "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (sub_automaton \<A> s' s')"
  shows "omega_run (cut_omega_run_sub omega_run s' (Suc j)) = s' \<and> cut_omega_run_sub omega_run s' (Suc j) > cut_omega_run_sub omega_run s' j"
proof - 
  have existence: "\<forall> n . \<exists> N > n . omega_run N = s'" using assms unfolding sub_automaton_def by simp
  {
    fix j
    obtain n where n: "cut_omega_run_sub omega_run s' j = n" by simp
    have equi: "cut_omega_run_sub omega_run s' (Suc j) = (LEAST i . i > n \<and> omega_run i = s')" using n by simp
    hence mono: "cut_omega_run_sub omega_run s' (Suc j) > cut_omega_run_sub omega_run s' j" using n existence LeastI_ex by (metis (mono_tags, lifting))
    have "omega_run (cut_omega_run_sub omega_run s' (Suc j)) = s'" using equi existence LeastI_ex by (metis (mono_tags, lifting))
    hence "omega_run (cut_omega_run_sub omega_run s' (Suc j)) = s' \<and> cut_omega_run_sub omega_run s' (Suc j) > cut_omega_run_sub omega_run s' j" using mono by blast
  }
  thus ?thesis by blast
qed

corollary omega_run_cut_j_is_s':
  assumes "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (sub_automaton \<A> s' s')" "omega_run 0 = s'"
  shows "omega_run (cut_omega_run_sub omega_run s' j) = s'"
proof(cases j)
  case 0 thus ?thesis using assms by simp
next
  case (Suc nat) thus ?thesis using assms cut_hits_s' by metis
qed

lemma no_s'_between_cuts: "cut_omega_run_sub omega_run s' j < t \<and> t < cut_omega_run_sub omega_run s' (Suc j) \<Longrightarrow> omega_run t \<noteq> s'"
  using not_less_Least by auto

definition block_run_sub :: "'s omega_run \<Rightarrow> 's state \<Rightarrow> nat \<Rightarrow> 's run" where "block_run_sub omega_run s' j = map omega_run [cut_omega_run_sub omega_run s' j ..< cut_omega_run_sub omega_run s' (Suc j) + 1]"

definition block_word_sub :: "'a omega_word \<Rightarrow> 's omega_run \<Rightarrow> 's state \<Rightarrow> nat \<Rightarrow> 'a word" where "block_word_sub omega_word omega_run s' j = map omega_word [cut_omega_run_sub omega_run s' j ..< cut_omega_run_sub omega_run s' (Suc j)]"

lemma not_empty_block_word_sub:
  assumes "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (sub_automaton \<A> s' s')"
  shows "block_word_sub omega_word omega_run s' j \<noteq> []"
proof - 
  have "cut_omega_run_sub omega_run s' (Suc j) > cut_omega_run_sub omega_run s' j" using assms cut_hits_s' by metis
  hence "[cut_omega_run_sub omega_run s' j ..< cut_omega_run_sub omega_run s' (Suc j)] \<noteq> []" by simp
  thus ?thesis unfolding block_word_sub_def by blast
qed

lemma block_run_sub_accepting_in_sub_auto:
  assumes "omega_run_accepting omega_run (sub_automaton \<A> s' s') omega_word"
  shows "run_accepting (block_run_sub omega_run s' j) (sub_automaton \<A> s' s') (block_word_sub omega_word omega_run s' j)"
proof - 
  let ?\<A> = "sub_automaton \<A> s' s'"
  have "\<forall> n . (omega_run n, omega_word n, omega_run (n + 1)) \<in> transitions ?\<A> \<and> omega_run 0 = initial_state ?\<A> \<and> initial_state ?\<A> \<in> states ?\<A> \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states ?\<A>)" using assms unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
  hence props: "\<forall> n . (omega_run n, omega_word n, omega_run (n + 1)) \<in> transitions ?\<A> \<and> omega_run 0 = s' \<and> omega_run 0 = initial_state ?\<A> \<and> initial_state ?\<A> \<in> states ?\<A> \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states ?\<A>)" unfolding sub_automaton_def by force
  {
    fix k assume assm: "k < length (block_run_sub omega_run s' j) - 1"
    hence "k < length (block_run_sub omega_run s' j)" by force
    hence equik: "(block_run_sub omega_run s' j) ! k = omega_run (cut_omega_run_sub omega_run s' j + k)" using length_map length_upt nth_map_upt unfolding block_run_sub_def by metis
    have "k + 1 < length (block_run_sub omega_run s' j)" using assm by force
    hence equik1: "(block_run_sub omega_run s' j) ! (k + 1) = omega_run (cut_omega_run_sub omega_run s' j + k + 1)" using add.assoc length_map length_upt nth_map_upt unfolding block_run_sub_def by metis
    have "k < length (block_word_sub omega_word omega_run s' j)" using assm diff_add_inverse2 diff_commute length_map length_upt unfolding block_word_sub_def block_run_sub_def by metis
    hence equiw: "(block_word_sub omega_word omega_run s' j) ! k = omega_word (cut_omega_run_sub omega_run s' j + k)" using assm unfolding block_word_sub_def by force
    have "(omega_run (cut_omega_run_sub omega_run s' j + k), omega_word (cut_omega_run_sub omega_run s' j + k), omega_run (cut_omega_run_sub omega_run s' j + k + 1)) \<in> transitions ?\<A>" using props by blast
    hence "(block_run_sub omega_run s' j ! k, block_word_sub omega_word omega_run s' j ! k, block_run_sub omega_run s' j ! (k + 1)) \<in> transitions ?\<A>" using equik equik1 equiw by auto
  }
  hence trans: "\<forall> k < length (block_run_sub omega_run s' j) - 1 . (block_run_sub omega_run s' j ! k, block_word_sub omega_word omega_run s' j ! k, block_run_sub omega_run s' j ! (k + 1)) \<in> transitions ?\<A>" by blast
  have "cut_omega_run_sub omega_run s' (Suc j) > cut_omega_run_sub omega_run s' j" using props cut_hits_s' by metis
  hence len: "length [cut_omega_run_sub omega_run s' j ..< cut_omega_run_sub omega_run s' (Suc j) + 1] = length [cut_omega_run_sub omega_run s' j ..< cut_omega_run_sub omega_run s' (Suc j)] + 1" by auto
  hence length: "length (block_run_sub omega_run s' j) = length (block_word_sub omega_word omega_run s' j) + 1" unfolding block_word_sub_def block_run_sub_def by auto
  have "(block_run_sub omega_run s' j) ! 0 = omega_run (cut_omega_run_sub omega_run s' j)" using Nat.add_0_right len add_gr_0 length_upt less_numeral_extra(1) nth_map_upt unfolding block_run_sub_def by metis
  hence init: "(block_run_sub omega_run s' j) ! 0 = initial_state ?\<A> \<and> initial_state ?\<A> \<in> states ?\<A>" using props omega_run_cut_j_is_s' by metis
  have "block_run_sub omega_run s' j \<noteq> []" using length by auto
  hence "last (block_run_sub omega_run s' j) = omega_run (cut_omega_run_sub omega_run s' (Suc j))" unfolding block_run_sub_def by auto
  hence "last (block_run_sub omega_run s' j) = s'" using props cut_hits_s' by metis
  hence "last (block_run_sub omega_run s' j) \<in> accepting_states ?\<A>" unfolding sub_automaton_def by auto
  thus ?thesis using length init trans unfolding pseudo_run_well_defined_def run_well_defined_def run_accepting_def by blast
qed

theorem omega_lang_sub_auto_in_omega_power:
  assumes "auto_well_defined \<A>"
  shows "omega_language_auto (sub_automaton \<A> s' s') \<subseteq> omega_power_language (language_auto (sub_automaton \<A> s' s'))"
proof -
  let ?\<A> = "sub_automaton \<A> s' s'"
  {
    fix omega_word assume "omega_word \<in> omega_language_auto ?\<A>"
    then obtain omega_run where acc: "omega_run_accepting omega_run ?\<A> omega_word" unfolding omega_language_auto_def by blast
    hence inf: "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states ?\<A>" unfolding omega_run_accepting_def by blast
    define inf_word_list where "inf_word_list = (\<lambda>n . (block_word_sub omega_word omega_run s' n))"
    {
      fix j
      have run: "run_accepting (block_run_sub omega_run s' j) ?\<A> (block_word_sub omega_word omega_run s' j)" using acc block_run_sub_accepting_in_sub_auto by fast
      have "block_word_sub omega_word omega_run s' j \<noteq> []" using inf not_empty_block_word_sub by metis
      hence first_prop: "(block_word_sub omega_word omega_run s' j) \<in> language_auto ?\<A> \<and> block_word_sub omega_word omega_run s' j \<noteq> []" using run unfolding language_auto_def by blast
      {
        fix k assume k: "k < length (inf_word_list j)"
        have  "inf_word_list j = block_word_sub omega_word omega_run s' j" unfolding inf_word_list_def by simp
        hence index: "(inf_word_list j) ! k = omega_word (cut_omega_run_sub omega_run s' j + k)" using k unfolding block_word_sub_def by auto
        have "length (prefix_concat inf_word_list j) = cut_omega_run_sub omega_run s' j" unfolding inf_word_list_def
        proof (induction j)
          case 0 thus ?case by simp
        next
          case (Suc j)
          have ge: "cut_omega_run_sub omega_run s' (Suc j) > cut_omega_run_sub omega_run s' j" using inf cut_hits_s' by metis   
          have "prefix_concat inf_word_list (Suc j)  = prefix_concat inf_word_list j @ inf_word_list j" by simp
          hence "length (prefix_concat inf_word_list (Suc j)) = length (prefix_concat inf_word_list j) + length (inf_word_list j)" by simp
          thus ?case using Suc ge unfolding inf_word_list_def block_word_sub_def by force
        qed
        hence "omega_word (length (prefix_concat inf_word_list j) + k) = (inf_word_list j) ! k" using index by simp
      }
      hence "\<forall> k . k < length (inf_word_list j) \<longrightarrow> omega_word (length (prefix_concat inf_word_list j) + k) = (inf_word_list j) ! k" by blast
      hence "inf_word_list j \<in> language_auto ?\<A> \<and> inf_word_list j \<noteq> [] \<and> (\<forall> k . k < length (inf_word_list j) \<longrightarrow> omega_word (length (prefix_concat inf_word_list j) + k) = (inf_word_list j) ! k)" using first_prop unfolding inf_word_list_def by blast
    }
    hence "omega_word \<in> omega_power_language (language_auto ?\<A>)" unfolding omega_power_language_def by blast
  }
  thus ?thesis by blast
qed

theorem omega_power_language_correctness_sub:
  assumes "auto_well_defined \<A>" "s' \<in> states \<A>"
  shows "omega_language_auto (sub_automaton \<A> s' s') = omega_power_language (language_auto (sub_automaton \<A> s' s'))"
  using assms omega_lang_sub_auto_in_omega_power omega_power_omega_power_auto_in_omega_lang by fast

theorem sub_automaton_concat_lang:
  assumes "auto_well_defined \<A>" "s' \<in> accepting_states \<A>"
  shows "concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) s')) (omega_language_auto (sub_automaton \<A> s' s')) \<subseteq> omega_language_auto \<A>"
proof - 
  let ?\<A>1 = "sub_automaton \<A> (initial_state \<A>) s'"
  let ?\<A>2 = "sub_automaton \<A> s' s'"
  {
    fix omega_word' assume "omega_word' \<in> concatenation_omega_language (language_auto ?\<A>1) (omega_language_auto ?\<A>2)"
    then obtain word omega_word where omega_word': "omega_word' = merge_lists_fun word omega_word \<and>  word \<in> language_auto ?\<A>1 \<and> omega_word \<in> omega_language_auto ?\<A>2" unfolding concatenation_omega_language_def by blast
    then obtain run omega_run where omega_run: "run_accepting run ?\<A>1 word \<and> omega_run_accepting omega_run ?\<A>2 omega_word" unfolding language_auto_def omega_language_auto_def by auto
    hence props_run: "length run = length word + 1 \<and> run ! 0 = initial_state ?\<A>1 \<and> initial_state ?\<A>1 \<in> states ?\<A>1 \<and> (\<forall> i < length run - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions ?\<A>1) \<and> last run \<in> accepting_states ?\<A>1" unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by auto
    hence init: "run ! 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A> \<and> last run = s'" using assms unfolding auto_well_defined_def sub_automaton_def by auto
    have props_omega_run: "omega_run 0 = initial_state ?\<A>2 \<and> (\<forall> n . (omega_run n, omega_word n, omega_run (n + 1)) \<in> transitions ?\<A>2) \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states ?\<A>2)" using omega_run unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
    hence acc: "omega_run 0 = s' \<and> (\<forall> n . \<exists> N > n . omega_run N = s')" unfolding sub_automaton_def by auto
    define omega_run' where "omega_run' = merge_lists_fun (butlast run) omega_run"
    have "omega_run_accepting omega_run' \<A> omega_word'"
    proof(cases word)
      case Nil
      hence "length run = 1" using props_run by auto
      hence "run = [initial_state \<A>] \<and> last run = s'" using init list_with_one_element by fast
      hence s': "initial_state \<A> = s' \<and> butlast run = []" by auto
      hence equi_omega_run: "omega_run' = omega_run" unfolding omega_run'_def merge_lists_fun_def by force
      hence "omega_run 0 = initial_state \<A> \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>)" using assms s' acc by fastforce
      hence init_omega_run: "omega_run 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A> \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>)" using assms unfolding auto_well_defined_def by argo
      have "\<forall> n . (omega_run n, omega_word n, omega_run (n + 1)) \<in> transitions \<A>" using props_omega_run unfolding sub_automaton_def by force
      hence omega_run_acc: "omega_run_accepting omega_run \<A> omega_word" using init_omega_run unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
      have "omega_word' = omega_word" using omega_word' Nil unfolding merge_lists_fun_def by auto 
      thus ?thesis using equi_omega_run omega_run_acc by auto
    next
      case (Cons a as)
      hence "word \<noteq> []" by blast
      hence len: "run ! 0 = initial_state \<A> \<and> length run > 1" using props_run init by simp 
      hence "butlast run ! 0 = initial_state \<A>" using length_butlast nth_butlast zero_less_diff by metis
      hence "butlast run ! 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
      hence start: "omega_run' 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using len unfolding omega_run'_def merge_lists_fun_def by simp
      have not_empty_butlast: "length (butlast run) > 0" using len by simp
      have length: "length (butlast run) = length word" using props_run by simp
      {
        fix i
        consider (case1) "i < length (butlast run) - 1" | (case2) "i = length (butlast run) - 1" | (case3) "i > length (butlast run) - 1" by linarith
        hence "(omega_run' i, omega_word' i, omega_run' (i + 1)) \<in> transitions \<A>"
        proof cases
          case case1
          hence equi_i: "omega_run' i = (butlast run) ! i" unfolding omega_run'_def merge_lists_fun_def by force
          have equi_i1: "omega_run' (i + 1) = (butlast run) ! (i + 1)" using case1 unfolding omega_run'_def merge_lists_fun_def by force
          have equi_w: "omega_word' i = word ! i" using length case1 omega_word' unfolding merge_lists_fun_def by auto
          have equi_ri: "run ! i = (butlast run) ! i" using case1 add_lessD1 less_diff_conv nth_butlast by metis
          have equi_ri1: "run ! (i + 1) = (butlast run) ! (i + 1)" using case1 add_lessD1 less_diff_conv nth_butlast by metis
          have "(run ! i, word ! i, run ! (i + 1)) \<in> transitions ?\<A>1" using case1 props_run by simp
          hence "(run ! i, word ! i, run ! (i + 1)) \<in> transitions \<A>" unfolding sub_automaton_def by auto
          thus ?thesis using equi_i equi_i1 equi_w equi_ri equi_ri1 by argo
        next
          case case2
          hence le_i: "i < length run - 1" using len by auto
          hence trans: "(run ! i, word ! i, run ! (i + 1)) \<in> transitions ?\<A>1 \<and> last run = s'" using props_run init by blast
          have "run \<noteq> []" using len by force
          hence "last run = run ! (length run - 1)" using list_properties_not_empty by metis
          hence last: "run ! (i + 1) = last run" using case2 len by (simp add: props_run)
          have "run ! i = (butlast run) ! i" using nth_butlast le_i by force
          hence "((butlast run) ! i, word ! i, s') \<in> transitions ?\<A>1" using trans last by simp
          hence spez_trans: "((butlast run) ! i, word ! i, s') \<in> transitions \<A>" unfolding sub_automaton_def by simp
          have equi_i: "omega_run' i = (butlast run) ! i" using le_i case2 unfolding omega_run'_def merge_lists_fun_def by auto
          have "length (butlast run) = length run - 1" by auto
          hence "i + 1 = length run - 1" using case2 not_empty_butlast by linarith
          hence "omega_run' (i + 1) = omega_run 0" unfolding omega_run'_def merge_lists_fun_def by simp
          hence equi_i1: "omega_run' (i + 1) = s'" using acc by auto
          have "omega_word' i = word ! i" using length case2 le_i omega_word' unfolding merge_lists_fun_def by auto     
          thus ?thesis using spez_trans equi_i equi_i1 by simp
        next
          case case3
          hence equi_i: "omega_run' i = omega_run (i - length (butlast run))" unfolding omega_run'_def merge_lists_fun_def by fastforce
          have ge: "i + 1 - length (butlast run) = i - length (butlast run) + 1" using Nat.diff_add_assoc2 add_leD2 case3 discrete le_add_diff_inverse2 not_empty_butlast by metis
          have equi_i1: "omega_run' (i + 1) = omega_run (i + 1 - length (butlast run))" using case3 unfolding omega_run'_def merge_lists_fun_def by auto
          have equi_w: "omega_word' i = omega_word (i - length (butlast run))" using length case3 omega_word' unfolding merge_lists_fun_def by force
          hence "(omega_run (i - length (butlast run)), omega_word  (i - length (butlast run)), omega_run (i - length (butlast run) + 1)) \<in> transitions ?\<A>2" using props_omega_run by simp
          hence "(omega_run (i - length (butlast run)), omega_word  (i - length (butlast run)), omega_run (i - length (butlast run) + 1)) \<in> transitions \<A>" unfolding sub_automaton_def by force
          thus ?thesis using equi_i equi_i1 equi_w ge by argo
        qed
      }
      hence "\<forall> i . (omega_run' i, omega_word' i, omega_run' (i + 1)) \<in> transitions \<A>" by blast
      hence omega_run: "omega_run_well_defined omega_run' \<A> omega_word'" using start unfolding omega_pseudo_run_well_defined_def omega_run_well_defined_def by blast
      have acc: "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>" using assms acc by metis
      {
        fix n
        obtain n' where n': "n' = n + length (butlast run)" by simp
        then obtain N where N: "N > n' \<and> omega_run N \<in> accepting_states \<A>" using acc by blast
        hence "N > n + length (butlast run) \<and> omega_run N \<in> accepting_states \<A>" using n' by blast
        then obtain k where k: "N = k - length (butlast run)" using diff_add_inverse by metis
        hence "k > n \<and> k > length (butlast run) \<and> omega_run N \<in> accepting_states \<A>" using N n' by linarith
        hence props: "k > n \<and> k > length (butlast run) \<and> omega_run (k - length (butlast run)) \<in> accepting_states \<A>" using k by blast
        hence "omega_run' k = omega_run (k - length (butlast run))" unfolding omega_run'_def merge_lists_fun_def by simp
        hence "\<exists> N > n . omega_run' N \<in> accepting_states \<A>" using props by auto
      }
      thus ?thesis using omega_run unfolding omega_run_accepting_def by blast
    qed
    hence "omega_word' \<in> omega_language_auto \<A>" unfolding omega_language_auto_def by blast
  }
  thus ?thesis by blast
qed

corollary sub_automaton_concat_lang_over_all_f_right:
  assumes "auto_well_defined \<A>"
  shows "(\<Union> f \<in> (accepting_states \<A>) . concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))) \<subseteq> omega_language_auto \<A>"
  using assms sub_automaton_concat_lang by fast

theorem sub_automaton_concat_lang_over_all_f_left:
  assumes "auto_well_defined \<A>"
  shows "omega_language_auto \<A> \<subseteq> (\<Union> f \<in> (accepting_states \<A>) . concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f)))"
proof - 
  {
    fix omega_word assume "omega_word \<in> omega_language_auto \<A>"
    then obtain omega_run where "omega_run_accepting omega_run \<A> omega_word" unfolding omega_language_auto_def by blast
    hence omega_run: "omega_run_well_defined omega_run \<A> omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>)" unfolding omega_run_accepting_def by blast
    hence infinite: "infinite {N . omega_run N \<in> accepting_states \<A>}" using infinite_set by blast
    have finite: "finite (accepting_states \<A>)" using assms NFA_is_finite by blast
    have "{N . omega_run N \<in> accepting_states \<A>} = (\<Union> f \<in> accepting_states \<A> . {N . omega_run N = f})" by blast
    hence "\<exists> f \<in> accepting_states \<A> . infinite {N . omega_run N = f}" using infinite finite by auto
    then obtain f where f: "f \<in> accepting_states \<A> \<and> infinite {N . omega_run N = f}" by blast
    hence "\<forall> n . \<exists> N > n . N \<in> {n . omega_run n = f}" using finite_nat_set_iff_bounded_le not_le_imp_less by metis
    hence props: "omega_run_well_defined omega_run \<A> omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N = f)" using omega_run by simp
    then obtain i where i: "i = (LEAST n . omega_run n = f)" by simp
    have "\<exists> n . omega_run n = f" using props by blast
    hence ex: "omega_run (LEAST n . omega_run n = f) = f" by (rule LeastI_ex) 
    define run' where "run' = pre_omega_run omega_run i"
    define word where "word = pre_omega_word omega_word i"
    have "pseudo_run_well_defined run' \<A> (initial_state \<A>) word \<and> last run' = omega_run i" using omega_run_implies_pre_run_well_def omega_run unfolding  omega_run_well_defined_def run'_def word_def by metis
    hence "pseudo_run_well_defined run' (sub_automaton \<A> (initial_state \<A>) f) (initial_state \<A>) word \<and> last run' = f" using ex i inheritance_pseudo_run_sub_automaton by metis
    hence "run_accepting run' (sub_automaton \<A> (initial_state \<A>) f) word" unfolding run_well_defined_def run_accepting_def sub_automaton_def by simp
    hence word_acc: "word \<in> language_auto (sub_automaton \<A> (initial_state \<A>) f)" unfolding language_auto_def by blast
    define omega_run_de where "omega_run_de = (\<lambda>n . omega_run (n + i))"
    define omega_word_de where "omega_word_de = (\<lambda>n . omega_word (n + i))"
    have "\<forall> n . (omega_run_de n, omega_word_de n, omega_run_de (n + 1)) \<in> transitions \<A>" using omega_run unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def omega_run_de_def omega_word_de_def by simp
    hence trans: "\<forall> n . (omega_run_de n, omega_word_de n, omega_run_de (n + 1)) \<in> transitions (sub_automaton \<A> f f)" unfolding sub_automaton_def by auto
    have "omega_run_de 0 = omega_run i" unfolding omega_run_de_def by simp
    hence "omega_run_de 0 = f" using ex i by simp
    hence "omega_run_de 0 = initial_state (sub_automaton \<A> f f) \<and> initial_state (sub_automaton \<A> f f) \<in> states (sub_automaton \<A> f f)" using f assms unfolding auto_well_defined_def sub_automaton_def by auto
    hence omega_run_well_def: "omega_run_well_defined omega_run_de (sub_automaton \<A> f f) omega_word_de" using trans unfolding omega_pseudo_run_well_defined_def omega_run_well_defined_def by blast
    {
      fix n 
      obtain k where k: "k = n + i + 1" by auto
      obtain N where N: "N > k \<and> omega_run N = f" using props by blast
      hence "omega_run_de (N - i) = omega_run N" using k unfolding omega_run_de_def by auto
      hence "omega_run_de (N - i) = f" using N by blast
      hence "omega_run_de (N - i) \<in> accepting_states (sub_automaton \<A> f f)" unfolding sub_automaton_def by auto
      hence "\<exists> N > n . omega_run_de N \<in> accepting_states (sub_automaton \<A> f f)" using k N add_lessD1 less_diff_conv by metis
    }
    hence "\<forall> n . \<exists> N > n . omega_run_de N \<in> accepting_states (sub_automaton \<A> f f)" by blast
    hence "omega_run_accepting omega_run_de (sub_automaton \<A> f f) omega_word_de" using omega_run_well_def unfolding omega_run_accepting_def by blast
    hence omega_word_acc: "omega_word_de \<in> omega_language_auto (sub_automaton \<A> f f)" unfolding omega_language_auto_def by blast
    have "omega_word = merge_lists_fun word omega_word_de" unfolding merge_lists_fun_def omega_word_de_def word_def pre_omega_word_def by auto
    hence "omega_word \<in> concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))" using word_acc omega_word_acc unfolding concatenation_omega_language_def by blast
    hence "\<exists> f \<in> accepting_states \<A> . omega_word \<in> concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))" using f by blast
  }
  thus ?thesis by blast
qed

theorem language_sub_automaton_equivalence:
  assumes "auto_well_defined \<A>"
  shows "(\<Union> f \<in> (accepting_states \<A>) . concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))) = omega_language_auto \<A>"
  using assms sub_automaton_concat_lang_over_all_f_right sub_automaton_concat_lang_over_all_f_left by fast

definition omega_RX :: "('s, 'a) automaton \<Rightarrow> 's state \<Rightarrow> 'a omega_regular_expression" where "omega_RX \<A> f = (SOME r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f)))"

lemma language_of_omega_RX:
  assumes "\<exists> r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))"
  shows "language_omega_reg_exp (omega_RX \<A> f) = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))"
  using assms someI_ex unfolding omega_RX_def by (metis (mono_tags, lifting))

proposition RX_well_def: 
  assumes "\<exists> r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))"
  shows "omega_RE_well_defined (omega_RX \<A> f) (alphabet \<A>)"
  using assms someI_ex unfolding omega_RX_def by (metis (mono_tags, lifting))

fun omega_RX_alternation :: "('s, 'a) automaton \<Rightarrow> 's state list \<Rightarrow> 'a omega_regular_expression" where
  "omega_RX_alternation \<A> [] = Omega_power Empty_set" |
  "omega_RX_alternation \<A> (f # acc_states) = Omega_alternation (omega_RX \<A> f) (omega_RX_alternation \<A> acc_states)"

proposition omega_RX_alternation_well_def: 
  assumes "auto_well_defined \<A>"
  shows "\<forall> f \<in> set acc_states . \<exists> r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f)) \<Longrightarrow> omega_RE_well_defined (omega_RX_alternation \<A> acc_states) (alphabet \<A>)"
proof(induction acc_states)
  case Nil thus ?case using assms empty_set_well_defined omega_inheritance_omega_power_well_def by fastforce
next
  case (Cons f acc_states)
  hence "f \<in> set (f # acc_states)" by force
  hence "\<exists> r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))" using Cons by blast
  hence "omega_RE_well_defined (omega_RX \<A> f) (alphabet \<A>)" using RX_well_def by fast 
  thus ?case using Cons omega_inheritance_alternation_well_def by auto
qed

lemma RX_big_alt_list_omega_language: "\<forall> f \<in> set acc_states . \<exists> r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f)) \<Longrightarrow> language_omega_reg_exp (omega_RX_alternation \<A> acc_states) = (\<Union> f \<in> (set acc_states) . concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f)))"
proof(induction acc_states)
  case Nil
  thus ?case using omega_power_of_empty_lan by auto
next
  case (Cons f acc_states)
  hence "f \<in> set (f # acc_states)" by auto
  hence "\<exists> r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))" using Cons by fast
  hence lang: "language_omega_reg_exp (omega_RX \<A> f) = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))" using language_of_omega_RX by fast
  have "language_omega_reg_exp (omega_RX_alternation \<A> (f # acc_states)) = language_omega_reg_exp (omega_RX \<A> f) \<union> language_omega_reg_exp (omega_RX_alternation \<A> acc_states)" by simp
  hence "language_omega_reg_exp (omega_RX_alternation \<A> (f # acc_states)) = language_omega_reg_exp (omega_RX \<A> f) \<union> (\<Union> f \<in> (set acc_states) . concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f)))" using Cons by auto
  thus ?case using lang by simp
qed

lemma enum_accepting_states:
  assumes "auto_well_defined \<A>"
  shows "set (enum_of_finite (accepting_states \<A>)) = accepting_states \<A>"
  using assms enum_of_finite_set_is_correct NFA_is_finite by blast

corollary RX_big_alt_list_omega_language_acc:
  assumes "auto_well_defined \<A>" "\<forall> f \<in> (accepting_states \<A>) . \<exists> r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))"
  shows "language_omega_reg_exp (omega_RX_alternation \<A> (enum_of_finite (accepting_states \<A>))) = (\<Union> f \<in> (accepting_states \<A>) . concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f)))"
proof -
  have "\<forall> f \<in> set (enum_of_finite (accepting_states \<A>)) . \<exists> r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))" using assms enum_accepting_states by blast
  hence "language_omega_reg_exp (omega_RX_alternation \<A> (enum_of_finite (accepting_states \<A>))) = (\<Union> f \<in> set (enum_of_finite (accepting_states \<A>)) . concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f)))" using RX_big_alt_list_omega_language by force
  thus ?thesis using assms enum_accepting_states by force
qed

definition RX_big_alternation_omega :: "('s, 'a) automaton \<Rightarrow> 'a omega_regular_expression" where "RX_big_alternation_omega \<A> = omega_RX_alternation \<A> (enum_of_finite (accepting_states \<A>))"

proposition RX_big_alternation_omega_well_def:
  assumes "auto_well_defined \<A>" "\<forall> f \<in> accepting_states \<A> . \<exists> r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))"
  shows "omega_RE_well_defined (RX_big_alternation_omega \<A>) (alphabet \<A>)"
  using omega_RX_alternation_well_def assms enum_accepting_states unfolding RX_big_alternation_omega_def by blast

theorem RX_big_alternation_omega_language:
  assumes "auto_well_defined \<A>" "\<forall> f \<in> accepting_states \<A> . \<exists> r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))"
  shows "language_omega_reg_exp (RX_big_alternation_omega \<A>) = (\<Union> f \<in> (accepting_states \<A>) . concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f)))"
  using assms RX_big_alt_list_omega_language_acc unfolding RX_big_alternation_omega_def by blast

text \<open>Key result for showing equivalence of expressive power between omega_RE and NBA: NBA --> omega_RE\<close>
theorem auto_implies_existence_of_omega_regular_expression:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)"
  shows "\<exists> (r :: 'a omega_regular_expression) . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = omega_language_auto \<A>"
proof - 
  have props: "initial_state \<A> \<in> states \<A> \<and> (\<forall> f \<in> accepting_states \<A> . f \<in> states \<A>)" using assms unfolding auto_well_defined_def by blast
  have finite: "finite (accepting_states \<A>)" using assms NFA_is_finite by blast
  {
    fix f assume f: "f \<in> accepting_states \<A>"
    hence "auto_well_defined (sub_automaton \<A> (initial_state \<A>) f) \<and> auto_well_defined (sub_automaton \<A> f f)" using props assms sub_automaton_well_defined by fast
    then obtain r1 r2 where r1: "RE_well_defined r1 (alphabet \<A>) \<and> language_reg_exp r1 = language_auto (sub_automaton \<A> (initial_state \<A>) f) \<and> RE_well_defined r2 (alphabet \<A>) \<and> language_reg_exp r2 = language_auto (sub_automaton \<A> f f)" using alphabet_sub_automaton auto_implies_existence_of_regular_expression by metis
    hence "omega_RE_well_defined (Omega_power r2) (alphabet \<A>) \<and> language_omega_reg_exp (Omega_power r2) = omega_power_language (language_auto (sub_automaton \<A> f f))" using omega_inheritance_omega_power_well_def by auto
    hence "omega_RE_well_defined (Omega_power r2) (alphabet \<A>) \<and> language_omega_reg_exp (Omega_power r2) = omega_language_auto (sub_automaton \<A> f f)" using assms props f omega_power_language_correctness_sub by fast
    hence "omega_RE_well_defined (Left_concatenation r1 (Omega_power r2)) (alphabet \<A>) \<and> language_omega_reg_exp (Left_concatenation r1 (Omega_power r2)) = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))" using r1 by (simp add: omega_inheritance_concatenation_well_def)
    hence "\<exists> r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))" by blast
  }
  hence "\<forall> f \<in> accepting_states \<A> . \<exists> r . omega_RE_well_defined r (alphabet \<A>) \<and> language_omega_reg_exp r = concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f))" by blast
  hence "omega_RE_well_defined (RX_big_alternation_omega \<A>) (alphabet \<A>) \<and> language_omega_reg_exp (RX_big_alternation_omega \<A>) = (\<Union> f \<in> (accepting_states \<A>) . concatenation_omega_language (language_auto (sub_automaton \<A> (initial_state \<A>) f)) (omega_language_auto (sub_automaton \<A> f f)))" using assms RX_big_alternation_omega_well_def RX_big_alternation_omega_language by force
  hence "omega_RE_well_defined (RX_big_alternation_omega \<A>) (alphabet \<A>) \<and> language_omega_reg_exp (RX_big_alternation_omega \<A>) = omega_language_auto \<A>" using assms language_sub_automaton_equivalence by auto
  thus ?thesis by auto
qed

theorem expressive_power_auto_omega_RE_main:
  assumes "infinite (UNIV :: 's set)"
  shows "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = omega_language_auto NFA_\<A>} = {L . \<exists> (r :: 'a omega_regular_expression) . omega_RE_well_defined r \<Sigma> \<and> L = language_omega_reg_exp r}"
  using assms auto_implies_existence_of_omega_regular_expression omega_regular_expression_implies_existence_of_auto by fast

end