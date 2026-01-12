theory regular_expressions

imports Main automaton_kleene_star

begin

text \<open>Author: Benno Thalmann, last update: 10.11.2025, Addition to masterarbeit_benno_thalmann\<close>

datatype 'a regular_expression = Empty_set | Empty_string | Singleton "'a symbol" | Concatenation "'a regular_expression" "'a regular_expression" | Alternation "'a regular_expression" "'a regular_expression" | Kleene_star "'a regular_expression"

fun alphabet_RE :: "'a regular_expression \<Rightarrow> 'a set" where
  "alphabet_RE Empty_set = {}" |
  "alphabet_RE Empty_string = {}" |
  "alphabet_RE (Singleton a) = {a}" |
  "alphabet_RE (Concatenation r1 r2) = alphabet_RE r1 \<union> alphabet_RE r2" |
  "alphabet_RE (Alternation r1 r2) = alphabet_RE r1 \<union> alphabet_RE r2" |
  "alphabet_RE (Kleene_star r) = alphabet_RE r"

lemma finite_alphabet_RE: "finite (alphabet_RE r)"
  by (induction r) auto

definition RE_well_defined :: "'a regular_expression \<Rightarrow> 'a alphabet \<Rightarrow> bool" where "RE_well_defined r \<Sigma> = (alphabet_RE r \<subseteq> \<Sigma> \<and> finite \<Sigma>)"

theorem "RE_well_defined r (alphabet_RE r)"
  using finite_alphabet_RE unfolding RE_well_defined_def by auto

lemma inheritance_alternation_well_def:
  assumes "RE_well_defined r1 \<Sigma>" "RE_well_defined r2 \<Sigma>"
  shows "RE_well_defined (Alternation r1 r2) \<Sigma>"
  using assms unfolding RE_well_defined_def by simp

lemma inheritance_concatenation_well_def:
  assumes "RE_well_defined r1 \<Sigma>" "RE_well_defined r2 \<Sigma>"
  shows "RE_well_defined (Concatenation r1 r2) \<Sigma>"
  using assms unfolding RE_well_defined_def by simp

lemma inheritance_kleene_star_well_def:
  assumes "RE_well_defined r \<Sigma>"
  shows "RE_well_defined (Kleene_star r) \<Sigma>"
  using assms unfolding RE_well_defined_def by simp

fun language_reg_exp :: "'a regular_expression \<Rightarrow> 'a language" where
  "language_reg_exp Empty_set = {}" |
  "language_reg_exp Empty_string = {[]}" |
  "language_reg_exp (Singleton a) = {[a]}" |
  "language_reg_exp (Concatenation r1 r2) = concatenation_language (language_reg_exp r1) (language_reg_exp r2)" |
  "language_reg_exp (Alternation r1 r2) = language_reg_exp r1 \<union> language_reg_exp r2" |
  "language_reg_exp (Kleene_star r) = kleene_star_language (language_reg_exp r)"

proposition word_in_language_reg_is_well_defined: "word \<in> language_reg_exp r \<and> RE_well_defined r \<Sigma> \<Longrightarrow> word_well_defined word \<Sigma>"
proof(induction r arbitrary: word)
  case Empty_set thus ?case by auto
next
  case Empty_string thus ?case unfolding word_well_defined_def by auto
next
  case (Singleton x) thus ?case unfolding word_well_defined_def RE_well_defined_def by auto
next
  case (Concatenation r1 r2)
  hence "word \<in> concatenation_language (language_reg_exp r1) (language_reg_exp r2)" by auto
  hence "word \<in> {word1 @ word2 | word1 word2 . word1 \<in> (language_reg_exp r1) \<and> word2 \<in> (language_reg_exp r2)}" unfolding concatenation_language_def by blast
  then obtain word1 word2 where word: "word = word1 @ word2 \<and> word1 \<in> (language_reg_exp r1) \<and> word2 \<in> (language_reg_exp r2)" by blast
  hence "word_well_defined word1 \<Sigma> \<and> word_well_defined word2 \<Sigma>" using Concatenation word unfolding RE_well_defined_def by auto
  thus ?case using word word_well_def_append by blast
next
  case (Alternation r1 r2) thus ?case unfolding word_well_defined_def RE_well_defined_def by auto
next
  case (Kleene_star r)
  hence "word \<in> kleene_star_language (language_reg_exp r)" by auto
  then obtain i where "word \<in> kleene_star_language_helper (language_reg_exp r) i" unfolding kleene_star_language_def by blast
  thus ?case
  proof(induction i arbitrary: word)
    case 0 thus ?case unfolding word_well_defined_def by auto
  next
    case (Suc i)
    hence "word \<in> concatenation_language (kleene_star_language_helper (language_reg_exp r) i) (language_reg_exp r)" by auto
    hence "word \<in> {word1 @ word2 | word1 word2 . word1 \<in> (kleene_star_language_helper (language_reg_exp r) i) \<and> word2 \<in> (language_reg_exp r)}" unfolding concatenation_language_def by blast
    then obtain word1 word2 where word: "word = word1 @ word2 \<and> word1 \<in> (kleene_star_language_helper (language_reg_exp r) i) \<and> word2 \<in> (language_reg_exp r)" by blast
    hence "word_well_defined word1 \<Sigma> \<and> word_well_defined word2 \<Sigma>" using word Kleene_star Suc unfolding RE_well_defined_def by auto
    thus ?case using word word_well_def_append by auto
  qed
qed

corollary word_in_language_re_is_well_defined: "word \<in> language_reg_exp r \<Longrightarrow> word_well_defined word (alphabet_RE r)"
  using word_in_language_reg_is_well_defined finite_alphabet_RE unfolding RE_well_defined_def by blast

proposition well_def_REs_language_is_well_def: "RE_well_defined r \<Sigma> \<Longrightarrow> language_well_defined (language_reg_exp r) \<Sigma>"
  using word_in_language_reg_is_well_defined unfolding language_well_defined_def by blast

corollary lang_well_def_of_RE: "language_well_defined (language_reg_exp r) (alphabet_RE r)"
  using word_in_language_re_is_well_defined unfolding language_well_defined_def by blast





definition \<A>_empty_set :: "'a alphabet \<Rightarrow> (nat, 'a) automaton" where "\<A>_empty_set \<Sigma> = Automaton {0} \<Sigma> {} 0 {}"

proposition automaton_for_empty_set:
  assumes "finite \<Sigma>"
  shows "auto_well_defined (\<A>_empty_set \<Sigma>) \<and> alphabet (\<A>_empty_set \<Sigma>) = \<Sigma> \<and> language_auto (\<A>_empty_set \<Sigma>) = {}"
  using assms no_acc_states unfolding auto_well_defined_def \<A>_empty_set_def by force

corollary language_well_def_empty_set_auto:
  assumes "finite \<Sigma>"
  shows "language_well_defined (language_auto (\<A>_empty_set \<Sigma>)) (alphabet (\<A>_empty_set \<Sigma>))"
  using automaton_for_empty_set assms automata_language_are_well_defined by auto

corollary existence_auto_empty_set:
  assumes "finite (\<Sigma> :: 'a alphabet)" "infinite (UNIV :: 's set)"
  shows "\<exists> empty_set_\<A> :: ('s, 'a) automaton . auto_well_defined empty_set_\<A> \<and> alphabet empty_set_\<A> = \<Sigma> \<and> language_auto empty_set_\<A> = {}"
  using assms automaton_for_empty_set existence_soft_iso_auto_lang by fast

definition \<A>_empty_string :: "'a alphabet \<Rightarrow> (nat, 'a) automaton" where "\<A>_empty_string \<Sigma> = Automaton {0} \<Sigma> {} 0 {0}"

lemma length_run_A_empty_string:
  assumes "run \<noteq> [] \<and> (\<forall> i < length run - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions (\<A>_empty_string \<Sigma>))"
  shows "length run = 1"
proof(rule ccontr)
  assume "length run \<noteq> 1"
  hence "length run > 1 \<or> length run = 0" by linarith
  then consider (case1) "length run = 0" | (case2) "length run > 1" by presburger
  thus False
  proof cases
    case case1 thus ?thesis using assms by fast
  next
    case case2
    hence "(run ! 0, word ! 0, run ! (0 + 1)) \<in> transitions (\<A>_empty_string \<Sigma>)" using assms by simp
    thus ?thesis unfolding \<A>_empty_string_def by fastforce
  qed
qed

theorem empty_string_lang: "{[]} = language_auto (\<A>_empty_string \<Sigma>)"
proof -
  have "run_accepting [0] (\<A>_empty_string \<Sigma>) []" unfolding \<A>_empty_string_def run_accepting_def run_well_defined_def pseudo_run_well_defined_def by force
  hence left: "{[]} \<subseteq> language_auto (\<A>_empty_string \<Sigma>)" unfolding language_auto_def by fast
  {
    fix word assume "word \<in> language_auto (\<A>_empty_string \<Sigma>)"
    then obtain run where run: "run_accepting run (\<A>_empty_string \<Sigma>) word" unfolding language_auto_def by auto
    hence props: "run \<noteq> [] \<and> length run = length word + 1 \<and> run ! 0 = 0 \<and> (\<forall> i < length run - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions (\<A>_empty_string \<Sigma>))" unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def \<A>_empty_string_def by force
    hence "length run = 1" using length_run_A_empty_string by blast
    hence "run = [0] \<and> word = []" using props list_with_one_element by force
    hence "word \<in> {[]}" by fast
  }
  thus ?thesis using left by blast
qed

proposition automaton_for_empty_string:
  assumes "finite \<Sigma>"
  shows "auto_well_defined (\<A>_empty_string \<Sigma>) \<and> alphabet (\<A>_empty_string \<Sigma>) = \<Sigma> \<and> language_auto (\<A>_empty_string \<Sigma>) = {[]}"
  using assms empty_string_lang unfolding auto_well_defined_def \<A>_empty_string_def by auto

corollary language_well_def_empty_string_auto:
  assumes "finite \<Sigma>"
  shows "language_well_defined (language_auto (\<A>_empty_string \<Sigma>)) (alphabet (\<A>_empty_string \<Sigma>))"
  using automaton_for_empty_string assms automata_language_are_well_defined by auto

corollary existence_auto_empty_string:
  assumes "finite (\<Sigma> :: 'a alphabet)" "infinite (UNIV :: 's set)"
  shows "\<exists> empty_string_\<A> :: ('s, 'a) automaton . auto_well_defined empty_string_\<A> \<and> alphabet empty_string_\<A> = \<Sigma> \<and> language_auto empty_string_\<A> = {[]}"
  using assms automaton_for_empty_string existence_soft_iso_auto_lang by metis

definition \<A>_singleton :: "'a alphabet \<Rightarrow> 'a symbol \<Rightarrow> (nat, 'a) automaton" where "\<A>_singleton \<Sigma> a = Automaton {0, 1} \<Sigma> {(0, a, 1)} 0 {1}"

lemma length_run_A_singleton:
  assumes "run \<noteq> [] \<and> (\<forall> i < length run - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions (\<A>_singleton \<Sigma> a))"
  shows "length run = 1 \<or> length run = 2"
proof(rule ccontr)
  assume "\<not> (length run = 1 \<or> length run = 2)"
  hence "length run = 0 \<or> length run > 2" by linarith
  then consider (case1) "length run = 0" | (case2) "length run > 2" by presburger
  thus False
  proof cases
    case case1 thus ?thesis using assms by fast
  next
    case case2
    hence "(run ! 0, word ! 0, run ! (0 + 1)) \<in> transitions (\<A>_singleton \<Sigma> a) \<and> (run ! 1, word ! 1, run ! (1 + 1)) \<in> transitions (\<A>_singleton \<Sigma> a)" using assms by force
    thus ?thesis unfolding \<A>_singleton_def by force
  qed
qed

theorem singleton_lang: "{[a]} = language_auto (\<A>_singleton \<Sigma> a)"
proof -
  have "run_accepting [0, 1] (\<A>_singleton \<Sigma> a) [a]" unfolding \<A>_singleton_def run_accepting_def run_well_defined_def pseudo_run_well_defined_def by force
  hence left: "{[a]} \<subseteq> language_auto (\<A>_singleton \<Sigma> a)" unfolding language_auto_def by fast
  {
    fix word assume "word \<in> language_auto (\<A>_singleton \<Sigma> a)"
    then obtain run where run: "run_accepting run (\<A>_singleton \<Sigma> a) word" unfolding language_auto_def by auto
    hence props: "run \<noteq> [] \<and> length run = length word + 1 \<and> run ! 0 = 0 \<and> (\<forall> i < length run - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions (\<A>_singleton \<Sigma> a))" unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def \<A>_singleton_def by force
    hence "length run = 1 \<or> length run = 2" using length_run_A_singleton by metis
    then consider (case1) "length run = 1" | (case2) "length run = 2" by argo
    hence "word \<in> {[a]}"
    proof cases
      case case1
      hence "run = [0] \<and> word = []" using props list_with_one_element by force
      hence "last run \<notin> accepting_states (\<A>_singleton \<Sigma> a)" unfolding \<A>_singleton_def by auto
      thus ?thesis using run unfolding run_accepting_def by fast
    next
      case case2
      hence "length word = 1 \<and> (run ! 0, word ! 0, run ! (0 + 1)) \<in> transitions (\<A>_singleton \<Sigma> a)" using props by force
      hence "length word = 1 \<and> word ! 0 = a" unfolding \<A>_singleton_def by force
      hence "word = [a]" using list_with_one_element by metis
      thus ?thesis by simp
    qed
  }
  thus ?thesis using left by blast
qed

proposition automaton_for_singleton:
  assumes "finite \<Sigma>" "a \<in> \<Sigma>"
  shows "auto_well_defined (\<A>_singleton \<Sigma> a) \<and> alphabet (\<A>_singleton \<Sigma> a) = \<Sigma> \<and> language_auto (\<A>_singleton \<Sigma> a) = {[a]}"
  using assms singleton_lang unfolding auto_well_defined_def \<A>_singleton_def by force

corollary language_well_def_singleton_auto:
  assumes "finite \<Sigma>" "a \<in> \<Sigma>"
  shows "language_well_defined (language_auto (\<A>_singleton \<Sigma> a)) (alphabet (\<A>_singleton \<Sigma> a))"
  using automaton_for_singleton assms automata_language_are_well_defined by fast

corollary existence_auto_singleton:
  assumes "finite (\<Sigma> :: 'a alphabet)" "a \<in> \<Sigma>" "infinite (UNIV :: 's set)"
  shows "\<exists> singleton_\<A> :: ('s, 'a) automaton . auto_well_defined singleton_\<A> \<and> alphabet singleton_\<A> = \<Sigma> \<and> language_auto singleton_\<A> = {[a]}"
  using assms automaton_for_singleton existence_soft_iso_auto_lang by metis

text \<open>Key result for showing equivalence of expressive power between RE and FA: RE --> FA\<close>
theorem regular_expression_implies_existence_of_auto:
  assumes "infinite (UNIV :: 's set)"
  shows "RE_well_defined (r :: 'a regular_expression) \<Sigma> \<Longrightarrow> \<exists> \<A> :: ('s, 'a) automaton . auto_well_defined \<A> \<and> alphabet \<A> = \<Sigma> \<and> language_auto \<A> = language_reg_exp r"
proof(induction r)
  case Empty_set thus ?case using existence_auto_empty_set assms unfolding RE_well_defined_def by auto
next
  case Empty_string thus ?case using existence_auto_empty_string assms unfolding RE_well_defined_def by auto
next
  case (Singleton a) thus ?case using existence_auto_singleton assms unfolding RE_well_defined_def by fastforce
next
  case (Concatenation r1 r2)
  hence well_def: "RE_well_defined r1 \<Sigma> \<and> RE_well_defined r2 \<Sigma>" unfolding RE_well_defined_def by auto
  then obtain \<A>1 :: "('s, 'a) automaton" where A1: "auto_well_defined \<A>1 \<and> alphabet \<A>1 = \<Sigma> \<and> language_auto \<A>1 = language_reg_exp r1" using Concatenation by blast
  obtain \<A>2 :: "('s, 'a) automaton" where A2: "auto_well_defined \<A>2 \<and> alphabet \<A>2 = \<Sigma> \<and> language_auto \<A>2 = language_reg_exp r2" using Concatenation well_def by presburger
  then obtain conc_\<A> :: "('s, 'a) automaton" where "auto_well_defined conc_\<A> \<and> alphabet conc_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> language_auto conc_\<A> = concatenation_language (language_auto \<A>1) (language_auto \<A>2)" using A1 assms existence_of_conc_same_type by metis
  thus ?case using A1 A2 by auto
next
  case (Alternation r1 r2)
  hence well_def: "RE_well_defined r1 \<Sigma> \<and> RE_well_defined r2 \<Sigma>" unfolding RE_well_defined_def by auto
  then obtain \<A>1 :: "('s, 'a) automaton" where A1: "auto_well_defined \<A>1 \<and> alphabet \<A>1 = \<Sigma> \<and> language_auto \<A>1 = language_reg_exp r1" using Alternation by blast
  obtain \<A>2 :: "('s, 'a) automaton" where A2: "auto_well_defined \<A>2 \<and> alphabet \<A>2 = \<Sigma> \<and> language_auto \<A>2 = language_reg_exp r2" using Alternation well_def by presburger  
  then obtain union_\<A> :: "('s, 'a) automaton" where "auto_well_defined union_\<A> \<and> alphabet union_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> language_auto union_\<A> = language_auto \<A>1 \<union> language_auto \<A>2" using A1 assms existence_of_union_same_type by metis
  thus ?case using A1 A2 by auto
next
  case (Kleene_star r)
  hence well_def: "RE_well_defined r \<Sigma>" unfolding RE_well_defined_def by auto
  then obtain \<A> :: "('s, 'a) automaton" where A: "auto_well_defined \<A> \<and> alphabet \<A> = \<Sigma> \<and> language_auto \<A> = language_reg_exp r" using Kleene_star by blast
  then obtain \<A>' :: "('s, 'a) automaton" where "auto_well_defined \<A>' \<and> alphabet \<A>' = alphabet \<A> \<and> language_auto \<A>' = kleene_star_language (language_auto \<A>)" using assms kleene_star_eps_free_main by blast
  thus ?case using A by auto
qed





text \<open>FA --> RE is more tricky\<close>
fun alternation_list :: "'a list \<Rightarrow> 'a regular_expression" where
  "alternation_list [] = Empty_set" |
  "alternation_list (a # as) = Alternation (Singleton a) (alternation_list as)"

lemma alphabet_RE_alt_list: "alphabet_RE (alternation_list alist) = set alist"
  by (induction alist) auto

lemma language_reg_exp_alist: "language_reg_exp (alternation_list alist) = {[a] | a . a \<in> set alist}"
  by (induction alist) auto

definition enum_of_finite :: "'a set \<Rightarrow> 'a list" where "enum_of_finite S = (SOME list . set list = S \<and> distinct list)"

proposition enum_empty_set: "enum_of_finite {} = []"
  unfolding enum_of_finite_def by auto

theorem enum_of_finite_set_is_correct:
  assumes "finite Set"
  shows "set (enum_of_finite Set) = Set \<and> distinct (enum_of_finite Set)"
  using assms finite_distinct_list someI_ex unfolding enum_of_finite_def by (metis (mono_tags, lifting))

definition transition_symbols_from_x_to_y :: "('s, 'a) automaton \<Rightarrow> 's state \<Rightarrow> 's state \<Rightarrow> 'a set" where "transition_symbols_from_x_to_y \<A> x y = {a . (x, a, y) \<in> transitions \<A>}"

proposition a_is_in_alphabet:
  assumes "auto_well_defined \<A>" "a \<in> transition_symbols_from_x_to_y \<A> x y"
  shows "a \<in> alphabet \<A>"
  using assms well_def_trans_components unfolding transition_symbols_from_x_to_y_def by fast

definition sum_of_singletons_from_x_to_y :: "('s, 'a) automaton \<Rightarrow> 's state \<Rightarrow> 's state \<Rightarrow> 'a regular_expression" where "sum_of_singletons_from_x_to_y \<A> x y = alternation_list (enum_of_finite (transition_symbols_from_x_to_y \<A> x y))"

lemma transition_symbols_sub:
  assumes "auto_well_defined \<A>"
  shows "transition_symbols_from_x_to_y \<A> x y \<subseteq> alphabet \<A>"
  using assms a_is_in_alphabet unfolding transition_symbols_from_x_to_y_def by fast

proposition alphabet_RE_sum_single:
  assumes "auto_well_defined \<A>"
  shows "alphabet_RE (sum_of_singletons_from_x_to_y \<A> x y) \<subseteq> alphabet \<A>"
proof -
  have "finite (alphabet \<A>)" using assms unfolding auto_well_defined_def by blast
  hence fin: "finite (transition_symbols_from_x_to_y \<A> x y)" using assms finite_subset transition_symbols_sub by metis
  have "alphabet_RE (sum_of_singletons_from_x_to_y \<A> x y) = set (enum_of_finite (transition_symbols_from_x_to_y \<A> x y))" using alphabet_RE_alt_list unfolding sum_of_singletons_from_x_to_y_def by fast
  hence "alphabet_RE (sum_of_singletons_from_x_to_y \<A> x y) = transition_symbols_from_x_to_y \<A> x y" using fin enum_of_finite_set_is_correct by blast
  thus ?thesis using assms transition_symbols_sub by fast
qed

proposition sum_singletons_list_well_def: 
  assumes "auto_well_defined \<A>"
  shows "RE_well_defined (sum_of_singletons_from_x_to_y \<A> x y) (alphabet \<A>)"
  using assms alphabet_RE_sum_single unfolding RE_well_defined_def auto_well_defined_def by fast

proposition lang_sum_singletons_well_def: 
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (language_reg_exp (sum_of_singletons_from_x_to_y \<A> x y)) (alphabet \<A>)"
  using assms well_def_REs_language_is_well_def sum_singletons_list_well_def by fast

proposition language_sum_of_singletons_xy:
  assumes "auto_well_defined \<A>"
  shows "language_reg_exp (sum_of_singletons_from_x_to_y \<A> x y) = {[a] | a . (x, a, y) \<in> transitions \<A>}"
proof -
  have "finite (alphabet \<A>)" using assms unfolding auto_well_defined_def by blast
  hence fin: "finite (transition_symbols_from_x_to_y \<A> x y)" using assms finite_subset transition_symbols_sub by metis
  have "language_reg_exp (sum_of_singletons_from_x_to_y \<A> x y) = {[a] | a . a \<in> set (enum_of_finite (transition_symbols_from_x_to_y \<A> x y))}" using language_reg_exp_alist unfolding sum_of_singletons_from_x_to_y_def by blast
  hence "language_reg_exp (sum_of_singletons_from_x_to_y \<A> x y) = {[a] | a . a \<in> (transition_symbols_from_x_to_y \<A> x y)}" using fin enum_of_finite_set_is_correct by auto
  thus ?thesis unfolding transition_symbols_from_x_to_y_def by simp
qed

lemma empty_string_well_defined:
  assumes "auto_well_defined \<A>"
  shows "RE_well_defined Empty_string (alphabet \<A>)"
  using assms unfolding auto_well_defined_def RE_well_defined_def by simp

lemma empty_set_well_defined:
  assumes "auto_well_defined \<A>"
  shows "RE_well_defined Empty_set (alphabet \<A>)"
  using assms unfolding auto_well_defined_def RE_well_defined_def by simp

definition RX_empty :: "('s, 'a) automaton \<Rightarrow> 's state \<Rightarrow> 's state \<Rightarrow> 'a regular_expression" where "RX_empty \<A> x y = Alternation (if x = y then Empty_string else Empty_set) (sum_of_singletons_from_x_to_y \<A> x y)" 

proposition RX_empty_well_def: 
  assumes "auto_well_defined \<A>"
  shows "RE_well_defined (RX_empty \<A> x y) (alphabet \<A>)"
  using assms inheritance_alternation_well_def sum_singletons_list_well_def empty_string_well_defined empty_set_well_defined unfolding RX_empty_def by fastforce

proposition lang_RX_empty_well_def: 
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (language_reg_exp (RX_empty \<A> x y)) (alphabet \<A>)"
  using assms well_def_REs_language_is_well_def RX_empty_well_def by fast

lemma language_RX_empty:
  assumes "auto_well_defined \<A>"
  shows "language_reg_exp (RX_empty \<A> x y) = (if x = y then {[]} \<union> {[a] | a . (x, a, y) \<in> transitions \<A>} else {[a] | a . (x, a, y) \<in> transitions \<A>})"
  using assms language_sum_of_singletons_xy unfolding RX_empty_def by force

function (domintros) RX :: "'s states \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 's state \<Rightarrow> 's state \<Rightarrow> 'a regular_expression" where
  "RX X \<A> x y = (if X = {} then RX_empty \<A> x y else let z = SOME z . z \<in> X in Alternation (Concatenation (RX (X - {z}) \<A> x z) (Concatenation (Kleene_star (RX (X - {z}) \<A> z z)) (RX (X - {z}) \<A> z y))) (RX (X - {z}) \<A> x y))"
  by pat_completeness auto

lemma RX_termination: "finite X \<Longrightarrow> RX_dom (X, \<A>, x, y)"
proof(induction "card X" arbitrary: X x y)
  case 0 
  hence "X = {}" by simp  
  thus ?case using RX.domintros by fast
next
  case (Suc n)
  hence "X \<noteq> {}" by auto
  hence in_X: "let z = SOME z . z \<in> X in z \<in> X" by (simp add: some_in_eq)
  have "\<forall> z \<in> X . finite (X - {z}) \<and> card (X - {z}) = n" using Suc by force
  hence "\<forall> z \<in> X . RX_dom ((X - {z}), \<A>, x, z) \<and> RX_dom ((X - {z}), \<A>, z, z) \<and> RX_dom ((X - {z}), \<A>, z, y) \<and> RX_dom ((X - {z}), \<A>, x, y)" using Suc by fast
  thus ?case using in_X RX.domintros by fastforce
qed 

proposition RX_empty_set: "RX {} \<A> x y = RX_empty \<A> x y"
proof - 
  have "finite {}" by simp
  thus ?thesis using  RX_termination RX.psimps by metis
qed

proposition RX_well_def: 
  assumes "auto_well_defined \<A>"
  shows "X \<subseteq> states \<A> \<Longrightarrow> RE_well_defined (RX X \<A> x y) (alphabet \<A>)"
proof(induction "card X" arbitrary: X x y)
  case 0
  hence "finite X" using assms finite_subset unfolding auto_well_defined_def by blast
  hence "X = {}" using 0 by force
  thus ?case using assms RX_empty_set RX_empty_well_def by metis
next
  case (Suc n)
  hence not_empty: "finite X \<and> X \<noteq> {}" using assms finite_subset unfolding auto_well_defined_def by fastforce
  hence "RX_dom (X, \<A>, x, y) \<and> X \<noteq> {}" using RX_termination by fast
  hence equi: "RX X \<A> x y = (let z = SOME z . z \<in> X in Alternation (Concatenation (RX (X - {z}) \<A> x z) (Concatenation (Kleene_star (RX (X - {z}) \<A> z z)) (RX (X - {z}) \<A> z y))) (RX (X - {z}) \<A> x y))" by (simp add: RX.psimps)
  have in_X: "let z = SOME z . z \<in> X in z \<in> X" using not_empty by (simp add: some_in_eq)
  have "\<forall> z \<in> X . finite (X - {z}) \<and> card (X - {z}) = n" using not_empty Suc by force
  hence "\<forall> z \<in> X . RE_well_defined (RX (X - {z}) \<A> x z) (alphabet \<A>) \<and> RE_well_defined (RX (X - {z}) \<A> z z) (alphabet \<A>) \<and> RE_well_defined (RX (X - {z}) \<A> z y) (alphabet \<A>) \<and> RE_well_defined (RX (X - {z}) \<A> x y) (alphabet \<A>)" using Suc by fast
  thus ?case using equi in_X inheritance_concatenation_well_def inheritance_kleene_star_well_def inheritance_alternation_well_def by metis
qed

proposition lang_RX_well_def: 
  assumes "auto_well_defined \<A>" "X \<subseteq> states \<A>"
  shows "language_well_defined (language_reg_exp (RX X \<A> x y)) (alphabet \<A>)"
  using assms well_def_REs_language_is_well_def RX_well_def by metis

definition LX :: "('s, 'a) automaton \<Rightarrow> 's states \<Rightarrow> 's state \<Rightarrow> 's state \<Rightarrow> 'a language" where "LX \<A> X x y = {word . \<exists> run . pseudo_run_well_defined run \<A> x word \<and> last run = y \<and> set (new_butlast (tl run)) \<subseteq> X}"

theorem LX_well_defined:
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (LX \<A> X x y) (alphabet \<A>)"
  using assms well_def_implies_word_well_defined unfolding LX_def language_well_defined_def by fast

proposition monotonicity_LX: "LX \<A> X x y \<subseteq> LX \<A> (X \<union> {z}) x y"
  unfolding LX_def by blast

lemma language_LX_x_equi_y:
  assumes "x \<in> states \<A>"
  shows "[] \<in> LX \<A> X x y \<longleftrightarrow> x = y"
proof - 
  {
    assume "[] \<in> LX \<A> X x y"
    then obtain run where "pseudo_run_well_defined run \<A> x [] \<and> last run = y" unfolding LX_def by blast
    hence "x = y" using list_with_one_element unfolding pseudo_run_well_defined_def by fastforce
  }
  hence left: "[] \<in> LX \<A> X x y \<longrightarrow> x = y" by blast
  {
    assume "x = y"
    hence "pseudo_run_well_defined [x] \<A> x [] \<and> last [x] = y \<and> set (new_butlast (tl [x])) \<subseteq> X" using assms unfolding pseudo_run_well_defined_def by simp
    hence "[] \<in> LX \<A> X x y" unfolding LX_def by blast
  }
  thus ?thesis using left by fast
qed

lemma language_LX_empty:
  assumes "auto_well_defined \<A>" "x \<in> states \<A>"
  shows "LX \<A> {} x y = language_reg_exp (RX_empty \<A> x y)"
proof - 
  {
    fix word assume "word \<in> LX \<A> {} x y"
    then obtain run where run: "pseudo_run_well_defined run \<A> x word \<and> last run = y \<and> set (new_butlast (tl run)) \<subseteq> {}" unfolding LX_def by blast
    hence "run \<noteq> [] \<and> last run = y \<and> set (new_butlast (tl run)) \<subseteq> {}" unfolding pseudo_run_well_defined_def by fastforce
    hence "length run = 1 \<or> length run = 2" using length_new_butlast_empty by blast
    then consider (case1) "length run = 1" | (case2) "length run = 2" by fast
    hence "word \<in> language_reg_exp (RX_empty \<A> x y)"
    proof cases
      case case1
      hence "word = [] \<and> x = y" using run list_with_one_element unfolding pseudo_run_well_defined_def by force
      thus ?thesis using assms language_RX_empty by fastforce
    next
      case case2
      hence "run \<noteq> []" by auto
      hence "last run = run ! 1" using case2 list_properties_not_empty by fastforce
      hence trans: "length word = 1 \<and> (x, word ! 0, y) \<in> transitions \<A>" using run case2 unfolding pseudo_run_well_defined_def by force
      then obtain a where "a = word ! 0" by blast
      hence "word = [a] \<and> (x, a, y) \<in> transitions \<A>" using trans list_with_one_element by force
      thus ?thesis using assms language_RX_empty by fastforce
    qed
  }
  hence sub: "LX \<A> {} x y \<subseteq> language_reg_exp (RX_empty \<A> x y)" by blast
  {
    fix word assume "word \<in> language_reg_exp (RX_empty \<A> x y)"
    hence word:  "word \<in> (if x = y then {[]} \<union> {[a] | a . (x, a, y) \<in> transitions \<A>} else {[a] | a . (x, a, y) \<in> transitions \<A>})" using assms language_RX_empty by fast
    then consider (case1) "x = y \<and> word \<in> {[]}" | (case2) "x = y \<and> word \<in> {[a] | a . (x, a, y) \<in> transitions \<A>}" | (case3) "x \<noteq> y" by fastforce
    hence "word \<in> LX \<A> {} x y"
    proof cases
      case case1 thus ?thesis using assms language_LX_x_equi_y by fast
    next
      case case2
      then obtain a where a: "word = [a] \<and> (x, a, y) \<in> transitions \<A>" by blast
      hence len: "length [x, y] = length [a] + 1 \<and> ([x, y] ! 0, [a] ! 0, [x, y] ! 1) \<in> transitions \<A>" by simp
      hence "[x, y] ! 0 = x \<and> x \<in> states \<A> \<and> last [x, y] = y" using well_def_trans_components assms by force
      hence "pseudo_run_well_defined [x, y] \<A> x [a] \<and> last [x, y] = y \<and> set (new_butlast (tl [x, y])) \<subseteq> {}" using len unfolding pseudo_run_well_defined_def by force
      thus ?thesis using a unfolding LX_def by blast
    next
      case case3
      hence "word \<in> {[a] | a . (x, a, y) \<in> transitions \<A>}" using word by auto
      then obtain a where a: "word = [a] \<and> (x, a, y) \<in> transitions \<A>" by blast
      hence len: "length [x, y] = length [a] + 1 \<and> ([x, y] ! 0, [a] ! 0, [x, y] ! 1) \<in> transitions \<A>" by simp
      hence "[x, y] ! 0 = x \<and> x \<in> states \<A> \<and> last [x, y] = y" using well_def_trans_components assms by force
      hence "pseudo_run_well_defined [x, y] \<A> x [a] \<and> last [x, y] = y \<and> set (new_butlast (tl [x, y])) \<subseteq> {}" using len unfolding pseudo_run_well_defined_def by force
      thus ?thesis using a unfolding LX_def by blast
    qed
  }
  thus ?thesis using sub by blast
qed

lemma z_not_in_take_k_set:
  assumes "k < length prun \<and> (\<nexists> j . j < k \<and> prun ! j = z)"
  shows "z \<notin> set (take k prun)"
proof(rule ccontr)
  assume "\<not> z \<notin> set (take k prun)"
  then obtain j where j: "(take k prun) ! j = z \<and> j < length (take k prun)" using in_set_conv_nth by metis
  hence "(take k prun) ! j = prun ! j" by force
  thus False using j assms by auto
qed

lemma z_not_in_omega_set:
  assumes "k < length prun \<and> (\<nexists> j . j < k \<and> prun ! j = z)"
  shows "z \<notin> set (new_butlast (take (Suc k) prun))"
  using assms z_not_in_take_k_set new_butlast_equi2 by metis

lemma sub_set_subrun1:
  assumes "set (new_butlast prun) \<subseteq> X \<union> {z}" "k < length prun"
  shows "set (new_butlast (take (Suc k) prun)) \<subseteq> X \<union> {z}"
proof - 
  have equi1: "new_butlast (take (Suc k) prun) = take k prun" using assms new_butlast_equi2 by metis
  have equi2: "new_butlast prun = take (length prun - 1) prun" using new_butlast.simps(1) new_butlast_equi3 take_Nil by metis
  have "set (take k prun) \<subseteq> set (take (length prun - 1) prun)" using assms diff_Suc_1 diff_le_mono less_eq_Suc_le set_take_subset_set_take by metis
  thus ?thesis using assms equi1 equi2 by auto
qed

lemma sub_set_subrun2:
  assumes "set (new_butlast prun) \<subseteq> X \<union> {z}" "k < length prun" "prun \<noteq> []"
  shows "set (new_butlast (tl (sublist k (length prun) prun))) \<subseteq> X \<union> {z}"
proof - 
  have equi1: "new_butlast (tl (sublist k (length prun) prun)) = tl (sublist k (length prun - 1) prun)" using assms new_butlast_equi new_butlast_equi4 by metis
  have equi2: "new_butlast prun = sublist 0 (length prun - 1) prun" using assms unfolding sublist_def by (simp add: new_butlast_equi new_butlast_equi3)  
  have sub: "set (tl (sublist 0 (length prun - 1) prun)) \<subseteq> set (sublist 0 (length prun - 1) prun)" using sub_set_tl by fast
  have "set (tl (sublist k (length prun - 1) prun)) \<subseteq> set (tl (sublist 0 (length prun - 1) prun))" using assms subset_sublist_k by fast
  thus ?thesis using assms equi1 equi2 sub by auto
qed

lemma word_partition_prun:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined prun \<A> x word \<and> last prun = y" "z \<in> set (new_butlast prun)" "set (new_butlast prun) \<subseteq> X \<union> {z}"
  shows "\<exists> word1 word2 prun1 prun2 . word = word1 @ word2 \<and> set (new_butlast prun1) \<subseteq> X \<and> pseudo_run_well_defined prun1 \<A> x word1 \<and> last prun1 = z \<and> pseudo_run_well_defined prun2 \<A> z word2 \<and> last prun2 = y \<and> set (new_butlast (tl prun2)) \<subseteq> X \<union> {z}"
proof -
  have not_empty: "prun \<noteq> []" using assms unfolding pseudo_run_well_defined_def by auto
  hence "z \<in> set prun" using assms bigger_set_butlast_tl by fast
  then obtain k where k: "k < length prun \<and> prun ! k = z \<and> (\<nexists> j . j < k \<and> prun ! j = z)" using minimal_index_for_element by fast
  let ?subword1 = "take k word"
  let ?subword2 = "sublist k (length word) word"
  let ?subrun1 = "take (Suc k) prun"
  let ?subrun2 = "sublist k (length prun) prun"
  have word_equi: "word = ?subword1 @ ?subword2" unfolding sublist_def by simp
  have "?subrun1 ! 0 = prun ! 0" by auto
  hence first: "?subrun1 ! 0 = x \<and> x \<in> states \<A>" using assms unfolding pseudo_run_well_defined_def by argo
  have last0: "prun ! k = ?subrun1 ! k \<and> length ?subrun1 = k + 1" using k by force
  hence "?subrun1 \<noteq> []" by fastforce
  hence "last ?subrun1 = ?subrun1 ! (length ?subrun1 - 1)" using list_properties_not_empty by metis
  hence last1: "last ?subrun1 = z" using last0 k by auto  
  have len_prop: "length prun = length word + 1 \<and> (\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>)" using assms unfolding pseudo_run_well_defined_def by blast
  hence len1: "length ?subrun1 = length ?subword1 + 1" by auto
  have "\<forall> i < length ?subrun1 - 1 . (?subrun1 ! i, ?subword1 ! i, ?subrun1 ! (i + 1)) \<in> transitions \<A>" using len_prop by force
  hence prun1: "pseudo_run_well_defined ?subrun1 \<A> x ?subword1 \<and> last ?subrun1 = z" using last1 len1 first unfolding  pseudo_run_well_defined_def by fast
  hence z_in_states: "z \<in> states \<A>" using assms last_of_prun_is_state by fast
  have "z \<notin> set (new_butlast ?subrun1) \<and> set (new_butlast ?subrun1) \<subseteq> X \<union> {z}" using k z_not_in_omega_set assms sub_set_subrun1 by metis
  hence subset_X: "set (new_butlast ?subrun1) \<subseteq> X" by blast
  hence prun2: "pseudo_run_well_defined ?subrun2 \<A> z ?subword2 \<and> last ?subrun2 = y \<and> set (new_butlast (tl ?subrun2)) \<subseteq> X \<union> {z}"
  proof(cases ?subword2)
    case Nil
    hence len_equi_1: "length ?subrun2 = 1" using len_prop k unfolding sublist_def by force
    have "k < length prun \<and> prun \<noteq> []" using assms k unfolding pseudo_run_well_defined_def by fastforce
    hence "last prun = last ?subrun2" unfolding sublist_def by auto
    hence last2: "last ?subrun2 = y" using assms by simp
    have first2: "?subrun2 ! 0 = z" using k unfolding sublist_def by fastforce
    hence "?subrun2 = [z]" using list_with_one_element len_equi_1 by fast
    thus ?thesis using assms sub_set_subrun2 Nil z_in_states last2 unfolding pseudo_run_well_defined_def by force
  next
    case(Cons a list)
    hence not_empty_list: "?subword2 \<noteq> []" by simp
    have "k < length prun \<and> prun \<noteq> []" using assms k unfolding pseudo_run_well_defined_def by fastforce
    hence not_empty2: "last prun = last ?subrun2 \<and> ?subrun2 \<noteq> []" unfolding sublist_def by auto
    hence last2: "last ?subrun2 = y" using assms by simp
    have first2: "?subrun2 ! 0 = z" using k unfolding sublist_def by fastforce
    have len_s2: "length ?subrun2 = length prun - k" unfolding sublist_def by auto
    have "length ?subword2 = length word - k" unfolding sublist_def by auto
    hence len2: "length ?subrun2 = length ?subword2 + 1" using len_s2 len_prop k by linarith
    {
      fix n assume assm: "n < length ?subrun2 - 1"
      hence run_n: "prun ! (k + n) = ?subrun2 ! n" unfolding sublist_def by auto
      have run_n1: "prun ! (k + n + 1) = ?subrun2 ! (n + 1)" using assm unfolding sublist_def by simp
      have word_n: "word ! (k + n) = ?subword2 ! n" using assm not_empty_list unfolding sublist_def by force
      have "(prun ! (k + n), word ! (k + n), prun ! (k + n + 1)) \<in> transitions \<A>" using len_prop assm len_s2 by simp
      hence "(?subrun2 ! n, ?subword2 ! n, ?subrun2 ! (n + 1)) \<in> transitions \<A>" using run_n run_n1 word_n by argo
    }
    hence "\<forall> i < length ?subrun2 - 1 . (?subrun2 ! i, ?subword2 ! i, ?subrun2 ! (i + 1)) \<in> transitions \<A>" by blast
    hence "pseudo_run_well_defined ?subrun2 \<A> z ?subword2" using len2 first2 z_in_states unfolding pseudo_run_well_defined_def by blast
    thus ?thesis using assms sub_set_subrun2 last2 not_empty k by metis 
  qed
  thus ?thesis using prun1 prun2 word_equi subset_X by blast
qed

lemma word_partition:
  assumes "auto_well_defined \<A>" "pseudo_run_well_defined prun \<A> x word \<and> last prun = y" "z \<in> set (new_butlast (tl prun))" "set (new_butlast (tl prun)) \<subseteq> X \<union> {z}"
  shows "\<exists> word1 word2 prun1 prun2 . word = word1 @ word2 \<and> word1 \<noteq> [] \<and> set (new_butlast (tl prun1)) \<subseteq> X \<and> pseudo_run_well_defined prun1 \<A> x word1 \<and> last prun1 = z \<and> pseudo_run_well_defined prun2 \<A> z word2 \<and> last prun2 = y \<and>set (new_butlast (tl prun2)) \<subseteq> X \<union> {z}"
proof -
  have not_empty: "prun \<noteq> [] \<and> length prun = length word + 1" using assms unfolding pseudo_run_well_defined_def by force
  hence len: "length prun > 2" using assms length_bigger_two by fast
  hence "length word > 1" using not_empty by simp  
  hence "word \<noteq> []" by force
  hence equis: "prun = x # (tl prun) \<and> word = (word ! 0) # (tl word)" using not_empty list_properties_not_empty assms unfolding pseudo_run_well_defined_def by metis
  hence tl_prun: "pseudo_run_well_defined (tl prun) \<A> ((tl prun) ! 0) (tl word) \<and> (x, (word ! 0), ((tl prun) ! 0)) \<in> transitions \<A>" using assms prun_well_defined_cons by metis
  have "tl prun \<noteq> []" using len not_empty not_numeral_less_one tl_empty by metis
  hence "last prun = last (tl prun)" by (simp add: last_tl)
  hence "last (tl prun) = y" using assms by argo
  hence "\<exists> word1 word2 prun1 prun2 . (tl word) = word1 @ word2 \<and> set (new_butlast prun1) \<subseteq> X \<and> pseudo_run_well_defined prun1 \<A> ((tl prun) ! 0) word1 \<and> last prun1 = z \<and> pseudo_run_well_defined prun2 \<A> z word2 \<and> last prun2 = y \<and> set (new_butlast (tl prun2)) \<subseteq> X \<union> {z}" using assms tl_prun word_partition_prun by fastforce
  then obtain word1 word2 prun1 prun2 where words: "(tl word) = word1 @ word2 \<and> set (new_butlast prun1) \<subseteq> X \<and> pseudo_run_well_defined prun1 \<A> ((tl prun) ! 0) word1 \<and> last prun1 = z \<and> pseudo_run_well_defined prun2 \<A> z word2 \<and> last prun2 = y \<and> set (new_butlast (tl prun2)) \<subseteq> X \<union> {z}" by blast
  hence prun: "pseudo_run_well_defined (x # prun1) \<A> x ((word ! 0) # word1)" using tl_prun assms prun_well_defined_induction_cons by metis
  have "prun1 \<noteq> []" using words unfolding pseudo_run_well_defined_def by force
  hence last: "last (x # prun1) = z" using words by simp
  have "word = ((word ! 0) # word1) @ word2 \<and> ((word ! 0) # word1) \<noteq> [] \<and> set (new_butlast (tl (x # prun1))) \<subseteq> X" using words equis by force
  thus ?thesis using last prun words by blast
qed

proposition LX_partition:
  assumes "auto_well_defined \<A>" "X \<subseteq> states \<A>" "word \<in> LX \<A> (X \<union> {z}) x y"
  shows "word \<in> LX \<A> X x y \<or> (\<exists> word1 word2 . word = word1 @ word2 \<and> word1 \<noteq> [] \<and> word1 \<in> LX \<A> X x z \<and> word2 \<in> LX \<A> (X \<union> {z}) z y)"
proof - 
  consider (case1) "z \<in> X" | (case2) "z \<notin> X" by blast
  thus ?thesis
  proof cases
    case case1
    hence "X \<union> {z} = X" by blast
    thus ?thesis using assms by simp
  next
    case case2
    then obtain run where run: "pseudo_run_well_defined run \<A> x word \<and> last run = y \<and> set (new_butlast (tl run)) \<subseteq> (X \<union> {z})" using assms unfolding LX_def by blast
    hence not_empty: "run \<noteq> []" unfolding pseudo_run_well_defined_def by fastforce
    consider (case3) "z \<notin> set (new_butlast (tl run))" | (case4) "z \<in> set (new_butlast (tl run))" by blast
    thus ?thesis
    proof cases
      case case3 thus ?thesis using run unfolding LX_def by blast
    next
      case case4
      hence "\<exists> word1 word2 prun1 prun2 . word = word1 @ word2 \<and> word1 \<noteq> [] \<and> set (new_butlast (tl prun1)) \<subseteq> X \<and> pseudo_run_well_defined prun1 \<A> x word1 \<and> last prun1 = z \<and> pseudo_run_well_defined prun2 \<A> z word2 \<and> last prun2 = y \<and>set (new_butlast (tl prun2)) \<subseteq> X \<union> {z}" using assms run word_partition by fastforce 
      thus ?thesis unfolding LX_def by blast
    qed
  qed
qed

lemma LX_append:
  assumes "auto_well_defined \<A>" "word1 \<in> LX \<A> X x z" "word2 \<in> LX \<A> X z y" "z \<in> X"
  shows "word1 @ word2 \<in> LX \<A> X x y"
proof -
  obtain prun1 prun2 where pruns: "pseudo_run_well_defined prun1 \<A> x word1 \<and> last prun1 = z \<and> set (new_butlast (tl prun1)) \<subseteq> X \<and> pseudo_run_well_defined prun2 \<A> z word2 \<and> last prun2 = y \<and> set (new_butlast (tl prun2)) \<subseteq> X" using assms unfolding LX_def by blast
  hence props: "length prun1 = length word1 + 1 \<and> prun1 ! 0 = x \<and> x \<in> states \<A> \<and> last prun1 = z \<and> (\<forall> i < length prun1 - 1 . (prun1 ! i, word1 ! i, prun1 ! (i + 1)) \<in> transitions \<A>) \<and> length prun2 = length word2 + 1 \<and> prun2 ! 0 = z \<and> last prun2 = y \<and> (\<forall> i < length prun2 - 1 . (prun2 ! i, word2 ! i, prun2 ! (i + 1)) \<in> transitions \<A>)" unfolding pseudo_run_well_defined_def by fast
  thus ?thesis
  proof(cases "tl prun2")
    case Nil
    have "prun2 \<noteq> []" using props by force
    hence "length prun2 = 1" using Nil tl_empty by blast
    hence empty_word1: "word2 = [] \<and> z = y" using props list_with_one_element by force
    thus ?thesis using props assms by force
  next
    case(Cons a list)
    hence not_empty_list: "tl prun2 \<noteq> []" by simp
    consider (case3) "tl (prun1) = []" | (case4) "tl (prun1) \<noteq> []" by blast
    thus ?thesis
    proof cases
      case case3
      have "prun1 \<noteq> []" using props by force
      hence "length prun1 = 1" using case3 tl_empty by blast
      hence empty_word1: "word1 = [] \<and> x = z" using props list_with_one_element by force
      thus ?thesis using props assms by force
    next
      case case4
      have len: "length (prun1 @ (tl prun2)) = length (word1 @ word2) + 1" using props by simp
      have length: "length (tl prun2) = length word2" using props by simp
      hence not_empty_word2: "word2 \<noteq> []" using not_empty_list length_0_conv by metis
      hence len_prun2: "length prun2 > 1" using props by auto
      have not_empty: "prun1 \<noteq> []" using props by force
      hence first: "(prun1 @ (tl prun2)) ! 0 = x \<and> x \<in> states \<A>" using props by (simp add: nth_append)
      have "last (tl prun2) = last prun2" using not_empty_list by (simp add: last_tl)
      hence last: "last (prun1 @ (tl prun2)) = y" using props not_empty_list by simp
      have "length prun1 > 1" using case4 tl_more_elements by blast
      hence not_empty2: "new_butlast prun1 \<noteq> []" using new_butlast_not_empty by blast
      have "prun1 = (new_butlast prun1) @ [z]" using not_empty props new_butlast.elims by (metis append_butlast_last_id)
      hence "tl prun1 = tl (new_butlast prun1) @ [z]" using tl_append2 not_empty2 by metis
      hence "new_butlast (tl (prun1 @ (tl prun2))) = (tl (new_butlast prun1) @ [z]) @ (new_butlast (tl prun2))" using not_empty_list not_empty list_append_new_butlast by force
      hence "set (new_butlast (tl (prun1 @ (tl prun2)))) = set (tl (new_butlast prun1)) \<union> set [z] \<union> set (new_butlast (tl prun2))" by simp
      hence "set (new_butlast (tl (prun1 @ (tl prun2)))) = set (new_butlast (tl prun1)) \<union> set [z] \<union> set (new_butlast (tl prun2))" using new_butlast_equi by metis
      hence in_X: "set (new_butlast (tl (prun1 @ (tl prun2)))) \<subseteq> X" using pruns assms by force
      {
        fix i assume assm: "i < length (prun1 @ (tl prun2)) - 1"
        then consider (case5) "i < length prun1 - 1" | (case6) "i = length prun1 - 1" | (case7) "i > length prun1 - 1" by linarith
        hence "((prun1 @ (tl prun2)) ! i, (word1 @ word2) ! i, (prun1 @ (tl prun2)) ! (i + 1)) \<in> transitions \<A>"
        proof cases
          case case5 thus ?thesis using assm len length list_append_position1 props by metis
        next
          case case6
          hence equi: "(prun1 @ (tl prun2)) ! i = last prun1 \<and> (prun1 @ (tl prun2)) ! (i + 1) = (tl prun2) ! 0 \<and> (word1 @ word2) ! i = word2 ! 0" using assm len length not_empty_word2 list_append_position2 by blast
          hence "(prun1 @ (tl prun2)) ! i = z" using props by blast
          hence trans: "(prun2 ! 0, word2 ! 0, prun2 ! 1) \<in> transitions \<A> \<and> prun2 ! 0 = (prun1 @ (tl prun2)) ! i" using props len_prun2 by force
          have " tl prun2 ! 0 = prun2 ! 1" using  j_pos_tl len_prun2 by force
          thus ?thesis using trans equi by argo
        next
          case case7
          hence equi_i: "(prun1 @ (tl prun2)) ! i = (tl prun2) ! (i - length prun1) \<and> (prun1 @ (tl prun2)) ! (i + 1) = (tl prun2) ! (i + 1 - length prun1) \<and> (word1 @ word2) ! i = word2 ! (i + 1 - length prun1)" using assm len length list_append_position3 not_empty_word2 by blast
          have "i \<ge> length prun1" using case7 by force
          hence "i + 1 - length prun1 = i - length prun1 + 1" by force
          hence equi: "(prun1 @ (tl prun2)) ! i = (tl prun2) ! (i - length prun1) \<and> (prun1 @ (tl prun2)) ! (i + 1) = (tl prun2) ! (i - length prun1 + 1) \<and> (word1 @ word2) ! i = word2 ! (i - length prun1 + 1)" using equi_i by presburger
          have "i < length prun1 + length (tl prun2) - 1" using assm by force
          hence "i - length prun1 < length (tl prun2) - 1" using case7 by linarith
          hence i: "i - length prun1 < length prun2 - 1 - 1" by simp
          hence equi_tl: "(tl prun2) ! (i - length prun1 + 1) = prun2 ! (i - length prun1 + 1 + 1)" using j_pos_tl less_diff_conv by blast
          hence "i - length prun1 < length prun2 - 1" using i by linarith
          hence "(tl prun2) ! (i - length prun1) = prun2 ! (i - length prun1 + 1)" using j_pos_tl by blast
          hence "(prun1 @ (tl prun2)) ! i = prun2 ! (i - length prun1 + 1) \<and> (prun1 @ (tl prun2)) ! (i + 1) = prun2 ! (i - length prun1 + 1 + 1) \<and> (word1 @ word2) ! i = word2 ! (i - length prun1 + 1)" using equi_tl equi by argo
          thus ?thesis using props i by simp
        qed
      }
      hence "\<forall> i < length (prun1 @ (tl prun2)) - 1 . ((prun1 @ (tl prun2)) ! i, (word1 @ word2) ! i, (prun1 @ (tl prun2)) ! (i + 1)) \<in> transitions \<A>" by blast
      thus ?thesis using len first last in_X unfolding pseudo_run_well_defined_def LX_def by blast
    qed
  qed
qed

proposition word_list_in_LX:
  assumes "auto_well_defined \<A>"
  shows "set word_list \<subseteq> LX \<A> X z z \<and> z \<in> states \<A> \<Longrightarrow> concat word_list \<in> LX \<A> (X \<union> {z}) z z"
proof(induction word_list rule: rev_induct)
  case Nil thus ?case using assms language_LX_x_equi_y by force
next
  case (snoc word word_list)
  hence "word \<in> LX \<A> (X \<union> {z}) z z" using monotonicity_LX by force
  thus ?case using assms LX_append snoc by fastforce
qed

theorem LX_X_z_left:
  assumes "auto_well_defined \<A>" "X \<subseteq> states \<A>"
  shows "word \<in> LX \<A> (X \<union> {z}) x y \<Longrightarrow> word \<in> concatenation_language (LX \<A> X x z) (concatenation_language (kleene_star_language (LX \<A> X z z)) (LX \<A> X z y)) \<union> LX \<A> X x y"
proof(induction word arbitrary: x y rule: length_induct)
  case (1 word)
  then consider (case1) "word \<in> LX \<A> X x y" | (case2) "\<exists> word1 word2 . word = word1 @ word2 \<and> word1 \<noteq> [] \<and> word1 \<in> LX \<A> X x z \<and> word2 \<in> LX \<A> (X \<union> {z}) z y" using 1 assms LX_partition by metis
  thus ?case
  proof cases
    case case1 thus ?thesis by blast
  next
    case case2
    then obtain word1 word2 where words: "word = word1 @ word2 \<and> word1 \<noteq> [] \<and> word1 \<in> LX \<A> X x z \<and> word2 \<in> LX \<A> (X \<union> {z}) z y" by presburger
    hence "length word2 < length word" by simp
    hence "word2 \<in> concatenation_language (LX \<A> X z z) (concatenation_language (kleene_star_language (LX \<A> X z z)) (LX \<A> X z y)) \<or> word2 \<in> LX \<A> X z y" using 1 words by blast
    then consider (case3) "word2 \<in> LX \<A> X z y" | (case4) "word2 \<in> concatenation_language (LX \<A> X z z) (concatenation_language (kleene_star_language (LX \<A> X z z)) (LX \<A> X z y))" by blast
    thus ?thesis 
    proof cases
      case case3 
      have "[] \<in> kleene_star_language (LX \<A> X z z)" using empty_string_in_kleene_star_lang by fast
      hence "word2 \<in> concatenation_language (kleene_star_language (LX \<A> X z z)) (LX \<A> X z y)" using case3 unfolding concatenation_language_def by blast
      thus ?thesis using words unfolding concatenation_language_def by blast
    next
      case case4
      then obtain word3 word4 word5 where more_words: "word2 = word3 @ word4 @ word5 \<and> word3 \<in> (LX \<A> X z z) \<and> word4 \<in> (kleene_star_language (LX \<A> X z z)) \<and> word5 \<in> (LX \<A> X z y)" unfolding concatenation_language_def by blast
      then obtain i where "word4 \<in> kleene_star_language_helper (LX \<A> X z z) i" unfolding kleene_star_language_def by blast
      hence "word3 @ word4 \<in> kleene_star_language_helper (LX \<A> X z z) (Suc i)" using kleene_star_cons more_words unfolding concatenation_language_def by blast
      hence concat: "word3 @ word4 \<in> kleene_star_language (LX \<A> X z z)" unfolding kleene_star_language_def by fast
      have "word2 = (word3 @ word4) @ word5" using more_words by simp
      hence "word2 \<in> concatenation_language (kleene_star_language (LX \<A> X z z)) (LX \<A> X z y)" using more_words concat unfolding concatenation_language_def by blast
      thus ?thesis using words unfolding concatenation_language_def by blast
    qed
  qed
qed

theorem LX_X_z_right:
  assumes "auto_well_defined \<A>" "X \<subseteq> states \<A>" "z \<in> states \<A>" "word \<in> concatenation_language (LX \<A> X x z) (concatenation_language (kleene_star_language (LX \<A> X z z)) (LX \<A> X z y)) \<union> LX \<A> X x y"
  shows "word \<in> LX \<A> (X \<union> {z}) x y"
proof -
  consider (case1) "word \<in> LX \<A> X x y" | (case2) "word \<in> concatenation_language (LX \<A> X x z) (concatenation_language (kleene_star_language (LX \<A> X z z)) (LX \<A> X z y))" using assms by blast
  thus ?thesis
  proof cases
    case case1 thus ?thesis using  monotonicity_LX by fast
  next
    case case2
    then obtain word1 word2 word3 where word: "word = word1 @ word2 @ word3 \<and> word1 \<in> (LX \<A> X x z) \<and> word2 \<in> (kleene_star_language (LX \<A> X z z)) \<and> word3 \<in> (LX \<A> X z y)" unfolding concatenation_language_def by blast
    then obtain i where "word2 \<in> kleene_star_language_helper (LX \<A> X z z) i" unfolding kleene_star_language_def by blast
    then obtain word_list where "word2 = concat word_list \<and> set word_list \<subseteq> LX \<A> X z z" using decomposition_of_kleene_star_word by blast
    hence word2: "word2 \<in> LX \<A> (X \<union> {z}) z z" using assms word_list_in_LX by fast
    have z_in: "z \<in> X \<union> {z}" by blast
    have "word1 \<in> LX \<A> (X \<union> {z}) x z \<and> word3 \<in> LX \<A> (X \<union> {z}) z y" using word monotonicity_LX by fast
    hence "(word1 @ word2) \<in> LX \<A> (X \<union> {z}) x z \<and> word3 \<in> LX \<A> (X \<union> {z}) z y" using assms word2 LX_append z_in by metis
    hence "(word1 @ word2) @ word3 \<in> LX \<A> (X \<union> {z}) x y" using z_in assms LX_append by fast
    thus ?thesis using word by simp
  qed
qed

theorem LX_equi:
  assumes "auto_well_defined \<A>" "X \<subseteq> states \<A>" "z \<in> states \<A>"
  shows "LX \<A> (X \<union> {z}) x y = concatenation_language (LX \<A> X x z) (concatenation_language (kleene_star_language (LX \<A> X z z)) (LX \<A> X z y)) \<union> LX \<A> X x y"
proof - 
  have left: "LX \<A> (X \<union> {z}) x y \<subseteq> concatenation_language (LX \<A> X x z) (concatenation_language (kleene_star_language (LX \<A> X z z)) (LX \<A> X z y)) \<union> LX \<A> X x y" using assms LX_X_z_left subsetI by metis
  have "concatenation_language (LX \<A> X x z) (concatenation_language (kleene_star_language (LX \<A> X z z)) (LX \<A> X z y)) \<union> LX \<A> X x y \<subseteq> LX \<A> (X \<union> {z}) x y" using assms LX_X_z_right subsetI by metis
  thus ?thesis using left by blast
qed

theorem equivalence_of_LX_and_RX:
  assumes "auto_well_defined \<A>"
  shows "X \<subseteq> states \<A> \<and> x \<in> states \<A> \<Longrightarrow> LX \<A> X x y = language_reg_exp (RX X \<A> x y)"
proof(induction "card X" arbitrary: X x y)
  case 0
  have "finite (states \<A>)" using assms unfolding auto_well_defined_def by blast
  hence "finite X" using 0 assms finite_subset by blast
  hence "X = {}" using 0 by simp
  thus ?case using assms 0 language_LX_empty RX_empty_set by metis
next
  case (Suc n)
  have "finite (states \<A>)" using assms unfolding auto_well_defined_def by blast
  hence fin: "finite X \<and> X \<noteq> {}" using Suc assms finite_subset by fastforce  
  hence dom: "RX_dom (X, \<A>, x, y)" using RX_termination by fast
  obtain z where z': "z = (SOME z' . z' \<in> X)" using Suc by force
  hence z: "z \<in> X" using fin by (simp add: some_in_eq)
  hence state: "z \<in> states \<A>" using Suc fin by blast
  have card: "card (X - {z}) = n \<and> (X - {z}) \<subseteq> states \<A>" using fin Suc z by force
  hence "LX \<A> (X - {z}) x y = language_reg_exp (RX (X - {z}) \<A> x y)" using Suc by presburger
  have "LX \<A> X x y = LX \<A> ((X - {z}) \<union> {z}) x y" using z by (simp add: insert_absorb)
  hence LX: "LX \<A> X x y = concatenation_language (LX \<A> (X - {z}) x z) (concatenation_language (kleene_star_language (LX \<A> (X - {z}) z z)) (LX \<A> (X - {z}) z y)) \<union> LX \<A> (X - {z}) x y" using Suc assms card state LX_equi by metis 
  hence "LX \<A> X x y = concatenation_language (language_reg_exp (RX (X - {z}) \<A> x z)) (concatenation_language (kleene_star_language (language_reg_exp (RX (X - {z}) \<A> z z))) (language_reg_exp (RX (X - {z}) \<A> z y))) \<union> (language_reg_exp (RX (X - {z}) \<A> x y))" using Suc card state by presburger 
  hence "LX \<A> X x y = language_reg_exp (Alternation (Concatenation (RX (X - {z}) \<A> x z) (Concatenation (Kleene_star (RX (X - {z}) \<A> z z)) (RX (X - {z}) \<A> z y))) (RX (X - {z}) \<A> x y))" by force
  thus ?case using z' RX.psimps dom fin by metis
qed

corollary equivalence_of_LX_and_RX_on_Q:
  assumes "auto_well_defined \<A>"
  shows "LX \<A> (states \<A>) (initial_state \<A>) y = language_reg_exp (RX (states \<A>) \<A> (initial_state \<A>) y)"
  using equivalence_of_LX_and_RX assms unfolding auto_well_defined_def by fast

proposition union_over_acc_states_of_LX_is_lang_auto:
  assumes "auto_well_defined \<A>"
  shows "language_auto \<A> = (\<Union> f \<in> (accepting_states \<A>) . LX \<A> (states \<A>) (initial_state \<A>) f)"
proof -  
  {
    fix word assume "word \<in> language_auto \<A>"
    then obtain run where run: "pseudo_run_well_defined run \<A> (initial_state \<A>) word \<and> last run \<in> accepting_states \<A>" unfolding language_auto_def run_accepting_def run_well_defined_def by auto
    then obtain f where f: "last run = f \<and> f \<in> accepting_states \<A>" by simp
    have set: "set run \<subseteq> states \<A>" using assms run well_def_implies_prun_states unfolding prun_states_def by fast
    have "run \<noteq> []" using run unfolding pseudo_run_well_defined_def by force
    hence "set (new_butlast (tl run)) \<subseteq> states \<A>" using set new_butlast_subset by auto
    hence "word \<in> LX \<A> (states \<A>) (initial_state \<A>) f" using run f unfolding LX_def by blast
    hence "word \<in> (\<Union> f \<in> (accepting_states \<A>) . LX \<A> (states \<A>) (initial_state \<A>) f)" using f by blast
  }
  hence sub: "language_auto \<A> \<subseteq> (\<Union> f \<in> (accepting_states \<A>) . LX \<A> (states \<A>) (initial_state \<A>) f)" by fast
  {
    fix word assume "word \<in> (\<Union> f \<in> (accepting_states \<A>) . LX \<A> (states \<A>) (initial_state \<A>) f)"
    then obtain f where f: "f \<in> (accepting_states \<A>) \<and> word \<in> LX \<A> (states \<A>) (initial_state \<A>) f" by blast
    then obtain run where run: "pseudo_run_well_defined run \<A> (initial_state \<A>) word \<and> last run = f" unfolding LX_def by blast
    hence "run_accepting run \<A> word" using f unfolding run_well_defined_def run_accepting_def by blast
    hence "word \<in> language_auto \<A>" unfolding language_auto_def by auto
  }
  thus ?thesis using sub by fast
qed

corollary union_over_acc_states_of_RX_is_lang_auto:
  assumes "auto_well_defined \<A>"
  shows "language_auto \<A> = (\<Union> f \<in> (accepting_states \<A>) . language_reg_exp (RX (states \<A>) \<A> (initial_state \<A>) f))"
  using assms union_over_acc_states_of_LX_is_lang_auto equivalence_of_LX_and_RX_on_Q by fastforce

fun RX_big_alt_list :: "('s, 'a) automaton \<Rightarrow> 's state list \<Rightarrow> 'a regular_expression" where
  "RX_big_alt_list \<A> [] = Empty_set" |
  "RX_big_alt_list \<A> (f # acc_states) = Alternation (RX (states \<A>) \<A> (initial_state \<A>) f) (RX_big_alt_list \<A> acc_states)"

proposition RX_big_alt_list_well_def: 
  assumes "auto_well_defined \<A>"
  shows "RE_well_defined (RX_big_alt_list \<A> acc_states) (alphabet \<A>)"
proof(induction acc_states)
  case Nil thus ?case using assms empty_set_well_defined by auto
next
  case (Cons f acc_states) thus ?case using assms RX_well_def inheritance_alternation_well_def by fastforce
qed

lemma RX_big_alt_list_language: "language_reg_exp (RX_big_alt_list \<A> acc_states) = (\<Union> f \<in> (set acc_states) . language_reg_exp (RX (states \<A>) \<A> (initial_state \<A>) f))"
  by (induction acc_states) auto

definition RX_big_alternation :: "('s, 'a) automaton \<Rightarrow> 'a regular_expression" where "RX_big_alternation \<A> = RX_big_alt_list \<A> (enum_of_finite (accepting_states \<A>))"

proposition RX_big_alternation_well_def:
  assumes "auto_well_defined \<A>"
  shows "RE_well_defined (RX_big_alternation \<A>) (alphabet \<A>)"
  using RX_big_alt_list_well_def assms unfolding RX_big_alternation_def by blast

theorem RX_big_alternation_language:
  assumes "auto_well_defined \<A>"
  shows "language_reg_exp (RX_big_alternation \<A>) = (\<Union> f \<in> (accepting_states \<A>) . language_reg_exp (RX (states \<A>) \<A> (initial_state \<A>) f))"
proof - 
  have "finite (accepting_states \<A>)" using assms NFA_is_finite by blast
  thus ?thesis using assms RX_big_alt_list_language enum_of_finite_set_is_correct unfolding RX_big_alternation_def by metis
qed

text \<open>Key result for showing equivalence of expressive power between RE and FA: FA --> RE\<close>
theorem auto_implies_existence_of_regular_expression:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)"
  shows "\<exists> (r :: 'a regular_expression) . RE_well_defined r (alphabet \<A>) \<and> language_reg_exp r = language_auto \<A>"
  using assms union_over_acc_states_of_RX_is_lang_auto RX_big_alternation_language RX_big_alternation_well_def by metis

theorem expressive_power_auto_RE_main:
  assumes "infinite (UNIV :: 's set)"
  shows "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>} = {L . \<exists> (r :: 'a regular_expression) . RE_well_defined r \<Sigma> \<and> L = language_reg_exp r}"
  using assms auto_implies_existence_of_regular_expression regular_expression_implies_existence_of_auto by fast

end