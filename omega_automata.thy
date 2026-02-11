theory omega_automata

imports Main regular_languages_and_pumping_lemma

begin

text \<open>Author: Benno Thalmann, last update: 11.2.2026, Addition to masterarbeit_benno_thalmann\<close>

text \<open>Type definitions\<close>
type_synonym 'a omega_word = "nat \<Rightarrow> 'a symbol"
type_synonym 'a omega_language = "'a omega_word set"
type_synonym 's omega_run = "nat \<Rightarrow> 's state"

text \<open>general definitions of omega_words and omega_languages\<close>
definition omega_word_well_defined :: "'a omega_word \<Rightarrow> 'a alphabet \<Rightarrow> bool" where "omega_word_well_defined omega_word \<Sigma> = (\<forall> n . omega_word n \<in> \<Sigma>)"

definition omega_language_well_defined :: "'a omega_language \<Rightarrow> 'a alphabet \<Rightarrow> bool" where "omega_language_well_defined L \<Sigma> = (\<forall> omega_word \<in> L . omega_word_well_defined omega_word \<Sigma>)"



text \<open>First property for well-definedness of a omega-pseudo-run\<close>
definition omega_pseudo_run_well_defined :: "'s omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 's state \<Rightarrow> 'a omega_word \<Rightarrow> bool" where
  "omega_pseudo_run_well_defined omega_prun \<A> s omega_word =
    (omega_prun 0 = s \<and> s \<in> states \<A> \<and>
    (\<forall> n . (omega_prun n, omega_word n, omega_prun (n + 1)) \<in> transitions \<A>))"

definition omega_prun_states :: "'s omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> bool" where "omega_prun_states omega_prun \<A> = (\<forall> n . omega_prun n \<in> states \<A>)"

theorem well_def_implies_omega_prun_states:
  assumes "auto_well_defined \<A>" "omega_pseudo_run_well_defined omega_prun \<A> s omega_word"
  shows "omega_prun_states omega_prun \<A>"
  using assms unfolding omega_pseudo_run_well_defined_def auto_well_defined_def omega_prun_states_def by blast

theorem well_def_implies_omega_word_well_defined:
  assumes "auto_well_defined \<A>" "omega_pseudo_run_well_defined omega_prun \<A> s omega_word"
  shows "omega_word_well_defined omega_word (alphabet \<A>)"
  using assms unfolding omega_pseudo_run_well_defined_def auto_well_defined_def omega_word_well_defined_def by fast

text \<open>Next goal: For a well-defined word, there is exactly one omega_pseudo_run on a DFA\<close>
fun omega_prun_from :: "'s state \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> nat \<Rightarrow> 's state" where
  "omega_prun_from s1 \<A> omega_word 0 = s1" |
  "omega_prun_from s1 \<A> omega_word (Suc n) = (THE s2 . s2 \<in> states \<A> \<and> (omega_prun_from s1 \<A> omega_word n, omega_word n, s2) \<in> transitions \<A>)"

lemma omega_run_from_are_states:
  assumes "DFA_property \<A>" "s \<in> states \<A>" "omega_word_well_defined omega_word (alphabet \<A>)"
  shows "omega_prun_from s \<A> omega_word n \<in> states \<A>"
proof(induction n)
  case 0 thus ?case using assms by auto
next
  case (Suc n)
  hence "omega_prun_from s \<A> omega_word n \<in> states \<A> \<and> omega_word n \<in> alphabet \<A>" using assms unfolding omega_word_well_defined_def by blast
  hence un_ex: "\<exists>! s2 \<in> states \<A> . (omega_prun_from s \<A> omega_word n, omega_word n, s2) \<in> transitions \<A>" using assms DFA_property_def by metis
  then obtain s2 where s2: "s2 \<in> states \<A> \<and> (omega_prun_from s \<A> omega_word n, omega_word n, s2) \<in> transitions \<A>" by blast
  hence "omega_prun_from s \<A> omega_word (Suc n) = s2" using the1_equality un_ex by fastforce
  thus ?case using s2 by blast
qed

lemma omega_run_from_transitions:
  assumes "DFA_property \<A>" "s \<in> states \<A>" "omega_word_well_defined omega_word (alphabet \<A>)"
  shows "(omega_prun_from s \<A> omega_word n, omega_word n, omega_prun_from s \<A> omega_word (n + 1)) \<in> transitions \<A>"
proof -
  have "omega_prun_from s \<A> omega_word n \<in> states \<A> \<and> omega_word n \<in> alphabet \<A>" using assms omega_run_from_are_states unfolding omega_word_well_defined_def by fast
  hence un_ex: "\<exists>! s2 \<in> states \<A> . (omega_prun_from s \<A> omega_word n, omega_word n, s2) \<in> transitions \<A>" using assms DFA_property_def by metis
  then obtain s2 where s2: "s2 \<in> states \<A> \<and> (omega_prun_from s \<A> omega_word n, omega_word n, s2) \<in> transitions \<A>" by blast
  hence "omega_prun_from s \<A> omega_word (Suc n) = s2" using the1_equality un_ex by fastforce
  thus ?thesis using s2 by auto
qed

lemma omega_run_from_well_defined:
  assumes "DFA_property \<A>" "s \<in> states \<A>" "omega_word_well_defined omega_word (alphabet \<A>)"
  shows "omega_pseudo_run_well_defined (omega_prun_from s \<A> omega_word) \<A> s omega_word"
  using assms omega_run_from_transitions unfolding omega_pseudo_run_well_defined_def by fastforce

lemma omega_run_unique:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "omega_pseudo_run_well_defined omega_prun1 \<A> s omega_word" "omega_pseudo_run_well_defined omega_prun2 \<A> s omega_word"
  shows "omega_prun1 = omega_prun2"
proof -
  {
    fix n
    have states: "omega_prun_states omega_prun1 \<A> \<and> omega_prun_states omega_prun2 \<A>" using assms well_def_implies_omega_prun_states by fast
    have "omega_prun1 n = omega_prun2 n"
    proof (induction n)
      case 0 thus ?case using assms unfolding omega_pseudo_run_well_defined_def by argo
    next
      case (Suc n)
      have "(omega_prun1 n, omega_word n, omega_prun1 (n + 1)) \<in> transitions \<A> \<and> (omega_prun2 n, omega_word n, omega_prun2 (n + 1)) \<in> transitions \<A>" using assms unfolding omega_pseudo_run_well_defined_def by blast
      hence trans: "(omega_prun1 n, omega_word n, omega_prun1 (n + 1)) \<in> transitions \<A> \<and> (omega_prun1 n, omega_word n, omega_prun2 (n + 1)) \<in> transitions \<A>" using Suc by auto
      have "omega_word n \<in> alphabet \<A>" using assms well_def_implies_omega_word_well_defined unfolding omega_word_well_defined_def by fast
      hence "omega_prun1 n \<in> states \<A> \<and> omega_prun2 n \<in> states \<A> \<and> omega_word n \<in> alphabet \<A>" using states unfolding omega_prun_states_def by auto
      hence "\<exists>! s2 \<in> states \<A> . (omega_prun1 n, omega_word n, s2) \<in> transitions \<A>" using assms DFA_property_def by metis
      thus ?case using assms trans well_def_trans_components by fastforce
    qed
  }
  thus ?thesis by blast
qed

theorem exists_only_one_omega_prun_for_DFA:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "omega_word_well_defined omega_word (alphabet \<A>)"
  shows "\<forall> s \<in> states \<A> . \<exists>! omega_prun . omega_pseudo_run_well_defined omega_prun \<A> s omega_word"
  using assms omega_run_from_well_defined omega_run_unique by metis

text \<open>Definition of an accepting omega_run over an omega_word\<close>
definition omega_run_well_defined :: "'s omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> bool" where "omega_run_well_defined omega_run \<A> omega_word = omega_pseudo_run_well_defined omega_run \<A> (initial_state \<A>) omega_word"

corollary exists_only_one_omega_run_for_DFA:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "omega_word_well_defined omega_word (alphabet \<A>)"
  shows "\<exists>! omega_run . omega_run_well_defined omega_run \<A> omega_word"
  using assms exists_only_one_omega_prun_for_DFA unfolding auto_well_defined_def omega_run_well_defined_def by fast

definition inf_omega_run :: "'s omega_run \<Rightarrow> 's set" where "inf_omega_run omega_run = {q . infinite {n . omega_run n = q}}"

lemma inf_crit_left:
  assumes "inf_omega_run omega_run \<inter> accepting_states \<A> \<noteq> {}"
  shows "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>"
proof - 
  obtain s where s: "s \<in> accepting_states \<A> \<and> s \<in> inf_omega_run omega_run" using assms by blast
  hence "infinite {n. omega_run n = s}" unfolding inf_omega_run_def by blast
  hence "\<forall> n . \<exists> N > n . N \<in> {n . omega_run n = s}" using finite_nat_set_iff_bounded_le not_le_imp_less by metis
  thus ?thesis using s by blast
qed

lemma infinite_set:
  assumes "\<forall> n . \<exists> N > n . (omega_run :: 's omega_run) N \<in> accepting_states \<A>"
  shows "infinite {N . omega_run N \<in> accepting_states \<A>}"
proof(rule ccontr)
  assume "\<not> infinite {N . omega_run N \<in> accepting_states \<A>}"
  hence "finite {N . omega_run N \<in> accepting_states \<A>}" by blast
  hence "\<exists> m . \<forall> n \<in> {N . omega_run N \<in> accepting_states \<A>} . n \<le> m" using finite_nat_set_iff_bounded_le by blast
  then obtain m where m: "\<forall> n \<in> {N . omega_run N \<in> accepting_states \<A>} . n \<le> m" by blast
  then obtain M where "M > m \<and> omega_run M \<in> accepting_states \<A>" using assms by blast
  thus False using m by force
qed

lemma inf_crit_right:
  assumes "auto_well_defined \<A>" "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>"
  shows "inf_omega_run omega_run \<inter> accepting_states \<A> \<noteq> {}"
proof - 
  have finite: "finite (accepting_states \<A>)" using assms NFA_is_finite by blast
  have decomp: "{N . omega_run N \<in> accepting_states \<A>} = (\<Union> s \<in> accepting_states \<A> . {N . omega_run N = s})" by blast
  have "infinite {N . omega_run N \<in> accepting_states \<A>}" using assms infinite_set by blast
  hence "\<exists> s \<in> accepting_states \<A> . infinite {N . omega_run N = s}" using decomp finite by auto
  thus ?thesis unfolding inf_omega_run_def by blast
qed

proposition inf_criterion_equivalence:
  assumes "auto_well_defined \<A>"
  shows "inf_omega_run omega_run \<inter> accepting_states \<A> \<noteq> {} \<longleftrightarrow> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>)"
  using inf_crit_right inf_crit_left assms by metis

definition omega_run_accepting :: "'s omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> bool" where "omega_run_accepting omega_run \<A> omega_word = (omega_run_well_defined omega_run \<A> omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>))"

text \<open>Definition of a omega_language accepted by an automaton\<close>
definition omega_language_auto :: "('s, 'a) automaton \<Rightarrow> 'a omega_language" where "omega_language_auto \<A> = {omega_word . \<exists> omega_run . omega_run_accepting omega_run \<A> omega_word}"

lemma no_acc_states_omega:
  assumes "accepting_states \<A> = {}"
  shows "omega_language_auto \<A> = {}"
  using assms unfolding omega_language_auto_def omega_run_accepting_def by blast

text \<open>If the automaton is well-defined, then the accepted omega_words will be well-defined\<close>
corollary omega_word_in_omega_language_is_well_defined:
  assumes "auto_well_defined \<A>" "omega_word \<in> omega_language_auto \<A>"
  shows "omega_word_well_defined omega_word (alphabet \<A>)"
  using assms well_def_implies_omega_word_well_defined unfolding omega_language_auto_def omega_run_accepting_def omega_run_well_defined_def by fast

corollary not_well_def_omega_words_not_in_omega_language:
  assumes "auto_well_defined \<A>" "\<not> omega_word_well_defined omega_word (alphabet \<A>)"
  shows "omega_word \<notin> omega_language_auto \<A>"
  using assms omega_word_in_omega_language_is_well_defined by auto

proposition automata_omega_language_are_well_defined:
  assumes "auto_well_defined \<A>"
  shows "omega_language_well_defined (omega_language_auto \<A>) (alphabet \<A>)"
  using assms omega_word_in_omega_language_is_well_defined unfolding omega_language_well_defined_def by blast

definition omega_sigma_star :: "'a alphabet \<Rightarrow> 'a omega_language" where "omega_sigma_star \<Sigma> = {omega_word . omega_word_well_defined omega_word \<Sigma>}"

proposition omega_sigma_star_well_defined: "omega_language_well_defined (omega_sigma_star \<Sigma>) \<Sigma>"
  unfolding omega_sigma_star_def omega_language_well_defined_def by blast

proposition omega_language_well_def_iff: "L \<subseteq> omega_sigma_star \<Sigma> \<longleftrightarrow> omega_language_well_defined L \<Sigma>"
  unfolding omega_sigma_star_def omega_language_well_defined_def by blast

proposition sigma_star_auto_omega_language_left:
  assumes "omega_word \<in> omega_language_auto (\<A>_sigma_star \<Sigma>)" "finite \<Sigma>"
  shows "omega_word \<in> omega_sigma_star \<Sigma>"
  using assms omega_word_in_omega_language_is_well_defined \<A>_sigma_star_well_def unfolding \<A>_sigma_star_def omega_sigma_star_def by fastforce

definition omega_run_sigma_star :: "nat omega_run" where "omega_run_sigma_star n = 0" 

lemma trans_of_\<A>_sigma_star:
  assumes "s1 \<in> states (\<A>_sigma_star \<Sigma>) \<and> a \<in> alphabet (\<A>_sigma_star \<Sigma>) \<and> s2 \<in> states (\<A>_sigma_star \<Sigma>)"
  shows "(s1, a, s2) \<in> transitions (\<A>_sigma_star \<Sigma>)"
  using assms unfolding \<A>_sigma_star_def by auto

lemma omega_run_sigma_star_well_defined:
  assumes "omega_word_well_defined omega_word \<Sigma>"
  shows "omega_run_well_defined omega_run_sigma_star (\<A>_sigma_star \<Sigma>) omega_word"
proof - 
  let ?\<A> = "\<A>_sigma_star \<Sigma>"
  have init: "omega_run_sigma_star 0 = initial_state ?\<A> \<and> initial_state ?\<A> \<in> states ?\<A>" unfolding omega_run_sigma_star_def \<A>_sigma_star_def by force
  {
    fix n
    have symbol: "omega_word n \<in> alphabet ?\<A>" using assms unfolding omega_word_well_defined_def \<A>_sigma_star_def by auto
    have "omega_run_sigma_star n \<in> states ?\<A> \<and> omega_run_sigma_star (n + 1) \<in> states ?\<A>" unfolding omega_run_sigma_star_def \<A>_sigma_star_def by simp
    hence "(omega_run_sigma_star n, omega_word n, omega_run_sigma_star (n + 1)) \<in> transitions ?\<A>" using symbol trans_of_\<A>_sigma_star by fast
  }
  thus ?thesis using init unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
qed

lemma every_omega_run_on_\<A>_sigma_star_is_accepting:
  assumes "finite \<Sigma>" "omega_run_well_defined omega_run (\<A>_sigma_star \<Sigma>) omega_word"
  shows "omega_run_accepting omega_run (\<A>_sigma_star \<Sigma>) omega_word"
proof -
  have "auto_well_defined (\<A>_sigma_star \<Sigma>)" using assms \<A>_sigma_star_well_def by fast
  hence "omega_prun_states omega_run (\<A>_sigma_star \<Sigma>)" using assms well_def_implies_omega_prun_states unfolding omega_run_well_defined_def by fast
  hence "\<forall> n . omega_run n = 0" unfolding \<A>_sigma_star_def omega_prun_states_def by force
  hence "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (\<A>_sigma_star \<Sigma>)" unfolding \<A>_sigma_star_def by auto
  thus ?thesis using assms unfolding omega_run_accepting_def by blast
qed

proposition sigma_star_auto_omega_language_right:
  assumes "finite \<Sigma>" "omega_word \<in> omega_sigma_star \<Sigma>"
  shows "omega_word \<in> omega_language_auto (\<A>_sigma_star \<Sigma>)"
proof -
  have "omega_word_well_defined omega_word \<Sigma>" using assms unfolding omega_sigma_star_def by blast
  hence "omega_run_well_defined omega_run_sigma_star (\<A>_sigma_star \<Sigma>) omega_word" using assms omega_run_sigma_star_well_defined by fast
  hence "omega_run_accepting omega_run_sigma_star (\<A>_sigma_star \<Sigma>) omega_word" using assms every_omega_run_on_\<A>_sigma_star_is_accepting by blast
  thus ?thesis unfolding omega_language_auto_def by blast
qed

theorem equivalence_of_sigma_star_omega_lang:
  assumes "finite \<Sigma>"
  shows "omega_sigma_star \<Sigma> = omega_language_auto (\<A>_sigma_star \<Sigma>)"
  using assms sigma_star_auto_omega_language_left sigma_star_auto_omega_language_right by blast

theorem omega_sigma_star_main:
  assumes "finite \<Sigma>"
  shows "\<exists> sigma_\<A> :: (nat , 'a) automaton . auto_well_defined sigma_\<A> \<and> alphabet sigma_\<A> = \<Sigma> \<and> omega_language_auto sigma_\<A> = omega_sigma_star \<Sigma>"
  using assms \<A>_sigma_star_alphabet \<A>_sigma_star_well_def equivalence_of_sigma_star_omega_lang by metis

definition comp_omega_language :: "'a alphabet \<Rightarrow> 'a omega_language \<Rightarrow> 'a omega_language" where "comp_omega_language \<Sigma> L = omega_sigma_star \<Sigma> - L"

proposition comp_omega_language_well_defined: "omega_language_well_defined (comp_omega_language \<Sigma> L) \<Sigma>"
  using omega_sigma_star_well_defined unfolding comp_omega_language_def omega_language_well_defined_def by blast

lemma comp_omega_language_symmetry:
  assumes "omega_language_well_defined L1 \<Sigma>" "omega_language_well_defined L2 \<Sigma>" "L1 = comp_omega_language \<Sigma> L2"
  shows "comp_omega_language \<Sigma> L1 = L2"
  using assms unfolding comp_omega_language_def omega_sigma_star_def omega_language_well_defined_def by fast

proposition comp_omega_language_characteristic:
  assumes "omega_language_well_defined L \<Sigma>"
  shows "comp_omega_language \<Sigma> L \<union> L = omega_sigma_star \<Sigma> \<and> comp_omega_language \<Sigma> L \<inter> L = {}"
  using assms omega_language_well_def_iff unfolding comp_omega_language_def by auto

lemma word_comp_omega_language1:
  assumes "word \<in> L"
  shows "word \<notin> comp_omega_language \<Sigma> L"
  using assms unfolding comp_omega_language_def by auto

lemma word_comp_omega_language2:
  assumes "omega_word_well_defined word \<Sigma>" "word \<notin> L"
  shows "word \<in> comp_omega_language \<Sigma> L"
  using assms unfolding comp_omega_language_def omega_sigma_star_def by auto

proposition word_comp_omega_language:
  assumes "omega_word_well_defined word \<Sigma>"
  shows "word \<in> L \<longleftrightarrow> word \<notin> comp_omega_language \<Sigma> L"
  using assms word_comp_omega_language1 word_comp_omega_language2 by blast

theorem comp_comp_omega_language: 
  assumes "omega_language_well_defined L \<Sigma>"
  shows "comp_omega_language \<Sigma> (comp_omega_language \<Sigma> L) = L"
  using assms comp_omega_language_symmetry comp_omega_language_well_defined by blast

text \<open>We can show equivalence of explicit omega_languages using the following theorem:\<close>
lemma omega_language_equivalence_right:
  assumes "omega_language_well_defined L1 \<Sigma>" "omega_language_well_defined L2 \<Sigma>" "L1 \<union> comp_omega_language \<Sigma> L2 = omega_sigma_star \<Sigma> \<and> L1 \<inter> comp_omega_language \<Sigma> L2 = {}"
  shows "L1 = L2"
proof(rule ccontr)
  assume "L1 \<noteq> L2"
  then obtain word where word: "(word \<in> L1 \<and> word \<notin> L2) \<or> (word \<in> L2 \<and> word \<notin> L1)" by blast
  hence well_def_word: "omega_word_well_defined word \<Sigma>" using assms unfolding omega_language_well_defined_def by fast
  consider (case1) "word \<in> L1 \<and> word \<notin> L2" | (case2) "word \<in> L2 \<and> word \<notin> L1" using word by fast
  thus False
  proof cases
    case case1 thus ?thesis using assms word_comp_omega_language well_def_word by blast
  next
    case case2 thus ?thesis using assms word_comp_omega_language well_def_word unfolding comp_omega_language_def by auto
  qed
qed

theorem eqiuvalence_of_omega_languages:
  assumes "omega_language_well_defined L1 \<Sigma>" "omega_language_well_defined L2 \<Sigma>"
  shows "L1 = L2 \<longleftrightarrow> L1 \<union> comp_omega_language \<Sigma> L2 = omega_sigma_star \<Sigma> \<and> L1 \<inter> comp_omega_language \<Sigma> L2 = {}"
proof - 
  have left: "L1 = L2 \<longrightarrow> L1 \<union> comp_omega_language \<Sigma> L2 = omega_sigma_star \<Sigma> \<and> L1 \<inter> comp_omega_language \<Sigma> L2 = {}" using assms comp_omega_language_characteristic by blast
  have "L1 \<union> comp_omega_language \<Sigma> L2 = omega_sigma_star \<Sigma> \<and> L1 \<inter> comp_omega_language \<Sigma> L2 = {} \<longrightarrow> L1 = L2" using assms omega_language_equivalence_right by auto
  thus ?thesis using left by linarith
qed





text \<open>Let us study the omega_languages of DBAs:\<close>
definition pre_omega_word :: "'a omega_word \<Rightarrow> nat \<Rightarrow> 'a word" where "pre_omega_word omega_word n = map omega_word [0..<n]"

lemma pre_omega_word_0: "pre_omega_word omega_word 0 = []"
  unfolding pre_omega_word_def by auto

lemma pre_omega_word_nth:
  assumes "i < n"
  shows "(pre_omega_word omega_word n) ! i = omega_word i"
  using assms unfolding pre_omega_word_def by auto

proposition pre_omega_word_set:
  assumes "N > n"
  shows "omega_word n \<in> set (pre_omega_word omega_word N)"
  using assms unfolding pre_omega_word_def by simp

lemma pre_omega_word_length: "length (pre_omega_word omega_word n) = n"
  unfolding pre_omega_word_def by auto

proposition pre_omega_word_well_defined:
  assumes "omega_word_well_defined omega_word \<Sigma>"
  shows "word_well_defined (pre_omega_word omega_word n) \<Sigma>"
  using assms unfolding omega_word_well_defined_def word_well_defined_def pre_omega_word_def by auto

definition pre_omega_run :: "'s omega_run \<Rightarrow> nat \<Rightarrow> 's run" where "pre_omega_run omega_run n = map omega_run [0..<Suc n]"

lemma pre_omega_run_nth:
  assumes "i < Suc n"
  shows "(pre_omega_run omega_run n) ! i = omega_run i"
  using assms Nat.add_diff_assoc2 One_nat_def Suc_diff_Suc Suc_pred add.left_neutral le_add2 nth_map_upt plus_1_eq_Suc zero_less_one unfolding pre_omega_run_def by metis

lemma pre_omega_run_length: "length (pre_omega_run omega_run n) = Suc n"
  unfolding pre_omega_run_def by auto

proposition pre_omega_run_states:
  assumes "omega_prun_states omega_prun \<A>"
  shows "prun_states (pre_omega_run omega_prun n) \<A>"
  using assms unfolding prun_states_def omega_prun_states_def pre_omega_run_def by auto

theorem omega_run_implies_pre_run_well_def:
  assumes "omega_pseudo_run_well_defined omega_run \<A> s omega_word"
  shows "pseudo_run_well_defined (pre_omega_run omega_run n) \<A> s (pre_omega_word omega_word n) \<and> last (pre_omega_run omega_run n) = omega_run n"
proof -
  have len: "length (pre_omega_run omega_run n) = length (pre_omega_word omega_word n) + 1" using pre_omega_run_length pre_omega_word_length Suc_eq_plus1 by metis
  hence "pre_omega_run omega_run n \<noteq> []" by force
  hence last: "last (pre_omega_run omega_run n) = (pre_omega_run omega_run n) ! (length (pre_omega_run omega_run n) - 1)" using list_properties_not_empty by metis
  have "length (pre_omega_run omega_run n) - 1 = n" by (simp add: pre_omega_run_length)
  hence last_last: "last (pre_omega_run omega_run n) = omega_run n" using last pre_omega_run_nth by auto
  have "omega_run 0 = s \<and> s \<in> states \<A>" using assms unfolding omega_pseudo_run_well_defined_def by simp
  hence init: "(pre_omega_run omega_run n) ! 0 = s \<and> s \<in> states \<A>" using pre_omega_run_nth by blast
  have len_run: "length (pre_omega_run omega_run n) = Suc n" using pre_omega_run_length by blast
  hence i: "\<forall> i < length (pre_omega_run omega_run n) - 1 . (pre_omega_run omega_run n) ! i = omega_run i" by (simp add: pre_omega_run_nth)
  have i1: "\<forall> i < length (pre_omega_run omega_run n) - 1 . (pre_omega_run omega_run n) ! (i + 1) = omega_run (i + 1)" using len_run by (simp add: pre_omega_run_nth)
  have "\<forall> i < length (pre_omega_run omega_run n) - 1 . (pre_omega_word omega_word n) ! i = omega_word i" using len_run by (simp add: pre_omega_word_nth)
  hence "\<forall> i < length (pre_omega_run omega_run n) - 1 . ((pre_omega_run omega_run n) ! i, (pre_omega_word omega_word n) ! i, (pre_omega_run omega_run n) ! (i + 1)) \<in> transitions \<A>" using assms i i1 unfolding omega_pseudo_run_well_defined_def by auto
  thus ?thesis using len init last_last unfolding pseudo_run_well_defined_def by blast
qed

corollary omega_run_implies_pre_states_and_word_well_def:
  assumes "auto_well_defined \<A>" "omega_pseudo_run_well_defined omega_run \<A> s omega_word"
  shows "prun_states (pre_omega_run omega_run n) \<A> \<and> word_well_defined (pre_omega_word omega_word n) (alphabet \<A>)"
  using assms omega_run_implies_pre_run_well_def well_def_implies_prun_states well_def_implies_word_well_defined by metis

definition pre_omega_words :: "'a omega_word \<Rightarrow> 'a language" where "pre_omega_words omega_word = {pre_omega_word omega_word n | n . True}"

proposition pre_omega_words_well_defined:
  assumes "omega_word_well_defined omega_word \<Sigma>"
  shows "language_well_defined (pre_omega_words omega_word) \<Sigma>"
  using assms pre_omega_word_well_defined unfolding pre_omega_words_def language_well_defined_def by fast

definition eilenberg_limit :: "'a language \<Rightarrow> 'a omega_language" where "eilenberg_limit L = {omega_word | omega_word . infinite (pre_omega_words omega_word \<inter> L)}"

lemma equi_criterion_eilenberg_left:
  assumes "omega_word \<in> eilenberg_limit L"
  shows "\<forall> n . \<exists> N > n . pre_omega_word omega_word N \<in> L"
proof(rule ccontr)
  assume "\<not> (\<forall> n . \<exists> N > n . pre_omega_word omega_word N \<in> L)"
  hence "\<exists> n . \<forall> N > n . pre_omega_word omega_word N \<notin> L" by blast
  then obtain n where n: "\<forall> N > n . pre_omega_word omega_word N \<notin> (pre_omega_words omega_word \<inter> L)" by blast
  {
    fix oword assume assm: "oword \<in> pre_omega_words omega_word \<inter> L"
    then obtain k where k: "oword = pre_omega_word omega_word k" unfolding pre_omega_words_def by blast
    hence "k \<le> n" using n assm not_le_imp_less by auto
    hence "oword \<in> {pre_omega_word omega_word k | k . k \<le> n }" using k by blast
  }
  hence subset: "pre_omega_words omega_word \<inter> L \<subseteq> {pre_omega_word omega_word k | k . k \<le> n }" by blast
  have "finite {pre_omega_word omega_word k | k . k \<le> n }" by auto
  hence "finite (pre_omega_words omega_word \<inter> L)" using subset finite_subset by blast
  thus False using assms unfolding eilenberg_limit_def by blast
qed

lemma equi_criterion_eilenberg_right:
  assumes "\<forall> n . \<exists> N > n . pre_omega_word omega_word N \<in> L"
  shows "omega_word \<in> eilenberg_limit L"
proof -
  have inf: "infinite {N . pre_omega_word omega_word N \<in> L}"
  proof(rule ccontr)
    assume "\<not> infinite {N . pre_omega_word omega_word N \<in> L}"
    hence "finite {N . pre_omega_word omega_word N \<in> L}" by simp
    hence "\<exists> m . \<forall> n \<in> {N . pre_omega_word omega_word N \<in> L} . n \<le> m" using finite_nat_set_iff_bounded_le by blast
    then obtain m where m: "\<forall> n \<in> {N . pre_omega_word omega_word N \<in> L} . n \<le> m" by blast
    then obtain M where "M > m \<and> pre_omega_word omega_word M \<in> L" using assms by force
    thus False using m by force
  qed
  have "inj_on (\<lambda>N . pre_omega_word omega_word N) {N . pre_omega_word omega_word N \<in> L}" using pre_omega_word_length inj_onI by metis
  hence img_inf: "infinite (image (\<lambda>N . pre_omega_word omega_word N) {N . pre_omega_word omega_word N \<in> L})" using inf by (simp add: finite_image_iff)
  have eq_set: "image (\<lambda>N . pre_omega_word omega_word N) {N . pre_omega_word omega_word N \<in> L} = (pre_omega_words omega_word \<inter> L)" unfolding pre_omega_words_def by auto
  hence "infinite (pre_omega_words omega_word \<inter> L)" using img_inf unfolding pre_omega_words_def by argo
  thus ?thesis unfolding eilenberg_limit_def by blast
qed

theorem equi_criterion_eilenberg: "(\<forall> n . \<exists> N > n . pre_omega_word omega_word N \<in> L) \<longleftrightarrow> omega_word \<in> eilenberg_limit L"
  using equi_criterion_eilenberg_right equi_criterion_eilenberg_left by blast

proposition eilenberg_limit_well_defined:
  assumes "language_well_defined L \<Sigma>"
  shows "omega_language_well_defined (eilenberg_limit L) \<Sigma>"
proof(rule ccontr)
  assume "\<not> omega_language_well_defined (eilenberg_limit L) \<Sigma>"
  then obtain omega_word where omega_word: "omega_word \<in> eilenberg_limit L \<and> \<not> omega_word_well_defined omega_word \<Sigma>" unfolding omega_language_well_defined_def by blast
  then obtain n where n: "omega_word n \<notin> \<Sigma>" unfolding omega_word_well_defined_def by blast
  hence not_well_def: "\<forall> N > n . \<not> word_well_defined (pre_omega_word omega_word N) \<Sigma>" using pre_omega_word_set unfolding word_well_defined_def by blast
  obtain N where N: "N > n \<and> pre_omega_word omega_word N \<in> L" using omega_word n equi_criterion_eilenberg_left by blast
  hence "\<not> word_well_defined (pre_omega_word omega_word N) \<Sigma>" using not_well_def by blast
  thus False using assms N unfolding language_well_defined_def by blast
qed

text \<open>The opposite implication is wrong\<close>
lemma pre_omega_word_eq_fixed_finite: "finite {n. pre_omega_word omega_word n = word}"
proof -
  {
    fix n assume "n \<in> {n . pre_omega_word omega_word n = word}"
    hence "pre_omega_word omega_word n = word" by blast
    hence "length (pre_omega_word omega_word n) = length word" by blast
    hence "n = length word" using pre_omega_word_length by metis
    hence "n \<in> {length word}" by blast
  }
  hence "{n . pre_omega_word omega_word n = word} \<subseteq> {length word}" by fast
  thus ?thesis using finite_subset by fast
qed

lemma eilenberg_limit_singleton_empty: "eilenberg_limit {word} = {}"
proof -
  {
    fix omega_word
    have "pre_omega_words omega_word \<inter> {word} \<subseteq> {word}" by blast
    hence "finite (pre_omega_words omega_word \<inter> {word})" using finite_subset by auto
  }
  hence "\<forall> omega_word. finite (pre_omega_words omega_word \<inter> {word})" by blast
  thus ?thesis unfolding eilenberg_limit_def by blast
qed

proposition not_converse_eilenberg_well_defined:
  assumes "a \<notin> \<Sigma>"
  shows "omega_language_well_defined (eilenberg_limit {[a]}) \<Sigma> \<and> \<not> language_well_defined {[a]} \<Sigma>"
proof -
  have "eilenberg_limit {[a]} = {}" using eilenberg_limit_singleton_empty by blast
  hence limit_well_def: "omega_language_well_defined (eilenberg_limit {[a]}) \<Sigma>" unfolding omega_language_well_defined_def by blast
  have "\<not> word_well_defined [a] \<Sigma>" using assms unfolding word_well_defined_def by auto
  hence "\<not> language_well_defined {[a]} \<Sigma>" unfolding language_well_defined_def by blast
  thus  ?thesis using limit_well_def by auto
qed

text \<open>Let us characterize the omega_languages of DBAs\<close>
lemma omega_lan_in_eilen: "omega_language_auto \<A> \<subseteq> eilenberg_limit (language_auto \<A>)"
proof - 
  {
    fix omega_word assume "omega_word \<in> omega_language_auto \<A>"
    then obtain omega_run where "omega_run_accepting omega_run \<A> omega_word" unfolding omega_language_auto_def by fast
    hence props: "omega_pseudo_run_well_defined omega_run \<A> (initial_state \<A>) omega_word  \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>)" unfolding omega_run_accepting_def omega_run_well_defined_def by blast
    {
      fix n obtain N where "N > n \<and> omega_run N \<in> accepting_states \<A>" using props by auto
      hence "N > n \<and> pseudo_run_well_defined (pre_omega_run omega_run N) \<A> (initial_state \<A>) (pre_omega_word omega_word N) \<and> last (pre_omega_run omega_run N) \<in> accepting_states \<A>" using props omega_run_implies_pre_run_well_def by metis
      hence "N > n \<and> (pre_omega_word omega_word N) \<in> language_auto \<A>" unfolding run_well_defined_def run_accepting_def language_auto_def by blast
      hence "\<exists> N > n . (pre_omega_word omega_word N) \<in> language_auto \<A>" by fast
    }
    hence "\<forall> n . \<exists> N > n . (pre_omega_word omega_word N) \<in> language_auto \<A>" by blast
    hence "omega_word \<in> eilenberg_limit (language_auto \<A>)" using equi_criterion_eilenberg by blast
  }
  thus ?thesis by auto
qed

lemma eilen_in_omega_lan: 
  assumes "auto_well_defined \<A>" "DFA_property \<A>" 
  shows "eilenberg_limit (language_auto \<A>) \<subseteq> omega_language_auto \<A>"
proof - 
  have "language_well_defined (language_auto \<A>) (alphabet \<A>)" using assms automata_language_are_well_defined by auto
  hence well_def: "omega_language_well_defined (eilenberg_limit (language_auto \<A>)) (alphabet \<A>)" using eilenberg_limit_well_defined by blast
  have init: "initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  {
    fix omega_word assume assm: "omega_word \<in> eilenberg_limit (language_auto \<A>)"
    hence omega_word_well_def: "omega_word_well_defined omega_word (alphabet \<A>)" using well_def unfolding omega_language_well_defined_def by auto
    hence "\<exists>! omega_run . omega_run_well_defined omega_run \<A> omega_word" using assms exists_only_one_omega_run_for_DFA by blast
    hence "\<exists>! omega_run . omega_pseudo_run_well_defined omega_run \<A> (initial_state \<A>) omega_word" unfolding omega_run_well_defined_def by auto
    then obtain omega_run where omega_run: "omega_pseudo_run_well_defined omega_run \<A> (initial_state \<A>) omega_word" by auto
    have props: "\<forall> n . \<exists> N > n . pre_omega_word omega_word N \<in> (language_auto \<A>)" using assm equi_criterion_eilenberg by blast
    {
      fix n obtain N where N: "N > n \<and> pre_omega_word omega_word N \<in> (language_auto \<A>)" using props by blast
      hence "word_well_defined (pre_omega_word omega_word N) (alphabet \<A>)" using omega_word_well_def pre_omega_word_well_defined by auto
      hence unique1: "\<exists>! run . pseudo_run_well_defined run \<A> (initial_state \<A>) (pre_omega_word omega_word N)" using exists_only_one_prun_for_DFA assms init by blast
      hence unique2: "\<exists>! run . pseudo_run_well_defined run \<A> (initial_state \<A>) (pre_omega_word omega_word N) \<and> last run \<in> accepting_states \<A>" using N unfolding language_auto_def run_accepting_def run_well_defined_def by blast
      have "pseudo_run_well_defined (pre_omega_run omega_run N) \<A> (initial_state \<A>) (pre_omega_word omega_word N)" using omega_run omega_run_implies_pre_run_well_def by metis
      hence "pseudo_run_well_defined (pre_omega_run omega_run N) \<A> (initial_state \<A>) (pre_omega_word omega_word N) \<and> last (pre_omega_run omega_run N) \<in> accepting_states \<A>" using unique1 unique2 by auto
      hence "pseudo_run_well_defined (pre_omega_run omega_run N) \<A> (initial_state \<A>) (pre_omega_word omega_word N) \<and> omega_run N \<in> accepting_states \<A>" using omega_run_implies_pre_run_well_def omega_run by metis
      hence "\<exists> N > n . omega_run N \<in> accepting_states \<A>" using N by auto
      hence "omega_run_well_defined omega_run \<A> omega_word \<and> (\<exists> N > n . omega_run N \<in> accepting_states \<A>)" using omega_run unfolding omega_run_well_defined_def by blast
    }
    hence "omega_run_accepting omega_run \<A> omega_word" unfolding omega_run_accepting_def by auto
    hence "omega_word \<in> omega_language_auto \<A>" unfolding omega_language_auto_def by blast
  }
  thus ?thesis by blast
qed

theorem omega_lang_is_eilenberg_limit:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "eilenberg_limit (language_auto \<A>) = omega_language_auto \<A>"
  using assms eilen_in_omega_lan omega_lan_in_eilen by auto




text \<open>Now we can prove, that DBAs have not the same expressive power as NBAs\<close>
definition \<A>_NBA :: "(nat, nat) automaton" where "\<A>_NBA = Automaton {0, 1} {0, 1} {(0, 0, 0), (0, 1, 0), (0, 1, 1), (1, 1, 1)} 0 {1}"

proposition well_def_\<A>_NBA: "auto_well_defined \<A>_NBA \<and> \<not> DFA_property \<A>_NBA" unfolding auto_well_defined_def DFA_property_def \<A>_NBA_def by force

theorem NBA_accepts_only_finitely_many_zeros:
  assumes "omega_word \<in> omega_language_auto \<A>_NBA"
  shows "finite {n . omega_word n = 0}"
proof -
  obtain omega_run where "omega_run_accepting omega_run \<A>_NBA omega_word" using assms unfolding omega_language_auto_def by blast
  hence acc: "omega_pseudo_run_well_defined omega_run \<A>_NBA (initial_state \<A>_NBA) omega_word \<and> (\<forall> n. \<exists> N > n. omega_run N \<in> accepting_states \<A>_NBA)" unfolding omega_run_accepting_def omega_run_well_defined_def by blast
  hence acc_states: "\<forall> n . \<exists> N > n . omega_run N = 1" unfolding \<A>_NBA_def by auto
  have zero_forces_state0: "\<forall> n . omega_word n = 0 \<longrightarrow> omega_run n = 0" using acc unfolding omega_pseudo_run_well_defined_def \<A>_NBA_def by auto
  have stay_in_1: "\<forall> n . omega_run n = 1 \<longrightarrow> omega_run (Suc n) = 1" using acc unfolding omega_pseudo_run_well_defined_def \<A>_NBA_def by force
  obtain N where N: "omega_run N = 1" using acc_states by blast
  {
    fix n
    have "n \<ge> N \<Longrightarrow> omega_run n = 1"
    proof (induction "n - N" arbitrary: n)
      case 0 thus ?case using N by auto
    next
      case (Suc nat) thus ?case using stay_in_1 Nat.add_diff_assoc add.right_neutral add_Suc_right add_diff_cancel_left' le0 le_add_same_cancel1 by metis
    qed
  }
  hence tail_all_1: "\<forall> n \<ge> N . omega_run n = 1" by blast
  {
    fix n assume "n \<in> {n . omega_run n = 0}"
    hence "omega_run n = 0" by simp
    hence "\<not> (n \<ge> N)" using tail_all_1 by auto
    hence "n \<in> {..<N}" by simp
  }
  hence "{n . omega_run n = 0} \<subseteq> {..<N}" by blast
  hence finite_run0: "finite {n . omega_run n = 0}" using finite_subset by blast
  have "{n . omega_word n = 0} \<subseteq> {n . omega_run n = 0}" using zero_forces_state0 by blast
  thus ?thesis using finite_subset finite_run0 by blast
qed

definition x_zero :: "nat omega_word" where "x_zero n = (if n = 0 then 0 else 1)"

definition run_zero :: "nat omega_run" where "run_zero n = (if n = 0 then 0 else (if n = 1 then 0 else 1))"

lemma x_zero_in_lang: "x_zero \<in> omega_language_auto \<A>_NBA"
proof -
  have init: "run_zero 0 = initial_state \<A>_NBA \<and> initial_state \<A>_NBA \<in> states \<A>_NBA" unfolding run_zero_def \<A>_NBA_def by simp
  {
    fix n
    have "(run_zero n, x_zero n, run_zero (n + 1)) \<in> transitions \<A>_NBA" unfolding run_zero_def x_zero_def \<A>_NBA_def by fastforce
  }
  hence well_def: "omega_pseudo_run_well_defined run_zero \<A>_NBA (initial_state \<A>_NBA) x_zero" using init unfolding omega_pseudo_run_well_defined_def by simp
  {
    fix n
    have "run_zero (Suc (Suc n)) \<in> accepting_states \<A>_NBA" unfolding run_zero_def \<A>_NBA_def by auto
    hence "\<exists> N > n . run_zero N \<in> accepting_states \<A>_NBA" using less_Suc_eq by blast
  }
  thus ?thesis using well_def unfolding omega_run_well_defined_def omega_run_accepting_def omega_language_auto_def by blast
qed

fun count_zeros :: "nat list \<Rightarrow> nat" where
  "count_zeros [] = 0" |
  "count_zeros (x # xs) = (if x = 0 then (1 + count_zeros xs) else (count_zeros xs))"

proposition count_zeros_append: "count_zeros (list1 @ list2) = count_zeros list1 + count_zeros list2"
  by (induction list1) auto

lemma no_zeros_in_list:
  assumes "\<forall> n < length list . list ! n \<noteq> 0"
  shows "count_zeros list = 0"
  using assms apply (induction list) apply simp by fastforce

lemma pre_omega_word_append: "pre_omega_word omega_word (Suc n) = pre_omega_word omega_word n @ [omega_word n]"
  using pre_omega_word_nth unfolding pre_omega_word_def by(induction n) auto

lemma count_zeros_pre_x_zero: "N > 0 \<Longrightarrow> count_zeros (pre_omega_word x_zero N) = 1"
proof(induction N)
  case 0 thus ?case by blast
next
  case (Suc N)
  consider (case1) "N = 0" | (case2) "N \<noteq> 0" by blast
  thus ?case
  proof cases
    case case1 thus ?thesis unfolding pre_omega_word_def x_zero_def by simp
  next
    case case2
    hence "count_zeros (pre_omega_word x_zero (Suc N)) = count_zeros (pre_omega_word x_zero N) + count_zeros [x_zero N]" using pre_omega_word_append count_zeros_append by metis
    thus ?thesis using Suc case2 unfolding x_zero_def by force
  qed
qed

definition merge_lists_fun :: "'t list \<Rightarrow> (nat \<Rightarrow> 't) \<Rightarrow> (nat \<Rightarrow> 't)" where "merge_lists_fun list fun = (\<lambda>n . if n < length list then list ! n else fun (n - length list))"

lemma merge_lists_fun_pre_omega_word: "list = pre_omega_word (merge_lists_fun list fun) (length list)"
proof -
  have len: "length list = length (pre_omega_word (merge_lists_fun list fun) (length list))" unfolding pre_omega_word_def by simp
  {
    fix i assume "i < length list"
    hence "list ! i = pre_omega_word (merge_lists_fun list fun) (length list) ! i" unfolding pre_omega_word_def merge_lists_fun_def by simp
  }
  thus ?thesis using len nth_equalityI by blast
qed

lemma decompose_merge_lists: "N = M + length word \<Longrightarrow> pre_omega_word (merge_lists_fun word x) N = word @ pre_omega_word x M"
proof(induction M arbitrary: N)
  case 0
  hence "pre_omega_word (merge_lists_fun word x) N = pre_omega_word (merge_lists_fun word x) (length word)" by auto
  hence "pre_omega_word (merge_lists_fun word x) N = word" using merge_lists_fun_pre_omega_word by metis
  thus ?case using pre_omega_word_0 0 by auto
next
  case (Suc M)
  hence N1: "N - 1 = M + length word" by simp
  have "pre_omega_word (merge_lists_fun word x) N = pre_omega_word (merge_lists_fun word x) (N - 1) @ [(merge_lists_fun word x) (N - 1)]" using Suc by (simp add: pre_omega_word_append)
  hence "pre_omega_word (merge_lists_fun word x) N = word @ pre_omega_word x M @ [(merge_lists_fun word x) (M + length word)]" using N1 Suc by force
  hence "pre_omega_word (merge_lists_fun word x) N = word @ pre_omega_word x M @ [x M]" unfolding merge_lists_fun_def by force
  thus ?case unfolding pre_omega_word_def by force
qed

lemma count_zeros_w_i:
  assumes "N > length w_i" "count_zeros w_i = Suc i"
  shows "count_zeros (pre_omega_word (merge_lists_fun w_i x_zero) N) = Suc (Suc i)"
proof - 
  obtain M where "M = N - length w_i" using assms by blast
  hence M: "N = M + length w_i" using assms by fastforce
  hence "pre_omega_word (merge_lists_fun w_i x_zero) N = w_i @ pre_omega_word x_zero M" using decompose_merge_lists by blast
  hence "count_zeros (pre_omega_word (merge_lists_fun w_i x_zero) N) = count_zeros w_i + count_zeros (pre_omega_word x_zero M)" using count_zeros_append by auto
  hence "count_zeros (pre_omega_word (merge_lists_fun w_i x_zero) N) = Suc i + 1" using assms count_zeros_pre_x_zero M by simp
  thus ?thesis by auto
qed

definition zero_list :: "nat \<Rightarrow> nat run" where "zero_list n = replicate n 0"

value "zero_list 5"

proposition zero_list_props: "length (zero_list n) = n \<and> (\<forall> i < n . zero_list n ! i = 0)"
  unfolding zero_list_def by auto

lemma merge_lists_word_x_zero_in_language:
  assumes "word_well_defined word (alphabet \<A>_NBA)"
  shows "merge_lists_fun word x_zero \<in> omega_language_auto \<A>_NBA"
proof(cases word)
  case Nil thus ?thesis using x_zero_in_lang unfolding merge_lists_fun_def by auto
next
  let ?run = "merge_lists_fun (zero_list (length word)) run_zero"
  let ?word = "merge_lists_fun word x_zero"
  case (Cons a as)
  hence not_empty: "word \<noteq> []" by blast
  hence "?run 0 = (zero_list (length word)) ! 0" unfolding merge_lists_fun_def zero_list_def by auto
  hence init: "?run 0 = initial_state \<A>_NBA \<and> initial_state \<A>_NBA \<in> states \<A>_NBA" using not_empty unfolding zero_list_def \<A>_NBA_def by simp
  have "word_well_defined word {0, 1}" using assms unfolding \<A>_NBA_def by auto
  hence i_word: "\<forall> i < length word . word ! i \<in> {0, 1}" using in_set_conv_nth not_empty word_well_def_equivalence by metis
  {
    fix n
    consider (case1) "n < length word - 1" | (case2) "n = length word - 1" | (case3) "n = length word" | (case4) "n = length word + 1" | (case5) "n > length word + 1"using not_empty by linarith
    hence "(?run n, ?word n, ?run (n + 1)) \<in> transitions \<A>_NBA"
    proof cases
      case case1
      hence rn: "?run n = 0" using zero_list_props unfolding merge_lists_fun_def by force
      have "?word n = word ! n" using case1 unfolding merge_lists_fun_def by force
      hence wn: "?word n \<in> {0, 1}" using i_word case1 by simp
      have "?run (n + 1) = 0" using case1 zero_list_props unfolding merge_lists_fun_def by auto
      thus ?thesis using rn wn unfolding \<A>_NBA_def by force
    next
      case case2
      hence rn: "?run n = 0" using zero_list_props unfolding run_zero_def merge_lists_fun_def by force
      have "?word n = word ! n" using case2 not_empty unfolding merge_lists_fun_def by force
      hence wn: "?word n \<in> {0, 1}" using i_word case2 not_empty by simp
      have "?run (n + 1) = 0" using case2 zero_list_props unfolding run_zero_def merge_lists_fun_def by presburger
      thus ?thesis using rn wn unfolding \<A>_NBA_def by force
    next
      case case3
      hence rn: "?run n = 0" using zero_list_props unfolding run_zero_def merge_lists_fun_def by simp
      have wn: "?word n = 0" using case3 unfolding merge_lists_fun_def x_zero_def by simp
      have "?run (n + 1) = 0" using case3 zero_list_props unfolding run_zero_def merge_lists_fun_def by auto
      thus ?thesis using rn wn unfolding \<A>_NBA_def by force
    next
      case case4
      hence rn: "?run n = 0" using zero_list_props unfolding run_zero_def merge_lists_fun_def by force
      have wn: "?word n = 1" using case4 unfolding merge_lists_fun_def x_zero_def by simp
      have "?run (n + 1) = 1" using case4 zero_list_props unfolding run_zero_def merge_lists_fun_def by auto
      thus ?thesis using rn wn unfolding \<A>_NBA_def by force
    next
      case case5
      hence rn: "?run n = 1" using zero_list_props unfolding run_zero_def merge_lists_fun_def by force
      have wn: "?word n = 1" using case5 unfolding merge_lists_fun_def x_zero_def by simp
      have "?run (n + 1) = 1" using case5 zero_list_props unfolding run_zero_def merge_lists_fun_def by auto
      thus ?thesis using rn wn unfolding \<A>_NBA_def by force
    qed
  }
  hence well_def: "omega_pseudo_run_well_defined ?run \<A>_NBA (initial_state \<A>_NBA) ?word" using init unfolding omega_pseudo_run_well_defined_def by simp
  have "\<forall> n > length word + 1 . ?run n = 1" using zero_list_props unfolding run_zero_def merge_lists_fun_def by force
  hence "\<forall> n > length word + 1 . ?run n \<in> accepting_states \<A>_NBA" unfolding \<A>_NBA_def by force
  hence "\<forall> n . \<exists> N > n . ?run N \<in> accepting_states \<A>_NBA" using dual_order.strict_trans less_not_refl not_less_eq by metis 
  thus ?thesis using well_def unfolding omega_run_well_defined_def omega_run_accepting_def omega_language_auto_def by blast
qed

lemma existence_of_xi_wi:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "\<forall> i w_i . w_i \<in> L \<and> word_well_defined w_i (alphabet \<A>_NBA) \<and> count_zeros w_i = Suc i \<longrightarrow> (\<exists> x_i w_next u_i . x_i = merge_lists_fun w_i x_zero \<and> x_i \<in> omega_language_auto \<A>_NBA \<and> w_next \<in> (pre_omega_words x_i \<inter> L) \<and> count_zeros w_next = Suc (Suc i) \<and> w_next = w_i @ u_i)"
proof -
  {
    fix i w_i assume assm: "w_i \<in> L \<and> word_well_defined w_i (alphabet \<A>_NBA) \<and> count_zeros w_i = Suc i"
    let ?x_i = "merge_lists_fun w_i x_zero"
    have x_in: "?x_i \<in> omega_language_auto \<A>_NBA" using assm merge_lists_word_x_zero_in_language by blast
    hence "?x_i \<in> eilenberg_limit L" using assms by simp
    hence "\<forall>n . \<exists>N > n . pre_omega_word ?x_i N \<in> L" using equi_criterion_eilenberg by blast
    then obtain N where N: "N > length w_i \<and> pre_omega_word ?x_i N \<in> L" by blast
    define u_i where "u_i = pre_omega_word x_zero (N - length w_i)"
    define w_next where "w_next = pre_omega_word ?x_i N"
    have "N = (N - length w_i) + length w_i" using N by simp
    hence "pre_omega_word (merge_lists_fun w_i x_zero) N = w_i @ pre_omega_word x_zero (N - length w_i)" using decompose_merge_lists by blast
    hence decomp: "w_next = w_i @ u_i" unfolding w_next_def u_i_def by simp
    have w_next_in: "w_next \<in> pre_omega_words ?x_i \<inter> L" using N  unfolding w_next_def pre_omega_words_def by blast
    have "count_zeros w_next = Suc (Suc i)" using count_zeros_w_i assm N unfolding w_next_def by blast
    hence "\<exists> x_i w_next u_i . x_i = merge_lists_fun w_i x_zero \<and> x_i \<in> omega_language_auto \<A>_NBA \<and> w_next \<in> pre_omega_words x_i \<inter> L \<and> count_zeros w_next = Suc (Suc i) \<and> w_next = w_i @ u_i" using x_in w_next_in decomp by blast
  }
  thus ?thesis by presburger
qed

lemma exists_w0:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "\<exists> w0. w0 \<in> L \<and> word_well_defined w0 (alphabet \<A>_NBA) \<and> count_zeros w0 = 1"
proof -
  have x_in: "x_zero \<in> omega_language_auto \<A>_NBA" using x_zero_in_lang by simp
  hence "x_zero \<in> eilenberg_limit L" using assms by simp
  hence "\<forall> n . \<exists> N > n . pre_omega_word x_zero N \<in> L" using equi_criterion_eilenberg by blast
  then obtain N where "N > 0 \<and> pre_omega_word x_zero N \<in> L" by blast
  hence "pre_omega_word x_zero N \<in> L \<and> count_zeros (pre_omega_word x_zero N) = 1" using count_zeros_pre_x_zero by blast
  thus ?thesis using x_in assms unfolding pre_omega_words_def language_well_defined_def by blast
qed

definition w0 :: "nat language \<Rightarrow> nat word" where "w0 L = (SOME w0. w0 \<in> L \<and> word_well_defined w0 (alphabet \<A>_NBA) \<and> count_zeros w0 = 1)"

lemma w0_props:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "(w0 L) \<in> L \<and> word_well_defined (w0 L) (alphabet \<A>_NBA) \<and> count_zeros (w0 L) = 1"
  using assms exists_w0 unfolding w0_def by (metis (mono_tags, lifting) some_eq_imp)

definition step_pair :: "nat \<Rightarrow> nat word \<Rightarrow> nat language \<Rightarrow> (nat word \<times> nat word)" where "step_pair i w_i L = (SOME p . \<exists> x_i . x_i = merge_lists_fun w_i x_zero \<and> x_i \<in> omega_language_auto \<A>_NBA \<and> fst p \<in> (pre_omega_words x_i \<inter> L) \<and> count_zeros (fst p) = Suc (Suc i) \<and> fst p = w_i @ snd p)"

fun w_i_fun :: "nat \<Rightarrow> nat language \<Rightarrow> nat word" where
  "w_i_fun 0 L = w0 L" |
  "w_i_fun (Suc i) L = fst (step_pair i (w_i_fun i L) L)"

definition u_i_fun :: "nat \<Rightarrow> nat language \<Rightarrow> nat list" where "u_i_fun i L = snd (step_pair i (w_i_fun i L) L)"

lemma step_pair_sound:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA" "w_i \<in> L \<and> word_well_defined w_i (alphabet \<A>_NBA) \<and> count_zeros w_i = Suc i"
  shows "fst (step_pair i w_i L) \<in> (pre_omega_words (merge_lists_fun w_i x_zero) \<inter> L) \<and> count_zeros (fst (step_pair i w_i L)) = Suc (Suc i) \<and> fst (step_pair i w_i L) = w_i @ snd (step_pair i w_i L)"
proof -
  have "\<exists> x_i w_next u_i . x_i = merge_lists_fun w_i x_zero \<and> x_i \<in> omega_language_auto \<A>_NBA \<and> w_next \<in> (pre_omega_words x_i \<inter> L) \<and> count_zeros w_next = Suc (Suc i) \<and> w_next = w_i @ u_i" using existence_of_xi_wi assms by presburger
  hence "\<exists> p . \<exists> x_i . x_i = merge_lists_fun w_i x_zero \<and> x_i \<in> omega_language_auto \<A>_NBA \<and> fst p \<in> (pre_omega_words x_i \<inter> L) \<and> count_zeros (fst p) = Suc (Suc i) \<and> fst p = w_i @ snd p" using assms by fastforce
  thus ?thesis unfolding step_pair_def by (smt (verit, best) some_eq_imp)
qed

lemma w_i_fun_invariants:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "\<forall> i . w_i_fun i L \<in> L \<and> word_well_defined (w_i_fun i L) (alphabet \<A>_NBA) \<and> count_zeros (w_i_fun i L) = Suc i"
proof -
  {
    fix i
    have "w_i_fun i L \<in> L \<and> word_well_defined (w_i_fun i L) (alphabet \<A>_NBA) \<and> count_zeros (w_i_fun i L) = Suc i"
    proof (induction i)
      case 0 thus ?case using assms w0_props by force
    next
      case (Suc i)
      hence "fst (step_pair i (w_i_fun i L) L) \<in> (pre_omega_words (merge_lists_fun (w_i_fun i L) x_zero) \<inter> L) \<and> count_zeros (fst (step_pair i (w_i_fun i L) L)) = Suc (Suc i) \<and> fst (step_pair i (w_i_fun i L) L) = w_i_fun i L @ snd (step_pair i (w_i_fun i L) L)" using assms step_pair_sound by blast
      hence props: "fst (step_pair i (w_i_fun i L) L) \<in> L \<and> count_zeros (fst (step_pair i (w_i_fun i L) L)) = Suc (Suc i)" by blast
      hence "word_well_defined (fst (step_pair i (w_i_fun i L) L)) (alphabet \<A>_NBA)" using assms unfolding language_well_defined_def by blast
      thus ?case using props by auto
    qed
  }
  thus ?thesis by blast
qed

lemma w_i_fun_suc_decomp:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "w_i_fun (Suc i) L = w_i_fun i L @ u_i_fun i L"
proof -
  have "w_i_fun i L \<in> L \<and> word_well_defined (w_i_fun i L) (alphabet \<A>_NBA) \<and> count_zeros (w_i_fun i L) = Suc i" using assms w_i_fun_invariants by blast
  hence "fst (step_pair i (w_i_fun i L) L) = w_i_fun i L @ snd (step_pair i (w_i_fun i L) L)" using step_pair_sound assms by blast
  thus ?thesis unfolding u_i_fun_def by auto
qed

lemma u_i_fun_nonempty:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "u_i_fun i L \<noteq> []"
proof -
  have inv_i: "count_zeros (w_i_fun i L) = Suc i" using w_i_fun_invariants assms by blast
  have inv_s: "count_zeros (w_i_fun (Suc i) L) = Suc (Suc i)" using w_i_fun_invariants assms by blast
  have "(w_i_fun (Suc i) L) = (w_i_fun i L) @ (u_i_fun i L)" using w_i_fun_suc_decomp assms by blast
  hence "count_zeros (u_i_fun i L) = 1" using inv_i inv_s count_zeros_append by auto
  thus ?thesis by auto
qed

lemma lengths_monoton:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "\<forall> i . length (w_i_fun i L) < length (w_i_fun (Suc i) L)"
proof -
  {
    fix i
    have append: "(w_i_fun (Suc i) L) = (w_i_fun i L) @ (u_i_fun i L)" using w_i_fun_suc_decomp assms by blast
    have "(u_i_fun i L) \<noteq> []" using u_i_fun_nonempty assms by blast
    hence "length (w_i_fun i L) < length (w_i_fun (Suc i) L)" using append by force
  }
  thus ?thesis by blast
qed

lemma lengths_unbounded:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "\<forall> n . \<exists> i . n < length (w_i_fun i L)"
proof -
  {
    fix n
    have "\<forall> i . length (w_i_fun i L) < length (w_i_fun (Suc i) L)" using assms lengths_monoton by blast
    hence "n < length (w_i_fun (n + 1) L)" apply(induction n) apply simp apply (metis less_nat_zero_code list.size(3) w_i_fun.simps(1)) using Suc_eq_plus1 less_trans_Suc by metis
    hence "\<exists> i . n < length (w_i_fun i L)" by blast
  }
  thus ?thesis by blast
qed

definition z :: "nat language \<Rightarrow> nat omega_word" where "z L n = (w_i_fun (LEAST i . n < length (w_i_fun i L)) L) ! n"

lemma w_i_fun_prefix: 
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA" 
  shows "i \<le> j \<Longrightarrow> w_i_fun i L = take (length (w_i_fun i L)) (w_i_fun j L)"
proof (induction j)
  case 0 thus ?case by auto
next
  case (Suc j)
  then consider (case1) "i \<le> j" | (case2) "i = Suc j" by linarith
  thus ?case
  proof cases
    case case1
    hence IH: "w_i_fun i L = take (length (w_i_fun i L)) (w_i_fun j L)" using Suc by blast
    have "w_i_fun (Suc j) L = w_i_fun j L @ u_i_fun j L" using assms w_i_fun_suc_decomp by auto
    thus ?thesis using IH append.assoc append_eq_conv_conj append_take_drop_id by metis
  next
    case case2 thus ?thesis by auto
  qed
qed

lemma pre_z_eq_w_i:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "pre_omega_word (z L) (length (w_i_fun i L)) = w_i_fun i L"
proof - 
  have length: "length (pre_omega_word (z L) (length (w_i_fun i L))) = length (w_i_fun i L)" by (simp add: pre_omega_word_length)
  { 
    fix n assume assm: "n < length (pre_omega_word (z L) (length (w_i_fun i L)))"
    hence nlt_i: "n < length (w_i_fun i L)" by (simp add: pre_omega_word_length)
    let ?j = "(LEAST j. n < length (w_i_fun j L))"
    have j_le_i: "?j \<le> i" using Least_le assms nlt_i by metis
    hence pref: "w_i_fun ?j L = take (length (w_i_fun ?j L)) (w_i_fun i L)" using assms w_i_fun_prefix by blast
    have nthz: "(pre_omega_word (z L) (length (w_i_fun i L))) ! n = (z L) n" using assm length pre_omega_word_nth by auto
    have "n < length (w_i_fun ?j L)" using LeastI_ex assms lengths_unbounded by metis
    hence "take (length (w_i_fun ?j L)) (w_i_fun i L) ! n = (w_i_fun i L) ! n" using  j_le_i by simp
    hence "(pre_omega_word (z L) (length (w_i_fun i L))) ! n = (w_i_fun i L) ! n" using pref nthz unfolding z_def by auto
  }
  thus ?thesis using length nth_equalityI by blast
qed

lemma infinitely_many_prefixes_of_z_in_L:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "\<forall> i . pre_omega_word (z L) (length (w_i_fun i L)) \<in> L"
  using pre_z_eq_w_i w_i_fun_invariants assms by presburger

lemma z_in_eilenberg_limit:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "z L \<in> eilenberg_limit L"
proof -
  have strict: "\<forall> i . length (w_i_fun i L) < length (w_i_fun (Suc i) L)" using lengths_monoton assms by blast
  {
    fix i j assume eq: "pre_omega_word (z L) (length (w_i_fun i L)) = pre_omega_word (z L) (length (w_i_fun j L))"
    hence "length (w_i_fun i L) = length (w_i_fun j L)" using pre_omega_word_length by metis
    hence "i = j" using strict assms nat.inject pre_z_eq_w_i w_i_fun_invariants by metis
  }
  hence "inj_on (\<lambda>i . pre_omega_word (z L) (length (w_i_fun i L))) UNIV" by (rule inj_onI)
  hence inf: "infinite {pre_omega_word (z L) (length (w_i_fun i L)) | i . True}" using infinite_UNIV_nat by (simp add: finite_image_iff full_SetCompr_eq)
  hence "{pre_omega_word (z L) (length (w_i_fun i L)) | i . True} \<subseteq> pre_omega_words (z L) \<inter> L" using infinitely_many_prefixes_of_z_in_L assms unfolding pre_omega_words_def by blast
  thus ?thesis using inf finite_subset unfolding eilenberg_limit_def by blast
qed

lemma finite_zeros_bounded:
  assumes "finite {n . (omega_word :: nat \<Rightarrow> nat) n = 0}"
  shows "\<exists> N . \<forall> n \<ge> N . omega_word n \<noteq> 0"
proof -
  have "\<exists> m . \<forall> n \<in> {n . omega_word n = 0} . n \<le> m" using assms finite_nat_set_iff_bounded_le by blast
  then obtain m where m: "\<forall> n \<in> {n . omega_word n = 0} . n \<le> m" by blast
  {
    fix n assume "n \<ge> Suc m"
    hence "\<not> (n \<le> m)" by simp
    hence "omega_word n \<noteq> 0" using m by auto
  }
  thus ?thesis by blast
qed

lemma count_zeros_le_length: "count_zeros list \<le> length list"
  by (induction list) auto

lemma count_zeros_all_nonzero:
  assumes "\<forall> a \<in> set list . a \<noteq> 0"
  shows "count_zeros list = 0"
  using assms by (induction list) auto

lemma exists_zero_index_ge:
  assumes "count_zeros list = Suc i"
  shows "\<exists> n < length list . n \<ge> i \<and> list ! n = 0"
proof (rule ccontr)
  assume assm: "\<not> (\<exists>n < length list . n \<ge> i \<and> list ! n = 0)"
  {
    fix a assume "a \<in> set (drop i list)"
    then obtain k where k: "k < length (drop i list) \<and> a = drop i list ! k" using in_set_conv_nth by metis
    hence ik_lt: "i + k < length list" by force
    have "\<not> (i + k < length list \<and> i + k \<ge> i \<and> list ! (i + k) = 0)" using assm by blast
    hence "list ! (i + k) \<noteq> 0" using ik_lt  by simp
    hence "a \<noteq> 0" using k by auto
  }
  hence "\<forall> a \<in> set (drop i list) . a \<noteq> 0" by blast
  hence cz_drop: "count_zeros (drop i list) = 0" using count_zeros_all_nonzero by blast
  have "count_zeros list = count_zeros (take i list) + count_zeros (drop i list)" using count_zeros_append[of "take i list" "drop i list"] by (simp add: take_drop)
  hence cz_take: "count_zeros list = count_zeros (take i list)" using cz_drop by simp
  have "count_zeros (take i list) \<le> length (take i list)" using count_zeros_le_length by blast
  hence "count_zeros list \<le> i" using count_zeros_le_length cz_take by simp
  thus False using assms by simp
qed

lemma z_has_unbounded_zeros:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "\<forall> N . \<exists> n \<ge> N . z L n = 0"
proof -
  {
    fix i
    have pref: "pre_omega_word (z L) (length (w_i_fun i L)) = w_i_fun i L" using pre_z_eq_w_i assms by auto
    have "count_zeros (w_i_fun i L) = Suc i" using w_i_fun_invariants assms by blast
    hence "\<exists> n < length (w_i_fun i L) . n \<ge> i \<and> (w_i_fun i L) ! n = 0" using exists_zero_index_ge by auto
    then obtain n where n: "n < length (w_i_fun i L) \<and> n \<ge> i \<and> (w_i_fun i L) ! n = 0" by blast
    hence "z L n = 0" using pref pre_omega_word_nth by metis
    hence "\<exists> n \<ge> i . z L n = 0" using n by blast
  }
  thus ?thesis by auto
qed

lemma z_not_in_omega_language:
  assumes "language_well_defined L (alphabet \<A>_NBA)" "eilenberg_limit L = omega_language_auto \<A>_NBA"
  shows "z L \<notin> omega_language_auto \<A>_NBA"
proof(rule ccontr)
  assume "\<not> z L \<notin> omega_language_auto \<A>_NBA"
  hence "z L \<in> omega_language_auto \<A>_NBA" by simp
  hence "finite {n. z L n = 0}" using NBA_accepts_only_finitely_many_zeros by blast
  then obtain N where N: "\<forall> n \<ge> N . z L n \<noteq> 0" using finite_zeros_bounded by blast
  have "\<forall> N . \<exists> n \<ge> N . z L n = 0" using z_has_unbounded_zeros assms by blast
  then obtain n where "n \<ge> N \<and> z L n = 0" using N by blast
  thus False using N by blast
qed

proposition there_is_no_DFA_for_A_NBA: "\<nexists> (DFA_\<A> :: (nat, nat) automaton). auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = alphabet \<A>_NBA \<and> omega_language_auto DFA_\<A> = omega_language_auto \<A>_NBA"
proof (rule ccontr)
  assume "\<not> (\<nexists> (DFA_\<A> :: (nat, nat) automaton). auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = alphabet \<A>_NBA \<and> omega_language_auto DFA_\<A> = omega_language_auto \<A>_NBA)"
  then obtain \<A> :: "(nat, nat) automaton" where A: "auto_well_defined \<A> \<and> DFA_property \<A> \<and> alphabet \<A> = alphabet \<A>_NBA \<and> omega_language_auto \<A> = omega_language_auto \<A>_NBA" by blast
  hence equi: "eilenberg_limit (language_auto \<A>) = omega_language_auto \<A>_NBA" using omega_lang_is_eilenberg_limit by auto
  have "language_well_defined (language_auto \<A>) (alphabet \<A>_NBA)" using automata_language_are_well_defined A by metis
  hence "z (language_auto \<A>) \<in> eilenberg_limit (language_auto \<A>) \<and> z (language_auto \<A>) \<notin> omega_language_auto \<A>_NBA" using z_not_in_omega_language z_in_eilenberg_limit equi by blast
  thus False using equi by auto
qed

text \<open>Reachability of Büchi automata\<close>
corollary omega_language_well_def_reach_auto:
  assumes "auto_well_defined \<A>"
  shows "omega_language_well_defined (omega_language_auto (reachable_automaton \<A>)) (alphabet (reachable_automaton \<A>))"
  using well_def_reachable_automaton assms automata_omega_language_are_well_defined by blast

lemma omega_prun_reachable_automaton_left:
  assumes "auto_well_defined \<A>" "omega_pseudo_run_well_defined omega_prun (reachable_automaton \<A>) s omega_word"
  shows "omega_pseudo_run_well_defined omega_prun \<A> s omega_word \<and> reachable_state s \<A>"
  using assms reachable_states_are_states unfolding omega_pseudo_run_well_defined_def reachable_automaton_def by auto

corollary omega_run_reachable_automaton_left:
  assumes "auto_well_defined \<A>" "omega_run_well_defined omega_run (reachable_automaton \<A>) omega_word"
  shows "omega_run_well_defined omega_run \<A> omega_word"
  using assms omega_prun_reachable_automaton_left initial_state_is_reachable unfolding omega_run_well_defined_def reachable_automaton_def by force

corollary omega_prun_reachable_automaton_left_acc:
  assumes "auto_well_defined \<A>" "omega_run_accepting omega_run (reachable_automaton \<A>) omega_word"
  shows "omega_run_accepting omega_run \<A> omega_word"
  using assms omega_run_reachable_automaton_left unfolding omega_run_accepting_def reachable_automaton_def by auto

lemma omega_prun_reachable_automaton_right:
  assumes "auto_well_defined \<A>" "omega_pseudo_run_well_defined omega_prun \<A> s omega_word \<and> reachable_state s \<A>"
  shows "omega_pseudo_run_well_defined omega_prun (reachable_automaton \<A>) s omega_word"
proof - 
  have "omega_prun 0 = s" using assms unfolding omega_pseudo_run_well_defined_def by blast
  hence init: "omega_prun 0 = s \<and> s \<in> states (reachable_automaton \<A>)" using assms unfolding reachable_automaton_def reachable_states_def by auto
  {
    fix i
    have "omega_prun i \<in> states (reachable_automaton \<A>)"
    proof(induction i)
      case 0 thus ?case using init by blast
    next
      case (Suc i) thus ?case using assms inheritance_reachable_state unfolding omega_pseudo_run_well_defined_def reachable_automaton_def reachable_states_def by fastforce
    qed
  }
  hence "\<forall> i . omega_prun i \<in> states (reachable_automaton \<A>)" by auto
  hence "\<forall> i . (omega_prun i, omega_word i, omega_prun (i + 1)) \<in> transitions (reachable_automaton \<A>)" using assms unfolding omega_pseudo_run_well_defined_def reachable_automaton_def reachable_states_def by force
  thus ?thesis using init unfolding omega_pseudo_run_well_defined_def by blast
qed

corollary omega_run_reachable_automaton_right:
  assumes "auto_well_defined \<A>" "omega_run_well_defined omega_run \<A> omega_word"
  shows "omega_run_well_defined omega_run (reachable_automaton \<A>) omega_word"
proof - 
  have omega_prun: "omega_pseudo_run_well_defined omega_run \<A> (initial_state \<A>) omega_word" using assms unfolding omega_run_well_defined_def by blast
  have "reachable_state (initial_state \<A>) \<A>" using assms initial_state_is_reachable by blast
  hence "omega_pseudo_run_well_defined omega_run (reachable_automaton \<A>) (initial_state \<A>) omega_word" using assms omega_prun omega_prun_reachable_automaton_right by fast
  thus ?thesis using omega_run_well_defined_def unfolding reachable_automaton_def by fastforce
qed

corollary omega_prun_reachable_automaton_right_acc:
  assumes "auto_well_defined \<A>" "omega_run_accepting omega_prun \<A> omega_word"
  shows "omega_run_accepting omega_prun (reachable_automaton \<A>) omega_word"
proof - 
  have omega_run: "omega_run_well_defined omega_prun (reachable_automaton \<A>) omega_word" using assms omega_run_reachable_automaton_right unfolding omega_run_accepting_def by blast
  have "omega_prun 0 = (initial_state \<A>)" using assms unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
  hence "omega_prun 0 = (initial_state \<A>) \<and> reachable_state (initial_state \<A>) \<A>" using assms initial_state_is_reachable by blast
  hence init: "omega_prun 0 = (initial_state \<A>) \<and> (initial_state \<A>) \<in> states (reachable_automaton \<A>)" unfolding reachable_automaton_def reachable_states_def by auto
  {
    fix i
    have "omega_prun i \<in> states (reachable_automaton \<A>)"
    proof(induction i)
      case 0 thus ?case using init by auto
    next
      case (Suc i) thus ?case using assms inheritance_reachable_state unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def reachable_automaton_def reachable_states_def by fastforce
    qed
  }
  hence "\<forall> i . omega_prun i \<in> states (reachable_automaton \<A>)" by auto
  hence "\<forall> i . omega_prun i \<in> accepting_states \<A> \<longrightarrow> omega_prun i \<in> accepting_states (reachable_automaton \<A>)" unfolding reachable_automaton_def by force
  thus ?thesis using omega_run assms unfolding omega_run_accepting_def by blast
qed

proposition omega_run_acc_reachable_automaton:
  assumes "auto_well_defined \<A>"
  shows "omega_run_accepting omega_prun \<A> omega_word \<longleftrightarrow> omega_run_accepting omega_prun (reachable_automaton \<A>) omega_word"
  using assms omega_prun_reachable_automaton_left_acc omega_prun_reachable_automaton_right_acc by blast

theorem reachable_automaton_omega_language_correctness:
  assumes "auto_well_defined \<A>"
  shows "omega_language_auto \<A> = omega_language_auto (reachable_automaton \<A>)"
  using assms omega_run_acc_reachable_automaton unfolding omega_language_auto_def by blast

theorem reachable_main_omega:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)"
  shows "\<exists> reach_\<A> :: ('s, 'a) automaton . auto_well_defined reach_\<A> \<and> alphabet reach_\<A> = alphabet \<A> \<and> omega_language_auto reach_\<A> = omega_language_auto \<A> \<and> connected_automaton reach_\<A>"
  using assms reachable_automaton_omega_language_correctness alphabet_reachable_auto well_def_reachable_automaton reachable_automaton_connected by fast

end