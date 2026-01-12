theory omega_automata

imports Main masterarbeit_benno_thalmann

begin

text \<open>Author: Benno Thalmann, last update: 11.1.2026, Addition to masterarbeit_benno_thalmann\<close>

text \<open>Type definitions\<close>
type_synonym 'a omega_word = "nat \<Rightarrow> 'a symbol"
type_synonym 'a omega_language = "'a omega_word set"
type_synonym 's omega_run = "nat \<Rightarrow> 's state"

text \<open>general definitions of omega_words and omega_languages\<close>
definition omega_word_well_defined :: "'a omega_word \<Rightarrow> 'a alphabet \<Rightarrow> bool" where "omega_word_well_defined omega_word \<Sigma> = (\<forall> n . omega_word n \<in> \<Sigma>)"

definition omega_language_well_defined :: "'a omega_language \<Rightarrow> 'a alphabet \<Rightarrow> bool" where "omega_language_well_defined L \<Sigma> = (\<forall> omega_word \<in> L . omega_word_well_defined omega_word \<Sigma>)"



text \<open>First property for well-definedness of a pseudo-run\<close>
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

text \<open>Next goal: For a well-defined word, there is exactly one pseudo_run on a DFA\<close>
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

text \<open>Definition of an accepting run over a word\<close>
definition omega_run_well_defined :: "'s omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> bool" where "omega_run_well_defined omega_run \<A> omega_word = omega_pseudo_run_well_defined omega_run \<A> (initial_state \<A>) omega_word"

corollary exists_only_one_omega_run_for_DFA:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "omega_word_well_defined omega_word (alphabet \<A>) \<Longrightarrow> \<exists>! omega_run . omega_run_well_defined omega_run \<A> omega_word"
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

lemma no_acc_states:
  assumes "accepting_states \<A> = {}"
  shows "omega_language_auto \<A> = {}"
  using assms unfolding omega_language_auto_def omega_run_accepting_def by blast

text \<open>If the automaton is well-defined, then the accepted omega_words will be well-defined\<close>
corollary omega_word_in_omega_language_is_well_defined:
  assumes "auto_well_defined \<A>" "omega_word \<in> omega_language_auto \<A>"
  shows "omega_word_well_defined omega_word (alphabet \<A>)"
  using assms well_def_implies_omega_word_well_defined unfolding omega_language_auto_def omega_run_accepting_def omega_run_well_defined_def by auto

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

lemma omega_language_subset_of_omega_sigma_star:
  assumes "omega_language_well_defined L \<Sigma>"
  shows "L \<subseteq> omega_sigma_star \<Sigma>"
  using assms unfolding omega_sigma_star_def omega_language_well_defined_def by auto

lemma subsets_of_omega_sigma_star:
  assumes "L \<subseteq> omega_sigma_star \<Sigma>"
  shows "omega_language_well_defined L \<Sigma>"
  using assms unfolding omega_sigma_star_def omega_language_well_defined_def by blast

proposition omega_language_well_def_iff: "L \<subseteq> omega_sigma_star \<Sigma> \<longleftrightarrow> omega_language_well_defined L \<Sigma>"
  using omega_language_subset_of_omega_sigma_star subsets_of_omega_sigma_star by blast

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

lemma every_run_on_\<A>_sigma_star_is_accepting:
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
  hence "omega_run_accepting omega_run_sigma_star (\<A>_sigma_star \<Sigma>) omega_word" using assms every_run_on_\<A>_sigma_star_is_accepting by blast
  thus ?thesis unfolding omega_language_auto_def by blast
qed

theorem equivalence_of_sigma_star_omega_lang:
  assumes "finite \<Sigma>"
  shows "omega_sigma_star \<Sigma> = omega_language_auto (\<A>_sigma_star \<Sigma>)"
  using assms sigma_star_auto_omega_language_left sigma_star_auto_omega_language_right by blast

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
  using assms omega_language_subset_of_omega_sigma_star unfolding comp_omega_language_def by auto

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

end