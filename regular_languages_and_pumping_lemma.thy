theory regular_languages_and_pumping_lemma

imports Main regular_grammars regular_expressions automaton_iterativ

begin

text \<open>Author: Benno Thalmann, last update: 27.12.2025, Addition to masterarbeit_benno_thalmann\<close>

text \<open>Regular_languages and Expressive Power Collection\<close>
definition regular_languages :: "'a alphabet \<Rightarrow> 'a language set" where "regular_languages \<Sigma> = {L . \<exists> (r :: 'a regular_expression) . RE_well_defined r \<Sigma> \<and> L = language_reg_exp r}"

proposition well_def_word_reg_languages:
  assumes "word \<in> L \<and> L \<in> regular_languages \<Sigma>"
  shows "word_well_defined word \<Sigma>"
  using assms word_in_language_reg_is_well_defined unfolding regular_languages_def by blast

proposition not_empty_reg_languages:
  assumes "regular_languages \<Sigma> \<noteq> {}"
  shows "finite \<Sigma>"
  using assms unfolding regular_languages_def RE_well_defined_def by blast

corollary inifinte_alphabet_implies_empty_reg_lang: "infinite \<Sigma> \<Longrightarrow> regular_languages \<Sigma> = {}"
  using not_empty_reg_languages by blast

proposition empty_reg_languages:
  assumes "regular_languages \<Sigma> = {}"
  shows "infinite \<Sigma>"
proof(rule ccontr)
  assume "\<not> infinite \<Sigma>"
  hence "finite \<Sigma>" by simp
  hence "RE_well_defined Empty_string \<Sigma>" unfolding RE_well_defined_def by simp
  hence "{[]} \<in> regular_languages \<Sigma>" unfolding regular_languages_def by force
  thus False using assms by blast
qed

theorem inifinite_alphabet: "infinite \<Sigma> \<longleftrightarrow> regular_languages \<Sigma> = {}"
  using empty_reg_languages inifinte_alphabet_implies_empty_reg_lang by blast

theorem reg_lang_nfas:
  assumes "infinite (UNIV :: 's set)" 
  shows "regular_languages \<Sigma> = {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}"
  using assms expressive_power_auto_RE_main unfolding regular_languages_def by blast

theorem reg_lang_dfas:
  assumes "infinite (UNIV :: 's set)" 
  shows "regular_languages \<Sigma> = {L . \<exists> (DFA_\<A> :: ('s, 'a) automaton) . auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = \<Sigma> \<and> L = language_auto DFA_\<A>}"
proof -
  have reg: "regular_languages \<Sigma> = {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" using assms reg_lang_nfas by blast
  have "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> \<Sigma> = alphabet NFA_\<A> \<and> L = language_auto NFA_\<A>} = {L . \<exists> (DFA_\<A> :: ('s, 'a) automaton) . auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = \<Sigma> \<and> L = language_auto DFA_\<A>}" using assms expressive_power_dfa_nfa_main by blast
  thus ?thesis using reg by auto
qed

theorem reg_lang_nfas_multis:
  assumes "infinite (UNIV :: 's set)" 
  shows "regular_languages \<Sigma> = {L . \<exists> (NFA_\<A>_multi :: ('s, 'a) nfa_multi) . auto_well_defined_multi NFA_\<A>_multi \<and> alphabet_multi NFA_\<A>_multi = \<Sigma> \<and> L = language_auto_multi NFA_\<A>_multi}"
proof -
  have reg: "regular_languages \<Sigma> = {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" using assms reg_lang_nfas by blast
  have "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>} = {L . \<exists> (NFA_\<A>_multi :: ('s, 'a) nfa_multi) . auto_well_defined_multi NFA_\<A>_multi \<and> alphabet_multi NFA_\<A>_multi = \<Sigma> \<and> L = language_auto_multi NFA_\<A>_multi}" using assms expressive_power_multi_nfa_main by blast
  thus ?thesis using reg by auto
qed

theorem reg_lang_nfas_epsilon:
  assumes "infinite (UNIV :: 's set)" 
  shows "regular_languages \<Sigma> = image eps_free_language {L . \<exists> (NFA_\<A>_eps :: ('s, 'a + unit) automaton) . auto_well_defined NFA_\<A>_eps \<and> original_alphabet (alphabet NFA_\<A>_eps) = \<Sigma> \<and> L = language_auto NFA_\<A>_eps}"
proof -
  have reg: "regular_languages \<Sigma> = {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" using assms reg_lang_nfas by blast
  have "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and>  alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>} = image eps_free_language {L . \<exists> (NFA_\<A>_eps :: ('s, 'a + unit) automaton) . auto_well_defined NFA_\<A>_eps \<and> original_alphabet (alphabet NFA_\<A>_eps) = \<Sigma> \<and> L = language_auto NFA_\<A>_eps}" using assms expressive_power_eps_nfa_main by blast
  thus ?thesis using reg by auto
qed

theorem reg_lang_rrg:
  assumes "infinite (UNIV :: 's set)" 
  shows "regular_languages \<Sigma> = {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}"
proof -
  have reg: "regular_languages \<Sigma> = {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" using assms reg_lang_nfas by blast
  have "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>} = {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}" using assms expressive_power_auto_RG_main by blast
  thus ?thesis using reg by auto
qed

theorem reg_lang_lrg:
  assumes "infinite (UNIV :: 's set)" 
  shows "regular_languages \<Sigma> = {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = left_grammar_language G}"
proof -
  have reg: "regular_languages \<Sigma> = {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" using assms reg_lang_nfas by blast
  have "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>} = {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = left_grammar_language G}" using assms expressive_power_auto_LG_main by blast
  thus ?thesis using reg by auto
qed

text \<open>closure properties\<close>
proposition reg_lang_well_def: "L \<in> regular_languages \<Sigma> \<Longrightarrow> language_well_defined L \<Sigma>"
  using well_def_REs_language_is_well_def unfolding regular_languages_def by fast

proposition simga_star_is_regular:
  assumes "finite \<Sigma>"
  shows "sigma_star \<Sigma> \<in> regular_languages \<Sigma>"
proof -
  have "infinite (UNIV :: nat set)" by simp
  hence "\<exists> sigma_\<A> :: (nat, 'a) automaton . auto_well_defined sigma_\<A> \<and> alphabet sigma_\<A> = \<Sigma> \<and> language_auto sigma_\<A> = sigma_star \<Sigma>" using assms existence_of_sigma_star_same_type by blast
  thus ?thesis using reg_lang_nfas by auto
qed

lemma for_word_exists_RE:
  assumes "finite \<Sigma>"
  shows "word_well_defined word \<Sigma> \<Longrightarrow> \<exists> r . RE_well_defined r \<Sigma> \<and> language_reg_exp r = {word}"
proof(induction word rule: rev_induct)
  case Nil thus ?case using assms alphabet_RE.simps(2) unfolding RE_well_defined_def by fastforce
next
  case (snoc a word)
  hence "word_well_defined word \<Sigma> \<and> a \<in> \<Sigma>" using word_well_def_snoc by metis
  then obtain r where r: "RE_well_defined r \<Sigma> \<and> language_reg_exp r = {word} \<and> a \<in> \<Sigma>" using snoc by presburger
  hence RE: "RE_well_defined (Concatenation r (Singleton a)) \<Sigma>" unfolding RE_well_defined_def by auto
  have "language_reg_exp (Concatenation r (Singleton a)) = concatenation_language (language_reg_exp r) (language_reg_exp (Singleton a))" by simp
  hence "language_reg_exp (Concatenation r (Singleton a)) = concatenation_language {word} {[a]}" using r by simp
  hence "language_reg_exp (Concatenation r (Singleton a)) = {word @ [a]}" unfolding concatenation_language_def by simp
  thus ?case using RE by blast
qed

proposition finite_languages_are_regular:
  assumes "finite \<Sigma>"
  shows "language_well_defined L \<Sigma> \<and> finite L \<Longrightarrow> L \<in> regular_languages \<Sigma>"
proof(induction n \<equiv> "card L" arbitrary: L)
  case 0
  hence empty: "L = {}" by auto
  have "RE_well_defined Empty_set \<Sigma> \<and> language_reg_exp Empty_set = {}" using assms unfolding RE_well_defined_def by auto
  thus ?case using empty unfolding regular_languages_def by blast
next
  case (Suc n)
  hence "L \<noteq> {} \<and> language_well_defined L \<Sigma>" by force
  then obtain word where word: "word \<in> L \<and> word_well_defined word \<Sigma>" unfolding language_well_defined_def by blast
  hence "language_well_defined (L - {word}) \<Sigma> \<and> finite (L - {word}) \<and> card (L - {word}) = n" using Suc unfolding language_well_defined_def by force
  hence "(L - {word}) \<in> regular_languages \<Sigma>" using Suc by blast
  then obtain r1 where r1: "RE_well_defined r1 \<Sigma> \<and> (L - {word}) = language_reg_exp r1" unfolding regular_languages_def by blast
  obtain r2 where r2: "RE_well_defined r2 \<Sigma> \<and> language_reg_exp r2 = {word}" using word assms for_word_exists_RE by blast
  hence RE: "RE_well_defined (Alternation r1 r2) \<Sigma>" using r1 unfolding RE_well_defined_def by auto
  have "language_reg_exp (Alternation r1 r2) = language_reg_exp r1 \<union> language_reg_exp r2" by simp
  hence "language_reg_exp (Alternation r1 r2) = (L - {word}) \<union> {word}" using r1 r2 by argo
  hence "language_reg_exp (Alternation r1 r2) = L" using word by blast
  thus ?case using RE unfolding regular_languages_def by blast
qed

proposition comp_is_regular:
  assumes "L \<in> regular_languages \<Sigma>"
  shows "comp_language \<Sigma> L \<in> regular_languages \<Sigma>"
proof - 
  have inf_nat: "infinite (UNIV :: nat set)" by simp
  hence "L \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" using assms reg_lang_nfas by blast
  hence "\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>" by blast
  hence "\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> comp_language \<Sigma> L = language_auto NFA_\<A>" using inf_nat existence_of_comp_same_type by metis
  hence "comp_language \<Sigma> L \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" by blast
  thus ?thesis using reg_lang_nfas by blast
qed

proposition inter_is_regular:
  assumes "L1 \<in> regular_languages \<Sigma>1" "L2 \<in> regular_languages \<Sigma>2"
  shows "L1 \<inter> L2 \<in> regular_languages (\<Sigma>1 \<union> \<Sigma>2)"
proof - 
  have inf_nat: "infinite (UNIV :: nat set)" by simp
  hence "L1 \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>1 \<and> L = language_auto NFA_\<A>} \<and> L2 \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>2 \<and> L = language_auto NFA_\<A>}" using assms reg_lang_nfas by blast
  hence "(\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>1 \<and> L1 = language_auto NFA_\<A>) \<and> (\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>2 \<and> L2 = language_auto NFA_\<A>)" by blast
  hence "\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>1 \<union> \<Sigma>2 \<and> L1 \<inter> L2 = language_auto NFA_\<A>" using inf_nat existence_of_inter_same_type by metis
  hence "L1 \<inter> L2 \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = (\<Sigma>1 \<union> \<Sigma>2) \<and> L = language_auto NFA_\<A>}" by blast
  thus ?thesis using reg_lang_nfas by blast
qed

proposition union_is_regular:
  assumes "L1 \<in> regular_languages \<Sigma>1" "L2 \<in> regular_languages \<Sigma>2"
  shows "L1 \<union> L2 \<in> regular_languages (\<Sigma>1 \<union> \<Sigma>2)"
proof - 
  have inf_nat: "infinite (UNIV :: nat set)" by simp
  hence "L1 \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>1 \<and> L = language_auto NFA_\<A>} \<and> L2 \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>2 \<and> L = language_auto NFA_\<A>}" using assms reg_lang_nfas by blast
  hence "(\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>1 \<and> L1 = language_auto NFA_\<A>) \<and> (\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>2 \<and> L2 = language_auto NFA_\<A>)" by blast
  hence "\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>1 \<union> \<Sigma>2 \<and> L1 \<union> L2 = language_auto NFA_\<A>" using inf_nat existence_of_union_same_type by metis
  hence "L1 \<union> L2 \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = (\<Sigma>1 \<union> \<Sigma>2) \<and> L = language_auto NFA_\<A>}" by blast
  thus ?thesis using reg_lang_nfas by blast
qed

proposition rev_is_regular:
  assumes "L \<in> regular_languages \<Sigma>"
  shows "rev_language L \<in> regular_languages \<Sigma>"
proof - 
  have inf_nat: "infinite (UNIV :: nat set)" by simp
  hence "L \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" using assms reg_lang_nfas by blast
  hence "\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>" by blast
  hence "\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> rev_language L = language_auto NFA_\<A>" using inf_nat existence_of_rev_same_type by metis
  hence "rev_language L \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" by blast
  thus ?thesis using reg_lang_nfas by blast
qed

proposition concatenation_is_regular:
  assumes "L1 \<in> regular_languages \<Sigma>1" "L2 \<in> regular_languages \<Sigma>2"
  shows "concatenation_language L1 L2 \<in> regular_languages (\<Sigma>1 \<union> \<Sigma>2)"
proof - 
  have inf_nat: "infinite (UNIV :: nat set)" by simp
  hence "L1 \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>1 \<and> L = language_auto NFA_\<A>} \<and> L2 \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>2 \<and> L = language_auto NFA_\<A>}" using assms reg_lang_nfas by blast
  hence "(\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>1 \<and> L1 = language_auto NFA_\<A>) \<and> (\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>2 \<and> L2 = language_auto NFA_\<A>)" by blast
  hence "\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma>1 \<union> \<Sigma>2 \<and> concatenation_language L1 L2 = language_auto NFA_\<A>" using inf_nat existence_of_conc_same_type by metis
  hence "concatenation_language L1 L2 \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = (\<Sigma>1 \<union> \<Sigma>2) \<and> L = language_auto NFA_\<A>}" by blast
  thus ?thesis using reg_lang_nfas by blast
qed

proposition kleene_star_is_regular:
  assumes "L \<in> regular_languages \<Sigma>"
  shows "kleene_star_language L \<in> regular_languages \<Sigma>"
proof - 
  have inf_nat: "infinite (UNIV :: nat set)" by simp
  hence "L \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" using assms reg_lang_nfas by blast
  hence "\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>" by blast
  hence "\<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> kleene_star_language L = language_auto NFA_\<A>" using inf_nat kleene_star_eps_free_main by metis
  hence "kleene_star_language L \<in> {L . \<exists> (NFA_\<A> :: (nat, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" by blast
  thus ?thesis using reg_lang_nfas by blast
qed



text \<open>Pumping-Lemma\<close>
fun pump :: "'a word \<Rightarrow> nat \<Rightarrow> 'a word" where
  "pump word 0 = []" |
  "pump word (Suc n) = word @ (pump word n)"

proposition pump_word_rev_induct: "pump word (Suc n) = pump word n @ word"
  by(induction n) auto

proposition pump_decomp: "i \<le> n \<Longrightarrow> pump word n = pump word i @ pump word (n - i)"
  apply(induction i) apply simp using Suc_diff_Suc Suc_leD Suc_le_lessD append.assoc pump.simps(2) pump_word_rev_induct by metis

corollary runs_multiple_states_geq:
  assumes "auto_well_defined \<A>"
  shows "length run \<ge> Suc (card (states \<A>)) \<and> run_well_defined run \<A> word \<Longrightarrow> \<exists> j < Suc (card (states \<A>)) . \<exists> i < Suc (card (states \<A>)) . i \<noteq> j \<and> run ! i = run ! j"
proof(induction n \<equiv> "length run - Suc (card (states \<A>))" arbitrary: run word)
  case 0 thus ?case using assms runs_multiple_states by fastforce
next
  case (Suc n)
  hence len: "length run = Suc n + Suc (card (states \<A>))" by linarith
  hence "run \<noteq> [] \<and> word \<noteq> []" using Suc unfolding pseudo_run_well_defined_def run_well_defined_def by force
  then obtain run' word' where step: "run = run' @ [last run] \<and> word = word' @ [last word]" using append_butlast_last_id by metis
  hence "length run' = n + Suc (card (states \<A>))" using len add_Suc_right add_Suc_shift length_append_singleton nat.inject by metis
  hence n: "n = length run' - Suc (card (states \<A>)) \<and> length run' \<ge> Suc (card (states \<A>))" by auto
  have "pseudo_run_well_defined run' \<A> (initial_state \<A>) word' \<and> (last run', last word, last run) \<in> transitions \<A>" using Suc step assms prun_well_defined_extension_snoc unfolding run_well_defined_def by metis
  hence "run_well_defined run' \<A> word'" unfolding run_well_defined_def by blast
  hence existence: "\<exists> j < Suc (card (states \<A>)) . \<exists> i < Suc (card (states \<A>)) . i \<noteq> j \<and> run' ! i = run' ! j" using n Suc by blast
  have "\<forall> i < length run' . run' ! i = run ! i" using step list_properties_length by metis
  thus ?case using existence n less_le_trans by metis
qed

lemma merging_pseudo_runs:
  assumes "auto_well_defined \<A>"
  shows "pseudo_run_well_defined prun1 \<A> s1 word1 \<and> pseudo_run_well_defined prun2 \<A> s2 word2 \<and> last prun1 = prun2 ! 0 \<Longrightarrow> pseudo_run_well_defined (prun1 @ (tl prun2)) \<A> s1 (word1 @ word2) \<and> last prun2 = last (prun1 @ (tl prun2))"
proof(induction word1 arbitrary: s1 prun1 s2 word2 prun2)
  case Nil
  hence "prun1 = [s1] \<and> last prun1 = prun2 ! 0 \<and> prun2 \<noteq> [] \<and> prun2 ! 0 = s2" using list_with_one_element unfolding pseudo_run_well_defined_def by fastforce
  hence "(prun1 @ (tl prun2)) = prun2 \<and> s1 = s2" using append.left_neutral append_Cons last.simps list_properties_not_empty by metis
  thus ?case using Nil by auto
next
  case (Cons a word1)
  hence len: "length prun1 = length (a # word1) + 1 \<and> prun1 ! 0 = s1" unfolding pseudo_run_well_defined_def by fast
  hence "prun1 \<noteq> [] \<and> prun1 ! 0 = s1" by force
  then obtain prun1' where prun1': "prun1 = s1 # prun1'" using hd_conv_nth list.collapse by metis
  hence "length prun1 = 1 + length prun1'" using length_Suc_conv by auto
  hence "length prun1' = length (a # word1)" using len by simp
  hence not_empty: "prun1' \<noteq> []" by auto
  hence last: "last prun1' = last prun1" using prun1' list_properties_not_empty by metis
  have "pseudo_run_well_defined (s1 # prun1') \<A> s1 (a # word1)" using Cons prun1' by argo
  hence "pseudo_run_well_defined prun1' \<A> (prun1' ! 0) word1 \<and> (s1, a, (prun1' ! 0)) \<in> transitions \<A>" using assms prun_well_defined_extension_cons by fast
  hence "pseudo_run_well_defined (prun1' @ (tl prun2)) \<A> (prun1' ! 0) (word1 @ word2) \<and> last prun2 = last (prun1' @ (tl prun2)) \<and> (s1, a, (prun1' ! 0)) \<in> transitions \<A>" using Cons last by metis
  hence well_def: "pseudo_run_well_defined (prun1 @ (tl prun2)) \<A> s1 ((a # word1) @ word2) \<and> last prun2 = last (prun1' @ (tl prun2))" using assms prun1' prun_well_defined_induction_cons by fastforce
  hence "prun1' @ (tl prun2) \<noteq> []" using not_empty by blast
  hence "last (prun1 @ (tl prun2)) = last (prun1' @ (tl prun2))" using list_properties_not_empty prun1' by auto
  thus ?case using well_def by argo
qed

lemma decompose_pseudo_runs:
  assumes "auto_well_defined \<A>"
  shows "pseudo_run_well_defined prun \<A> s (word1 @ word2) \<Longrightarrow> \<exists> prun1 prun2 . pseudo_run_well_defined prun1 \<A> s word1 \<and> pseudo_run_well_defined prun2 \<A> (last prun1) word2 \<and> prun = prun1 @ (tl prun2) \<and> last prun1 = prun ! (length word1) \<and> last prun2 = last prun \<and> (\<forall> n < length prun1 - 1 . prun1 ! n = prun ! n)"
proof(induction word1 arbitrary: prun s word2)
  case Nil
  hence props: "pseudo_run_well_defined [s] \<A> s [] \<and> pseudo_run_well_defined prun \<A> s word2 \<and> last [s] = prun ! 0 \<and> prun \<noteq> []" unfolding pseudo_run_well_defined_def by force
  thus ?case using list_properties_not_empty by fastforce
next
  case (Cons a word1)
  hence "prun \<noteq> [] \<and> prun ! 0 = s" unfolding pseudo_run_well_defined_def by force
  then obtain prun' where prun': "prun = s # prun'" using hd_conv_nth list.collapse by metis
  hence "pseudo_run_well_defined (s # prun') \<A> s ((a # word1) @ word2)" using Cons by simp
  hence "pseudo_run_well_defined prun' \<A> (prun' ! 0) (word1 @ word2) \<and> (s, a, prun' ! 0) \<in> transitions \<A>" using assms append_Cons prun_well_defined_cons by metis
  hence "prun' \<noteq> [] \<and> pseudo_run_well_defined prun' \<A> (prun' ! 0) (word1 @ word2) \<and> (s, a, prun' ! 0) \<in> transitions \<A>" unfolding pseudo_run_well_defined_def by fastforce
  then obtain prun1 prun2 where "prun' \<noteq> [] \<and> pseudo_run_well_defined prun1 \<A> (prun' ! 0) word1 \<and> (s, a, prun' ! 0) \<in> transitions \<A> \<and> pseudo_run_well_defined prun2 \<A> (last prun1) word2 \<and> prun' = prun1 @ (tl prun2) \<and> last prun2 = last prun' \<and> last prun1 = prun' ! (length word1) \<and> (\<forall> n < length prun1 - 1 . prun1 ! n = prun' ! n)" using assms Cons by blast
  hence "prun' \<noteq> [] \<and> prun1 \<noteq> [] \<and> pseudo_run_well_defined prun1 \<A> (prun' ! 0) word1 \<and> (s, a, prun' ! 0) \<in> transitions \<A> \<and> pseudo_run_well_defined prun2 \<A> (last prun1) word2 \<and> prun' = prun1 @ (tl prun2) \<and> last prun2 = last prun' \<and> last prun1 = prun' ! (length word1) \<and> (\<forall> n < length prun1 - 1 . prun1 ! n = prun' ! n)" unfolding pseudo_run_well_defined_def by force
  hence props: "prun' \<noteq> [] \<and> prun1 \<noteq> [] \<and> pseudo_run_well_defined (s # prun1) \<A> s (a # word1) \<and> pseudo_run_well_defined prun2 \<A> (last prun1) word2 \<and> prun' = prun1 @ (tl prun2) \<and> last prun2 = last prun' \<and> last prun1 = prun' ! (length word1) \<and> (\<forall> n < length prun1 - 1 . prun1 ! n = prun' ! n)" using assms prun_well_defined_induction_cons by metis 
  hence "last prun' = last prun \<and> last (s # prun1) = last prun1 \<and> last prun1 = (s # prun') ! (length (a # word1)) \<and> (s # prun') = (s # prun1) @ (tl prun2) \<and> (\<forall> n < length (s # prun1) - 1 . (s # prun1) ! n = (s # prun') ! n)" using prun' list_properties_not_empty by (simp add: nth_Cons')
  thus ?case using props prun' by metis
qed

theorem pumping_lemma:
  assumes "L \<in> regular_languages \<Sigma>"
  shows "\<exists> n > 0 . \<forall> word \<in> L . length word \<ge> n \<longrightarrow> (\<exists> u v w . word = u @ v @ w \<and> length (u @ v) \<le> n \<and> length v \<ge> 1 \<and> (\<forall> i . (u @ (pump v i) @ w) \<in> L))"
proof - 
  have "infinite (UNIV :: nat set)" by simp
  hence "L \<in> regular_languages \<Sigma> \<and> regular_languages \<Sigma> = {L . \<exists> (DFA_\<A> :: (nat, 'a) automaton) . auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = \<Sigma> \<and> L = language_auto DFA_\<A>}" using assms reg_lang_dfas by blast
  then obtain \<A> :: "(nat, 'a) automaton" where "auto_well_defined \<A> \<and> DFA_property \<A> \<and> alphabet \<A> = \<Sigma> \<and> L = language_auto \<A>" by blast
  hence auto: "auto_well_defined \<A> \<and> DFA_property \<A> \<and> alphabet \<A> = \<Sigma> \<and> L = language_auto \<A> \<and> card (states \<A>) > 0" using at_least_one_state by fast
  let ?n = "card (states \<A>)"
  {
    fix word assume assm: "word \<in> L \<and> length word \<ge> ?n"
    then obtain run where "run_accepting run \<A> word \<and> length word \<ge> ?n" using auto unfolding language_auto_def by fast
    hence well_def: "run_well_defined run \<A> word \<and> last run \<in> accepting_states \<A> \<and> length word \<ge> ?n" unfolding run_accepting_def by blast
    hence "length run \<ge> ?n + 1" unfolding pseudo_run_well_defined_def run_well_defined_def by auto
    hence len_run: "length run \<ge> Suc (card (states \<A>))" by simp
    then obtain i j where ij: "i < Suc (card (states \<A>)) \<and> j < Suc (card (states \<A>)) \<and> i \<noteq> j \<and> run ! i = run ! j" using auto well_def runs_multiple_states_geq by blast
    then consider (case1) "i < j" | (case2) "j < i" by linarith
    hence "\<exists> u v w . word = u @ v @ w \<and> length (u @ v) \<le> ?n \<and> length v \<ge> 1 \<and> (\<forall> i . (u @ (pump v i) @ w) \<in> L)"
    proof cases
      case case1
      let ?u = "take i word"
      let ?v = "sublist i j word"
      let ?w = "sublist j (length word) word"
      have "length run = length word + 1" using well_def unfolding run_well_defined_def pseudo_run_well_defined_def by blast
      hence "length word \<ge> j" using len_run ij by auto
      hence ij_len: "i = length ?u \<and> j = length (?u @ ?v)" using case1 unfolding sublist_def by fastforce
      have word: "word = ?u @ ?v @ ?w" unfolding sublist_def using case1 append_take_drop_id diff_add drop_drop length_drop less_or_eq_imp_le take_all by metis
      hence "run_well_defined run \<A> (?u @ ?v @ ?w) \<and> word_well_defined (?u @ ?v @ ?w) \<Sigma>" using well_def assms assm well_def_word_reg_languages by auto
      hence word_well: "pseudo_run_well_defined run \<A> (initial_state \<A>) (?u @ ?v @ ?w) \<and> word_well_defined (?u @ ?v) \<Sigma>" using word_well_def_append unfolding run_well_defined_def by metis
      hence "pseudo_run_well_defined run \<A> (initial_state \<A>) ((?u @ ?v) @ ?w)" by simp
      hence "\<exists> prun1 prun2 . pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (?u @ ?v) \<and> pseudo_run_well_defined prun2 \<A> (last prun1) ?w \<and> run = prun1 @ (tl prun2) \<and> last prun1 = run ! (length (?u @ ?v)) \<and> last prun2 = last run \<and> (\<forall> n < length prun1 - 1 . prun1 ! n = run ! n)" using auto decompose_pseudo_runs by fast
      then obtain prun1 where "pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (?u @ ?v) \<and> last prun1 = run ! (length (?u @ ?v)) \<and> (\<forall> n < length prun1 - 1 . prun1 ! n = run ! n)" by blast
      hence "pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (?u @ ?v) \<and> last prun1 = run ! j \<and> length prun1 = length (?u @ ?v) + 1 \<and> (\<forall> n < length prun1 - 1 . prun1 ! n = run ! n)" using ij_len unfolding pseudo_run_well_defined_def by fastforce
      hence prun1: "pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (?u @ ?v) \<and> last prun1 = run ! j \<and> prun1 ! (length ?u) = run ! i" using case1 ij_len by force
      have len_uv: "length (?u @ ?v) \<le> ?n" using ij unfolding sublist_def by force
      have len_v: "length ?v \<ge> 1" using assm case1 ij unfolding sublist_def by auto
      {
        fix k :: nat
        have "(?u @ (pump ?v k) @ ?w) \<in> L"
        proof(induction k)
          case 0
          hence "auto_well_defined \<A> \<and> run_well_defined run \<A> word \<and> i < length run \<and> j < length run \<and> i \<noteq> j \<and> run ! i = run ! j \<and> i < j \<and> last run \<in> accepting_states \<A>" using auto well_def ij case1 len_run by linarith
          hence "run_well_defined ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) \<A> (?u @ ?w) \<and> last ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) \<in> accepting_states \<A>" using run_sublist by metis 
          thus ?case using auto unfolding run_accepting_def language_auto_def by auto
        next
          case (Suc k)
          consider (case3) "k = 0" | (case4) "k > 0" by linarith 
          thus ?case
          proof cases
            case case3 thus ?thesis using word assm by simp
          next
            case case4
            then obtain l where l: "k = Suc l" using Nat.lessE by metis
            have "(?u @ (pump ?v k) @ ?w) \<in> L" using Suc by blast
            hence "(?u @ (pump ?v (Suc l)) @ ?w) \<in> L" using l by blast
            hence "(?u @ ?v @ (pump ?v l) @ ?w) \<in> L" by simp
            then obtain run' where "pseudo_run_well_defined run' \<A> (initial_state \<A>) (?u @ ?v @ (pump ?v l) @ ?w) \<and> last run' \<in> accepting_states \<A>" using auto case4 unfolding language_auto_def run_accepting_def run_well_defined_def by blast 
            hence "pseudo_run_well_defined run' \<A> (initial_state \<A>) ((?u @ ?v) @ (pump ?v l) @ ?w) \<and> last run' \<in> accepting_states \<A>" by simp
            hence "\<exists> prun1' prun2 . pseudo_run_well_defined prun1' \<A> (initial_state \<A>) (?u @ ?v) \<and> pseudo_run_well_defined prun2 \<A> (last prun1') ((pump ?v l) @ ?w) \<and> last prun1' = run' ! (length (?u @ ?v)) \<and> run' = prun1' @ (tl prun2) \<and> last prun2 = last run' \<and> last run' \<in> accepting_states \<A>" using auto decompose_pseudo_runs by fast
            then obtain prun1' prun2 where prun1': "pseudo_run_well_defined prun1' \<A> (initial_state \<A>) (?u @ ?v) \<and> pseudo_run_well_defined prun2 \<A> (last prun1') ((pump ?v l) @ ?w) \<and> last prun1' = run' ! (length (?u @ ?v)) \<and> run' = prun1' @ (tl prun2) \<and> last prun2 = last run' \<and> last run' \<in> accepting_states \<A>" by blast
            hence "word_well_defined (?u @ ?v) \<Sigma> \<and> auto_well_defined \<A> \<and> DFA_property \<A> \<and> alphabet \<A> = \<Sigma> \<and> initial_state \<A> \<in> states \<A> \<and> pseudo_run_well_defined prun1' \<A> (initial_state \<A>) (?u @ ?v)" using word_well auto unfolding auto_well_defined_def by linarith
            hence "prun1 = prun1'" using prun1 exists_only_one_prun_for_DFA by blast
            hence "pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (?u @ ?v) \<and> pseudo_run_well_defined prun2 \<A> (run ! j) ((pump ?v l) @ ?w) \<and> last prun1 = run ! j \<and> prun1 ! (length ?u) = run ! i \<and> last prun2 = last run' \<and> last run' \<in> accepting_states \<A>" using prun1 prun1' by metis
            hence "pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (?u @ ?v) \<and> pseudo_run_well_defined prun2 \<A> (run ! j) ((pump ?v l) @ ?w) \<and> last prun1 = run ! j \<and> prun1 ! (length ?u) = run ! i \<and> last prun2 \<in> accepting_states \<A>" by presburger
            hence "(\<exists> prun3 prun4 . pseudo_run_well_defined prun3 \<A> (initial_state \<A>) ?u \<and> pseudo_run_well_defined prun4 \<A> (last prun3) ?v \<and> last prun3 = prun1 ! (length ?u) \<and> last prun4 = last prun1) \<and> pseudo_run_well_defined prun2 \<A> (run ! j) ((pump ?v l) @ ?w) \<and> last prun1 = run ! j \<and> prun1 ! (length ?u) = run ! i \<and> last prun2 \<in> accepting_states \<A>" using auto decompose_pseudo_runs by fast 
            then obtain prun3 prun4 where "pseudo_run_well_defined prun3 \<A> (initial_state \<A>) ?u \<and> pseudo_run_well_defined prun4 \<A> (last prun3) ?v \<and> last prun3 = prun1 ! (length ?u) \<and> last prun4 = last prun1 \<and> pseudo_run_well_defined prun2 \<A> (run ! j) ((pump ?v l) @ ?w) \<and> last prun1 = run ! j \<and> prun1 ! (length ?u) = run ! i \<and> last prun2 \<in> accepting_states \<A>" by blast
            hence "pseudo_run_well_defined prun3 \<A> (initial_state \<A>) ?u \<and> last prun3 = run ! i \<and> pseudo_run_well_defined prun4 \<A> (run ! i) ?v \<and> last prun4 = run ! j \<and> pseudo_run_well_defined prun2 \<A> (run ! j) ((pump ?v l) @ ?w) \<and> last prun2 \<in> accepting_states \<A>" by argo
            hence "pseudo_run_well_defined prun3 \<A> (initial_state \<A>) ?u \<and> last prun3 = run ! i \<and> pseudo_run_well_defined prun4 \<A> (run ! i) ?v \<and> last prun4 = run ! i \<and> pseudo_run_well_defined prun2 \<A> (run ! i) ((pump ?v l) @ ?w) \<and> last prun2 \<in> accepting_states \<A>" using ij by simp
            hence "pseudo_run_well_defined prun3 \<A> (initial_state \<A>) ?u \<and> last prun3 = run ! i \<and> prun4 ! 0 = run ! i \<and> pseudo_run_well_defined prun4 \<A> (run ! i) ?v \<and> last prun4 = run ! i \<and> prun2 ! 0 = run ! i \<and>  pseudo_run_well_defined prun2 \<A> (run ! i) ((pump ?v l) @ ?w) \<and> last prun2 \<in> accepting_states \<A>" unfolding pseudo_run_well_defined_def by fast
            hence "pseudo_run_well_defined (prun3 @ (tl prun4)) \<A> (initial_state \<A>) (?u @ ?v) \<and> last prun4 = last (prun3 @ (tl prun4)) \<and> last prun4 = run ! i \<and> pseudo_run_well_defined (prun4 @ (tl prun2)) \<A> (run ! i) (?v @ (pump ?v l) @ ?w) \<and> last prun2 = last (prun4 @ (tl prun2)) \<and> last prun2 \<in> accepting_states \<A>" using auto merging_pseudo_runs by metis
            hence "pseudo_run_well_defined (prun3 @ (tl prun4)) \<A> (initial_state \<A>) (?u @ ?v) \<and> last (prun3 @ (tl prun4)) = run ! i \<and> pseudo_run_well_defined (prun4 @ (tl prun2)) \<A> (run ! i) (?v @ (pump ?v l) @ ?w) \<and> last (prun4 @ (tl prun2)) \<in> accepting_states \<A>" by argo
            hence "pseudo_run_well_defined (prun3 @ (tl prun4)) \<A> (initial_state \<A>) (?u @ ?v) \<and> last (prun3 @ (tl prun4)) = run ! i \<and> (prun4 @ (tl prun2)) ! 0 = run ! i \<and>  pseudo_run_well_defined (prun4 @ (tl prun2)) \<A> (run ! i) (?v @ (pump ?v l) @ ?w) \<and> last (prun4 @ (tl prun2)) \<in> accepting_states \<A>" unfolding pseudo_run_well_defined_def by fast
            hence "pseudo_run_well_defined (prun3 @ (tl prun4)) \<A> (initial_state \<A>) (?u @ ?v) \<and> last (prun3 @ (tl prun4)) = run ! i \<and> (prun4 @ (tl prun2)) ! 0 = run ! i \<and>  pseudo_run_well_defined (prun4 @ (tl prun2)) \<A> (run ! i) ((pump ?v (Suc l)) @ ?w) \<and> last (prun4 @ (tl prun2)) \<in> accepting_states \<A>" by simp
            hence "pseudo_run_well_defined ((prun3 @ (tl prun4)) @ (tl (prun4 @ (tl prun2)))) \<A> (initial_state \<A>) ((?u @ ?v) @ ((pump ?v (Suc l)) @ ?w)) \<and> last (prun4 @ (tl prun2)) = last ((prun3 @ (tl prun4)) @ (tl (prun4 @ (tl prun2)))) \<and> last (prun4 @ (tl prun2)) \<in> accepting_states \<A>" using auto merging_pseudo_runs by metis
            hence "pseudo_run_well_defined ((prun3 @ (tl prun4)) @ (tl (prun4 @ (tl prun2)))) \<A> (initial_state \<A>) (?u @ ?v @ ((pump ?v k) @ ?w)) \<and> last ((prun3 @ (tl prun4)) @ (tl (prun4 @ (tl prun2)))) \<in> accepting_states \<A>" using l by force
            hence "(?u @ ?v @ ((pump ?v k) @ ?w)) \<in> language_auto \<A>" unfolding pseudo_run_well_defined_def run_well_defined_def run_accepting_def language_auto_def by blast         
            thus ?thesis using auto by simp
          qed
        qed
      }
      hence "(\<forall> k . (?u @ (pump ?v k) @ ?w) \<in> L)" by blast
      thus ?thesis using word len_uv len_v by blast
    next
      case case2
      let ?u = "take j word"
      let ?v = "sublist j i word"
      let ?w = "sublist i (length word) word"
      have "length run = length word + 1" using well_def unfolding run_well_defined_def pseudo_run_well_defined_def by blast
      hence "length word \<ge> i" using len_run ij by auto
      hence ij_len: "j = length ?u \<and> i = length (?u @ ?v)" using case2 unfolding sublist_def by fastforce
      have word: "word = ?u @ ?v @ ?w" unfolding sublist_def using case2 append_take_drop_id diff_add drop_drop length_drop less_or_eq_imp_le take_all by metis
      hence "run_well_defined run \<A> (?u @ ?v @ ?w) \<and> word_well_defined (?u @ ?v @ ?w) \<Sigma>" using well_def assms assm well_def_word_reg_languages by auto
      hence word_well: "pseudo_run_well_defined run \<A> (initial_state \<A>) (?u @ ?v @ ?w) \<and> word_well_defined (?u @ ?v) \<Sigma>" using word_well_def_append unfolding run_well_defined_def by metis
      hence "pseudo_run_well_defined run \<A> (initial_state \<A>) ((?u @ ?v) @ ?w)" by simp
      hence "\<exists> prun1 prun2 . pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (?u @ ?v) \<and> pseudo_run_well_defined prun2 \<A> (last prun1) ?w \<and> run = prun1 @ (tl prun2) \<and> last prun1 = run ! (length (?u @ ?v)) \<and> last prun2 = last run \<and> (\<forall> n < length prun1 - 1 . prun1 ! n = run ! n)" using auto decompose_pseudo_runs by fast
      then obtain prun1 where "pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (?u @ ?v) \<and> last prun1 = run ! (length (?u @ ?v)) \<and> (\<forall> n < length prun1 - 1 . prun1 ! n = run ! n)" by blast
      hence "pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (?u @ ?v) \<and> last prun1 = run ! i \<and> length prun1 = length (?u @ ?v) + 1 \<and> (\<forall> n < length prun1 - 1 . prun1 ! n = run ! n)" using ij_len unfolding pseudo_run_well_defined_def by fastforce
      hence prun1: "pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (?u @ ?v) \<and> last prun1 = run ! i \<and> prun1 ! (length ?u) = run ! j" using case2 ij_len by force
      have len_uv: "length (?u @ ?v) \<le> ?n" using ij unfolding sublist_def by force
      have len_v: "length ?v \<ge> 1" using assm case2 ij unfolding sublist_def by auto
      {
        fix k :: nat
        have "(?u @ (pump ?v k) @ ?w) \<in> L"
        proof(induction k)
          case 0
          hence "auto_well_defined \<A> \<and> run_well_defined run \<A> word \<and> i < length run \<and> j < length run \<and> i \<noteq> j \<and> run ! i = run ! j \<and> j < i \<and> last run \<in> accepting_states \<A>" using auto well_def ij case2 len_run by linarith
          hence "run_well_defined ((take (Suc j) run) @ (sublist (Suc i) (length run) run)) \<A> (?u @ ?w) \<and> last ((take (Suc j) run) @ (sublist (Suc i) (length run) run)) \<in> accepting_states \<A>" using run_sublist by metis 
          thus ?case using auto unfolding run_accepting_def language_auto_def by auto
        next
          case (Suc k)
          consider (case5) "k = 0" | (case6) "k > 0" by linarith 
          thus ?case
          proof cases
            case case5 thus ?thesis using word assm by simp
          next
            case case6
            then obtain l where l: "k = Suc l" using Nat.lessE by metis
            have "(?u @ (pump ?v k) @ ?w) \<in> L" using Suc by blast
            hence "(?u @ (pump ?v (Suc l)) @ ?w) \<in> L" using l by blast
            hence "(?u @ ?v @ (pump ?v l) @ ?w) \<in> L" by simp
            then obtain run' where "pseudo_run_well_defined run' \<A> (initial_state \<A>) (?u @ ?v @ (pump ?v l) @ ?w) \<and> last run' \<in> accepting_states \<A>" using auto case6 unfolding language_auto_def run_accepting_def run_well_defined_def by blast 
            hence "pseudo_run_well_defined run' \<A> (initial_state \<A>) ((?u @ ?v) @ (pump ?v l) @ ?w) \<and> last run' \<in> accepting_states \<A>" by simp
            hence "\<exists> prun1' prun2 . pseudo_run_well_defined prun1' \<A> (initial_state \<A>) (?u @ ?v) \<and> pseudo_run_well_defined prun2 \<A> (last prun1') ((pump ?v l) @ ?w) \<and> last prun1' = run' ! (length (?u @ ?v)) \<and> run' = prun1' @ (tl prun2) \<and> last prun2 = last run' \<and> last run' \<in> accepting_states \<A>" using auto decompose_pseudo_runs by fast
            then obtain prun1' prun2 where prun1': "pseudo_run_well_defined prun1' \<A> (initial_state \<A>) (?u @ ?v) \<and> pseudo_run_well_defined prun2 \<A> (last prun1') ((pump ?v l) @ ?w) \<and> last prun1' = run' ! (length (?u @ ?v)) \<and> run' = prun1' @ (tl prun2) \<and> last prun2 = last run' \<and> last run' \<in> accepting_states \<A>" by blast
            hence "word_well_defined (?u @ ?v) \<Sigma> \<and> auto_well_defined \<A> \<and> DFA_property \<A> \<and> alphabet \<A> = \<Sigma> \<and> initial_state \<A> \<in> states \<A> \<and> pseudo_run_well_defined prun1' \<A> (initial_state \<A>) (?u @ ?v)" using word_well auto unfolding auto_well_defined_def by linarith
            hence "prun1 = prun1'" using prun1 exists_only_one_prun_for_DFA by blast
            hence "pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (?u @ ?v) \<and> pseudo_run_well_defined prun2 \<A> (run ! i) ((pump ?v l) @ ?w) \<and> last prun1 = run ! i \<and> prun1 ! (length ?u) = run ! j \<and> last prun2 = last run' \<and> last run' \<in> accepting_states \<A>" using prun1 prun1' by metis
            hence "pseudo_run_well_defined prun1 \<A> (initial_state \<A>) (?u @ ?v) \<and> pseudo_run_well_defined prun2 \<A> (run ! i) ((pump ?v l) @ ?w) \<and> last prun1 = run ! i \<and> prun1 ! (length ?u) = run ! j \<and> last prun2 \<in> accepting_states \<A>" by presburger
            hence "(\<exists> prun3 prun4 . pseudo_run_well_defined prun3 \<A> (initial_state \<A>) ?u \<and> pseudo_run_well_defined prun4 \<A> (last prun3) ?v \<and> last prun3 = prun1 ! (length ?u) \<and> last prun4 = last prun1) \<and> pseudo_run_well_defined prun2 \<A> (run ! i) ((pump ?v l) @ ?w) \<and> last prun1 = run ! i \<and> prun1 ! (length ?u) = run ! j \<and> last prun2 \<in> accepting_states \<A>" using auto decompose_pseudo_runs by fast 
            then obtain prun3 prun4 where "pseudo_run_well_defined prun3 \<A> (initial_state \<A>) ?u \<and> pseudo_run_well_defined prun4 \<A> (last prun3) ?v \<and> last prun3 = prun1 ! (length ?u) \<and> last prun4 = last prun1 \<and> pseudo_run_well_defined prun2 \<A> (run ! i) ((pump ?v l) @ ?w) \<and> last prun1 = run ! i \<and> prun1 ! (length ?u) = run ! j \<and> last prun2 \<in> accepting_states \<A>" by blast
            hence "pseudo_run_well_defined prun3 \<A> (initial_state \<A>) ?u \<and> last prun3 = run ! j \<and> pseudo_run_well_defined prun4 \<A> (run ! j) ?v \<and> last prun4 = run ! i \<and> pseudo_run_well_defined prun2 \<A> (run ! i) ((pump ?v l) @ ?w) \<and> last prun2 \<in> accepting_states \<A>" by argo
            hence "pseudo_run_well_defined prun3 \<A> (initial_state \<A>) ?u \<and> last prun3 = run ! i \<and> pseudo_run_well_defined prun4 \<A> (run ! i) ?v \<and> last prun4 = run ! i \<and> pseudo_run_well_defined prun2 \<A> (run ! i) ((pump ?v l) @ ?w) \<and> last prun2 \<in> accepting_states \<A>" using ij by simp
            hence "pseudo_run_well_defined prun3 \<A> (initial_state \<A>) ?u \<and> last prun3 = run ! i \<and> prun4 ! 0 = run ! i \<and> pseudo_run_well_defined prun4 \<A> (run ! i) ?v \<and> last prun4 = run ! i \<and> prun2 ! 0 = run ! i \<and>  pseudo_run_well_defined prun2 \<A> (run ! i) ((pump ?v l) @ ?w) \<and> last prun2 \<in> accepting_states \<A>" unfolding pseudo_run_well_defined_def by fast
            hence "pseudo_run_well_defined (prun3 @ (tl prun4)) \<A> (initial_state \<A>) (?u @ ?v) \<and> last prun4 = last (prun3 @ (tl prun4)) \<and> last prun4 = run ! i \<and> pseudo_run_well_defined (prun4 @ (tl prun2)) \<A> (run ! i) (?v @ (pump ?v l) @ ?w) \<and> last prun2 = last (prun4 @ (tl prun2)) \<and> last prun2 \<in> accepting_states \<A>" using auto merging_pseudo_runs by metis
            hence "pseudo_run_well_defined (prun3 @ (tl prun4)) \<A> (initial_state \<A>) (?u @ ?v) \<and> last (prun3 @ (tl prun4)) = run ! i \<and> pseudo_run_well_defined (prun4 @ (tl prun2)) \<A> (run ! i) (?v @ (pump ?v l) @ ?w) \<and> last (prun4 @ (tl prun2)) \<in> accepting_states \<A>" by argo
            hence "pseudo_run_well_defined (prun3 @ (tl prun4)) \<A> (initial_state \<A>) (?u @ ?v) \<and> last (prun3 @ (tl prun4)) = run ! i \<and> (prun4 @ (tl prun2)) ! 0 = run ! i \<and>  pseudo_run_well_defined (prun4 @ (tl prun2)) \<A> (run ! i) (?v @ (pump ?v l) @ ?w) \<and> last (prun4 @ (tl prun2)) \<in> accepting_states \<A>" unfolding pseudo_run_well_defined_def by fast
            hence "pseudo_run_well_defined (prun3 @ (tl prun4)) \<A> (initial_state \<A>) (?u @ ?v) \<and> last (prun3 @ (tl prun4)) = run ! i \<and> (prun4 @ (tl prun2)) ! 0 = run ! i \<and>  pseudo_run_well_defined (prun4 @ (tl prun2)) \<A> (run ! i) ((pump ?v (Suc l)) @ ?w) \<and> last (prun4 @ (tl prun2)) \<in> accepting_states \<A>" by simp
            hence "pseudo_run_well_defined ((prun3 @ (tl prun4)) @ (tl (prun4 @ (tl prun2)))) \<A> (initial_state \<A>) ((?u @ ?v) @ ((pump ?v (Suc l)) @ ?w)) \<and> last (prun4 @ (tl prun2)) = last ((prun3 @ (tl prun4)) @ (tl (prun4 @ (tl prun2)))) \<and> last (prun4 @ (tl prun2)) \<in> accepting_states \<A>" using auto merging_pseudo_runs by metis
            hence "pseudo_run_well_defined ((prun3 @ (tl prun4)) @ (tl (prun4 @ (tl prun2)))) \<A> (initial_state \<A>) (?u @ ?v @ ((pump ?v k) @ ?w)) \<and> last ((prun3 @ (tl prun4)) @ (tl (prun4 @ (tl prun2)))) \<in> accepting_states \<A>" using l by force
            hence "(?u @ ?v @ ((pump ?v k) @ ?w)) \<in> language_auto \<A>" unfolding pseudo_run_well_defined_def run_well_defined_def run_accepting_def language_auto_def by blast         
            thus ?thesis using auto by simp
          qed
        qed
      }
      hence "(\<forall> k . (?u @ (pump ?v k) @ ?w) \<in> L)" by blast
      thus ?thesis using word len_uv len_v by blast
    qed
  }
  hence "\<forall> word \<in> L . length word \<ge> ?n \<longrightarrow> (\<exists> u v w . word = u @ v @ w \<and> length (u @ v) \<le> ?n \<and> length v \<ge> 1 \<and> (\<forall> i . (u @ (pump v i) @ w) \<in> L))" by simp
  thus ?thesis using auto by blast
qed
    
end