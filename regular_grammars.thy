theory regular_grammars

imports Main automaton_kleene_star automaton_reversal

begin

text \<open>Author: Benno Thalmann, last update: 10.11.2025, Addition to masterarbeit_benno_thalmann\<close>

type_synonym 's non_terminal = "'s"
type_synonym 's non_terminals = "'s non_terminal set"
type_synonym ('s, 'a) rule = "('s non_terminal \<times> 'a symbol \<times> 's non_terminal)"
type_synonym ('s, 'a) rules = "('s, 'a) rule set"

datatype ('s, 'a) regular_grammar = Grammar
  (non_terminals : "('s + unit) non_terminals")
  (alphabet_grammar : "('a + unit) alphabet")
  (rules : "('s + unit, 'a + unit) rules")
  (starting_non_terminal : "('s + unit) non_terminal")

definition grammar_well_defined :: "('s, 'a) regular_grammar \<Rightarrow> bool" where
  "grammar_well_defined G = 
    (finite (non_terminals G) \<and>
    finite (alphabet_grammar G) \<and>
    starting_non_terminal G \<in> non_terminals G \<and> starting_non_terminal G \<noteq> Inr() \<and>
    (\<forall> (A, a, B) \<in> rules G . A \<in> non_terminals G \<and> A \<noteq> Inr() \<and> a \<in> alphabet_grammar G \<and> B \<in> non_terminals G))"

lemma well_def_rule_components:
  assumes "grammar_well_defined G" "(A, a, B) \<in> rules G"
  shows "A \<in> non_terminals G \<and> a \<in> alphabet_grammar G \<and> B \<in> non_terminals G"
  using assms unfolding grammar_well_defined_def by fast

type_synonym 's rule_sequence = "('s + unit) non_terminal list"

definition right_rule_sequence_well_defined :: "'s rule_sequence \<Rightarrow> ('s, 'a) regular_grammar \<Rightarrow> ('a + unit) word \<Rightarrow> bool" where
  "right_rule_sequence_well_defined rseq G word =
    (length rseq = length word + 1 \<and>
    (rseq ! 0) = starting_non_terminal G \<and> 
    (\<forall> i < length rseq - 1 . (rseq ! i, word ! i, rseq ! (i + 1)) \<in> rules G))"

definition rseq_non_terminals :: "'s rule_sequence \<Rightarrow> ('s, 'a) regular_grammar \<Rightarrow> bool" where "rseq_non_terminals rseq G = (set rseq \<subseteq> non_terminals G)"

proposition rseq_non_terminals_equivalence: "rseq_non_terminals rseq G \<longleftrightarrow> (\<forall> S \<in> set rseq . S \<in> non_terminals G)"
  unfolding rseq_non_terminals_def by auto

theorem well_def_implies_rseq_non_terminals:
  assumes "grammar_well_defined G" "right_rule_sequence_well_defined rseq G word"
  shows "rseq_non_terminals rseq G"
proof(cases word)
  case Nil
  hence "rseq = [rseq ! 0] \<and> (rseq ! 0) = starting_non_terminal G" using assms list_with_one_element unfolding right_rule_sequence_well_defined_def by fastforce
  hence "rseq = [starting_non_terminal G] \<and> starting_non_terminal G \<in> non_terminals G" using assms unfolding grammar_well_defined_def by argo
  thus ?thesis using rseq_non_terminals_equivalence by fastforce
next
  let ?n = "length rseq"
  case (Cons a word)
  hence len: "?n > 1" using assms unfolding right_rule_sequence_well_defined_def by auto
  have rseq_i: "\<forall> i < ?n - 1 . rseq ! i \<in> non_terminals G" using well_def_rule_components assms unfolding right_rule_sequence_well_defined_def by fast
  have "\<forall> i < ?n - 1 . rseq ! (i + 1) \<in> non_terminals G" using well_def_rule_components assms unfolding right_rule_sequence_well_defined_def by fast
  hence "rseq ! (?n - 2 + 1) \<in> non_terminals G" using len by force
  hence "rseq ! (?n - 1) \<in> non_terminals G" using len simple_math by metis
  hence "\<forall> i < ?n . rseq ! i \<in> non_terminals G" using rseq_i merge_one_more by simp
  thus ?thesis using rseq_non_terminals_equivalence in_set_conv_nth by metis
qed

theorem well_def_grammar_implies_word_well_defined:
  assumes "grammar_well_defined G" "right_rule_sequence_well_defined rseq G word"
  shows "word_well_defined word (alphabet_grammar G)"
proof - 
  have "length rseq = length word + 1 \<and> (\<forall> i < length rseq - 1 . (rseq ! i, word ! i, rseq ! (i + 1)) \<in> rules G)" using assms unfolding right_rule_sequence_well_defined_def by blast
  hence "\<forall> i < length word . word ! i \<in> alphabet_grammar G" using well_def_rule_components assms by fastforce
  hence "\<forall> a \<in> set word . a \<in> alphabet_grammar G" using in_set_conv_nth by metis
  thus ?thesis using word_well_def_equivalence by fast
qed

lemma rseq_well_defined_induction_snoc:
  assumes "grammar_well_defined G" "right_rule_sequence_well_defined rseq G word" "(last rseq, a, S) \<in> rules G"
  shows "right_rule_sequence_well_defined (rseq @ [S]) G (word @ [a])"
proof -
  let ?n = "length rseq"
  let ?rseq = "rseq @ [S]"
  let ?word = "word @ [a]"
  have properties: "?n = length word + 1 \<and> ?n - 1 = length word \<and> rseq \<noteq> [] \<and> rseq ! 0 = starting_non_terminal G \<and> rseq ! 0 \<in> non_terminals G" using assms unfolding grammar_well_defined_def right_rule_sequence_well_defined_def by force
  hence snoc_rule_step: "\<forall> i < ?n - 1 . (?rseq ! i, ?word ! i, ?rseq ! (i + 1)) \<in> rules G" using assms list_properties_length unfolding right_rule_sequence_well_defined_def by metis
  have "?rseq ! (?n - 1) = last rseq \<and> ?rseq ! ?n = S \<and> ?word ! (?n - 1) = a" using properties list_properties_not_empty nth_append_length by metis
  hence "(?rseq ! (?n - 1), ?word ! (?n - 1), ?rseq ! ((?n - 1) + 1)) \<in> rules G" using properties assms by auto
  hence "\<forall> i < length ?rseq - 1 . (?rseq ! i, ?word ! i, ?rseq ! (i + 1)) \<in> rules G" using snoc_rule_step merge_one_more by simp
  thus ?thesis using properties list_properties_not_empty unfolding right_rule_sequence_well_defined_def by force
qed

lemma last_rule:
  assumes "right_rule_sequence_well_defined (rseq @ [S]) G (word @ [a])"
  shows "(last rseq, a, S) \<in> rules G"
proof - 
  let ?n = "length (rseq @ [S])"
  let ?rseq = "rseq @ [S]"
  let ?word = "word @ [a]"
  have "?n = length ?word + 1" using assms unfolding right_rule_sequence_well_defined_def by blast
  hence properties: "?n > 1 \<and> ?n = length ?word + 1 \<and> ?rseq \<noteq> []" by auto
  have "\<forall> i < ?n - 1 . (?rseq ! i, ?word ! i, ?rseq ! (i + 1)) \<in>  rules G" using assms unfolding right_rule_sequence_well_defined_def by auto
  hence rule: "(?rseq ! (?n - 2), ?word ! (?n - 2), ?rseq ! (?n - 2 + 1)) \<in> rules G" using properties by force
  have last: "?rseq ! (length ?rseq - 2) = last rseq \<and> ?word ! (?n - 2) = a" using list_properties_not_empty properties by force
  have "rseq \<noteq> []" using properties by auto
  hence "?rseq ! (?n - 2 + 1) = S" by auto
  thus ?thesis using last rule by auto
qed

lemma rseq_well_defined_snoc:
  assumes "grammar_well_defined G" "right_rule_sequence_well_defined (rseq @ [S]) G (word @ [a])"
  shows "right_rule_sequence_well_defined rseq G word \<and> (last rseq, a, S) \<in> rules G"
proof -
  let ?n = "length rseq"
  let ?rseq = "rseq @ [S]"
  let ?word = "word @ [a]"
  have "length ?rseq = length ?word + 1 \<and> ?rseq ! 0 = starting_non_terminal G \<and> ?rseq ! 0 \<in> non_terminals G" using assms unfolding right_rule_sequence_well_defined_def grammar_well_defined_def by presburger
  hence properties: "length ?rseq = length ?word + 1 \<and> ?n - 1 = length word \<and> ?rseq ! 0 = starting_non_terminal G \<and> ?rseq ! 0 \<in> non_terminals G \<and> rseq \<noteq> []" by auto
  hence initial_state: "rseq ! 0 = starting_non_terminal G \<and> rseq ! 0 \<in> non_terminals G" using list_properties_not_empty by metis
  have "\<forall> i < ?n - 1 . (?rseq ! i, ?word ! i, ?rseq ! (i + 1)) \<in> rules G" using assms unfolding right_rule_sequence_well_defined_def by auto
  hence i_step: "\<forall> i < ?n - 1 . (rseq ! i, word ! i, rseq ! (i + 1)) \<in> rules G" using properties list_properties_length by metis
  have "(last rseq, a, S) \<in> rules G" using assms last_rule by fast
  thus ?thesis using properties initial_state i_step unfolding right_rule_sequence_well_defined_def by auto
qed

proposition rseq_well_defined_extension_snoc:
  assumes "grammar_well_defined G"
  shows "right_rule_sequence_well_defined (rseq @ [S]) G (word @ [a]) \<longleftrightarrow> right_rule_sequence_well_defined rseq G word \<and> (last rseq, a, S) \<in> rules G"
  using assms rseq_well_defined_snoc rseq_well_defined_induction_snoc by metis

definition right_rule_seq_terminated :: "'s rule_sequence \<Rightarrow> ('s, 'a) regular_grammar \<Rightarrow> ('a + unit) word \<Rightarrow> bool" where "right_rule_seq_terminated rseq G word = (right_rule_sequence_well_defined rseq G word \<and> last rseq = Inr())"

definition right_grammar_language :: "('s, 'a) regular_grammar \<Rightarrow> 'a language" where "right_grammar_language G = eps_free_language {word . \<exists> rseq . right_rule_seq_terminated rseq G word}"

lemma induced_grammar_language_well_def:
  assumes "grammar_well_defined G"
  shows "language_well_defined {word . \<exists> rseq . right_rule_seq_terminated rseq G word} (alphabet_grammar G)"
  using assms well_def_grammar_implies_word_well_defined unfolding right_rule_seq_terminated_def language_well_defined_def by blast

proposition right_grammar_language_well_defined:
  assumes "grammar_well_defined G"
  shows "language_well_defined (right_grammar_language G) (original_alphabet (alphabet_grammar G))"
  using assms induced_grammar_language_well_def eps_free_language_well_defined unfolding right_grammar_language_def by fast

proposition empty_word_not_in_induced_language:
  assumes "grammar_well_defined G"
  shows "[] \<notin> {word . \<exists> rseq . right_rule_seq_terminated rseq G word}"
proof(rule ccontr)
  assume "\<not> ([] \<notin> {word . \<exists> rseq . right_rule_seq_terminated rseq G word})"
  hence "[] \<in> {word . \<exists> rseq . right_rule_seq_terminated rseq G word}" by blast
  then obtain rseq where "right_rule_sequence_well_defined rseq G [] \<and> last rseq = Inr()" unfolding right_rule_seq_terminated_def by blast
  hence "length rseq = 1 \<and> rseq ! 0 = starting_non_terminal G \<and> last rseq = Inr()" unfolding right_rule_sequence_well_defined_def by auto
  thus False using assms list_with_one_element unfolding grammar_well_defined_def by metis
qed

definition grammar_to_eps_auto :: "('s, 'a) regular_grammar \<Rightarrow> ('s + unit, 'a + unit) automaton" where
  "grammar_to_eps_auto G = Automaton
    (non_terminals G \<union> {Inr()})
    (alphabet_grammar G)
    (rules G)
    (starting_non_terminal G)
    {Inr()}"

lemma grammar_to_eps_auto_alphabet: "alphabet_grammar G = alphabet (grammar_to_eps_auto G)"
  unfolding grammar_to_eps_auto_def by auto

proposition well_def_grammar_implies_well_def_eps_auto:
  assumes "grammar_well_defined G"
  shows "auto_well_defined (grammar_to_eps_auto G)"
  using assms unfolding grammar_well_defined_def auto_well_defined_def grammar_to_eps_auto_def by force

theorem grammar_to_eps_auto_language_correctness:
  assumes "grammar_well_defined G"
  shows "right_grammar_language G = eps_free_language (language_auto (grammar_to_eps_auto G))"
proof -
  let ?\<A> = "grammar_to_eps_auto G"
  {
    fix word assume "word \<in> right_grammar_language G"
    hence "word \<in> eps_free_language {word . \<exists> rseq . right_rule_seq_terminated rseq G word}" unfolding right_grammar_language_def by blast
    then obtain word' where word: "evaluate_eps_word word' = word \<and> word' \<in> {word . \<exists> rseq . right_rule_seq_terminated rseq G word}" unfolding eps_free_language_def by blast
    then obtain rseq where "right_rule_seq_terminated rseq G word'" by blast
    hence "right_rule_sequence_well_defined rseq G word' \<and> last rseq = Inr()" unfolding right_rule_seq_terminated_def by blast
    hence "length rseq = length word' + 1 \<and> (rseq ! 0) = starting_non_terminal G \<and> (\<forall> i < length rseq - 1 . (rseq ! i, word' ! i, rseq ! (i + 1)) \<in> rules G) \<and> last rseq = Inr()" unfolding right_rule_sequence_well_defined_def by blast
    hence "length rseq = length word' + 1 \<and> (rseq ! 0) = starting_non_terminal G \<and> rseq ! 0 \<in> non_terminals G \<and> (\<forall> i < length rseq - 1 . (rseq ! i, word' ! i, rseq ! (i + 1)) \<in> rules G) \<and> last rseq = Inr()" using assms unfolding grammar_well_defined_def by presburger
    hence "length rseq = length word' + 1 \<and> (rseq ! 0) = initial_state ?\<A> \<and> rseq ! 0 \<in> states ?\<A> \<and> (\<forall> i < length rseq - 1 . (rseq ! i, word' ! i, rseq ! (i + 1)) \<in> transitions ?\<A>) \<and> last rseq \<in> accepting_states ?\<A>" unfolding grammar_to_eps_auto_def by force
    hence "run_accepting rseq ?\<A> word'" unfolding pseudo_run_well_defined_def run_well_defined_def run_accepting_def by force
    hence "word \<in> eps_free_language (language_auto ?\<A>)" using word unfolding language_auto_def eps_free_language_def by blast
  }
  hence sub: "right_grammar_language G \<subseteq> eps_free_language (language_auto ?\<A>)" by blast
  {
    fix word assume "word \<in> eps_free_language (language_auto ?\<A>)"
    hence "word \<in> eps_free_language {word . \<exists> run . run_accepting run ?\<A> word}" unfolding language_auto_def by blast
    then obtain word' where word: "evaluate_eps_word word' = word \<and> word' \<in> {word . \<exists> run . run_accepting run ?\<A> word}" unfolding eps_free_language_def by blast
    then obtain run where "run_accepting run ?\<A> word'" by blast
    hence "run_well_defined run ?\<A> word' \<and> last run \<in> accepting_states ?\<A>" unfolding run_accepting_def by blast
    hence "length run = length word' + 1 \<and> (run ! 0) = starting_non_terminal G \<and> (\<forall> i < length run - 1 . (run ! i, word' ! i, run ! (i + 1)) \<in> rules G) \<and> last run = Inr()" unfolding run_well_defined_def pseudo_run_well_defined_def grammar_to_eps_auto_def by auto
    hence "right_rule_seq_terminated run G word'" unfolding right_rule_seq_terminated_def right_rule_sequence_well_defined_def by blast
    hence "word \<in> right_grammar_language G" using word unfolding right_grammar_language_def eps_free_language_def by fast
  }
  thus ?thesis using sub by blast
qed
    
definition auto_to_grammar :: "('s, 'a) automaton \<Rightarrow> ('s, 'a) regular_grammar" where
  "auto_to_grammar \<A> = Grammar
    (image Inl (states \<A>) \<union> {Inr()})
    (image Inl (alphabet \<A>) \<union> {Inr()})
    (image (\<lambda>(s1, a, s2) . (Inl s1, Inl a, Inl s2)) (transitions \<A>) \<union> {(Inl s, Inr(), Inr()) | s . s \<in> accepting_states \<A>})
    (Inl (initial_state \<A>))"

lemma auto_to_grammar_alphabet: "alphabet \<A> = original_alphabet (alphabet_grammar (auto_to_grammar \<A>))"
  unfolding auto_to_grammar_def original_alphabet_def by auto

proposition well_def_auto_implies_well_def_grammar:
  assumes "auto_well_defined \<A>"
  shows "grammar_well_defined (auto_to_grammar \<A>)"
  using assms unfolding grammar_well_defined_def auto_well_defined_def auto_to_grammar_def by auto

lemma auto_to_grammar_run_to_rseq:
  assumes "run_well_defined run \<A> word"
  shows "right_rule_sequence_well_defined (map Inl run) (auto_to_grammar \<A>) (map Inl word)"
  using assms unfolding run_well_defined_def pseudo_run_well_defined_def right_rule_sequence_well_defined_def auto_to_grammar_def by force

lemma auto_to_grammar_run_acc_to_rseq_term:
  assumes "auto_well_defined \<A>" "run_accepting run \<A> word"
  shows "right_rule_seq_terminated ((map Inl run) @ [Inr()]) (auto_to_grammar \<A>) ((map Inl word) @ [Inr()])"
proof -
  have well_def: "grammar_well_defined (auto_to_grammar \<A>)" using assms well_def_auto_implies_well_def_grammar by blast 
  have run: "run_well_defined run \<A> word \<and> last run \<in> accepting_states \<A>" using assms unfolding run_accepting_def by blast
  hence rseq: "right_rule_sequence_well_defined (map Inl run) (auto_to_grammar \<A>) (map Inl word) \<and> last run \<in> accepting_states \<A>" using auto_to_grammar_run_to_rseq by auto
  hence rule: "(Inl (last run), Inr(), Inr()) \<in> rules (auto_to_grammar \<A>)" unfolding auto_to_grammar_def by force
  have "run \<noteq> []" using run unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "last (map Inl run) = Inl (last run)" using last_map by blast
  hence "right_rule_sequence_well_defined ((map Inl run) @ [Inr()]) (auto_to_grammar \<A>) ((map Inl word) @ [Inr()])" using rseq rule well_def rseq_well_defined_extension_snoc by metis
  thus ?thesis unfolding right_rule_seq_terminated_def by auto
qed

lemma auto_to_grammar_rseq_to_run:
  assumes "auto_well_defined \<A>"
  shows "right_rule_sequence_well_defined rseq (auto_to_grammar \<A>) word \<Longrightarrow> run_well_defined (evaluate_eps_run rseq) \<A> (evaluate_eps_word word)"
proof(induction word arbitrary: rseq rule: rev_induct)
  case Nil
  hence "rseq = [starting_non_terminal (auto_to_grammar \<A>)]" using list_with_one_element unfolding right_rule_sequence_well_defined_def by force
  hence "rseq = [starting_non_terminal (auto_to_grammar \<A>)] \<and> rseq ! 0 \<noteq> Inr() \<and> rseq ! 0 \<in> non_terminals (auto_to_grammar \<A>)" using assms well_def_auto_implies_well_def_grammar unfolding grammar_well_defined_def by auto
  thus ?case unfolding run_well_defined_def pseudo_run_well_defined_def auto_to_grammar_def by force
next
  case (snoc a word)
  hence "rseq \<noteq> []" unfolding right_rule_sequence_well_defined_def by force
  then obtain rseq' where rseq: "rseq = rseq' @ [last rseq]" using append_butlast_last_id by metis
  hence "right_rule_sequence_well_defined rseq' (auto_to_grammar \<A>) word \<and> (last rseq', a, last rseq) \<in> rules (auto_to_grammar \<A>)" using snoc rseq_well_defined_extension_snoc assms well_def_auto_implies_well_def_grammar by metis 
  hence props: "run_well_defined (evaluate_eps_run rseq') \<A> (evaluate_eps_word word) \<and> (last rseq', a, last rseq) \<in> rules (auto_to_grammar \<A>) \<and> rseq' \<noteq> []" using snoc unfolding right_rule_sequence_well_defined_def by force
  consider (case1) "a = Inr()" | (case2) "a \<noteq> Inr()" by auto 
  thus ?case
  proof cases
    case case1
    have "evaluate_eps_word (word @ [a]) = evaluate_eps_word word @ evaluate_eps_word [a]" using evaluate_eps_word_snoc by auto
    hence eva_word_equi: "evaluate_eps_word (word @ [a]) = evaluate_eps_word word" using case1 by auto
    have "last rseq = Inr()" using props case1 unfolding auto_to_grammar_def by force
    hence "evaluate_eps_run rseq = evaluate_eps_run rseq' @ evaluate_eps_run [Inr()]" using rseq evaluate_eps_run_snoc by metis
    hence "evaluate_eps_run rseq = evaluate_eps_run rseq'" by auto
    thus ?thesis using props eva_word_equi by auto
  next
    case case2
    then obtain b where b: "a = Inl b" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    have "last rseq \<noteq> Inr() \<and> last rseq' \<noteq> Inr()" using props case2 unfolding auto_to_grammar_def by force
    then obtain s1 s2 where s: "last rseq = Inl s2 \<and> last rseq' = Inl s1" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    hence run: "run_well_defined (evaluate_eps_run rseq') \<A> (evaluate_eps_word word) \<and> (s1, b, s2) \<in> transitions \<A> \<and> rseq' \<noteq> []" using b props unfolding auto_to_grammar_def by force
    hence "evaluate_eps_run rseq' \<noteq> [] \<and> last (evaluate_eps_run rseq') = s1" using last_evaluate_eps_run s by fast
    hence "run_well_defined ((evaluate_eps_run rseq') @ [s2]) \<A> ((evaluate_eps_word word) @ [b])" using run assms prun_well_defined_extension_snoc unfolding run_well_defined_def by metis
    hence "run_well_defined ((evaluate_eps_run rseq') @ (evaluate_eps_run [last rseq])) \<A> ((evaluate_eps_word word) @ (evaluate_eps_word [a]))" using b s by force
    thus ?thesis using rseq evaluate_eps_run_snoc evaluate_eps_word_snoc by metis
  qed
qed

lemma auto_to_grammar_rseq_term_to_run_acc:
  assumes "auto_well_defined \<A>" "right_rule_seq_terminated rseq (auto_to_grammar \<A>) word"
  shows "run_accepting (evaluate_eps_run rseq) \<A> (evaluate_eps_word word)"
proof(cases word)
  case Nil
  thus ?thesis using assms empty_word_not_in_induced_language well_def_auto_implies_well_def_grammar by blast
next
  case (Cons a list)
  hence not_empty: "word \<noteq> []" by simp
  have rseq: "right_rule_sequence_well_defined rseq (auto_to_grammar \<A>) word \<and> last rseq = Inr()" using assms unfolding right_rule_seq_terminated_def by blast
  hence "rseq \<noteq> [] \<and> word \<noteq> []" using not_empty right_rule_sequence_well_defined_def by force
  then obtain rseq' word' where step: "rseq = rseq' @ [last rseq] \<and> word = word' @ [last word]" using append_butlast_last_id by metis
  hence "right_rule_sequence_well_defined (rseq' @ [last rseq]) (auto_to_grammar \<A>) (word' @ [last word]) \<and> last rseq = Inr()" using rseq by auto
  hence "right_rule_sequence_well_defined rseq' (auto_to_grammar \<A>) word' \<and> (last rseq', last word, last rseq) \<in> rules (auto_to_grammar \<A>) \<and> last rseq = Inr()" using rseq_well_defined_extension_snoc assms well_def_auto_implies_well_def_grammar by blast
  hence "run_well_defined (evaluate_eps_run rseq') \<A> (evaluate_eps_word word') \<and> (last rseq', last word, last rseq) \<in> rules (auto_to_grammar \<A>) \<and> last rseq = Inr() \<and> rseq' \<noteq> []" using assms auto_to_grammar_rseq_to_run unfolding right_rule_sequence_well_defined_def by fastforce
  hence props: "run_well_defined (evaluate_eps_run rseq') \<A> (evaluate_eps_word word') \<and> (last rseq', last word, last rseq) \<in> rules (auto_to_grammar \<A>) \<and> last rseq' \<noteq> Inr() \<and> last word = Inr() \<and> last rseq = Inr() \<and> rseq' \<noteq> []" unfolding auto_to_grammar_def by force
  then obtain s where s: "last rseq' = Inl s" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
  hence "(Inl s, Inr(), Inr()) \<in> rules (auto_to_grammar \<A>) \<and> last rseq' \<noteq> Inr() \<and> last word = Inr() \<and> last rseq = Inr() \<and> rseq' \<noteq> []" using props by auto
  hence "s \<in> accepting_states \<A> \<and> rseq' \<noteq> []" unfolding auto_to_grammar_def by auto
  hence last: "last (evaluate_eps_run rseq') = s \<and> s \<in> accepting_states \<A>" using last_evaluate_eps_run s by force
  have "evaluate_eps_word word = evaluate_eps_word word' @ evaluate_eps_word [last word]" using step evaluate_eps_word_snoc by metis
  hence eva_word_equi: "evaluate_eps_word word = evaluate_eps_word word'" using props by auto
  have "evaluate_eps_run rseq = evaluate_eps_run rseq' @ evaluate_eps_run [last rseq]" using step evaluate_eps_run_snoc by metis
  hence "evaluate_eps_run rseq = evaluate_eps_run rseq'" using props by auto
  thus ?thesis using props eva_word_equi last unfolding run_accepting_def by auto
qed

theorem auto_to_grammarlanguage_correctness:
  assumes "auto_well_defined \<A>"
  shows "right_grammar_language (auto_to_grammar \<A>) = language_auto \<A>"
proof -
  let ?G = "auto_to_grammar \<A>"
    {
    fix word assume "word \<in> language_auto \<A>"
    hence "word \<in> {word . \<exists> run . run_accepting run \<A> word}" unfolding language_auto_def by blast
    then obtain run where "run_accepting run \<A> word" by blast
    hence "right_rule_seq_terminated ((map Inl run) @ [Inr()]) ?G ((map Inl word) @ [Inr()])" using assms auto_to_grammar_run_acc_to_rseq_term by blast
    hence "evaluate_eps_word ((map Inl word) @ [Inr()]) \<in> right_grammar_language ?G" unfolding right_grammar_language_def eps_free_language_def by blast
    hence "evaluate_eps_word (map Inl word) @ evaluate_eps_word [Inr()] \<in> right_grammar_language ?G" using evaluate_eps_word_snoc by metis
    hence "word @ [] \<in> right_grammar_language ?G" using inverse_evaluate_eps evaluate_eps_word.simps(1) evaluate_eps_word.simps(3) by metis
    hence "word \<in> right_grammar_language ?G" by simp
  }
  hence sub: "language_auto \<A> \<subseteq> right_grammar_language ?G" by blast   
  {
    fix word assume "word \<in> right_grammar_language ?G"
    hence "word \<in> eps_free_language {word . \<exists> rseq . right_rule_seq_terminated rseq ?G word}" unfolding right_grammar_language_def by blast
    then obtain word' where word: "evaluate_eps_word word' = word \<and> word' \<in> {word . \<exists> rseq . right_rule_seq_terminated rseq ?G word}" unfolding eps_free_language_def by blast
    then obtain rseq where "right_rule_seq_terminated rseq ?G word'" by blast
    hence "word \<in> language_auto \<A>" using assms word auto_to_grammar_rseq_term_to_run_acc unfolding language_auto_def by blast
  }
  thus ?thesis using sub by blast
qed


text \<open>Key result for showing equivalence of expressive power between right_regular_grammars and autos\<close>
theorem right_regular_grammar_implies_existence_of_auto:
  assumes "grammar_well_defined (G :: ('s, 'a) regular_grammar)"
  shows "\<exists> \<A> :: ('s + unit, 'a + unit) automaton . auto_well_defined \<A> \<and> alphabet \<A> = alphabet_grammar G \<and> eps_free_language (language_auto \<A>) = right_grammar_language G"
  using assms grammar_to_eps_auto_alphabet well_def_grammar_implies_well_def_eps_auto grammar_to_eps_auto_language_correctness by blast

theorem right_regular_grammar_to_auto_main:
  assumes "grammar_well_defined (G :: ('s, 'a) regular_grammar)" "infinite (UNIV :: 's set)"
  shows "\<exists> \<A> :: ('s, 'a) automaton . auto_well_defined \<A> \<and> alphabet \<A> = original_alphabet (alphabet_grammar G) \<and> language_auto \<A> = right_grammar_language G"
  using assms right_regular_grammar_implies_existence_of_auto eps_main existence_soft_iso_auto_lang by metis

theorem auto_to_right_regular_grammar_main:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)"
  shows "\<exists> G :: ('s, 'a) regular_grammar . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = alphabet \<A> \<and> right_grammar_language G = language_auto \<A>"
  using auto_to_grammar_alphabet well_def_auto_implies_well_def_grammar assms auto_to_grammarlanguage_correctness by fast

theorem expressive_power_auto_RG_main:
  assumes "infinite (UNIV :: 's set)"
  shows "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>} = {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}"
  using assms right_regular_grammar_to_auto_main auto_to_right_regular_grammar_main by fastforce



text \<open>left_regular_grammars\<close>
definition left_rule_sequence_well_defined :: "'s rule_sequence \<Rightarrow> ('s, 'a) regular_grammar \<Rightarrow> ('a + unit) word \<Rightarrow> bool" where
  "left_rule_sequence_well_defined rseq G word =
    (length rseq = length word + 1 \<and>
    (rseq ! 0) = starting_non_terminal G \<and> 
    (\<forall> i < length rseq - 1 . (rseq ! i, word ! (length word - Suc i), rseq ! (i + 1)) \<in> rules G))"

definition left_rule_seq_terminated :: "'s rule_sequence \<Rightarrow> ('s, 'a) regular_grammar \<Rightarrow> ('a + unit) word \<Rightarrow> bool" where "left_rule_seq_terminated rseq G word = (left_rule_sequence_well_defined rseq G word \<and> last rseq = Inr())"

definition left_grammar_language :: "('s, 'a) regular_grammar \<Rightarrow> 'a language" where "left_grammar_language G = eps_free_language {word . \<exists> rseq . left_rule_seq_terminated rseq G word}"

lemma left_to_right_seq:
  assumes "left_rule_sequence_well_defined rseq G word"
  shows "right_rule_sequence_well_defined rseq G (rev word)"
proof -
  have length: "length rseq = length word + 1" using assms unfolding left_rule_sequence_well_defined_def by blast
  hence len: "length rseq = length (rev word) + 1" by auto
  have start: "rseq ! 0 = starting_non_terminal G" using assms unfolding left_rule_sequence_well_defined_def by blast
  have rev: "\<forall> i < length word . word ! i = (rev word) ! (length word - Suc i)" by (simp add: rev_nth)
  {
    fix i assume "i < length rseq - 1"
    hence i: "i < length word" using length by auto
    hence "(rseq ! i, word ! (length word - Suc i), rseq ! (i + 1)) \<in> rules G" using assms unfolding left_rule_sequence_well_defined_def by auto
    hence "(rseq ! i, (rev word) ! i, rseq ! (i + 1)) \<in> rules G" using rev i by fastforce
  }
  thus ?thesis using len start unfolding right_rule_sequence_well_defined_def by argo
qed

lemma right_to_left_seq:
  assumes "right_rule_sequence_well_defined rseq G (rev word)"
  shows "left_rule_sequence_well_defined rseq G word"
proof -
  have length: "length rseq = length (rev word) + 1" using assms unfolding right_rule_sequence_well_defined_def by blast
  hence len: "length rseq = length word + 1" by auto
  have start: "rseq ! 0 = starting_non_terminal G" using assms unfolding right_rule_sequence_well_defined_def by blast
  have rev: "\<forall> i < length (rev word) . (rev word) ! i = word ! (length word - Suc i)" by (simp add: rev_nth)
  {
    fix i assume "i < length rseq - 1"
    hence i: "i < length (rev word)" using length by auto
    hence "(rseq ! i, (rev word) ! i, rseq ! (i + 1)) \<in> rules G" using assms unfolding right_rule_sequence_well_defined_def by force
    hence "(rseq ! i, word ! (length word - Suc i), rseq ! (i + 1)) \<in> rules G" using rev i by force
  }
  thus ?thesis using len start unfolding left_rule_sequence_well_defined_def by blast
qed

theorem equivalence_between_left_and_right_seq: "right_rule_seq_terminated rseq G (rev word) = left_rule_seq_terminated rseq G word"
  using left_to_right_seq right_to_left_seq unfolding right_rule_seq_terminated_def left_rule_seq_terminated_def by blast

lemma rev_eva_one: "rev (evaluate_eps_word [a]) = evaluate_eps_word [a]"
proof -
  consider (case1) "a = Inr()" | (case2) "a \<noteq> Inr()" by auto
  thus ?thesis
  proof cases
    case case1
    thus ?thesis by simp
  next
    case case2
    then obtain b where b: "Inl b = a" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    thus ?thesis by force
  qed
qed

lemma switch_rev_eva: "evaluate_eps_word (rev word) = rev (evaluate_eps_word word)"
proof(induction word rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc a word)
  have "evaluate_eps_word (rev (word @ [a])) = evaluate_eps_word ([a] @ (rev word))" by simp
  hence "evaluate_eps_word (rev (word @ [a])) = evaluate_eps_word [a] @ evaluate_eps_word (rev word)" using evaluate_eps_word_snoc by metis
  hence equi: "evaluate_eps_word (rev (word @ [a])) = evaluate_eps_word [a] @ rev (evaluate_eps_word word)" using snoc by auto
  have "rev (evaluate_eps_word (word @ [a])) = rev (evaluate_eps_word word @ evaluate_eps_word [a])" using evaluate_eps_word_snoc by blast
  hence "rev (evaluate_eps_word (word @ [a])) = rev (evaluate_eps_word [a]) @ rev (evaluate_eps_word word)" by simp
  hence "rev (evaluate_eps_word (word @ [a])) = evaluate_eps_word [a] @ rev (evaluate_eps_word word)" using rev_eva_one by auto
  thus ?case using equi by simp
qed

proposition equivalence_left_grammar_lang_rev_lang: "left_grammar_language G = rev_language (right_grammar_language G)"
proof -
  {
    fix word assume "word \<in> left_grammar_language G"
    hence "word \<in> eps_free_language {word . \<exists> rseq . left_rule_seq_terminated rseq G word}" unfolding left_grammar_language_def by blast
    then obtain word' where "word = evaluate_eps_word word' \<and> word' \<in> {word . \<exists> rseq . left_rule_seq_terminated rseq G word}" unfolding eps_free_language_def by blast
    then obtain rseq where "word = evaluate_eps_word word' \<and> left_rule_seq_terminated rseq G word'" by fast
    hence "word = evaluate_eps_word word' \<and> right_rule_seq_terminated rseq G (rev word')" using equivalence_between_left_and_right_seq by fast
    hence "word = evaluate_eps_word word' \<and> (rev word') \<in> {word . \<exists> rseq . right_rule_seq_terminated rseq G word}" by blast
    hence "word = evaluate_eps_word word' \<and> evaluate_eps_word (rev word') \<in> eps_free_language {word . \<exists> rseq . right_rule_seq_terminated rseq G word}" unfolding eps_free_language_def by blast
    hence "word = evaluate_eps_word word' \<and> evaluate_eps_word (rev word') \<in> right_grammar_language G" unfolding right_grammar_language_def by blast
    hence "rev word \<in> right_grammar_language G" using switch_rev_eva by metis
    hence "word \<in> rev_language (right_grammar_language G)" unfolding rev_language_def by force
  }
  hence sub: "left_grammar_language G \<subseteq> rev_language (right_grammar_language G)" by blast
  {
    fix word assume "word \<in> rev_language (right_grammar_language G)"
    hence "rev word \<in> right_grammar_language G" unfolding rev_language_def by force
    hence "rev word \<in> eps_free_language {word . \<exists> rseq . right_rule_seq_terminated rseq G word}" unfolding right_grammar_language_def by blast
    then obtain word' where "rev word = evaluate_eps_word word' \<and> word' \<in> {word . \<exists> rseq . right_rule_seq_terminated rseq G word}" unfolding eps_free_language_def by blast
    then obtain rseq where "rev word = evaluate_eps_word word' \<and> right_rule_seq_terminated rseq G word'" by fast
    hence "rev word = evaluate_eps_word word' \<and> left_rule_seq_terminated rseq G (rev word')" using equivalence_between_left_and_right_seq by fastforce
    hence "rev word = evaluate_eps_word word' \<and> (rev word') \<in> {word . \<exists> rseq . left_rule_seq_terminated rseq G word}" by blast
    hence "rev word = evaluate_eps_word word' \<and> evaluate_eps_word (rev word') \<in> eps_free_language {word . \<exists> rseq . left_rule_seq_terminated rseq G word}" unfolding eps_free_language_def by blast
    hence "rev word = evaluate_eps_word word' \<and> evaluate_eps_word (rev word') \<in> left_grammar_language G" unfolding left_grammar_language_def by blast
    hence "word \<in> left_grammar_language G" using switch_rev_eva rev_rev_ident by metis
  }
  thus ?thesis using sub by fast
qed

corollary left_grammar_language_well_defined:
  assumes "grammar_well_defined G"
  shows "language_well_defined (left_grammar_language G) (original_alphabet (alphabet_grammar G))"
  using right_grammar_language_well_defined equivalence_left_grammar_lang_rev_lang assms rev_language_well_defined by metis

lemma rev_language_in_RG:
  assumes "infinite (UNIV :: 's set)" "L \<in> {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}"
  shows "rev_language L \<in> {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}"
proof -
  have "L \<in> {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" using assms expressive_power_auto_RG_main by auto
  hence "rev_language L \<in> {L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>}" using assms expressive_power_rev_main by blast
  thus ?thesis using assms expressive_power_auto_RG_main by blast
qed
  
corollary rev_language_in_RG_cor:
  assumes "infinite (UNIV :: 's set)" "rev_language L \<in> {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}"
  shows "L \<in> {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}"
proof - 
  have "rev_language (rev_language L) \<in> {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}" using assms rev_language_in_RG by blast
  thus ?thesis using rev_rev_language by blast
qed

theorem expressive_power_RG_LG_main:
  assumes "infinite (UNIV :: 's set)"
  shows "{L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = left_grammar_language G} = {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}"
proof -
  {
    fix L assume "L \<in> {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = left_grammar_language G}"
    then obtain G :: "('s, 'a) regular_grammar" where G: "grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = left_grammar_language G" by blast
    hence "L = rev_language (right_grammar_language G)" using equivalence_left_grammar_lang_rev_lang by blast
    hence "rev_language L = right_grammar_language G" using rev_rev_language by blast
    hence "rev_language L \<in> {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}" using G by fast
    hence "L \<in> {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}" using assms rev_language_in_RG_cor by blast
  }
  hence sub: "{L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = left_grammar_language G} \<subseteq> {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}" by blast
  {
    fix L assume "L \<in> {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}"
    hence "rev_language L \<in> {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}" using assms rev_language_in_RG by blast
    then obtain G :: "('s, 'a) regular_grammar" where G: "grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> rev_language L = right_grammar_language G" by blast
    hence "L = rev_language (right_grammar_language G)" using rev_rev_language by metis
    hence "L = left_grammar_language G" using equivalence_left_grammar_lang_rev_lang by blast
    hence "L \<in> {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = left_grammar_language G}" using G by blast
  }
  thus ?thesis using sub by blast
qed

corollary expressive_power_auto_LG_main:
  assumes "infinite (UNIV :: 's set)"
  shows "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>} = {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = left_grammar_language G}"
proof -
  have equi: "{L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = left_grammar_language G} = {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}" using assms expressive_power_RG_LG_main by blast
  have "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>} = {L . \<exists> (G :: ('s, 'a) regular_grammar) . grammar_well_defined G \<and> original_alphabet (alphabet_grammar G) = \<Sigma> \<and> L = right_grammar_language G}" using assms expressive_power_auto_RG_main by blast
  thus ?thesis using equi by auto
qed

end