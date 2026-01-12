theory automaton_kleene_star

imports Main automaton_concatenation

begin

text \<open>Author: Benno Thalmann, last update: 12.1.2026, Addition to masterarbeit_benno_thalmann\<close>

fun kleene_star_language_helper :: "'a language \<Rightarrow> nat \<Rightarrow> 'a language" where
  "kleene_star_language_helper L 0 = {[]}" |
  "kleene_star_language_helper L (Suc n) = concatenation_language (kleene_star_language_helper L n) L"

proposition kleene_star_language_helper_well_defined:
  assumes "language_well_defined L \<Sigma>"
  shows "language_well_defined (kleene_star_language_helper L n) \<Sigma>"
proof(induction n)
  case 0 thus ?case unfolding language_well_defined_def word_well_defined_def by simp
next
  case (Suc n)
  have "kleene_star_language_helper L (Suc n) = concatenation_language (kleene_star_language_helper L n) L" by auto
  thus ?case using Suc assms conc_language_well_defined by fastforce
qed

lemma kleene_star_lang_1: "kleene_star_language_helper L 1 = L"
proof -
  have "kleene_star_language_helper L 1 = concatenation_language (kleene_star_language_helper L 0) L" by force
  hence "kleene_star_language_helper L 1 = concatenation_language {[]} L" by auto
  thus ?thesis unfolding concatenation_language_def by auto
qed

lemma kleene_star_cons: "kleene_star_language_helper L (Suc n) = concatenation_language L (kleene_star_language_helper L n)"
proof(induction n)
  case 0 thus ?case using kleene_star_lang_1 unfolding concatenation_language_def by auto
next
  case (Suc n)
  hence "kleene_star_language_helper L (Suc (Suc n)) = concatenation_language (concatenation_language L (kleene_star_language_helper L n)) L" by auto
  hence "kleene_star_language_helper L (Suc (Suc n)) = concatenation_language L (concatenation_language (kleene_star_language_helper L n) L)" using conc_language_assoziative by blast
  hence "kleene_star_language_helper L (Suc (Suc n)) = concatenation_language L (kleene_star_language_helper L (Suc n))" by simp
  thus ?case by blast
qed

lemma kleene_star_helper_additive: "concatenation_language (kleene_star_language_helper L i) (kleene_star_language_helper L j) = kleene_star_language_helper L (i + j)"
proof(induction i arbitrary: j)
  case 0 thus ?case unfolding concatenation_language_def by auto
next
  case (Suc i)
  hence "concatenation_language (kleene_star_language_helper L (Suc i)) (kleene_star_language_helper L j) = concatenation_language (concatenation_language (kleene_star_language_helper L i) L) (kleene_star_language_helper L j)" by simp
  hence "concatenation_language (kleene_star_language_helper L (Suc i)) (kleene_star_language_helper L j) = concatenation_language (kleene_star_language_helper L i) (concatenation_language L (kleene_star_language_helper L j))" using conc_language_assoziative by blast
  hence "concatenation_language (kleene_star_language_helper L (Suc i)) (kleene_star_language_helper L j) = concatenation_language (kleene_star_language_helper L i) (kleene_star_language_helper L (Suc j))" using kleene_star_cons by metis
  hence "concatenation_language (kleene_star_language_helper L (Suc i)) (kleene_star_language_helper L j) = kleene_star_language_helper L (i + Suc j)" using Suc by blast
  thus ?case by auto
qed

lemma kleene_star_of_empty_string: "kleene_star_language_helper {[]} i = {[]}"
proof(induction i)
  case 0 thus ?case by simp
next
  case (Suc i)
  hence "kleene_star_language_helper {[]} (Suc i) = concatenation_language (kleene_star_language_helper {[]} i) {[]}" by auto
  thus ?case using Suc unfolding concatenation_language_def by fastforce
qed 

proposition kleene_star_multiplicative: "kleene_star_language_helper (kleene_star_language_helper L i) j = kleene_star_language_helper L (i * j)"
proof(induction j arbitrary: i)
  case 0 thus ?case by force
next
  case (Suc j)
  hence "kleene_star_language_helper (kleene_star_language_helper L i) (Suc j) = concatenation_language (kleene_star_language_helper (kleene_star_language_helper L i) j) (kleene_star_language_helper L i)" by simp
  hence "kleene_star_language_helper (kleene_star_language_helper L i) (Suc j) = concatenation_language (kleene_star_language_helper L (i * j)) (kleene_star_language_helper L i)" using Suc by simp
  hence "kleene_star_language_helper (kleene_star_language_helper L i) (Suc j) = kleene_star_language_helper L (i * j + i)" using kleene_star_helper_additive by blast
  thus ?case using simple_math2 by presburger
qed

proposition decomposition_of_kleene_star_word: "word \<in> kleene_star_language_helper L i \<Longrightarrow> \<exists> word_list . word = concat word_list \<and> set word_list \<subseteq> L"
proof(induction i arbitrary: word)
  case 0
  hence "word = []" by simp
  hence "word = concat [] \<and> set [] \<subseteq> L" by simp
  thus ?case by blast
next
  case (Suc i)
  hence "word \<in> concatenation_language (kleene_star_language_helper L i) L" by force
  then obtain word1 word2 where word: "word = word1 @ word2 \<and> word1 \<in> (kleene_star_language_helper L i) \<and> word2 \<in> L" unfolding concatenation_language_def by blast
  then obtain word_list where "word1 = concat word_list \<and> set word_list \<subseteq> L" using Suc by presburger
  hence "word = concat (word_list @ [word2]) \<and> set (word_list @ [word2]) \<subseteq> L" using word by simp
  thus ?case by blast
qed

definition kleene_star_language :: "'a language \<Rightarrow> 'a language" where "kleene_star_language L = (\<Union> i . kleene_star_language_helper L i)"

proposition kleene_star_language_well_defined:
  assumes "language_well_defined L \<Sigma>"
  shows "language_well_defined (kleene_star_language L) \<Sigma>"
  using assms kleene_star_language_helper_well_defined unfolding language_well_defined_def kleene_star_language_def by blast

proposition empty_string_in_kleene_star_lang: "[] \<in> kleene_star_language L"
proof -
  have "[] \<in> kleene_star_language_helper L 0" by simp
  thus ?thesis unfolding kleene_star_language_def by fast
qed

lemma double_kleene_star_lang_unfold: "word \<in> kleene_star_language_helper (kleene_star_language L) i \<Longrightarrow> \<exists> j k . word \<in> kleene_star_language_helper (kleene_star_language_helper L j) k"
proof(induction i arbitrary: word)
  case 0
  hence "word \<in> {[]}" by simp
  hence "\<forall> j . word \<in> kleene_star_language_helper (kleene_star_language_helper L j) 0" by simp
  thus ?case by blast
next
  case (Suc i)
  hence "word \<in> concatenation_language (kleene_star_language_helper (kleene_star_language L) i) (kleene_star_language L)" by auto
  then obtain word1 word2 where word: "word = word1 @ word2 \<and> word1 \<in> kleene_star_language_helper (kleene_star_language L) i \<and> word2 \<in> kleene_star_language L" unfolding concatenation_language_def by blast
  then obtain j k l where "word1 \<in> kleene_star_language_helper (kleene_star_language_helper L j) k \<and> word2 \<in> kleene_star_language_helper L l" using Suc unfolding kleene_star_language_def by blast
  hence "word1 \<in> kleene_star_language_helper L (j * k) \<and> word2 \<in> kleene_star_language_helper L l" using kleene_star_multiplicative by blast
  hence "word \<in> kleene_star_language_helper L (j * k + l)" using word kleene_star_helper_additive unfolding concatenation_language_def by blast
  thus ?case using kleene_star_lang_1 by blast
qed

theorem kleene_star_is_closed: "kleene_star_language (kleene_star_language L) = kleene_star_language L"
proof - 
  {
    fix word assume "word \<in> kleene_star_language L"
    then obtain i where "word \<in> kleene_star_language_helper L i" unfolding kleene_star_language_def by blast
    hence "word \<in> kleene_star_language (kleene_star_language L)" using Union_iff kleene_star_lang_1 range_eqI unfolding kleene_star_language_def by metis
  }
  hence sub: "kleene_star_language L \<subseteq> kleene_star_language (kleene_star_language L)" by blast
  {
    fix word assume "word \<in> kleene_star_language (kleene_star_language L)"
    then obtain i where "word \<in> kleene_star_language_helper (kleene_star_language L) i" unfolding kleene_star_language_def by blast
    then obtain j k where "word \<in> kleene_star_language_helper (kleene_star_language_helper L j) k" using double_kleene_star_lang_unfold by blast
    hence "word \<in> kleene_star_language_helper L (j * k)" using kleene_star_multiplicative by blast
    hence "word \<in> kleene_star_language L" unfolding kleene_star_language_def by blast
  }
  thus ?thesis using sub by blast
qed



text \<open>Automaton construction for kleene_star_language\<close>
definition kleene_star_auto :: "('s, 'a) automaton \<Rightarrow> (('s + unit), ('a + unit)) automaton" where
  "kleene_star_auto \<A> = Automaton
    (image Inl (states \<A>) \<union> {Inr()})
    (image Inl (alphabet \<A>) \<union> {Inr()})
    (image (\<lambda>(s1, a, s2) . (Inl s1, Inl a, Inl s2)) (transitions \<A>) \<union> {(Inr(), Inr(), Inl (initial_state \<A>))} \<union> {(Inl s, Inr(), Inr()) | s . s \<in> accepting_states \<A>})
    (Inr())
    (image Inl (accepting_states \<A>) \<union> {Inr()})"

proposition kleene_star_alphabet: "alphabet (kleene_star_auto \<A>) = image Inl (alphabet \<A>) \<union> {Inr()}" unfolding kleene_star_auto_def by force

proposition kleene_star_auto_well_defined:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (kleene_star_auto \<A>)"
  using assms unfolding auto_well_defined_def kleene_star_auto_def by auto

corollary language_well_def_kleene_star_auto:
  assumes "auto_well_defined \<A>"
  shows "language_well_defined (language_auto (kleene_star_auto \<A>)) (alphabet (kleene_star_auto \<A>))"
  using kleene_star_auto_well_defined assms automata_language_are_well_defined by blast

proposition prun_kleene_star_auto: "pseudo_run_well_defined prun \<A> s word \<Longrightarrow> pseudo_run_well_defined (map Inl prun) (kleene_star_auto \<A>) (Inl s) (map Inl word)"
proof(induction word arbitrary: prun rule: rev_induct)
  case Nil thus ?case unfolding kleene_star_auto_def pseudo_run_well_defined_def by force
next
  case (snoc a word)
  hence "prun \<noteq> []" unfolding pseudo_run_well_defined_def by force
  then obtain prun' where prun': "prun = prun' @ [last prun]" using append_butlast_last_id by metis
  hence "pseudo_run_well_defined prun' \<A> s word \<and> (last prun', a, last prun) \<in> transitions \<A>" using prun_well_defined_extension_snoc snoc by metis
  hence "pseudo_run_well_defined (map Inl prun') (kleene_star_auto \<A>) (Inl s) (map Inl word) \<and> (last prun', a, last prun) \<in> transitions \<A>" using snoc by blast
  hence prun: "pseudo_run_well_defined (map Inl prun') (kleene_star_auto \<A>) (Inl s) (map Inl word) \<and> (Inl (last prun'), Inl a, Inl (last prun)) \<in> transitions (kleene_star_auto \<A>)" unfolding kleene_star_auto_def by force
  hence "map Inl prun' \<noteq> []" unfolding pseudo_run_well_defined_def by force
  hence "last (map Inl prun') = Inl (last prun')" using last_map by blast
  hence step: "pseudo_run_well_defined ((map Inl prun') @ [Inl (last prun)]) (kleene_star_auto \<A>) (Inl s) ((map Inl word) @ [Inl a])" using prun_well_defined_extension_snoc prun by metis
  have "((map Inl prun') @ [Inl (last prun)]) = map Inl (prun' @ [last prun])" by auto
  hence inl_prun: "((map Inl prun') @ [Inl (last prun)]) = map Inl prun" using prun' by auto
  have "((map Inl word) @ [Inl a]) = map Inl (word @ [a])" by auto
  thus ?case using step inl_prun by metis
qed

proposition run_accepting_kleene_star_auto:
  assumes "auto_well_defined \<A>" "run_accepting run \<A> word"
  shows "run_accepting (run_transformation_eps run) (kleene_star_auto \<A>) (word_transformation_eps word) \<and> last (run_transformation_eps run) \<noteq> Inr()"
proof -
  let ?\<A> = "kleene_star_auto \<A>"
  have well_def: "auto_well_defined ?\<A>" using assms kleene_star_auto_well_defined by auto
  have props: "pseudo_run_well_defined run \<A> (initial_state \<A>) word \<and> last run \<in> accepting_states \<A>" using assms unfolding run_accepting_def run_well_defined_def by simp
  hence prun: "pseudo_run_well_defined (map Inl run) ?\<A> (Inl (initial_state \<A>)) (map Inl word)" using prun_kleene_star_auto by fast
  have "(initial_state ?\<A>, Inr(), Inl (initial_state \<A>)) \<in> transitions ?\<A>" unfolding kleene_star_auto_def by fastforce
  hence "pseudo_run_well_defined ((initial_state ?\<A>) # (map Inl run)) ?\<A> (initial_state ?\<A>) (Inr() # (map Inl word))" using well_def prun prun_well_defined_induction_cons by metis
  hence run: "run_well_defined (run_transformation_eps run) ?\<A> (word_transformation_eps word)" unfolding run_well_defined_def run_transformation_eps_def word_transformation_eps_def kleene_star_auto_def by force
  have "run \<noteq> []" using props unfolding pseudo_run_well_defined_def by fastforce
  hence last: "Inl (last run) = last (run_transformation_eps run) \<and> last run \<in> accepting_states \<A>" using props unfolding run_transformation_eps_def by (simp add: last_map)
  hence "run_accepting (run_transformation_eps run) ?\<A> (word_transformation_eps word) \<and> last (run_transformation_eps run) \<noteq> Inr()" using run unfolding kleene_star_auto_def run_accepting_def by force
  thus ?thesis by auto
qed

corollary originial_language_in_lang_kleene_star_auto:
  assumes "auto_well_defined \<A>"
  shows "language_auto \<A> \<subseteq> eps_free_language (language_auto (kleene_star_auto \<A>))"
proof -
  {
    fix word assume "word \<in> language_auto \<A>"
    hence word: "(word_transformation_eps word) \<in> language_auto (kleene_star_auto \<A>)" using assms run_accepting_kleene_star_auto unfolding language_auto_def by blast
    have "word_transformation_eps word = Inr() # map Inl word" unfolding word_transformation_eps_def by auto
    hence "evaluate_eps_word (word_transformation_eps word) = evaluate_eps_word (Inr() # map Inl word)" by auto
    hence "evaluate_eps_word (word_transformation_eps word) = evaluate_eps_word (map Inl word)" by auto
    hence equi: "evaluate_eps_word (word_transformation_eps word) = word" using inverse_evaluate_eps by auto  
    hence "word \<in> eps_free_language (language_auto (kleene_star_auto \<A>))" using word unfolding eps_free_language_def by force
  }
  thus ?thesis by auto
qed

proposition run_kleene_star_extension:
  assumes "run_accepting run (kleene_star_auto \<A>) word \<and> last word \<noteq> Inr() \<and> word \<noteq> []"
  shows "run_accepting (run @ [Inr()]) (kleene_star_auto \<A>) (word @ [Inr()])"
proof - 
  let ?\<A> = "kleene_star_auto \<A>"
  have prun: "pseudo_run_well_defined run ?\<A> (initial_state ?\<A>) word" using assms unfolding run_accepting_def run_well_defined_def by simp  
  hence last: "last run \<in> accepting_states ?\<A> \<and> length run > 1" using assms unfolding run_accepting_def pseudo_run_well_defined_def by simp
  hence "length run - 2 < length run - 1 \<and> run \<noteq> []" by auto
  hence trans: "(run ! (length run - 2), word ! (length run - 2), run ! (length run - 1)) \<in> transitions ?\<A> \<and> length run - 1 = length word \<and> run \<noteq> []" using prun last unfolding pseudo_run_well_defined_def by fastforce
  hence "last word = word ! (length run - 1 - 1)" using assms list_properties_not_empty by metis
  hence "last word = word ! (length run - 2)" using diff_diff_left nat_1_add_1 by presburger
  hence "(run ! (length run - 2), last word, last run) \<in> transitions ?\<A>" using trans list_properties_not_empty by metis
  hence "last run \<in> accepting_states ?\<A> \<and> last run \<noteq> Inr()" using last assms unfolding kleene_star_auto_def by fastforce
  then obtain y where "Inl y = last run" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
  hence "y \<in> accepting_states \<A> \<and> Inl y = last run" using last unfolding kleene_star_auto_def by force
  hence "(last run, Inr(), Inr()) \<in> transitions ?\<A>" unfolding kleene_star_auto_def by force
  hence "pseudo_run_well_defined (run @ [Inr()]) ?\<A> (initial_state ?\<A>) (word @ [Inr()])" using prun prun_well_defined_extension_snoc by fast
  hence "run_accepting (run @ [Inr()]) ?\<A> (word @ [Inr()])" unfolding run_well_defined_def run_accepting_def kleene_star_auto_def by fastforce
  thus ?thesis by blast
qed

proposition run_kleene_star_extension2:
  assumes "run_accepting (run @ [s]) (kleene_star_auto \<A>) (word @ [Inr()])"
  shows "run_accepting run (kleene_star_auto \<A>) word"
proof - 
  let ?\<A> = "kleene_star_auto \<A>"
  have "pseudo_run_well_defined (run @ [s]) ?\<A> (initial_state ?\<A>) (word @ [Inr()])" using assms unfolding run_accepting_def run_well_defined_def by simp  
  hence prun: "pseudo_run_well_defined run ?\<A> (initial_state ?\<A>) word \<and> (last run, Inr(), s) \<in> transitions ?\<A>" using prun_well_defined_extension_snoc by fast
  hence "last run = Inr() \<or> (\<exists> s' . last run = Inl s' \<and> s' \<in> accepting_states \<A>)" unfolding kleene_star_auto_def by auto
  hence "last run \<in> accepting_states ?\<A>" unfolding kleene_star_auto_def by auto
  thus ?thesis using prun unfolding run_well_defined_def run_accepting_def by auto
qed

fun evaluate_eps_run :: "('s + unit) run \<Rightarrow> 's run" where
  "evaluate_eps_run [] = []" |
  "evaluate_eps_run (Inl s # run) = s # evaluate_eps_run run" |
  "evaluate_eps_run (Inr() # run) = evaluate_eps_run run"

proposition evaluate_eps_run_snoc: "evaluate_eps_run (run1 @ run2) = evaluate_eps_run run1 @ evaluate_eps_run run2"
proof(induction run1 arbitrary: run2 rule: rev_induct)
  case Nil thus ?case by auto
next
  case (snoc x xs)
  hence "evaluate_eps_run ((xs @ [x]) @ run2) = evaluate_eps_run (xs @ (x # run2))" by force
  hence split: "evaluate_eps_run ((xs @ [x]) @ run2) = evaluate_eps_run xs @ evaluate_eps_run (x # run2)" using snoc by auto
  consider (case1) "x = Inr()" | (case2) "x \<noteq> Inr()" by auto
  thus ?case
  proof cases
    case case1 thus ?thesis using snoc by auto
  next
    case case2
    then obtain y where y: "Inl y = x" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    hence "evaluate_eps_run ((xs @ [x]) @ run2) = evaluate_eps_run xs @ [y] @ evaluate_eps_run run2" using split by auto
    hence "evaluate_eps_run ((xs @ [x]) @ run2) = evaluate_eps_run xs @ evaluate_eps_run [x] @ evaluate_eps_run run2" using y by auto
    thus ?thesis using snoc by force
  qed
qed

lemma last_evaluate_eps_run: "last list = Inl x \<and> list \<noteq> [] \<Longrightarrow> evaluate_eps_run list \<noteq> [] \<and> last (evaluate_eps_run list) = x"
proof(induction list)
  case Nil thus ?case by argo
next
  case (Cons y list)
  consider (case1) "list = []" | (case2) "list \<noteq> []" by argo 
  thus ?case
  proof cases
    case case1 thus ?thesis using Cons by force
  next
    case case2
    hence "last list = Inl x \<and> list \<noteq> []" using Cons by force
    hence last: "evaluate_eps_run list \<noteq> [] \<and> last (evaluate_eps_run list) = x" using Cons by fast
    consider (case3) "y = Inr()" | (case4) "y \<noteq> Inr()" by argo
    thus ?thesis
    proof cases
      case case3 thus ?thesis using last by simp
    next
      case case4
      then obtain y' where "Inl y' = y" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
      thus ?thesis using last by force
    qed
  qed
qed

proposition run_well_def_without_inr:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined run (kleene_star_auto \<A>) ([Inr()] @ word) \<and> Inr() \<notin> set word \<Longrightarrow> run_well_defined (evaluate_eps_run run) \<A> (evaluate_eps_word word)"
proof(induction word arbitrary: run rule: rev_induct)
  case Nil
  hence props: "length run = 2 \<and> run ! 0 = Inr() \<and> (Inr(), Inr(), run ! 1) \<in> transitions (kleene_star_auto \<A>)" unfolding run_well_defined_def pseudo_run_well_defined_def kleene_star_auto_def by force
  hence "run ! 1 = Inl (initial_state \<A>)" unfolding kleene_star_auto_def by force
  hence "run = [Inr(), Inl (initial_state \<A>)]" using props list_with_two_elements by fast
  hence eva_run: "evaluate_eps_run run = [initial_state \<A>]" by auto
  have "initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by auto
  hence "run_well_defined [initial_state \<A>] \<A> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  thus ?case using eva_run by auto
next
  let ?\<A> = "kleene_star_auto \<A>"
  case (snoc a word)
  hence "run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain run' where run': "run = run' @ [last run]" using append_butlast_last_id by metis
  hence run: "run_well_defined run' ?\<A> ([Inr()] @ word) \<and> (last run', a, last run) \<in> transitions ?\<A>" using append_assoc prun_well_defined_extension_snoc snoc unfolding run_well_defined_def by metis
  hence trans: "run_well_defined (evaluate_eps_run run') \<A> (evaluate_eps_word word) \<and> (last run', a, last run) \<in> transitions ?\<A>" using snoc by force
  have "a \<noteq> Inr()" using snoc by force
  hence im: "(last run', a, last run) \<in> (image (\<lambda>(s1, a, s2) . (Inl s1, Inl a, Inl s2)) (transitions \<A>))" using trans unfolding kleene_star_auto_def by force
  then obtain x y b where xyb: "Inl b = a \<and> Inl x = last run' \<and> Inl y = last run" using old.unit.exhaust sum.exhaust_sel by auto
  hence trans_in: "(x, b, y) \<in> transitions \<A>" using im unfolding kleene_star_auto_def by force
  have not_empty: "run' \<noteq> [] \<and> last run' = Inl x \<and> run \<noteq> [] \<and> last run = Inl y" using snoc run xyb unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence last: "last (evaluate_eps_run run') = x \<and> last (evaluate_eps_run run) = y" using last_evaluate_eps_run by force
  hence run_well_def: "run_well_defined ((evaluate_eps_run run') @ [last (evaluate_eps_run run)]) \<A> ((evaluate_eps_word word) @ [b])" using assms trans trans_in prun_well_defined_extension_snoc unfolding run_well_defined_def by fast
  have "evaluate_eps_run run = ((evaluate_eps_run run') @ [last (evaluate_eps_run run)])" using run' evaluate_eps_run_snoc not_empty last evaluate_eps_run.simps(1) evaluate_eps_run.simps(2) by metis
  hence final: "run_well_defined (evaluate_eps_run run) \<A> ((evaluate_eps_word word) @ [b])" using run_well_def by argo
  have "evaluate_eps_word (word @ [a]) = ((evaluate_eps_word word) @ [b])" using evaluate_eps_word_snoc evaluate_eps_word.simps(1) evaluate_eps_word.simps(2) xyb by metis
  thus ?case using final by argo
qed

theorem in_language_without_inr:
  assumes "auto_well_defined \<A>" "([Inr()] @ word) \<in> language_auto (kleene_star_auto \<A>)" "Inr() \<notin> set word"
  shows "evaluate_eps_word word \<in> language_auto \<A>"
proof -
  obtain run where run: "run_well_defined run (kleene_star_auto \<A>) ([Inr()] @ word) \<and> Inr() \<notin> set word \<and> last run \<in> accepting_states (kleene_star_auto \<A>)" using assms unfolding language_auto_def run_accepting_def by blast
  hence run_well_def: "run_well_defined (evaluate_eps_run run) \<A> (evaluate_eps_word word)" using assms run_well_def_without_inr by blast
  thus ?thesis
  proof(cases word)
    case Nil
    hence props: "length run = 2 \<and> run ! 0 = Inr() \<and> (Inr(), Inr(), run ! 1) \<in> transitions (kleene_star_auto \<A>)" using run unfolding run_well_defined_def pseudo_run_well_defined_def kleene_star_auto_def by force
    hence "run ! 1 = Inl (initial_state \<A>)" unfolding kleene_star_auto_def by force
    hence run2: "run = [Inr(), Inl (initial_state \<A>)]" using props list_with_two_elements by fast
    hence "Inl (initial_state \<A>) \<in> accepting_states (kleene_star_auto \<A>)" using run by force
    hence acc: "initial_state \<A> \<in> accepting_states \<A>" unfolding kleene_star_auto_def by force
    have "evaluate_eps_run run = [initial_state \<A>]" using run2 by force
    hence "last (evaluate_eps_run run) \<in> accepting_states \<A>" using acc by force
    thus ?thesis using run_well_def unfolding run_accepting_def language_auto_def by blast
  next
    case(Cons a list)
    hence not_empty: "word \<noteq> []" by simp
    hence last: "last run \<in> accepting_states (kleene_star_auto \<A>) \<and> length run > 1" using run assms unfolding run_well_defined_def pseudo_run_well_defined_def by simp
    hence "length run - 2 < length run - 1 \<and> run \<noteq> []" by auto
    hence trans: "(run ! (length run - 2), ([Inr()] @ word) ! (length run - 2), run ! (length run - 1)) \<in> transitions (kleene_star_auto \<A>) \<and> length run - 1 = length ([Inr()] @ word) \<and> run \<noteq> []" using run last unfolding run_well_defined_def pseudo_run_well_defined_def by force
    hence "last ([Inr()] @ word) = ([Inr()] @ word) ! (length run - 1 - 1)" using not_empty list_properties_not_empty by fastforce
    hence "last ([Inr()] @ word) = ([Inr()] @ word) ! (length run - 2)" using diff_diff_left nat_1_add_1 by presburger
    hence "last word = ([Inr()] @ word) ! (length run - 2)" using not_empty by simp
    hence "(run ! (length run - 2), last word, last run) \<in> transitions (kleene_star_auto \<A>)" using trans list_properties_not_empty by metis   
    hence "last run \<in> accepting_states (kleene_star_auto \<A>) \<and> last run \<noteq> Inr()" using last not_empty assms last_in_set unfolding kleene_star_auto_def by fastforce
    then obtain y where "Inl y = last run" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    hence "y \<in> accepting_states \<A> \<and> Inl y = last run \<and> run \<noteq> []" using last unfolding kleene_star_auto_def by force
    hence "last (evaluate_eps_run run) \<in> accepting_states \<A>" using last_evaluate_eps_run by metis
    thus ?thesis using run_well_def unfolding run_accepting_def language_auto_def by blast
  qed
qed

lemma empty_word_kleene_star: "[] \<in> language_auto (kleene_star_auto \<A>)"
proof -
  have prun: "pseudo_run_well_defined [initial_state (kleene_star_auto \<A>)] (kleene_star_auto \<A>) (initial_state (kleene_star_auto \<A>)) []" unfolding kleene_star_auto_def pseudo_run_well_defined_def by force
  have "initial_state (kleene_star_auto \<A>) \<in> accepting_states (kleene_star_auto \<A>)" unfolding kleene_star_auto_def by force
  thus ?thesis using prun unfolding run_well_defined_def run_accepting_def language_auto_def by auto
qed

lemma tl_transition:
  assumes "\<forall> i < length prun - 1 . (prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>"
  shows "\<forall> i < length (tl prun) - 1 . ((tl prun) ! i, word ! (i + 1), (tl prun) ! (i + 1)) \<in> transitions \<A>"
proof -
  {
    fix i assume "i < length (tl prun) - 1"
    hence assm: "i < length prun - 1 \<and> i + 1 < length prun - 1" by force
    hence trans: "(prun ! (i + 1), word ! (i + 1), prun ! (i + 1 + 1)) \<in> transitions \<A>" using assms by blast
    have "prun ! (i + 1) = (tl prun) ! i \<and> prun ! (i + 1 + 1) = (tl prun) ! (i + 1)" using assm j_pos_tl by metis
    hence "((tl prun) ! i, word ! (i + 1), (tl prun) ! (i + 1)) \<in> transitions \<A>" using trans by auto
  }
  thus ?thesis by blast
qed

lemma concatenation_of_words_in_lang_kleene_star_auto:
  assumes "word1 \<in> language_auto (kleene_star_auto \<A>) \<and> word2 \<in> language_auto (kleene_star_auto \<A>)"
  shows "word1 @ word2 \<in> language_auto (kleene_star_auto \<A>) \<or> word1 @ [Inr()] @ word2 \<in> language_auto (kleene_star_auto \<A>)"
proof -
  let ?\<A> = "kleene_star_auto \<A>"
  obtain run1 run2 where "run_accepting run1 ?\<A> word1 \<and> run_accepting run2 ?\<A> word2" using assms unfolding language_auto_def by blast
  hence pruns: "pseudo_run_well_defined run1 ?\<A> (initial_state ?\<A>) word1 \<and> last run1 \<in> accepting_states ?\<A> \<and> pseudo_run_well_defined run2 ?\<A> (initial_state ?\<A>) word2 \<and> last run2 \<in> accepting_states ?\<A>" unfolding run_accepting_def run_well_defined_def by auto
  consider (case1) "last run1 = Inr()" | (case2) "last run1 \<noteq> Inr()" by argo
  hence "run_accepting (run1 @ (tl run2)) ?\<A> (word1 @ word2) \<or> run_accepting (run1 @ run2) ?\<A> (word1 @ [Inr()] @ word2)"
  proof cases
    case case1
    have props: "length run1 = length word1 + 1 \<and> length run2 = length word2 + 1 \<and> length run1 > 0 \<and> run1 \<noteq> [] \<and> run2 \<noteq> [] \<and> run1 ! 0 \<in> states ?\<A>" using pruns unfolding pseudo_run_well_defined_def by force
    hence length: "length (run1 @ (tl run2)) = length (word1 @ word2) + 1" by simp
    have first: "(run1 @ (tl run2)) ! 0 = run1 ! 0" using props list_properties_not_empty by metis
    have "run1 ! 0 = initial_state ?\<A>" using pruns unfolding pseudo_run_well_defined_def by blast
    hence init: "(run1 @ (tl run2)) ! 0 \<in> states ?\<A> \<and> (run1 @ (tl run2)) ! 0 = initial_state ?\<A>" using props first by argo
    {
      fix i assume assm: "i < length (run1 @ (tl run2)) - 1"
      consider (case8) "i < length run1 - 1" | (case9) "i = length run1 - 1" | (case10) "i > length run1 - 1" by linarith
      hence "((run1 @ (tl run2)) ! i, (word1 @ word2) ! i, (run1 @ (tl run2)) ! (i + 1)) \<in> transitions ?\<A>"
      proof cases
        case case8
        hence equi: "(run1 @ (tl run2)) ! i = run1 ! i \<and> (run1 @ (tl run2)) ! (i + 1) = run1 ! (i + 1)" using props list_append_position4 by blast
        have word_equi: "(word1 @ word2) ! i = word1 ! i" using props case8 by (simp add: nth_append)
        have "(run1 ! i, word1 ! i, run1 ! (i + 1)) \<in> transitions ?\<A>" using pruns case8 unfolding pseudo_run_well_defined_def by blast
        thus ?thesis using equi word_equi by argo
      next
        case case9 thus ?thesis
        proof(cases "tl run2")
          case Nil thus ?thesis using case9 assm by fastforce
        next
          case (Cons a list)
          hence not_empty: "tl run2 \<noteq> []" by simp
          hence equi: "(run1 @ (tl run2)) ! i = last run1 \<and> (run1 @ (tl run2)) ! (i + 1) = (tl run2) ! 0" using props case9 list_append_position5 by fast
          have "word2 \<noteq> []" using props not_empty case9 assm by force
          hence word_equi: "(word1 @ word2) ! i = word2 ! 0" using props case9 by (simp add: nth_append)
          have last_equi: "run2 ! 0 = last run1" using case1 pruns unfolding pseudo_run_well_defined_def kleene_star_auto_def by simp
          have "length run2 > 1" using not_empty tl_more_elements by blast
          hence "(run2 ! 0, word2 ! 0, run2 ! 1) \<in> transitions ?\<A>" using pruns not_empty unfolding pseudo_run_well_defined_def by fastforce
          hence "(last run1, word2 ! 0, (tl run2) ! 0) \<in> transitions ?\<A>" using not_empty last_equi tl_more_elements2 by force
          thus ?thesis using equi word_equi by argo
        qed
      next
        case case10 thus ?thesis
        proof(cases "tl run2")
          case Nil thus ?thesis using case10 assm by force
        next
          case(Cons a list)
          hence "tl run2 \<noteq> []" by simp
          hence equi: "(run1 @ (tl run2)) ! i = (tl run2) ! (i - length run1) \<and> (run1 @ (tl run2)) ! (i + 1) = (tl run2) ! (i + 1 - length run1)" using props list_append_position6 assm case10 by blast
          have word_equi: "(word1 @ word2) ! i = word2 ! (i - length run1 + 1)" using props case10 Suc_diff_Suc by (simp add: nth_append)
          have "(i - length run1) < length (tl run2) - 1" using case10 assm props by auto
          hence trans: "((tl run2) ! (i - length run1), word2 ! (i - length run1 + 1), (tl run2) ! (i - length run1 + 1)) \<in> transitions ?\<A>" using pruns tl_transition unfolding pseudo_run_well_defined_def by blast
          have "i - length run1 + 1 = i + 1 - length run1" using case10 by force
          hence "((tl run2) ! (i - length run1), word2 ! (i - length run1 + 1), (tl run2) ! (i + 1 - length run1)) \<in> transitions ?\<A>" using trans by argo
          thus ?thesis using equi word_equi by argo
        qed
      qed
    }
    hence "\<forall> i < length (run1 @ (tl run2)) - 1 . ((run1 @ (tl run2)) ! i, (word1 @ word2) ! i, (run1 @ (tl run2)) ! (i + 1)) \<in> transitions ?\<A>" by blast
    hence prun: "pseudo_run_well_defined (run1 @ (tl run2)) ?\<A> (initial_state ?\<A>) (word1 @ word2)" using length init unfolding pseudo_run_well_defined_def by fastforce
    hence "last (run1 @ (tl run2)) \<in> accepting_states ?\<A>" 
    proof(cases "tl run2")
      case Nil thus ?thesis using pruns by auto
    next
      case (Cons a list) 
      hence "tl run2 \<noteq> []" by simp
      thus ?thesis using pruns by (simp add: last_tl)
    qed
    thus ?thesis using prun unfolding run_well_defined_def run_accepting_def by blast
  next
    case case2
    have props: "length run1 = length word1 + 1 \<and> length run2 = length word2 + 1 \<and> run1 \<noteq> [] \<and> run2 \<noteq> [] \<and> run1 ! 0 \<in> states ?\<A>" using pruns unfolding pseudo_run_well_defined_def by force
    hence length: "length (run1 @ run2) = length (word1 @ [Inr()] @ word2) + 1" by simp
    have first: "(run1 @ run2) ! 0 = run1 ! 0" using props list_properties_not_empty by metis
    have "run1 ! 0 = initial_state ?\<A>" using pruns unfolding pseudo_run_well_defined_def by blast
    hence init: "(run1 @ run2) ! 0 \<in> states ?\<A> \<and> (run1 @ run2) ! 0 = initial_state ?\<A>" using props first by argo
    have "last (run1 @ run2) = last run2" using props by auto
    hence last: "last (run1 @ run2) \<in> accepting_states ?\<A>" using pruns by argo
    {
      fix i assume assm: "i < length (run1 @ run2) - 1"
      consider (case5) "i < length run1 - 1" | (case6) "i = length run1 - 1" | (case7) "i > length run1 - 1" by linarith
      hence "((run1 @ run2) ! i, (word1 @ [Inr()] @ word2) ! i, (run1 @ run2) ! (i + 1)) \<in> transitions ?\<A>"
      proof cases
        case case5
        hence equi: "(run1 @ run2) ! i = run1 ! i \<and> (run1 @ run2) ! (i + 1) = run1 ! (i + 1)" using props list_append_position4 by blast
        have word_equi: "(word1 @ [Inr()] @ word2) ! i = word1 ! i" using props case5 by (simp add: nth_append)
        have "(run1 ! i, word1 ! i, run1 ! (i + 1)) \<in> transitions ?\<A>" using pruns case5 unfolding pseudo_run_well_defined_def by blast
        thus ?thesis using equi word_equi by argo
      next
        case case6
        hence equi: "(run1 @ run2) ! i = last run1 \<and> (run1 @ run2) ! (i + 1) = run2 ! 0" using props list_append_position5 by fast
        have word_equi: "(word1 @ [Inr()] @ word2) ! i = Inr()" using props case6 by simp
        have "last run1 \<in> accepting_states ?\<A> \<and> last run1 \<noteq> Inr() \<and> run2 ! 0 = initial_state ?\<A>" using case2 pruns unfolding pseudo_run_well_defined_def by blast
        hence "(last run1, Inr(), run2 ! 0) \<in> transitions ?\<A>" unfolding kleene_star_auto_def by fastforce
        thus ?thesis using equi word_equi by presburger
      next
        case case7
        hence equi: "(run1 @ run2) ! i = run2 ! (i - length run1) \<and> (run1 @ run2) ! (i + 1) = run2 ! (i + 1 - length run1)" using props list_append_position6 assm by blast
        have word_equi: "(word1 @ [Inr()] @ word2) ! i = word2 ! (i - length run1)" using props case7 by (simp add: nth_append)
        have "(i - length run1) < length run2 - 1" using case7 assm props by auto
        hence trans: "(run2 ! (i - length run1), word2 ! (i - length run1), run2 ! (i - length run1 + 1)) \<in> transitions ?\<A>" using pruns unfolding pseudo_run_well_defined_def by blast
        have "i - length run1 + 1 = i + 1 - length run1" using case7 by force
        hence "(run2 ! (i - length run1), word2 ! (i - length run1), run2 ! (i + 1 - length run1)) \<in> transitions ?\<A>" using trans by argo
        thus ?thesis using equi word_equi by argo
      qed
    }
    hence "\<forall> i < length (run1 @ run2) - 1 . ((run1 @ run2) ! i, (word1 @ [Inr()] @ word2) ! i, (run1 @ run2) ! (i + 1)) \<in> transitions ?\<A>" by blast
    hence "pseudo_run_well_defined (run1 @ run2) ?\<A> (initial_state ?\<A>) (word1 @ [Inr()] @ word2)" using length init unfolding pseudo_run_well_defined_def by fastforce
    thus ?thesis using last unfolding run_well_defined_def run_accepting_def by blast
  qed
  thus ?thesis unfolding language_auto_def by blast
qed

theorem kleene_star_helper_language_left:
  assumes "auto_well_defined \<A>"
  shows "kleene_star_language_helper (language_auto \<A>) i \<subseteq> eps_free_language (language_auto (kleene_star_auto \<A>))"
proof(induction i)
  case 0 thus ?case using empty_word_kleene_star unfolding eps_free_language_def by force
next
  case (Suc i)
  {
    fix word assume "word \<in> kleene_star_language_helper (language_auto \<A>) (Suc i)"
    hence "word \<in> concatenation_language (kleene_star_language_helper (language_auto \<A>) i) (language_auto \<A>)" by simp
    then obtain word1 word2 where word: "word1 \<in> (kleene_star_language_helper (language_auto \<A>) i) \<and> word2 \<in> language_auto \<A> \<and> word = word1 @ word2" unfolding concatenation_language_def by fast
    hence "word1 \<in> eps_free_language (language_auto (kleene_star_auto \<A>)) \<and> word2 \<in> eps_free_language (language_auto (kleene_star_auto \<A>))" using assms Suc originial_language_in_lang_kleene_star_auto by blast
    then obtain word1' word2' where words': "word1' \<in> language_auto (kleene_star_auto \<A>) \<and> evaluate_eps_word word1' = word1 \<and> word2' \<in> language_auto (kleene_star_auto \<A>) \<and> evaluate_eps_word word2' = word2" unfolding eps_free_language_def by force
    hence "word1' @ word2' \<in> language_auto (kleene_star_auto \<A>) \<or> word1' @ [Inr()] @ word2' \<in> language_auto (kleene_star_auto \<A>)" using concatenation_of_words_in_lang_kleene_star_auto by blast
    then consider (case1) "word1' @ word2' \<in> language_auto (kleene_star_auto \<A>)" | (case2) "word1' @ [Inr()] @ word2' \<in> language_auto (kleene_star_auto \<A>)" by blast
    hence "word \<in> eps_free_language (language_auto (kleene_star_auto \<A>))"
    proof cases
      case case1
      hence "evaluate_eps_word (word1' @ word2') \<in> eps_free_language (language_auto (kleene_star_auto \<A>))" unfolding eps_free_language_def by blast
      thus ?thesis using words' word evaluate_eps_word_snoc by metis
    next
      case case2
      hence "evaluate_eps_word (word1' @ [Inr()] @ word2') \<in> eps_free_language (language_auto (kleene_star_auto \<A>))" unfolding eps_free_language_def by blast
      hence "evaluate_eps_word word1' @ evaluate_eps_word [Inr()] @ evaluate_eps_word word2' \<in> eps_free_language (language_auto (kleene_star_auto \<A>))" using evaluate_eps_word_snoc by metis
      hence "evaluate_eps_word word1' @ evaluate_eps_word word2' \<in> eps_free_language (language_auto (kleene_star_auto \<A>))" by simp
      thus ?thesis using words' word by simp
    qed
  }
  thus ?case by blast
qed

corollary kleene_star_language_left:
  assumes "auto_well_defined \<A>"
  shows "kleene_star_language (language_auto \<A>) \<subseteq> eps_free_language (language_auto (kleene_star_auto \<A>))"
  using assms kleene_star_helper_language_left unfolding kleene_star_language_def by blast

fun inr_counter :: "('a + unit) word \<Rightarrow> nat" where
  "inr_counter [] = 0" |
  "inr_counter (Inr() # word) = 1 + inr_counter word" |
  "inr_counter (Inl a # word) = inr_counter word"

proposition inr_counter_append: "inr_counter (word1 @ word2) = inr_counter word1 + inr_counter word2"
proof(induction word1 arbitrary: word2 rule: rev_induct)
  case Nil thus ?case by auto
next
  case (snoc x xs)
  hence "inr_counter ((xs @ [x]) @ word2) = inr_counter (xs @ (x # word2))" by force
  hence split: "inr_counter ((xs @ [x]) @ word2) = inr_counter xs + inr_counter (x # word2)" using snoc by auto
  consider (case1) "x = Inr()" | (case2) "x \<noteq> Inr()" by auto
  thus ?case
  proof cases
    case case1 thus ?thesis using snoc by auto
  next
    case case2
    then obtain y where y: "Inl y = x" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
    hence "inr_counter ((xs @ [x]) @ word2) = inr_counter xs + inr_counter (x # word2)" using split by auto
    hence "inr_counter ((xs @ [x]) @ word2) = inr_counter xs + inr_counter [x] + inr_counter word2" using y by auto
    thus ?thesis using snoc by force
  qed
qed

lemma inr_counter_not_zero: "length word > 0 \<and> word ! 0 = Inr() \<Longrightarrow> inr_counter word > 0"
  by (induction word) auto

lemma inr_in_set_word: "Inr() \<in> set word \<Longrightarrow> inr_counter word > 0"
proof(induction word)
  case Nil thus ?case by simp
next
  case (Cons a word)
  consider (case1) "Inr() \<in> set word" | (case2) "Inr() \<notin> set word" by auto
  thus ?case
  proof cases
    case case1
    hence props: "Inr() \<in> set (a # word) \<and> inr_counter word > 0" using Cons by auto
    hence "(a # word) = [a] @ word" by simp
    hence "inr_counter (a # word) = inr_counter [a] + inr_counter word" using inr_counter_append by metis
    thus ?thesis using props by auto
  next
    case case2
    hence "Inr() = a" using Cons by auto
    thus ?thesis by auto
  qed
qed

lemma inr_not_in_set_word: "Inr() \<notin> set word \<Longrightarrow> inr_counter word = 0"
proof(induction word)
  case Nil thus ?case by simp
next
  case (Cons a word)
  hence "Inr() \<notin> set word \<and> a \<noteq> Inr()" by auto
  hence "a \<noteq> Inr() \<and> inr_counter word = 0" using Cons by auto
  then obtain b where b: "Inl b = a \<and> inr_counter word = 0" using old.unit.exhaust sum.exhaust_sel by (metis (full_types))
  thus ?case by force
qed 

lemma inr_counter_ge_0: "inr_counter word > 0 \<Longrightarrow> Inr() \<in> set word"
  using inr_not_in_set_word by fastforce

proposition greater_inr_counter: "inr_counter word > 0 \<longleftrightarrow> Inr() \<in> set word"
  using inr_counter_ge_0 inr_in_set_word by blast

lemma length_run_kleene_star_auto:
  assumes "pseudo_run_well_defined run (kleene_star_auto \<A>) (initial_state (kleene_star_auto \<A>)) word" "inr_counter word = 0"
  shows "length run = 1"
proof(rule ccontr)
  assume "\<not> length run = 1"
  hence len: "length run = 0 \<or> length run > 1" by linarith
  have "run ! 0 = Inr() \<and> length run = length word + 1" using assms unfolding pseudo_run_well_defined_def kleene_star_auto_def by simp
  hence "length run > 1 \<and> run ! 0 = Inr()" using len by force
  hence "length word > 0 \<and> (run ! 0, word ! 0, run ! 1) \<in> transitions (kleene_star_auto \<A>) \<and> run ! 0 = Inr()" using assms unfolding pseudo_run_well_defined_def by fastforce
  hence "length word > 0 \<and> word ! 0 = Inr()" unfolding kleene_star_auto_def by force
  hence "inr_counter word > 0" using inr_counter_not_zero by blast
  thus False using assms by force
qed

lemma s_is_inr:
  assumes "(s, Inr(), run ! 1) \<in> transitions (kleene_star_auto \<A>) \<and> (run ! 1, (a # word) ! 1, run ! 2) \<in> transitions (kleene_star_auto \<A>)" "s = Inr() \<or> (\<exists> s' . s = Inl s' \<and> s' \<in> accepting_states \<A>)" "(a # word) ! 1 \<noteq> Inr()"
  shows "s = Inr()"
proof(rule ccontr)
  assume "s \<noteq> Inr()"
  hence "(\<exists> s' . s = Inl s' \<and> s' \<in> accepting_states \<A>)" using assms by argo
  then obtain s' where "s = Inl s' \<and> s' \<in> accepting_states \<A>" by blast
  hence "run ! 1 = Inr()" using assms unfolding kleene_star_auto_def by auto
  hence "(Inr(), (a # word) ! 1, run ! 2) \<in> transitions (kleene_star_auto \<A>)" using assms by argo
  hence "(a # word) ! 1 = Inr()" unfolding kleene_star_auto_def by auto
  thus False using assms by blast
qed

lemma last_and_first_of_subruns:
  assumes "auto_well_defined \<A>"
  shows "k < length word \<and> word ! k = Inr() \<and> Inr() \<notin> set (sublist (Suc k) (length word) word) \<and> pseudo_run_well_defined run (kleene_star_auto \<A>) s word \<and> last word \<noteq> Inr() \<Longrightarrow> last (take (Suc k) run) \<in> accepting_states (kleene_star_auto \<A>) \<and> (sublist k (length run) run) ! 0 = initial_state (kleene_star_auto \<A>)"
proof(induction word arbitrary: run s k)
  case Nil thus ?case by force
next
  case (Cons a word)
  consider (case1) "word = []" | (case2) "word \<noteq> []" by argo
  thus ?case
  proof cases
    case case1 thus ?thesis using Cons case1 by force
  next
    case case2 thus ?thesis
    proof(cases k)
      case 0
      hence a: "a = Inr() \<and> (sublist (Suc k) (length (a # word)) (a # word)) = word" using Cons unfolding sublist_def by auto
      have len: "length run = length (a # word) + 1" using Cons unfolding pseudo_run_well_defined_def by blast
      hence "length run > 2" using case2 by force
      hence run_len: "length run - 1 > 1" by linarith
      have props: "(take (Suc k) run) =  [run ! 0] \<and> (sublist k (length run) run) = run" using 0 len unfolding sublist_def by (induction run) auto
      hence first: "(sublist k (length run) run) ! 0 = s" using Cons unfolding pseudo_run_well_defined_def by argo
      have last: "last (take (Suc k) run) = s" using props Cons unfolding pseudo_run_well_defined_def by auto
      have "\<forall> i < length run - 1 . (run ! i, (a # word) ! i, run ! (i + 1)) \<in> transitions (kleene_star_auto \<A>)" using Cons unfolding pseudo_run_well_defined_def by argo
      hence "(run ! 0, (a # word) ! 0, run ! 1) \<in> transitions (kleene_star_auto \<A>) \<and> (run ! 1, (a # word) ! 1, run ! (1 + 1)) \<in> transitions (kleene_star_auto \<A>)" using run_len by fastforce 
      hence trans: "(s, Inr(), run ! 1) \<in> transitions (kleene_star_auto \<A>) \<and> (run ! 1, (a # word) ! 1, run ! 2) \<in> transitions (kleene_star_auto \<A>)" using a nat_1_add_1 nth_Cons_0 Cons unfolding pseudo_run_well_defined_def by metis
      hence "(s, Inr(), run ! 1) \<in> transitions (kleene_star_auto \<A>)" using a by argo
      hence or: "s = Inr() \<or> (\<exists> s' . s = Inl s' \<and> s' \<in> accepting_states \<A>)" unfolding kleene_star_auto_def by auto
      hence acc: "s \<in> accepting_states (kleene_star_auto \<A>)" unfolding kleene_star_auto_def by auto
      have word_equi: "(a # word) ! 1 = word ! 0" by auto
      have "sublist (Suc k) (length (a # word)) (a # word) = word" using 0 unfolding sublist_def by auto
      hence "Inr() \<notin> set word" using Cons by argo 
      hence "(a # word) ! 1 \<noteq> Inr()" using word_equi case2 nth_mem by force
      hence "s = Inr()" using s_is_inr or trans s_is_inr by blast
      thus ?thesis using first last acc unfolding kleene_star_auto_def by force
    next
      have well_def: "auto_well_defined (kleene_star_auto \<A>)" using assms kleene_star_auto_well_defined by blast
      case(Suc nat)
      hence not_empty: "run \<noteq> [] \<and> run ! 0 = s" using Cons unfolding pseudo_run_well_defined_def by fastforce
      then obtain run' s' where equi: "run = (s' # run')" using list.collapse by metis
      hence "s = s'" using not_empty by auto 
      hence run_ind: "pseudo_run_well_defined run' (kleene_star_auto \<A>) (run' ! 0) word \<and> (s, a, (run' ! 0)) \<in> transitions (kleene_star_auto \<A>)" using equi well_def prun_well_defined_extension_cons Cons by metis
      hence run': "run' \<noteq> []" unfolding pseudo_run_well_defined_def by fastforce
      have "k - 1 < length word \<and> last word \<noteq> Inr() \<and> word ! (k - 1) = Inr() \<and> Inr() \<notin> set (sublist (Suc (k - 1)) (length word) word)" using Suc case2 Cons unfolding sublist_def by force
      hence "last (take (Suc (k - 1)) run') \<in> accepting_states (kleene_star_auto \<A>) \<and> (sublist (k - 1) (length run') run') ! 0 = initial_state (kleene_star_auto \<A>)" using Cons run_ind by blast
      hence "last (take (Suc k) run) \<in> accepting_states (kleene_star_auto \<A>) \<and> (sublist k (length run) run) ! 0 = initial_state (kleene_star_auto \<A>)" using equi Suc run' unfolding sublist_def by (simp add: drop_Cons')
      thus ?thesis by argo
    qed
  qed
qed

theorem kleene_star_helper_language_right:
  assumes "auto_well_defined \<A>"
  shows "word \<in> language_auto (kleene_star_auto \<A>) \<and> inr_counter word = i \<Longrightarrow> \<exists> j . j \<le> i \<and> evaluate_eps_word word \<in> kleene_star_language_helper (language_auto \<A>) j"
proof(induction i arbitrary: word)
  let ?\<A> = "kleene_star_auto \<A>"
  case 0
  then obtain run where "run_accepting run ?\<A> word" unfolding language_auto_def by blast
  hence prun: "pseudo_run_well_defined run ?\<A> (initial_state ?\<A>) word" unfolding run_accepting_def run_well_defined_def by simp
  hence "length run = 1" using length_run_kleene_star_auto 0 by blast
  hence "word = []" using prun unfolding pseudo_run_well_defined_def by force
  thus ?case by simp 
next
  case (Suc i)
  hence not_empty: "Inr() \<in> set word \<and> word \<noteq> []" using greater_inr_counter by fastforce
  consider (case1) "last word = Inr()" | (case2) "last word \<noteq> Inr()" by argo 
  thus ?case
  proof cases
    let ?\<A> = "kleene_star_auto \<A>"
    case case1
    then obtain run where run: "run_accepting run ?\<A> word" using Suc unfolding language_auto_def by blast
    hence "run \<noteq> [] \<and> word \<noteq> []" using not_empty unfolding pseudo_run_well_defined_def run_well_defined_def run_accepting_def by force
    then obtain run' s' word' where equi: "run = (run' @ [s']) \<and> word = (word' @ [Inr()])" using case1 append_butlast_last_id by metis
    hence "run_accepting run' ?\<A> word'" using run run_kleene_star_extension2 by blast
    hence in_lang: "word' \<in> language_auto ?\<A>" unfolding language_auto_def by auto
    have "inr_counter word = inr_counter word' + 1" using equi inr_counter_append by (simp add: inr_counter_append)
    hence "inr_counter word' = i" using Suc by fastforce
    then obtain j where j: "j \<le> i \<and> evaluate_eps_word word' \<in> kleene_star_language_helper (language_auto \<A>) j" using Suc in_lang by presburger
    have "evaluate_eps_word word = evaluate_eps_word word'" using equi by (simp add: evaluate_eps_word_snoc)
    hence "evaluate_eps_word word \<in> kleene_star_language_helper (language_auto \<A>) j \<and> j \<le> Suc i" using j by force
    thus ?thesis by blast
  next
    let ?\<A> = "kleene_star_auto \<A>"
    have well_def: "auto_well_defined ?\<A>" using assms kleene_star_auto_well_defined by auto
    case case2
    have "\<exists> i < length word . word ! i = Inr() \<and> Inr() \<notin> set (sublist (Suc i) (length word) word)" using not_empty maximal_index_for_element by fast
    then obtain k where k: "k < length word \<and> word ! k = Inr() \<and> Inr() \<notin> set (sublist (Suc k) (length word) word)" by blast
    obtain run where run: "run_accepting run ?\<A> word" using Suc unfolding language_auto_def by blast
    let ?subword1 = "take k word"
    let ?subword2 = "sublist k (length word) word"
    let ?subrun1 = "take (Suc k) run"
    let ?subrun2 = "sublist k (length run) run"
    have last_word: "last word \<noteq> Inr()" using case2 k by argo
    hence suc_word: "Suc k < length word" using not_empty last_and_take_list k not_le_imp_less take_all by metis
    hence props: "?subword2 \<noteq> [] \<and> ?subword2 ! 0 = Inr() \<and> Inr() \<notin> set (tl ?subword2)" using k tl_subword unfolding sublist_def by force
    hence equi2: "?subword2 = [Inr()] @ (tl ?subword2)" using list_properties_not_empty by fastforce
    hence "inr_counter ?subword2 = inr_counter ([Inr()] @ (tl ?subword2))" by simp
    hence "inr_counter ?subword2 = inr_counter [Inr()] + inr_counter (tl ?subword2)" using inr_counter_append by force
    hence counter2: "inr_counter ?subword2 = 1" using props inr_not_in_set_word by auto
    have "word = ?subword1 @ ?subword2" unfolding sublist_def by simp
    hence "inr_counter word = inr_counter ?subword1 + inr_counter ?subword2" using inr_counter_append by metis
    hence "Suc i = inr_counter ?subword1 + 1" using Suc counter2 by argo
    hence counter1: "inr_counter ?subword1 = i" by force
    have last_and_first: "last ?subrun1 \<in> accepting_states ?\<A> \<and> ?subrun2 ! 0 = initial_state ?\<A>" using assms last_and_first_of_subruns k last_word run unfolding run_accepting_def run_well_defined_def by blast 
    have "?subrun1 ! 0 = run ! 0" by auto
    hence first: "?subrun1 ! 0 = initial_state ?\<A>" using run unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by argo
    have "k < length run \<and> run \<noteq> []" using run k unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by fastforce
    hence "last run = last ?subrun2" unfolding sublist_def by auto
    hence last: "last ?subrun2 \<in> accepting_states ?\<A>" using run unfolding run_accepting_def by simp
    have len_prop: "length run = length word + 1 \<and> (\<forall> i < length run - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions ?\<A>)" using run unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by blast
    hence len1: "length ?subrun1 = length ?subword1 + 1" by auto
    have "\<forall> i < length ?subrun1 - 1 . (?subrun1 ! i, ?subword1 ! i, ?subrun1 ! (i + 1)) \<in> transitions ?\<A>" using len_prop by force
    hence "pseudo_run_well_defined ?subrun1 ?\<A> (initial_state ?\<A>) ?subword1" using len1 first well_def unfolding auto_well_defined_def pseudo_run_well_defined_def by blast
    hence "run_accepting ?subrun1 ?\<A> ?subword1" using last_and_first unfolding run_accepting_def run_well_defined_def by blast
    hence "?subword1 \<in> language_auto ?\<A> \<and> inr_counter ?subword1 = i" using counter1 unfolding language_auto_def by blast
    hence "\<exists> j . j \<le> i \<and> evaluate_eps_word ?subword1 \<in> kleene_star_language_helper (language_auto \<A>) j" using Suc by blast
    then obtain j where j: "j \<le> i \<and> evaluate_eps_word ?subword1 \<in> kleene_star_language_helper (language_auto \<A>) j" by blast
    have len_s2: "length ?subrun2 = length run - k" unfolding sublist_def by auto
    have "length ?subword2 = length word - k" unfolding sublist_def by auto
    hence len2: "length ?subrun2 = length ?subword2 + 1" using len_s2 len_prop k by linarith
    {
      fix n assume assm: "n < length ?subrun2 - 1"
      hence run_n: "run ! (k + n) = ?subrun2 ! n" unfolding sublist_def by auto
      have run_n1: "run ! (k + n + 1) = ?subrun2 ! (n + 1)" using assm unfolding sublist_def by simp
      have word_n: "word ! (k + n) = ?subword2 ! n" using assm suc_word unfolding sublist_def by force
      have "(run ! (k + n), word ! (k + n), run ! (k + n + 1)) \<in> transitions ?\<A>" using len_prop assm len_s2 by simp
      hence "(?subrun2 ! n, ?subword2 ! n, ?subrun2 ! (n + 1)) \<in> transitions ?\<A>" using run_n run_n1 word_n by argo
    } 
    hence "\<forall> i < length ?subrun2 - 1 . (?subrun2 ! i, ?subword2 ! i, ?subrun2 ! (i + 1)) \<in> transitions ?\<A>" by blast
    hence "pseudo_run_well_defined ?subrun2 ?\<A> (initial_state ?\<A>) ?subword2" using len2 last_and_first well_def unfolding auto_well_defined_def pseudo_run_well_defined_def by blast
    hence "run_accepting ?subrun2 ?\<A> ?subword2" using last unfolding run_accepting_def run_well_defined_def by blast
    hence "?subword2 \<in> language_auto ?\<A>" unfolding language_auto_def by blast 
    hence "([Inr()] @ (tl ?subword2)) \<in> language_auto ?\<A> \<and> Inr() \<notin> set (tl ?subword2)" using equi2 props by argo
    hence in_lang: "evaluate_eps_word (tl ?subword2) \<in> language_auto \<A>" using assms in_language_without_inr by blast
    have "evaluate_eps_word ?subword2 = evaluate_eps_word [Inr()] @ evaluate_eps_word (tl ?subword2)" using equi2 evaluate_eps_word_snoc by metis
    hence "evaluate_eps_word ?subword2 = evaluate_eps_word (tl ?subword2)" by simp
    hence s2_lang: "evaluate_eps_word ?subword2 \<in> language_auto \<A>" using in_lang by simp
    have "kleene_star_language_helper (language_auto \<A>) (Suc j) = concatenation_language (kleene_star_language_helper (language_auto \<A>) j) (language_auto \<A>)" by simp
    hence "kleene_star_language_helper (language_auto \<A>) (Suc j) = {word1 @ word2 | word1 word2 . word1 \<in> (kleene_star_language_helper (language_auto \<A>) j) \<and> word2 \<in> (language_auto \<A>)}" unfolding concatenation_language_def by blast
    hence "((evaluate_eps_word ?subword1) @ (evaluate_eps_word ?subword2)) \<in> kleene_star_language_helper (language_auto \<A>) (Suc j)" using j s2_lang by blast
    hence "(evaluate_eps_word (?subword1 @ ?subword2)) \<in> kleene_star_language_helper (language_auto \<A>) (Suc j)" using evaluate_eps_word_snoc by metis
    hence "evaluate_eps_word word \<in> kleene_star_language_helper (language_auto \<A>) (Suc j)" unfolding sublist_def by auto
    thus ?thesis using j by fast
  qed
qed

corollary kleene_star_language_right:
  assumes "auto_well_defined \<A>"
  shows "eps_free_language (language_auto (kleene_star_auto \<A>)) \<subseteq> kleene_star_language (language_auto \<A>)"
proof -
  {
    fix word assume "word \<in> eps_free_language (language_auto (kleene_star_auto \<A>))"
    then obtain word' where word: "word = evaluate_eps_word word' \<and> word' \<in> language_auto (kleene_star_auto \<A>)" unfolding eps_free_language_def by fast
    hence "\<exists> j . evaluate_eps_word word' \<in> kleene_star_language_helper (language_auto \<A>) j" using assms kleene_star_helper_language_right by blast
    hence "evaluate_eps_word word' \<in> kleene_star_language (language_auto \<A>)" unfolding kleene_star_language_def by blast
    hence "word \<in> kleene_star_language (language_auto \<A>)" using word by simp
  }
  thus ?thesis by force
qed

theorem kleene_star_language_correctness:
  assumes "auto_well_defined \<A>"
  shows "eps_free_language (language_auto (kleene_star_auto \<A>)) = kleene_star_language (language_auto \<A>)"
  using assms kleene_star_language_right kleene_star_language_left by blast

corollary kleene_star_main:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)"
  shows "\<exists> kleene_star_\<A> :: ('s + unit, 'a + unit) automaton . auto_well_defined kleene_star_\<A> \<and> alphabet kleene_star_\<A> = image Inl (alphabet \<A>) \<union> {Inr()} \<and> eps_free_language (language_auto kleene_star_\<A>) = kleene_star_language (language_auto \<A>)"
  using assms kleene_star_language_correctness kleene_star_auto_well_defined kleene_star_alphabet by metis

theorem kleene_star_eps_free_main:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> kleene_star_\<A> :: ('s, 'a) automaton . auto_well_defined kleene_star_\<A> \<and> alphabet kleene_star_\<A> = alphabet \<A> \<and> language_auto kleene_star_\<A> = kleene_star_language (language_auto \<A>)"
proof -
  have "\<exists> \<A>' :: ('s + unit, 'a + unit) automaton . auto_well_defined \<A>' \<and> alphabet \<A>' = image Inl (alphabet \<A>) \<union> {Inr()} \<and> eps_free_language (language_auto \<A>') = kleene_star_language (language_auto \<A>)" using assms kleene_star_main by blast
  hence "\<exists> eps_free_\<A> :: ('s + unit, 'a) automaton . auto_well_defined eps_free_\<A> \<and> alphabet eps_free_\<A> = {a . Inl a \<in> ((image Inl (alphabet \<A>)) \<union> {Inr()})} \<and> language_auto eps_free_\<A> = kleene_star_language (language_auto \<A>)" using eps_main unfolding original_alphabet_def by fastforce
  hence "\<exists> kleene_star_\<A> :: ('s + unit, 'a) automaton . auto_well_defined kleene_star_\<A> \<and> alphabet kleene_star_\<A> = alphabet \<A> \<and> language_auto kleene_star_\<A> = kleene_star_language (language_auto \<A>)" using conc_alpha_and_eps_alpha by fast
  thus ?thesis using assms existence_soft_iso_auto_lang by metis
qed

end