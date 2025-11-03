theory automaton_iterativ

imports Main automaton_reachability automaton_epsilon_transitions

begin

text \<open>Author: Benno Thalmann, last update: 29.10.2025, Addition to masterarbeit_benno_thalmann\<close>

text \<open>Since for a DFA there will be always one run, we can extract it\<close>
fun return_run_helper :: "'s state \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a word \<Rightarrow> 's run" where
  "return_run_helper s1 \<A> [] = []" |
  "return_run_helper s1 \<A> (a # as) = (THE s2 . s2 \<in> states \<A> \<and> (s1, a, s2) \<in> transitions \<A>) # return_run_helper (THE s2 . s2 \<in> states \<A> \<and> (s1, a, s2) \<in> transitions \<A>) \<A> as"

definition return_run :: "'a word \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 's run" where "return_run word \<A> = (initial_state \<A>) # return_run_helper (initial_state \<A>) \<A> word"

proposition "return_run [] \<A> = [initial_state \<A>]"
  unfolding return_run_def by force

lemma run_states_return_run_helper:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "word_well_defined word (alphabet \<A>) \<and> s1 \<in> states \<A> \<Longrightarrow> prun_states (return_run_helper s1 \<A> word) \<A>"
proof(induction word arbitrary: s1)
  case Nil thus ?case unfolding prun_states_def by auto
next
  case (Cons a word)
  hence "a \<in> alphabet \<A> \<and> s1 \<in> states \<A>" unfolding word_well_defined_def by auto
  hence "\<exists>! s2 \<in> states \<A> . (s1, a, s2) \<in> transitions \<A>" using assms unfolding DFA_property_def by auto
  then obtain s where s: "(THE s2 . s2 \<in> states \<A> \<and> (s1, a, s2) \<in> transitions \<A>) = s \<and> s \<in> states \<A> \<and> (s1, a, s) \<in> transitions \<A>" by blast
  hence return_run: "return_run_helper s1 \<A> (a # word) = s # return_run_helper s \<A> word" using return_run_helper.simps by auto
  have "word_well_defined word (alphabet \<A>)" using Cons word_well_def_cons by fast
  hence "prun_states (return_run_helper s \<A> word) \<A>" using s Cons unfolding prun_states_def by blast
  thus ?case using s return_run unfolding prun_states_def by fastforce
qed

proposition run_states_return_run:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "word_well_defined word (alphabet \<A>)"
  shows "prun_states (return_run word \<A>) \<A>"
proof - 
  have "initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  thus ?thesis using assms run_states_return_run_helper unfolding return_run_def prun_states_def by fastforce
qed

lemma length_return_run_helper:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "word_well_defined word (alphabet \<A>) \<and> s1 \<in> states \<A> \<and> s2 \<in> states \<A> \<Longrightarrow> length (return_run_helper s1 \<A> word) = length (return_run_helper s2 \<A> word)"
proof(induction word arbitrary: s1 s2)
  case Nil thus ?case by auto
next
  case (Cons a word)
  hence "a \<in> alphabet \<A> \<and> s1 \<in> states \<A> \<and> s2 \<in> states \<A>" unfolding word_well_defined_def by auto
  hence "(\<exists>! t1 \<in> states \<A> . (s1, a, t1) \<in> transitions \<A>) \<and> (\<exists>! t2 \<in> states \<A> . (s2, a, t2) \<in> transitions \<A>)" using assms unfolding DFA_property_def by auto
  then obtain state1 state2 where states: "(THE state1 . state1 \<in> states \<A> \<and> (s1, a, state1) \<in> transitions \<A>) = state1 \<and> state1 \<in> states \<A> \<and> (s1, a, state1) \<in> transitions \<A> \<and> (THE state2 . state2 \<in> states \<A> \<and> (s2, a, state2) \<in> transitions \<A>) = state2 \<and> state2 \<in> states \<A> \<and> (s2, a, state2) \<in> transitions \<A>" by blast
  hence return_run: "return_run_helper s1 \<A> (a # word) = (state1) # return_run_helper state1 \<A> word \<and> return_run_helper s2 \<A> (a # word) = (state2) # return_run_helper state2 \<A> word" using return_run_helper.simps by simp
  have "word_well_defined word (alphabet \<A>)" using Cons word_well_def_cons by metis
  hence "length (return_run_helper state1 \<A> word) = length (return_run_helper state2 \<A> word)" using states Cons by blast
  thus ?case using return_run by auto
qed

lemma length_return_run:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "word_well_defined (word @ [a]) (alphabet \<A>) \<Longrightarrow> (length (return_run word \<A>)) + 1 = length (return_run (word @ [a]) \<A>)"
proof(induction word arbitrary: a)
  case Nil thus ?case unfolding return_run_def by auto
next
  case (Cons a' word)
  hence props: "a' \<in> alphabet \<A> \<and> initial_state \<A> \<in> states \<A>" using assms unfolding word_well_defined_def auto_well_defined_def by auto
  have word_well_def: "word_well_defined ((a' # word) @ [a]) (alphabet \<A>) \<and> word_well_defined (word @ [a]) (alphabet \<A>) \<and> word_well_defined word (alphabet \<A>)" using Cons unfolding word_well_defined_def by auto
  hence "\<exists>! s2 \<in> states \<A> . ((initial_state \<A>), a', s2) \<in> transitions \<A>" using assms props unfolding DFA_property_def by auto
  then obtain s where s: "(THE s2 . s2 \<in> states \<A> \<and> ((initial_state \<A>), a', s2) \<in> transitions \<A>) = s \<and> s \<in> states \<A> \<and> ((initial_state \<A>), a', s) \<in> transitions \<A>" by blast  
  have "return_run (a' # (word @ [a])) \<A> = (initial_state \<A>) # return_run_helper (initial_state \<A>) \<A> (a' # (word @ [a]))" unfolding return_run_def by auto
  hence return_runa: "return_run (a' # (word @ [a])) \<A> = (initial_state \<A>) # (s) # return_run_helper s \<A> (word @ [a]) \<and> s \<in> states \<A>" using s return_run_helper.simps(2) by auto
  hence "length (return_run_helper s \<A> (word @ [a])) = length (return_run_helper (initial_state \<A>) \<A> (word @ [a]))" using assms props length_return_run_helper word_well_def by fast
  hence "length (return_run (a' # (word @ [a])) \<A>) = length (return_run_helper (initial_state \<A>) \<A> (word @ [a])) + 2" using return_runa by auto
  hence length_res: "length (return_run (a' # (word @ [a])) \<A>) = length (return_run (word @ [a]) \<A>) + 1" unfolding return_run_def by auto
  have "return_run (a' # word) \<A> = (initial_state \<A>) # return_run_helper (initial_state \<A>) \<A> (a' # word)" unfolding return_run_def by auto
  hence return_run: "return_run (a' # word) \<A> = (initial_state \<A>) # (s) # return_run_helper s \<A> word \<and> s \<in> states \<A>" using s return_run_helper.simps(2) by auto
  hence "length (return_run_helper s \<A> word) = length (return_run_helper (initial_state \<A>) \<A> word)" using assms props length_return_run_helper word_well_def by fast
  hence "length (return_run (a' # word) \<A>) = length (return_run_helper (initial_state \<A>) \<A> word) + 2" using return_run by auto
  hence "length (return_run (a' # word) \<A>) = length (return_run word \<A>) + 1" unfolding return_run_def by auto
  thus ?case using length_res using Cons word_well_def by auto
qed

theorem return_run_length_word:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "word_well_defined word (alphabet \<A>) \<Longrightarrow> length (return_run word \<A>) = length word + 1"
proof(induction word rule: rev_induct)
  case Nil thus ?case unfolding return_run_def by auto
next
  case (snoc a word)
  hence "(length (return_run word \<A>)) + 1 = length (return_run (word @ [a]) \<A>) \<and> word_well_defined word (alphabet \<A>)" using assms length_return_run word_well_def_snoc by metis
  hence "length (return_run (word @ [a]) \<A>) = length word + 1 + 1" using snoc by argo
  thus ?case by auto
qed

lemma return_run_helper_partial_equi:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "word_well_defined (word @ [a]) (alphabet \<A>) \<and> s1 \<in> states \<A> \<Longrightarrow> \<forall> i < length (return_run_helper s1 \<A> word) . (return_run_helper s1 \<A> word) ! i = (return_run_helper s1 \<A> (word @ [a])) ! i"
proof(induction word arbitrary: s1 a)
  case Nil thus ?case by auto
next
  case (Cons a' word)
  hence "a' \<in> alphabet \<A> \<and> s1 \<in> states \<A>" unfolding word_well_defined_def by force
  hence "\<exists>! s2 \<in> states \<A> . (s1, a', s2) \<in> transitions \<A>" using assms unfolding DFA_property_def by auto
  then obtain s where s: "(THE s2 . s2 \<in> states \<A> \<and> (s1, a', s2) \<in> transitions \<A>) = s \<and> s \<in> states \<A> \<and> (s1, a', s) \<in> transitions \<A>" by blast  
  have return_run: "return_run_helper s1 \<A> (a' # word) = s # return_run_helper s \<A> word" using return_run_helper.simps s by auto
  have return_runa: "return_run_helper s1 \<A> ((a' # word) @ [a]) = s # return_run_helper s \<A> (word @ [a])" using return_run_helper.simps s by auto
  have "word_well_defined (word @ [a]) (alphabet \<A>)" using Cons unfolding word_well_defined_def by auto
  hence "\<forall> i < length (return_run_helper s \<A> word) . (return_run_helper s \<A> word) ! i = (return_run_helper s \<A> (word @ [a])) ! i" using s Cons by blast
  hence "\<forall> i < length (s # return_run_helper s \<A> word) . (s # return_run_helper s \<A> word) ! i = (s # return_run_helper s \<A> (word @ [a])) ! i" by (simp add: nth_Cons')
  thus ?case using return_run return_runa by presburger
qed

lemma return_run_partial_equi:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "word_well_defined (word @ [a]) (alphabet \<A>)"
  shows "\<forall> i < length (return_run word \<A>) . (return_run word \<A>) ! i = (return_run (word @ [a]) \<A>) ! i"
proof - 
  have return_run: "return_run word \<A> = (initial_state \<A>) # return_run_helper (initial_state \<A>) \<A> word" unfolding return_run_def by auto
  have return_runa: "return_run (word @ [a]) \<A> = (initial_state \<A>) # return_run_helper (initial_state \<A>) \<A> (word @ [a])" unfolding return_run_def by auto
  have init: "initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  hence "\<forall> i < length (return_run_helper (initial_state \<A>) \<A> word) . (return_run_helper (initial_state \<A>) \<A> word) ! i = (return_run_helper (initial_state \<A>) \<A> (word @ [a])) ! i" using assms return_run_helper_partial_equi by fast
  thus ?thesis using return_run return_runa by (simp add: nth_Cons')
qed

theorem return_run_butlast:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "word_well_defined (word @ [a]) (alphabet \<A>)"
  shows "return_run word \<A> = butlast (return_run (word @ [a]) \<A>)"
proof - 
  let ?butlast = "butlast (return_run (word @ [a]) \<A>)"
  have equi: "\<forall> i < length (return_run word \<A>) . (return_run word \<A>) ! i = (return_run (word @ [a]) \<A>) ! i" using assms return_run_partial_equi by fast
  have "length (return_run word \<A>) + 1 = length (return_run (word @ [a]) \<A>)" using assms length_return_run by fast
  hence "length ?butlast = length (return_run word \<A>)" using length_butlast by auto
  thus ?thesis using assms equi nth_butlast nth_equalityI by metis
qed

lemma return_run_helper_i_step:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "run = return_run_helper s1 \<A> word \<and> s1 \<in> states \<A> \<and> word_well_defined word (alphabet \<A>) \<Longrightarrow> (\<forall> i < length ([s1] @ run) - 1 . (([s1] @ run) ! i, word ! i, ([s1] @ run) ! (i + 1)) \<in> transitions \<A>)"
proof(induction word arbitrary: s1 run)
  case Nil thus ?case by auto
next
  case (Cons a word)
  hence props: "a \<in> alphabet \<A> \<and> s1 \<in> states \<A> \<and> word_well_defined word (alphabet \<A>)" unfolding word_well_defined_def by force
  hence "\<exists>! s2 \<in> states \<A> . (s1, a, s2) \<in> transitions \<A>" using assms unfolding DFA_property_def by auto
  then obtain s where s: "(THE s2 . s2 \<in> states \<A> \<and> (s1, a, s2) \<in> transitions \<A>) = s \<and> s \<in> states \<A> \<and> (s1, a, s) \<in> transitions \<A>" by blast
  let ?run = "return_run_helper s1 \<A> (a # word)"
  have return_run: "[s1] @ ?run = [s1] @ (s) # return_run_helper s \<A> word" using return_run_helper.simps s by auto
  hence "?run = [s] @ return_run_helper s \<A> word" by auto
  hence i_step: "\<forall> i < length ?run - 1 . (?run ! i, word ! i, ?run ! (i + 1)) \<in> transitions \<A>" using s Cons props by presburger 
  have length: "length ?run + 1 = length ([s1] @ ?run)" by auto
  {
    fix i assume assm: "i < length ([s1] @ ?run) - 1" 
    hence "(([s1] @ ?run) ! i, (a # word) ! i, ([s1] @ ?run) ! (i + 1)) \<in> transitions \<A>"
    proof(cases i)
      case 0 thus ?thesis using s return_run by auto 
    next
      case (Suc nat)
      have "(?run ! i, word ! i, ?run ! (i + 1)) = (([s1] @ ?run) ! (i + 1), (a # word) ! (i + 1), ([s1] @ ?run) ! ((i + 1) + 1))" by auto
      hence equi: "(?run ! (i - 1), word ! (i - 1), ?run ! i) = (([s1] @ ?run) ! i, (a # word) ! i, ([s1] @ ?run) ! (i + 1))" using Suc by auto
      have "(?run ! (i - 1), word ! (i - 1), ?run ! i) \<in> transitions \<A>" using i_step length Suc assm by auto
      thus ?thesis using equi by argo
    qed
  }
  thus ?case using Cons by blast
qed

proposition return_run_i_step:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "run = return_run word \<A>" "word_well_defined word (alphabet \<A>)"
  shows "\<forall> i < length run - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions \<A>"
proof - 
  let ?run = "[initial_state \<A>] @ return_run_helper (initial_state \<A>) \<A> word"
  have equi: "return_run word \<A> = ?run" unfolding return_run_def by auto
  have "initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by argo
  hence "\<forall> i < length ?run - 1 . (?run ! i, word ! i, ?run ! (i + 1)) \<in> transitions \<A>" using equi return_run_helper_i_step assms by fast
  thus ?thesis using assms unfolding return_run_def by simp
qed

lemma return_run_left:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "run = return_run word \<A>" "word_well_defined word (alphabet \<A>)"
  shows "run_well_defined run \<A> word"
proof - 
  have len: "length run = length word + 1" using assms return_run_length_word by auto
  have "(run ! 0) = initial_state \<A>" using assms unfolding return_run_def by auto
  hence init: "(run ! 0) = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  have "(\<forall> i < length run - 1 . (run ! i, word ! i, run ! (i + 1)) \<in> transitions \<A>)" using assms return_run_i_step by blast
  thus ?thesis using len init unfolding run_well_defined_def pseudo_run_well_defined_def by fast
qed

lemma return_run_right:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "run_well_defined run \<A> word"
  shows "run = return_run word \<A> \<and> word_well_defined word (alphabet \<A>)"
proof - 
  have "word_well_defined word (alphabet \<A>)" using assms well_def_implies_word_well_defined unfolding run_well_defined_def by fast
  then obtain run' where run': "run' = return_run word \<A> \<and> word_well_defined word (alphabet \<A>)" by auto
  hence "run_well_defined run' \<A> word \<and> word_well_defined word (alphabet \<A>)" using assms return_run_left by auto
  hence "run' = run" using assms exists_only_one_run_for_DFA by blast
  thus ?thesis using run' by auto
qed

text \<open>Main Theorem for iterativ runs\<close>
theorem return_run_main:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "run_well_defined run \<A> word \<longleftrightarrow> run = return_run word \<A> \<and> word_well_defined word (alphabet \<A>)"
  using assms return_run_left return_run_right by metis













text \<open>How to get iteratively the reachable states\<close>
fun reachable_states_iter :: "nat \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 's states \<Rightarrow> 's states" where
  "reachable_states_iter 0 \<A> S = S" |
  "reachable_states_iter (Suc n) \<A> S = S \<union> reachable_states_iter n \<A> {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>}"

definition reachable_states_iterativ :: "('s, 'a) automaton \<Rightarrow> 's states" where "reachable_states_iterativ \<A> = reachable_states_iter (card (states \<A>) - 1) \<A> {initial_state \<A>}"

lemma reachable_states_iter_helper:
  assumes "auto_well_defined \<A>" 
  shows "S \<subseteq> states \<A> \<Longrightarrow> reachable_states_iter n \<A> S \<subseteq> states \<A>"
proof(induction n arbitrary: S)
  case 0 thus ?case using assms by auto
next
  case (Suc n)
  have equi: "reachable_states_iter (Suc n) \<A> S = S \<union> reachable_states_iter n \<A> {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>}" by auto
  have "S \<subseteq> states \<A>" using Suc by auto
  hence "{s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>} \<subseteq> states \<A>" using assms well_def_trans_components by fast
  thus ?case using Suc equi by auto
qed

proposition reachable_states_iter_subset_states:
  assumes "auto_well_defined \<A>"
  shows "reachable_states_iterativ \<A> \<subseteq> states \<A>"
proof -
  have "{initial_state \<A>} \<subseteq> states \<A>" using assms unfolding auto_well_defined_def by blast
  thus ?thesis using reachable_states_iter_helper assms unfolding reachable_states_iterativ_def by metis
qed

proposition init_reachable_states: "initial_state \<A> \<in> reachable_states_iterativ \<A>"
proof(cases "(card (states \<A>)) - 1")
  case 0
  have "reachable_states_iterativ \<A> = reachable_states_iter (card (states \<A>) - 1) \<A> {initial_state \<A>}" unfolding reachable_states_iterativ_def by fast
  hence "reachable_states_iterativ \<A> = reachable_states_iter 0 \<A> {initial_state \<A>}" using 0 by argo
  thus ?thesis by auto
next
  case (Suc n)
  have "reachable_states_iterativ \<A> = reachable_states_iter (card (states \<A>) - 1) \<A> {initial_state \<A>}" unfolding reachable_states_iterativ_def by auto
  hence "reachable_states_iterativ \<A> = reachable_states_iter (Suc n) \<A> {initial_state \<A>}" using Suc by argo
  hence "reachable_states_iterativ \<A> = {initial_state \<A>} \<union> reachable_states_iter n \<A> {s2 . \<exists> s1 a . s1 \<in> {initial_state \<A>} \<and> (s1, a, s2) \<in> transitions \<A>}" by auto
  thus ?thesis by auto 
qed

proposition iter_subset_division:
  assumes "auto_well_defined \<A>"
  shows "S \<subseteq> states \<A> \<and> S' \<subseteq> states \<A> \<Longrightarrow> reachable_states_iter n \<A> (S \<union> S') = reachable_states_iter n \<A> S \<union> reachable_states_iter n \<A> S'"
proof(induction n arbitrary: S S')
  case 0 thus ?case by auto
next
  case (Suc n)
  hence "S \<union> S' \<subseteq> states \<A>" by auto
  hence sub: "S \<union> S' \<subseteq> states \<A> \<and> {s2 . \<exists> s1 a . s1 \<in> (S \<union> S') \<and> (s1, a, s2) \<in> transitions \<A>} \<subseteq> states \<A>" using assms well_def_trans_components by fast
  have "S \<subseteq> states \<A> \<and> S' \<subseteq> states \<A>" using Suc by argo
  hence subsub: "S \<subseteq> states \<A> \<and> S' \<subseteq> states \<A> \<and> {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>} \<subseteq> states \<A> \<and> {s2 . \<exists> s1 a . s1 \<in> S' \<and> (s1, a, s2) \<in> transitions \<A>} \<subseteq> states \<A> " using assms well_def_trans_components by fast
  have "{s2 . \<exists> s1 a . s1 \<in> (S \<union> S') \<and> (s1, a, s2) \<in> transitions \<A>} = {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>} \<union> {s2 . \<exists> s1 a . s1 \<in> S' \<and> (s1, a, s2) \<in> transitions \<A>}" by blast
  hence left: "reachable_states_iter (Suc n) \<A> (S \<union> S') = S \<union> S' \<union> reachable_states_iter n \<A> {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>} \<union> reachable_states_iter n \<A> {s2 . \<exists> s1 a . s1 \<in> S' \<and> (s1, a, s2) \<in> transitions \<A>}" using Suc subsub by force
  have "reachable_states_iter (Suc n) \<A> S \<union> reachable_states_iter (Suc n) \<A> S' = S \<union> reachable_states_iter n \<A> {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>} \<union> S' \<union> reachable_states_iter n \<A> {s2 . \<exists> s1 a . s1 \<in> S' \<and> (s1, a, s2) \<in> transitions \<A>}" using Suc subsub by auto
  thus ?case using left by blast
qed

lemma reachable_state_trans:
  assumes "auto_well_defined \<A>"
  shows "s \<in> reachable_states_iter (Suc n) \<A> S \<and> S \<subseteq> states \<A> \<Longrightarrow> s \<in> S \<or> (\<exists> s1 a . s1 \<in> (reachable_states_iter n \<A> S) \<and> (s1, a, s) \<in> transitions \<A>)"
proof(induction n arbitrary: s S)
  case 0 thus ?case by auto
next
  case (Suc n)
  hence "s \<in> S \<union> reachable_states_iter (Suc n) \<A> {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>}" by auto
  hence props: "s \<in> S \<or> s \<in> reachable_states_iter (Suc n) \<A> {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>}" by auto
  let ?S' = "{s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>}"
  have "S \<subseteq> states \<A>" using Suc by blast
  hence "?S' \<subseteq> states \<A>" using assms well_def_trans_components by fast
  hence "s \<in> S \<or> s \<in> ?S' \<or> (\<exists> s1 a . s1 \<in> (reachable_states_iter n \<A> ?S') \<and> (s1, a, s) \<in> transitions \<A>)" using Suc props by presburger
  hence step: "s \<in> S \<or> (\<exists> s1 a . s1 \<in> S \<and> (s1, a, s) \<in> transitions \<A>) \<or> (\<exists> s1 a . s1 \<in> (reachable_states_iter n \<A> ?S') \<and> (s1, a, s) \<in> transitions \<A>)" by fast
  have "S \<subseteq> (reachable_states_iter (Suc n) \<A> S) \<and> reachable_states_iter n \<A> ?S' \<subseteq> (reachable_states_iter (Suc n) \<A> S)" by auto
  thus ?case using step by blast
qed

lemma iter_reachable_state_are_reachable_helper:
  assumes "auto_well_defined \<A>"
  shows "s \<in> reachable_states_iter n \<A> {initial_state \<A>} \<Longrightarrow> reachable_state s \<A>"
proof(induction n arbitrary: s)
  case 0
  hence s: "s = initial_state \<A>" by auto
  hence "s = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  hence "run_well_defined [initial_state \<A>] \<A> []" unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  thus ?case using s unfolding reachable_state_def by fastforce
next
  case (Suc n)
  have "{initial_state \<A>} \<subseteq> states \<A>" using assms unfolding auto_well_defined_def by auto
  hence "s = initial_state \<A> \<or> (\<exists> s1 a . s1 \<in> (reachable_states_iter n \<A> {initial_state \<A>}) \<and> (s1, a, s) \<in> transitions \<A>)" using assms reachable_state_trans Suc by fast
  then consider (case1) "s = initial_state \<A>" | (case2) "(\<exists> s1 a . s1 \<in> (reachable_states_iter n \<A> {initial_state \<A>}) \<and> (s1, a, s) \<in> transitions \<A>)" by blast
  thus ?case
  proof cases
    case case1 thus ?thesis using assms initial_state_is_reachable by blast
  next
    case case2
    then obtain s1 a where "s1 \<in> (reachable_states_iter n \<A> {initial_state \<A>}) \<and> (s1, a, s) \<in> transitions \<A>" by auto
    hence "reachable_state s1 \<A> \<and> (s1, a, s) \<in> transitions \<A>" using Suc by auto
    thus ?thesis using inheritance_reachable_state assms by fast
  qed
qed

theorem iter_reachable_state_are_reachable:
  assumes "auto_well_defined \<A>"
  shows "s \<in> reachable_states_iterativ \<A> \<Longrightarrow> reachable_state s \<A>"
  using assms iter_reachable_state_are_reachable_helper unfolding reachable_states_iterativ_def by fast

lemma reachable_iter_inheritance_general:
  assumes "auto_well_defined \<A>"
  shows "s' \<in> reachable_states_iter n \<A> S \<and> (s', a, s) \<in> transitions \<A> \<Longrightarrow> s \<in> reachable_states_iter (Suc n) \<A> S"
proof(induction n arbitrary: S s' s a)
  case 0 thus ?case by auto
next
  case (Suc n)
  hence "s' \<in> reachable_states_iter (Suc n) \<A> S \<and> (s', a, s) \<in> transitions \<A>" by auto
  hence "s' \<in> S \<or> s'\<in> reachable_states_iter n \<A> {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>} \<and> (s', a, s) \<in> transitions \<A>" by auto
  hence "s' \<in> S \<and> (s', a, s) \<in> transitions \<A> \<or> s \<in> reachable_states_iter (Suc n) \<A> {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>}" using Suc by blast
  hence "s \<in> {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>} \<or> s \<in> reachable_states_iter (Suc n) \<A> {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>}" by blast
  hence "s \<in> reachable_states_iter (Suc n) \<A> {s2 . \<exists> s1 a . s1 \<in> S \<and> (s1, a, s2) \<in> transitions \<A>}" by auto
  thus ?case by auto
qed

lemma sub_runs:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word"
  shows "n \<le> length word \<Longrightarrow> run_well_defined (take (Suc n) run) \<A> (take n word) \<and> length (take (Suc n) run) \<le> length run"
proof(induction n)
  case 0
  have len: "length run = length word + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  hence "take 1 run = [run ! 0]" by (simp add: take_Suc_conv_app_nth)
  hence "take 1 run = [initial_state \<A>] \<and> take 0 word = []" using assms 0 unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "take 1 run = [initial_state \<A>] \<and> take 0 word = [] \<and> initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  thus ?case using len unfolding run_well_defined_def pseudo_run_well_defined_def by auto
next
  case (Suc n)
  hence length: "Suc n < length run \<and> run \<noteq> [] \<and> length run = length word + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "n < length run \<and> run \<noteq> []" by auto
  hence equi: "last (take (Suc n) run) = (take (Suc n) run) ! n" using last_and_take_list by auto
  have "\<forall> i < length word . (run ! i, word ! i, run ! (i + 1)) \<in> transitions \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence "(last (take (Suc n) run), word ! n, run ! (n + 1)) \<in> transitions \<A>" using Suc equi by auto
  hence well_def: "run_well_defined ((take (Suc n) run) @ [run ! (n + 1)]) \<A> ((take n word) @ [word ! n])" using assms prun_well_defined_extension_snoc Suc unfolding run_well_defined_def by fastforce
  have run: "((take (Suc n) run) @ [run ! (Suc n)]) = take (Suc (Suc n)) run" using length Suc take_suc_length by blast
  have len: "length (((take (Suc n) run) @ [run ! (n + 1)])) \<le> length run" using length by auto
  have word: "((take n word) @ [word ! n]) = take (Suc n) word" using length Suc take_suc_length by blast
  thus ?case using run word well_def len by simp
qed

lemma run_def_sublist1:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word" "i < length run \<and> j < length run \<and> i \<noteq> j \<and> run ! i = run ! j \<and> i < j" "j = length word"
  shows "length ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) = length ((take i word) @ (sublist j (length word) word)) + 1 \<and> (\<forall> k < length ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) - 1 . (((take (Suc i) run) @ (sublist (Suc j) (length run) run)) ! k, ((take i word) @ (sublist j (length word) word)) ! k, ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) ! (k + 1)) \<in> transitions \<A>)"
proof -
  let ?subrun = "((take (Suc i) run) @ (sublist (Suc j) (length run) run))"
  let ?subword = "((take i word) @ (sublist j (length word) word))"
  have "length run = length word + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  hence equi_run: "?subrun = (take (Suc i) run)" using assms unfolding sublist_def by fastforce
  have equi_word: "?subword = (take i word)" using assms unfolding sublist_def by fastforce
  have "i \<le> length word" using assms by linarith
  hence "run_well_defined ?subrun \<A> ?subword" using assms sub_runs equi_run equi_word by metis
  thus ?thesis using equi_run equi_word unfolding run_well_defined_def pseudo_run_well_defined_def by blast
qed

lemma equi_sublist:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word" "i < length run \<and> j < length run \<and> i \<noteq> j \<and> run ! i = run ! j \<and> i < j" "j \<noteq> length word"
  shows "\<forall> k < length (sublist (Suc j) (length run) run) - 1 . (((sublist (Suc j) (length run) run)) ! k, ((sublist (Suc j) (length run) run)) ! (k + 1), ((sublist j (length word) word)) ! (k + 1)) = (run ! (j + k + 1), run ! (j + k + 1 + 1), word ! (j + k + 1))"
proof -
  {
    fix k assume assm: "k < length (sublist (Suc j) (length run) run) - 1"
    have len: "length run = length word + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast
    hence runk: "run ! (j + 1 + k) = (sublist (Suc j) (length run) run) ! k" using assms unfolding sublist_def by fastforce
    hence runk1: "run ! (j + 1 + k + 1) = (sublist (Suc j) (length run) run) ! (k + 1)" using assms unfolding sublist_def by simp
    have "i < length word + 1 \<and> j < length word + 1 \<and> i \<noteq> j \<and> i < j" using assms len by auto
    hence "word ! (j + k + 1)  = (sublist j (length word) word) ! (k + 1)" unfolding sublist_def by auto
    hence "(((sublist (Suc j) (length run) run)) ! k, ((sublist (Suc j) (length run) run)) ! (k + 1), ((sublist j (length word) word)) ! (k + 1)) = (run ! (j + k + 1), run ! (j + k + 1 + 1), word ! (j + k + 1))" using runk runk1 by force
  }
  thus ?thesis by fast
qed

lemma run_def_sublist2:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word" "i < length run \<and> j < length run \<and> i \<noteq> j \<and> run ! i = run ! j \<and> i < j" "j \<noteq> length word"
  shows "length ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) = length ((take i word) @ (sublist j (length word) word)) + 1 \<and> (\<forall> k < length ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) - 1 . (((take (Suc i) run) @ (sublist (Suc j) (length run) run)) ! k, ((take i word) @ (sublist j (length word) word)) ! k, ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) ! (k + 1)) \<in> transitions \<A>)"
proof -
  let ?subrun1 = "take (Suc i) run"
  let ?subrun2 = "sublist (Suc j) (length run) run"
  let ?subrun = "?subrun1 @ ?subrun2"
  let ?subword1 = "take i word"
  let ?subword2 = "sublist j (length word) word"
  let ?subword = "?subword1 @ ?subword2"
  have len: "run \<noteq> [] \<and> length run = length word + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence len_sub_run: "length ?subrun = (length run) + i - j" using assms length_sublist1 length_sublist2 by blast
  have len_sub_word: "length ?subword = (length run) + i - j - 1" using assms len length_sublist2 by blast
  have ge: "length ?subrun > 0" using assms len_sub_run by fastforce
  hence "length ?subrun - 1 = length ?subword" using len_sub_run len_sub_word by argo
  hence length: "length ?subrun = length ?subword + 1" using ge by linarith
  have original_trans: "\<forall> k < length run - 1 . (run ! k, word ! k, run ! (k + 1)) \<in> transitions \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  hence trans: "\<forall> k < length ?subrun1 - 1 . (?subrun1 ! k, ?subword1 ! k, ?subrun1 ! (k + 1)) \<in> transitions \<A>" by force 
  have step: "(run ! j, word ! j, run ! (j + 1)) \<in> transitions \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce
  have "last ?subrun1 = ?subrun1 ! i" using assms len last_and_take_list by blast
  hence runj: "run ! j = last ?subrun1" using assms by auto
  have runj1: "run ! (j + 1) = ?subrun2 ! 0" using assms len unfolding sublist_def by force
  have "word ! j = ?subword2 ! 0" using assms len unfolding sublist_def by force
  hence trans_step: "(last ?subrun1, ?subword2 ! 0, ?subrun2 ! 0) \<in> transitions \<A>" using step runj1 runj by auto
  have equi: "\<forall> k < length ?subrun2 - 1 . (?subrun2 ! k, ?subrun2 ! (k + 1), ?subword2 ! (k + 1)) = (run ! (j + k + 1), run ! (j + k + 1 + 1), word ! (j + k + 1))" using assms equi_sublist by simp
  have "j > 0 \<and> length ?subrun2 = length run - Suc j" using assms len unfolding sublist_def by force
  hence "\<forall> l < length ?subrun2 - 1 . (run ! (j + l + 1), word ! (j + l + 1), run ! (Suc j + l + 1)) \<in> transitions \<A>" using original_trans less_diff_conv by auto
  hence Nil_l: "\<forall> l < length ?subrun2 - 1 . (?subrun2 ! l, ?subword2 ! (l + 1), ?subrun2 ! (l + 1)) \<in> transitions \<A>" using equi by auto
  hence sub_trans: "\<forall> m . m < length ?subrun2 + length ?subrun1 - 1 \<and> m \<ge> length ?subrun1 \<longrightarrow> (?subrun2 ! (m - length ?subrun1), ?subword2 ! (m + 1 - length ?subrun1), ?subrun2 ! (m + 1 - length ?subrun1)) \<in> transitions \<A>"
  proof -
    {
      fix m assume assm: "m < length ?subrun2 + length ?subrun1 - 1 \<and> m \<ge> length ?subrun1"
      let ?l = "m - length ?subrun1"
      have range: "0 \<le> ?l \<and> ?l < length ?subrun2 -1" using assm by linarith
      hence in_trans: "(?subrun2 ! ?l, ?subword2 ! (?l + 1), ?subrun2 ! (?l + 1)) \<in> transitions \<A>" using Nil_l assm by blast
      have "?subrun2 ! ?l = ?subrun2 ! (m - length ?subrun1) \<and> ?subrun2 ! (?l + 1) = ?subrun2 ! (m + 1 - length ?subrun1) \<and> ?subword2 ! (?l + 1) = ?subword2 ! (m + 1 - length ?subrun1)" using assm Nat.add_diff_assoc2 by presburger
      hence "(?subrun2 ! (m - length ?subrun1), ?subword2 ! (m + 1 - length ?subrun1), ?subrun2 ! (m + 1 - length ?subrun1)) \<in> transitions \<A>" using in_trans by argo
    }
    thus ?thesis by argo
  qed
  hence "\<forall> k < length ?subrun - 1 . (?subrun ! k, ?subword ! k, ?subrun ! (k + 1)) \<in> transitions \<A>"
  proof -
    {
      fix k assume "k < length ?subrun - 1"
      then consider (case1) "k < length ?subrun1 - 1" | (case2) "k = length ?subrun1 - 1" | (case3) "k > length ?subrun1 - 1 \<and> k < length ?subrun - 1" by linarith
      hence "(?subrun ! k, ?subword ! k, ?subrun ! (k + 1)) \<in> transitions \<A>"
      proof cases
        case case1
        have "length ?subrun2 = length ?subword2 \<and> length (?subrun1 @ ?subrun2) = length (?subword1 @ ?subword2) + 1" using len unfolding sublist_def by auto
        hence "?subrun1 ! k = (?subrun1 @ ?subrun2) ! k \<and> ?subrun1 ! (k + 1) = (?subrun1 @ ?subrun2) ! (k + 1) \<and> ?subword1 ! k = (?subword1 @ ?subword2) ! k " using case1 list_append_position1 by metis
        thus ?thesis using trans case1 by metis
      next
        case case2
        have "j \<noteq> length word \<and> length ?subword2 = length word - j \<and> j < length word + 1" using assms len unfolding sublist_def by auto
        hence "?subword2 \<noteq> []" by auto
        hence "length ?subrun2 = length ?subword2 \<and> length (?subrun1 @ ?subrun2) = length (?subword1 @ ?subword2) + 1 \<and> ?subword2 \<noteq> [] " using len unfolding sublist_def by fastforce
        hence "?subrun ! k = last ?subrun1 \<and> ?subrun ! (k + 1) = ?subrun2 ! 0 \<and> ?subword ! k = ?subword2 ! 0" using case2 list_append_position2 by blast
        thus ?thesis using case2 trans_step by argo
      next
        case case3
        have assm: "j \<noteq> length word \<and> length ?subword2 = length word - j \<and> j < length word + 1" using assms len unfolding sublist_def by force
        hence "?subword2 \<noteq> []" by auto
        hence "length ?subrun2 = length ?subword2 \<and> length (?subrun1 @ ?subrun2) = length (?subword1 @ ?subword2) + 1 \<and> ?subword2 \<noteq> [] " using len unfolding sublist_def by simp
        hence equi_k: "(?subrun1 @ ?subrun2) ! k = ?subrun2 ! (k - length ?subrun1) \<and> (?subrun1 @ ?subrun2) ! (k + 1) = ?subrun2 ! (k + 1 - length ?subrun1) \<and> (?subword1 @ ?subword2) ! k = ?subword2 ! (k + 1 - length ?subrun1)" using case3 list_append_position3 by blast
        have "k < length ?subrun2 + length ?subrun1 - 1 \<and> k \<ge> length ?subrun1" using case3 by auto
        thus ?thesis using sub_trans equi_k by presburger
      qed
    }
    thus ?thesis by blast
  qed
  thus ?thesis using length by blast
qed

lemma subrun_initial_state:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word" "i < length run \<and> j < length run \<and> i \<noteq> j \<and> run ! i = run ! j \<and> i < j" 
  shows "((take (Suc i) run) @ (sublist (Suc j) (length run) run)) ! 0 = initial_state \<A>"
proof -
  let ?subrun1 = "take (Suc i) run"
  let ?subrun2 = "sublist (Suc j) (length run) run"
  let ?subrun = "?subrun1 @ ?subrun2"
  have "run \<noteq> []" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce
  hence "run ! 0 = ?subrun ! 0" using assms by (simp add: nth_append)
  thus ?thesis using assms unfolding run_well_defined_def pseudo_run_well_defined_def by argo
qed

lemma subrun_last_state:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word" "i < length run \<and> j < length run \<and> i \<noteq> j \<and> run ! i = run ! j \<and> i < j" "s = last run"
  shows "s = last ((take (Suc i) run) @ (sublist (Suc j) (length run) run))"
proof -
  let ?subrun1 = "take (Suc i) run"
  let ?subrun2 = "sublist (Suc j) (length run) run"
  let ?subrun = "?subrun1 @ ?subrun2"
  have not_empty: "run \<noteq> []" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  consider (case1) "j = length run - 1" | (case2) "j < length run - 1" using assms by linarith
  thus ?thesis
  proof cases
    case case1 
    hence "run ! i = s" using assms not_empty list_properties_not_empty by metis
    thus ?thesis using assms not_empty unfolding sublist_def by (simp add: last_and_take_list last_append)
  next
    case case2 thus ?thesis using assms unfolding sublist_def by simp
  next
  qed
qed

proposition run_sublist:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word" "i < length run \<and> j < length run \<and> i \<noteq> j \<and> run ! i = run ! j \<and> i < j" "s = last run"
  shows "run_well_defined ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) \<A> ((take i word) @ (sublist j (length word) word)) \<and> s = last ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) \<and> length run > length ((take (Suc i) run) @ (sublist (Suc j) (length run) run))"
proof - 
  let ?subrun = "((take (Suc i) run) @ (sublist (Suc j) (length run) run))"
  let ?subword = "((take i word) @ (sublist j (length word) word))"
  have "length run = length word + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  then consider (case1) "j < length word" | (case2) "j = length word" using assms by linarith
  thus ?thesis
  proof cases
    case case1
    hence "length ?subrun = length ?subword + 1 \<and> (\<forall> k < length ?subrun - 1 . (?subrun ! k, ?subword ! k, ?subrun ! (k + 1)) \<in> transitions \<A>)" using assms run_def_sublist2 by blast
    hence well_def: "run_well_defined ?subrun \<A> ?subword" using assms subrun_initial_state unfolding run_well_defined_def pseudo_run_well_defined_def by blast
    have "run \<noteq> []" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
    hence "length run > length ?subrun" using assms length_sublist3 by blast
    thus ?thesis using assms subrun_last_state well_def by metis
  next
    case case2
    hence "length ?subrun = length ?subword + 1 \<and> (\<forall> k < length ?subrun - 1 . (?subrun ! k, ?subword ! k, ?subrun ! (k + 1)) \<in> transitions \<A>)" using assms run_def_sublist1 by blast
    hence well_def: "run_well_defined ?subrun \<A> ?subword" using assms subrun_initial_state unfolding run_well_defined_def pseudo_run_well_defined_def by blast
    have "run \<noteq> []" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
    hence "length run > length ?subrun" using assms length_sublist3 by blast
    thus ?thesis using assms subrun_last_state well_def by metis
  qed
qed

lemma runs_multiple_states:
  assumes "auto_well_defined \<A>" "length run = Suc (card (states \<A>))" "run_well_defined run \<A> word"
  shows "\<exists> i < length run . \<exists> j < length run . i \<noteq> j \<and> run ! i = run ! j"
proof(rule ccontr)
  assume assm: "\<not> (\<exists> i < length run . \<exists> j < length run . i \<noteq> j \<and> run ! i = run ! j)"
  have run_states: "prun_states run \<A>" using assms well_def_implies_prun_states unfolding run_well_defined_def by fast
  have "finite (states \<A>)" using assms unfolding auto_well_defined_def by blast
  hence card: "card (set run) \<le> card (states \<A>)" using run_states Finite_Set.card_mono unfolding prun_states_def by auto
  have "distinct run" using assm distinct_conv_nth by blast
  hence "card (set run) > card (states \<A>)" using assms distinct_card by fastforce
  thus "False" using card by auto
qed

lemma worst_case_shorter_runs:
  assumes "auto_well_defined \<A>" "length run = Suc (card (states \<A>))" "run_well_defined run \<A> word" "s \<in> set run" "k = length word" "run ! k = s"
  shows "\<exists> run' word' . run_well_defined run' \<A> word' \<and> length run' < length run \<and> last run' = s"
proof - 
  have "length run = k + 1 \<and> run \<noteq> []" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce
  hence last: "s = last run" using assms list_properties_not_empty by fastforce
  have "\<exists> i < length run . \<exists> j < length run . i \<noteq> j \<and> run ! i = run ! j" using assms runs_multiple_states by blast
  then obtain i j where ij: "i < length run \<and> j < length run \<and> i \<noteq> j \<and> run ! i = run ! j" by blast
  then consider (case1) "i < j" | (case2) "j < i" by linarith
  thus ?thesis
  proof cases
    case case1 thus ?thesis using assms last run_sublist ij by metis
  next
    case case2 thus ?thesis using assms last run_sublist ij by metis
  qed
qed

lemma existence_shorter_runs:
  assumes "auto_well_defined \<A>" "length run = Suc (card (states \<A>))" "run_well_defined run \<A> word" "s \<in> set run"
  shows "\<exists> run' word' . run_well_defined run' \<A> word' \<and> length run' < length run \<and> last run' = s"
proof -
  have "\<exists> k < length run . run ! k = s" using assms in_set_conv_nth by metis
  then obtain k where k: "k < length run \<and> run ! k = s" by auto
  hence len: "k \<le> length word" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by linarith
  hence well_def: "run_well_defined (take (Suc k) run) \<A> (take k word) \<and> length (take (Suc k) run) \<le> length run" using assms sub_runs by blast
  have "run \<noteq> []" using k assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence run: "run_well_defined (take (Suc k) run) \<A> (take k word) \<and> length (take (Suc k) run) \<le> length run \<and> last (take (Suc k) run) = s" using k last_and_take_list well_def by auto
  consider (case1) "k < length word" | (case2) "k = length word" using len by fastforce
  thus ?thesis
  proof cases
    case case1 
    have "length run = length word + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast
    hence "length (take (Suc k) run) < length run" using case1 by auto
    hence "run_well_defined (take (Suc k) run) \<A> (take k word) \<and> length (take (Suc k) run) < length run \<and> last (take (Suc k) run) = s" using run by blast
    thus ?thesis by blast
  next
    case case2 thus ?thesis using assms worst_case_shorter_runs k by fast
  qed
qed

proposition existence_sub_runs:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined run \<A> word \<longrightarrow> (\<exists> run' word' . run_well_defined run' \<A> word' \<and> last run' = last run \<and> length run' \<le> card (states \<A>))"
proof - 
  consider (case1) "length run \<le> card (states \<A>)" | (case2) "length run \<ge> Suc (card (states \<A>))" by linarith
  thus ?thesis
  proof cases
    case case1 thus ?thesis by blast
  next
    case case2
    {
      fix run word assume assm: "run_well_defined run \<A> word \<and> length run \<ge> Suc (card (states \<A>))"
      hence "\<exists> run' word' . run_well_defined run' \<A> word' \<and> last run' = last run \<and> length run' \<le> card (states \<A>)"
      proof(induction "length run - Suc (card (states \<A>))" arbitrary: run word)
        case 0
        hence len: "length run = Suc (card (states \<A>))" by simp
        hence "run \<noteq> []" by auto
        hence "last run \<in> set run" by auto
        hence "\<exists> run' word' . run_well_defined run' \<A> word' \<and> length run' < length run \<and> last run' = last run" using assms len 0 existence_shorter_runs by fast
        thus ?case using len by auto
      next
        case (Suc n)
        hence "run_well_defined run \<A> word \<and> length run = Suc (card (states \<A>)) + Suc n \<and> length run > 1" by linarith
        hence props: "length run = Suc (card (states \<A>)) + Suc n \<and> length run > 1 \<and> length run = length word + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast
        hence "run \<noteq> [] \<and> word \<noteq> []" by auto
        then obtain run' word' where run': "run = run' @ [last run] \<and> word = word' @ [last word]" using append_butlast_last_id by metis
        hence well_def: "run_well_defined run' \<A> word' \<and> (last run', last word, last run) \<in> transitions \<A>" using prun_well_defined_extension_snoc assms Suc unfolding run_well_defined_def by metis
        have "length (run' @ [last run]) = Suc (card (states \<A>)) + Suc n \<and> length (run' @ [last run]) > 1" using run' props by argo
        hence len: "length run' = Suc (card (states \<A>)) + n \<and> length run' \<ge> Suc (card (states \<A>))" by auto
        hence "\<exists> run'' word''. run_well_defined run'' \<A> word'' \<and> last run'' = last run' \<and> length run'' \<le> card (states \<A>)" using well_def Suc by force
        then obtain run'' word'' where run'': "run_well_defined run'' \<A> word'' \<and> last run'' = (last run') \<and> length run'' \<le> card (states \<A>)" by blast
        then consider (case3) "length run'' < card (states \<A>)" | (case4) "length run'' = card (states \<A>)" by linarith
        thus ?case
        proof cases
          case case3 
          hence length: "length (run'' @ [last run]) < Suc (card (states \<A>))" by auto
          have "run_well_defined (run'' @ [last run]) \<A> (word'' @ [last word])" using prun_well_defined_extension_snoc assms run'' well_def unfolding run_well_defined_def by metis
          thus ?thesis using length by auto
        next
          case case4
          hence length: "length (run'' @ [last run]) = Suc (card (states \<A>)) \<and> last run \<in> set (run'' @ [last run])" by auto
          have "run_well_defined (run'' @ [last run]) \<A> (word'' @ [last word])" using prun_well_defined_extension_snoc assms run'' well_def unfolding run_well_defined_def by fastforce
          hence "\<exists> run2 word2 . run_well_defined run2 \<A> word2 \<and> length run2 < length (run'' @ [last run]) \<and> last run2 = last run" using length existence_shorter_runs assms by fast
          thus ?thesis using length by auto
        qed
      qed
    }
    thus ?thesis by fastforce
  qed
qed

lemma equivalence_reachable_iter_subruns_left:
  assumes "auto_well_defined \<A>" "s \<in> reachable_states_iterativ \<A>"
  shows "\<exists> run word. run_well_defined run \<A> word \<and> last run = s \<and> length run \<le> card (states \<A>)"
proof -
  have "reachable_state s \<A>" using assms iter_reachable_state_are_reachable by fast
  hence "\<exists> word run . run_well_defined run \<A> word \<and> last run = s" unfolding reachable_state_def by auto
  then obtain word run where "run_well_defined run \<A> word \<and> last run = s" by auto
  thus ?thesis using existence_sub_runs assms by blast
qed

lemma equivalence_reachable_iter_subruns_right_helper:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined run \<A> word \<and> length run \<le> Suc n \<Longrightarrow> last run \<in> reachable_states_iter n \<A> {initial_state \<A>}"
proof(induction n arbitrary: run word)
  case 0
  hence "length run = 1 \<and> run ! 0 = initial_state \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "last run = initial_state \<A>" using list_with_one_element by metis
  thus ?case by auto
next
  case (Suc n)
  hence props: "run_well_defined run \<A> word \<and> length run \<le> Suc (Suc n)" by auto
  thus ?case
  proof(cases word)
    case Nil
    hence "length run = 1 \<and> run ! 0 = initial_state \<A>" using props unfolding run_well_defined_def pseudo_run_well_defined_def by force
    hence "last run = initial_state \<A>" using list_with_one_element by metis    
    thus ?thesis by auto
  next
    case(Cons a list)
    hence "run \<noteq> [] \<and> word \<noteq> []" using props unfolding run_well_defined_def pseudo_run_well_defined_def by auto
    then obtain run' word' where run': "run = run' @ [last run] \<and> word = word' @ [last word]" using append_butlast_last_id by metis
    hence well_def: "run_well_defined run' \<A> word' \<and> (last run', last word, last run) \<in> transitions \<A>" using prun_well_defined_extension_snoc assms Suc unfolding run_well_defined_def by metis
    have "length (run' @ [last run]) \<le> Suc (Suc n)" using run' props by auto
    hence "length run' \<le> Suc n" by auto
    hence "last run' \<in> reachable_states_iter n \<A> {initial_state \<A>} \<and> (last run', last word, last run) \<in> transitions \<A>" using well_def Suc by blast
    thus ?thesis using reachable_iter_inheritance_general assms by fast
  qed
qed

lemma equivalence_reachable_iter_subruns_right:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word" "length run \<le> card (states \<A>)"
  shows "last run \<in> reachable_states_iterativ \<A>"
  using assms equivalence_reachable_iter_subruns_right_helper unfolding reachable_states_iterativ_def by force

proposition equivalence_reachable_iter_subruns:
  assumes "auto_well_defined \<A>"
  shows "s \<in> reachable_states_iterativ \<A> \<longleftrightarrow> (\<exists> run word. run_well_defined run \<A> word \<and> last run = s \<and> length run \<le> card (states \<A>))"
  using assms equivalence_reachable_iter_subruns_right equivalence_reachable_iter_subruns_left by fast

text \<open>Main Theorem for iterativ reachable states\<close>
theorem equivalence_of_reachable_states:
  assumes "auto_well_defined \<A>"
  shows "reachable_states \<A> = reachable_states_iterativ \<A>"
proof -
  {
    fix s assume "s \<in> reachable_states \<A>"
    hence "reachable_state s \<A>" unfolding reachable_states_def by auto
    hence "\<exists> run word. run_well_defined run \<A> word \<and> last run = s" unfolding reachable_state_def by auto
    hence "\<exists> run word. run_well_defined run \<A> word \<and> last run = s \<and> length run \<le> card (states \<A>)" using assms existence_sub_runs by fast
    hence "s \<in> reachable_states_iterativ \<A>" using assms equivalence_reachable_iter_subruns by fast
  }
  hence left: "reachable_states \<A> \<subseteq> reachable_states_iterativ \<A>" by auto
  {
    fix s assume "s \<in> reachable_states_iterativ \<A>"
    hence "\<exists> run word. run_well_defined run \<A> word \<and> last run = s" using assms equivalence_reachable_iter_subruns by fast
    hence "s \<in> reachable_states \<A>" unfolding reachable_state_def reachable_states_def by auto
  }
  hence "reachable_states_iterativ \<A> \<subseteq> reachable_states \<A>" by auto
  thus ?thesis using left by auto
qed










text \<open>Iterativ epsilon closure\<close>
fun epsilon_closure_iter :: "nat \<Rightarrow> ('s, 'a + unit) automaton \<Rightarrow> 's states \<Rightarrow> 's states" where
  "epsilon_closure_iter 0 \<A> S = S" |
  "epsilon_closure_iter (Suc n) \<A> S = S \<union> epsilon_closure_iter n \<A> {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>}"

definition epsilon_closure_iterativ :: "'s state \<Rightarrow> ('s, 'a + unit) automaton \<Rightarrow> 's states" where
  "epsilon_closure_iterativ s \<A> = epsilon_closure_iter (card (states \<A>) - 1) \<A> {s}"

lemma eps_clos_iter_helper:
  assumes "auto_well_defined \<A>" 
  shows "S \<subseteq> states \<A> \<Longrightarrow> epsilon_closure_iter n \<A> S \<subseteq> states \<A>"
proof(induction n arbitrary: S)
  case 0 thus ?case by auto
next
  case (Suc n)
  have equi: "epsilon_closure_iter (Suc n) \<A> S = S \<union> epsilon_closure_iter n \<A> {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>}" by auto
  have "S \<subseteq> states \<A>" using Suc by auto
  hence "{s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>} \<subseteq> states \<A>" using assms well_def_trans_components by fast
  thus ?case using Suc equi by auto
qed

proposition eps_clos_iter_subset_states:
  assumes "auto_well_defined \<A>" "s \<in> states \<A>"
  shows "epsilon_closure_iterativ s \<A> \<subseteq> states \<A>"
proof -
  have s: "{s} \<subseteq> states \<A>" using assms by auto
  have "epsilon_closure_iterativ s \<A> = epsilon_closure_iter (card (states \<A>) - 1) \<A> {s}" unfolding epsilon_closure_iterativ_def by blast
  thus ?thesis using assms s eps_clos_iter_helper by metis
qed

proposition init_eps_clos: "s \<in> epsilon_closure_iterativ s \<A>"
proof - 
  have def: "epsilon_closure_iterativ s \<A> = epsilon_closure_iter (card (states \<A>) - 1) \<A> {s}" unfolding epsilon_closure_iterativ_def by blast
  thus ?thesis
  proof(cases "(card (states \<A>)) - 1")
    case 0 thus ?thesis using def by auto
  next
    case (Suc n) thus ?thesis using def by auto 
  qed
qed

proposition eps_iter_subset_division:
  assumes "auto_well_defined \<A>"
  shows "S \<subseteq> states \<A> \<and> S' \<subseteq> states \<A> \<Longrightarrow> epsilon_closure_iter n \<A> (S \<union> S') = epsilon_closure_iter n \<A> S \<union> epsilon_closure_iter n \<A> S'"
proof(induction n arbitrary: S S')
  case 0 thus ?case by auto
next
  case (Suc n)
  hence "S \<union> S' \<subseteq> states \<A>" by auto
  hence sub: "S \<union> S' \<subseteq> states \<A> \<and> {s2 . \<exists> s1 \<in> (S \<union> S') . (s1, Inr(), s2) \<in> transitions \<A>} \<subseteq> states \<A>" using assms well_def_trans_components by fast
  have "S \<subseteq> states \<A> \<and> S' \<subseteq> states \<A>" using Suc by auto
  hence subsub: "S \<subseteq> states \<A> \<and> S' \<subseteq> states \<A> \<and> {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>} \<subseteq> states \<A> \<and> {s2 . \<exists> s1 \<in> S' . (s1, Inr(), s2) \<in> transitions \<A>} \<subseteq> states \<A> " using assms well_def_trans_components by fast
  have "{s2 . \<exists> s1 \<in> (S \<union> S') . (s1, Inr(), s2) \<in> transitions \<A>} = {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>} \<union> {s2 . \<exists> s1 \<in> S' . (s1, Inr(), s2) \<in> transitions \<A>}" by blast
  hence left: "epsilon_closure_iter (Suc n) \<A> (S \<union> S') = S \<union> S' \<union> epsilon_closure_iter n \<A> {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>} \<union> epsilon_closure_iter n \<A> {s2 . \<exists> s1 \<in> S' . (s1, Inr(), s2) \<in> transitions \<A>}" using Suc subsub by auto
  have "epsilon_closure_iter (Suc n) \<A> S \<union> epsilon_closure_iter (Suc n) \<A> S' = S \<union> epsilon_closure_iter n \<A> {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>} \<union> S' \<union> epsilon_closure_iter n \<A> {s2 . \<exists> s1 \<in> S' . (s1, Inr(), s2) \<in> transitions \<A>}" using Suc subsub by auto
  thus ?case using left by blast
qed

lemma eps_closure_trans:
  assumes "auto_well_defined \<A>"
  shows "s \<in> epsilon_closure_iter (Suc n) \<A> S \<and> S \<subseteq> states \<A> \<Longrightarrow> s \<in> S \<or> (\<exists> s1 \<in> (epsilon_closure_iter n \<A> S) . (s1, Inr(), s) \<in> transitions \<A>)"
proof(induction n arbitrary: s S)
  case 0 thus ?case by auto
next
  case (Suc n)
  hence "s \<in> S \<union> epsilon_closure_iter (Suc n) \<A> {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>}" by auto
  hence props: "s \<in> S \<or> s \<in> epsilon_closure_iter (Suc n) \<A> {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>}" by blast
  let ?S' = "{s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>}"
  have "S \<subseteq> states \<A>" using Suc by argo
  hence "?S' \<subseteq> states \<A>" using assms well_def_trans_components by fast
  hence "s \<in> S \<or> s \<in> ?S' \<or> (\<exists> s1 \<in> (epsilon_closure_iter n \<A> ?S') . (s1, Inr(), s) \<in> transitions \<A>)" using Suc props by presburger
  hence step: "s \<in> S \<or> (\<exists> s1 \<in> S . (s1, Inr(), s) \<in> transitions \<A>) \<or> (\<exists> s1 \<in> (epsilon_closure_iter n \<A> ?S') . (s1, Inr(), s) \<in> transitions \<A>)" by blast
  have "S \<subseteq> (epsilon_closure_iter (Suc n) \<A> S) \<and> epsilon_closure_iter n \<A> ?S' \<subseteq> (epsilon_closure_iter (Suc n) \<A> S)" by auto
  thus ?case using step by blast
qed

lemma eps_clos_states_are_in_epsilon_closure_helper:
  assumes "auto_well_defined \<A>" "s' \<in> states \<A>"
  shows "s \<in> epsilon_closure_iter n \<A> {s'} \<Longrightarrow> epsilon_connected s' \<A> s"
proof(induction n arbitrary: s)
  case 0
  hence s: "s = s'" by auto
  thus ?case using assms s_to_s_epsilon_connection by fast
next
  case (Suc n)
  have "{s'} \<subseteq> states \<A>" using assms by auto
  hence "s = s' \<or> (\<exists> s1 \<in> (epsilon_closure_iter n \<A> {s'}) . (s1, Inr(), s) \<in> transitions \<A>)" using assms eps_closure_trans Suc by fast
  then consider (case1) "s = s'" | (case2) "(\<exists> s1 \<in> (epsilon_closure_iter n \<A> {s'}) . (s1, Inr(), s) \<in> transitions \<A>)" by blast
  thus ?case
  proof cases
    case case1 thus ?thesis using assms s_to_s_epsilon_connection by fast
  next
    case case2
    then obtain s1 where "s1 \<in> (epsilon_closure_iter n \<A> {s'}) \<and> (s1, Inr(), s) \<in> transitions \<A>" by auto
    hence "epsilon_connected s' \<A> s1 \<and> (s1, Inr(), s) \<in> transitions \<A>" using Suc by blast
    thus ?thesis using assms transitivity_esp_connected by fast
  qed
qed

theorem eps_clos_states_are_in_epsilon_closure:
  assumes "auto_well_defined \<A>" "s' \<in> states \<A>"
  shows "s \<in> epsilon_closure_iterativ s' \<A> \<Longrightarrow> epsilon_connected s' \<A> s"
  using assms eps_clos_states_are_in_epsilon_closure_helper unfolding epsilon_closure_iterativ_def by fast

lemma eps_clos_inheritance_general:
  assumes "auto_well_defined \<A>"
  shows "s' \<in> epsilon_closure_iter n \<A> S \<and> (s', Inr(), s) \<in> transitions \<A> \<Longrightarrow> s \<in> epsilon_closure_iter (Suc n) \<A> S"
proof(induction n arbitrary: S s' s)
  case 0 thus ?case by auto
next
  case (Suc n)
  hence "s' \<in> epsilon_closure_iter (Suc n) \<A> S \<and> (s', Inr(), s) \<in> transitions \<A>" by blast
  hence "s' \<in> S \<or> s'\<in> epsilon_closure_iter n \<A> {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>} \<and> (s', Inr(), s) \<in> transitions \<A>" by auto
  hence "s' \<in> S \<and> (s', Inr(), s) \<in> transitions \<A> \<or> s \<in> epsilon_closure_iter (Suc n) \<A> {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>}" using Suc by blast
  hence "s \<in> {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>} \<or> s \<in> epsilon_closure_iter (Suc n) \<A> {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>}" by fast
  hence "s \<in> epsilon_closure_iter (Suc n) \<A> {s2 . \<exists> s1 \<in> S . (s1, Inr(), s2) \<in> transitions \<A>}" by simp
  thus ?case by auto
qed

lemma sub_eps_runs:
  assumes "eps_run_well_defined eps_run \<A> s" "n \<le> length eps_run - 1"
  shows "eps_run_well_defined (take (Suc n) eps_run) \<A> s \<and> length (take (Suc n) eps_run) \<le> length eps_run"
proof -
  have not_empty: "eps_run \<noteq> [] \<and> n \<le> length eps_run - 1 \<and> s \<in> states \<A> \<and> eps_run ! 0 = s " using assms unfolding eps_run_well_defined_def by blast
  hence "length eps_run > 0" by auto
  hence "Suc n > 0 \<and> Suc n \<le> length eps_run" using not_empty by linarith
  hence "length (take (Suc n) eps_run) = Suc n" using assms not_empty by auto
  hence len: "0 < length (take (Suc n) eps_run) \<and> length (take (Suc n) eps_run) - 1 \<le> length eps_run - 1" using assms by auto
  hence equi: "\<forall> i < length (take (Suc n) eps_run) - 1 . eps_run ! i = (take (Suc n) eps_run) ! i \<and> eps_run ! (i + 1) = (take (Suc n) eps_run) ! (i + 1)" by fastforce
  hence init: "eps_run ! 0 = (take (Suc n) eps_run) ! 0" by auto
  have "\<forall> i < length eps_run - 1 . (eps_run ! i, Inr(), eps_run ! (i + 1)) \<in> transitions \<A>" using assms unfolding eps_run_well_defined_def by argo
  hence "\<forall> i < length (take (Suc n) eps_run) - 1 . (eps_run ! i, Inr(), eps_run ! (i + 1)) \<in> transitions \<A>" using len by auto
  hence "\<forall> i < length (take (Suc n) eps_run) - 1 . ((take (Suc n) eps_run) ! i, Inr(), (take (Suc n) eps_run) ! (i + 1)) \<in> transitions \<A>" using equi by metis
  hence "eps_run_well_defined (take (Suc n) eps_run) \<A> s" using not_empty len init unfolding eps_run_well_defined_def by metis
  thus ?thesis using len by auto
qed

lemma eps_run_def_sublist1:
  assumes "eps_run_well_defined eps_run \<A> s" "i < length eps_run \<and> j < length eps_run \<and> i \<noteq> j \<and> eps_run ! i = eps_run ! j \<and> i < j" "j = length eps_run - 1"
  shows "\<forall> k < length ((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run)) - 1 . (((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run)) ! k, Inr(), ((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run)) ! (k + 1)) \<in> transitions \<A>"
proof -
  let ?subrun = "((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run))"
  have equi_run: "?subrun = (take (Suc i) eps_run)" using assms unfolding sublist_def by fastforce
  have "i \<le> length eps_run - 1" using assms by linarith
  hence "eps_run_well_defined ?subrun \<A> s" using assms sub_eps_runs equi_run by metis
  thus ?thesis using equi_run unfolding eps_run_well_defined_def by argo
qed

lemma eps_equi_sublist:
  assumes "eps_run_well_defined eps_run \<A> s" "j < length eps_run - 1"
  shows "\<forall> k < length (sublist (Suc j) (length eps_run) eps_run) - 1 . (((sublist (Suc j) (length eps_run) eps_run)) ! k, ((sublist (Suc j) (length eps_run) eps_run)) ! (k + 1), Inr()) = (eps_run ! (j + k + 1), eps_run ! (j + k + 1 + 1), Inr())"
proof -
  {
    fix k assume "k < length (sublist (Suc j) (length eps_run) eps_run) - 1"
    have len: "length eps_run > 0" using assms by force
    hence runk: "eps_run ! (j + 1 + k) = (sublist (Suc j) (length eps_run) eps_run) ! k" using assms unfolding sublist_def by force
    hence runk1: "eps_run ! (j + 1 + k + 1) = (sublist (Suc j) (length eps_run) eps_run) ! (k + 1)" using assms unfolding sublist_def by force
    hence "(((sublist (Suc j) (length eps_run) eps_run)) ! k, ((sublist (Suc j) (length eps_run) eps_run)) ! (k + 1), Inr()) = (eps_run ! (j + k + 1), eps_run ! (j + k + 1 + 1), Inr())" using runk runk1 by auto
  }
  thus ?thesis by blast
qed

lemma eps_run_def_sublist2:
  assumes "eps_run_well_defined eps_run \<A> s" "i < length eps_run \<and> j < length eps_run \<and> i \<noteq> j \<and> eps_run ! i = eps_run ! j \<and> i < j" "j < length eps_run - 1"
  shows "length ((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run)) > 0 \<and> (\<forall> k < length ((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run)) - 1 . (((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run)) ! k, Inr(), ((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run)) ! (k + 1)) \<in> transitions \<A>)"
proof -
  let ?subrun1 = "take (Suc i) eps_run"
  let ?subrun2 = "sublist (Suc j) (length eps_run) eps_run"
  let ?subrun = "?subrun1 @ ?subrun2"
  have not_empty: "eps_run \<noteq> [] \<and> i < length eps_run" using assms by fastforce
  have length: "length ?subrun > 0" using assms by auto
  have original_trans: "\<forall> k < length eps_run - 1 . (eps_run ! k, Inr(), eps_run ! (k + 1)) \<in> transitions \<A>" using assms unfolding eps_run_well_defined_def by blast
  hence trans: "\<forall> k < length ?subrun1 - 1 . (?subrun1 ! k, Inr(), ?subrun1 ! (k + 1)) \<in> transitions \<A>" by force 
  have step: "(eps_run ! j, Inr(), eps_run ! (j + 1)) \<in> transitions \<A>" using assms unfolding eps_run_well_defined_def by blast
  have "last ?subrun1 = ?subrun1 ! i" using last_and_take_list list_properties_not_empty not_empty by blast
  hence runj: "eps_run ! j = last ?subrun1" using assms by auto
  have runj1: "eps_run ! (j + 1) = ?subrun2 ! 0" using assms not_empty unfolding sublist_def by fastforce
  hence trans_step: "(last ?subrun1, Inr(), ?subrun2 ! 0) \<in> transitions \<A>" using step runj1 runj by auto
  have equi: "\<forall> k < length ?subrun2 - 1 . (?subrun2 ! k, ?subrun2 ! (k + 1), Inr()) = (eps_run ! (j + k + 1), eps_run ! (j + k + 1 + 1), Inr())" using assms eps_equi_sublist by fast
  have "j > 0 \<and> length ?subrun2 = length eps_run - Suc j" using assms not_empty unfolding sublist_def by auto
  hence "\<forall> l < length ?subrun2 - 1 . (eps_run ! (j + l + 1), Inr(), eps_run ! (Suc j + l + 1)) \<in> transitions \<A>" using original_trans less_diff_conv by auto
  hence Nil_l: "\<forall> l < length ?subrun2 - 1 . (?subrun2 ! l, Inr(), ?subrun2 ! (l + 1)) \<in> transitions \<A>" using equi by auto
  hence sub_trans: "\<forall> m . m < length ?subrun2 + length ?subrun1 - 1 \<and> m \<ge> length ?subrun1 \<longrightarrow> (?subrun2 ! (m - length ?subrun1), Inr(), ?subrun2 ! (m + 1 - length ?subrun1)) \<in> transitions \<A>"
  proof -
    {
      fix m assume assm: "m < length ?subrun2 + length ?subrun1 - 1 \<and> m \<ge> length ?subrun1"
      let ?l = "m - length ?subrun1"
      have range: "0 \<le> ?l \<and> ?l < length ?subrun2 -1" using assm by linarith
      hence in_trans: "(?subrun2 ! ?l, Inr(), ?subrun2 ! (?l + 1)) \<in> transitions \<A>" using Nil_l assm by fast
      have "?subrun2 ! ?l = ?subrun2 ! (m - length ?subrun1) \<and> ?subrun2 ! (?l + 1) = ?subrun2 ! (m + 1 - length ?subrun1)" using assm Nat.add_diff_assoc2 by presburger
      hence "(?subrun2 ! (m - length ?subrun1), Inr(), ?subrun2 ! (m + 1 - length ?subrun1)) \<in> transitions \<A>" using in_trans by presburger
    }
    thus ?thesis by blast
  qed
  hence "\<forall> k < length ?subrun - 1 . (?subrun ! k, Inr(), ?subrun ! (k + 1)) \<in> transitions \<A>"
  proof -
    {
      fix k assume k: "k < length ?subrun - 1"
      hence "(?subrun ! k, Inr(), ?subrun ! (k + 1)) \<in> transitions \<A>"
      proof - 
        consider (case1) "k < length ?subrun1 - 1" | (case2) "k = length ?subrun1 - 1" | (case3) "k > length ?subrun1 - 1 \<and> k < length ?subrun - 1" using k by linarith
        thus ?thesis
        proof cases
          case case1 thus ?thesis using trans list_append_position4 by metis
        next
          case case2
          hence "length ?subrun1 > 0 \<and> ?subrun2 \<noteq> []" using assms unfolding sublist_def by fastforce
          hence "?subrun ! k = last ?subrun1 \<and> ?subrun ! (k + 1) = ?subrun2 ! 0" using case2 list_append_position5 by fast
          thus ?thesis using case2 trans_step by argo
        next
          case case3
          hence "length ?subrun1 > 0 \<and> ?subrun2 \<noteq> []" using assms unfolding sublist_def by fastforce 
          hence equi_k: "(?subrun1 @ ?subrun2) ! k = ?subrun2 ! (k - length ?subrun1) \<and> (?subrun1 @ ?subrun2) ! (k + 1) = ?subrun2 ! (k + 1 - length ?subrun1)" using case3 list_append_position6 by blast
          have "k < length ?subrun2 + length ?subrun1 - 1 \<and> k \<ge> length ?subrun1" using case3 by force
          thus ?thesis using sub_trans equi_k by presburger
        qed
      qed
    }
    thus ?thesis by blast
  qed
  thus ?thesis using length by blast
qed

lemma eps_run_initial_state:
  assumes "eps_run_well_defined eps_run \<A> s"
  shows "((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run)) ! 0 = s"
proof -
  have not_empty: "eps_run \<noteq> [] \<and> (take (Suc i) eps_run) \<noteq> [] \<and> eps_run ! 0 = s" using assms unfolding eps_run_well_defined_def by auto
  hence "eps_run ! 0 = (take (Suc i) eps_run) ! 0" by auto 
  thus ?thesis using assms not_empty list_properties_not_empty by metis
qed

lemma eps_run_last_state:
  assumes "i < length eps_run \<and> j < length eps_run \<and> i \<noteq> j \<and> eps_run ! i = eps_run ! j \<and> i < j"
  shows "last eps_run = last ((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run))"
proof -
  have not_empty: "eps_run \<noteq> []" using assms by force
  consider (case1) "j = length eps_run - 1" | (case2) "j < length eps_run - 1" using assms by linarith
  thus ?thesis
  proof cases
    case case1 
    hence "eps_run ! i = last eps_run" using assms not_empty list_properties_not_empty by metis
    thus ?thesis using assms not_empty unfolding sublist_def by (simp add: last_and_take_list list_properties_not_empty last_append)
  next
    case case2 thus ?thesis using assms unfolding sublist_def by auto
  next
  qed
qed

proposition eps_run_sublist:
  assumes "eps_run_well_defined eps_run \<A> s'" "i < length eps_run \<and> j < length eps_run \<and> i \<noteq> j \<and> eps_run ! i = eps_run ! j \<and> i < j"
  shows "eps_run_well_defined ((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run)) \<A> s' \<and> last eps_run = last ((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run)) \<and> length eps_run > length ((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run))"
proof - 
  let ?subrun = "((take (Suc i) eps_run) @ (sublist (Suc j) (length eps_run) eps_run))"
  have not_empty: "eps_run \<noteq> [] \<and> eps_run ! 0 = s' \<and> s' \<in> states \<A>" using assms unfolding eps_run_well_defined_def by fast
  consider (case1) "j < length eps_run - 1" | (case2) "j = length eps_run - 1" using assms by linarith
  thus ?thesis
  proof cases
    case case1
    hence "length ?subrun > 0 \<and> (\<forall> k < length ?subrun - 1 . (?subrun ! k, Inr(), ?subrun ! (k + 1)) \<in> transitions \<A>)" using not_empty assms eps_run_def_sublist2 by metis
    hence well_def: "eps_run_well_defined ?subrun \<A> s'" using assms not_empty eps_run_initial_state unfolding eps_run_well_defined_def by metis
    hence "length eps_run > length ?subrun" using assms not_empty length_sublist3 by blast
    thus ?thesis using assms eps_run_last_state well_def by metis
  next
    case case2
    hence length: "length ?subrun > 0" using not_empty by auto
    hence "\<forall> k < length ?subrun - 1 . (?subrun ! k, Inr(), ?subrun ! (k + 1)) \<in> transitions \<A>" using case2 not_empty assms eps_run_def_sublist1 by metis
    hence well_def: "eps_run_well_defined ?subrun \<A> s'" using length assms not_empty eps_run_initial_state unfolding eps_run_well_defined_def by metis
    hence "length eps_run > length ?subrun" using assms not_empty length_sublist3 by blast
    thus ?thesis using assms eps_run_last_state well_def by fast
  qed
qed

lemma eps_runs_multiple_states:
  assumes "auto_well_defined \<A>" "length eps_run = Suc (card (states \<A>))" "eps_run_well_defined eps_run \<A> s'"
  shows "\<exists> i < length eps_run . \<exists> j < length eps_run . i \<noteq> j \<and> eps_run ! i = eps_run ! j"
proof(rule ccontr)
  assume assm: "\<not> (\<exists> i < length eps_run . \<exists> j < length eps_run . i \<noteq> j \<and> eps_run ! i = eps_run ! j)"
  have eps_run_states: "prun_states eps_run \<A>" using assms eps_run_states by fast
  have "finite (states \<A>)" using assms unfolding auto_well_defined_def by blast
  hence card: "card (set eps_run) \<le> card (states \<A>)" using eps_run_states Finite_Set.card_mono unfolding prun_states_def by auto
  have "distinct eps_run" using assm distinct_conv_nth by blast
  hence "card (set eps_run) > card (states \<A>)" using assms distinct_card by fastforce
  thus "False" using card by linarith
qed

lemma worst_case_shorter_eps_runs:
  assumes "auto_well_defined \<A>" "length eps_run = Suc (card (states \<A>))" "eps_run_well_defined eps_run \<A> s'" "s \<in> set eps_run" "k = length eps_run - 1 \<and> eps_run ! k = s"
  shows "\<exists> eps_run' . eps_run_well_defined eps_run' \<A> s' \<and> length eps_run' < length eps_run \<and> last eps_run' = s"
proof - 
  have "length eps_run = k + 1 \<and> eps_run \<noteq> []" using assms by auto
  hence last: "s = last eps_run" using assms list_properties_not_empty by fast
  have "\<exists> i < length eps_run . \<exists> j < length eps_run . i \<noteq> j \<and> eps_run ! i = eps_run ! j" using assms eps_runs_multiple_states by fast
  then obtain i j where ij: "i < length eps_run \<and> j < length eps_run \<and> i \<noteq> j \<and> eps_run ! i = eps_run ! j" by blast
  then consider (case1) "i < j" | (case2) "j < i" by linarith
  thus ?thesis
  proof cases
    case case1 thus ?thesis using assms last eps_run_sublist ij by metis
  next
    case case2 thus ?thesis using assms last eps_run_sublist ij by metis
  qed
qed

lemma existence_shorter_eps_runs:
  assumes "auto_well_defined \<A>" "length eps_run = Suc (card (states \<A>))" "eps_run_well_defined eps_run \<A> s'" "s \<in> set eps_run"
  shows "\<exists> eps_run' . eps_run_well_defined eps_run' \<A> s' \<and> length eps_run' < length eps_run \<and> last eps_run' = s"
proof - 
  have "\<exists> k < length eps_run . eps_run ! k = s" using assms in_set_conv_nth by metis
  then obtain k where k: "k < length eps_run \<and> eps_run ! k = s" by auto
  hence len: "k \<le> length eps_run - 1" using assms by auto
  hence well_def: "eps_run_well_defined (take (Suc k) eps_run) \<A> s' \<and> length (take (Suc k) eps_run) \<le> length eps_run" using assms sub_eps_runs by fast
  have "eps_run \<noteq> []" using assms by auto
  hence eps_run: "eps_run_well_defined (take (Suc k) eps_run) \<A> s' \<and> last (take (Suc k) eps_run) = s" using k last_and_take_list list_properties_not_empty well_def by auto
  consider (case1) "k < length eps_run - 1" | (case2) "k = length eps_run - 1" using len by fastforce
  thus ?thesis
 proof cases
   case case1 thus ?thesis using eps_run by auto
 next
   case case2 thus ?thesis using assms worst_case_shorter_eps_runs k by fast
 qed
qed

proposition existence_sub_eps_runs:
  assumes "auto_well_defined \<A>"
  shows "eps_run_well_defined eps_run \<A> s' \<longrightarrow> (\<exists> eps_run' . eps_run_well_defined eps_run' \<A> s' \<and> last eps_run' = last eps_run \<and> length eps_run' \<le> card (states \<A>))"
proof - 
  consider (case1) "length eps_run \<le> card (states \<A>)" | (case2) "length eps_run \<ge> Suc (card (states \<A>))" by linarith
  thus ?thesis
  proof cases
    case case1 thus ?thesis by auto
  next
    case case2
    {
      fix eps_run assume assm: "eps_run_well_defined eps_run \<A> s' \<and> length eps_run \<ge> Suc (card (states \<A>))"
      hence "\<exists> eps_run' . eps_run_well_defined eps_run' \<A> s' \<and> last eps_run' = last eps_run \<and> length eps_run' \<le> card (states \<A>)"
      proof(induction "length eps_run - Suc (card (states \<A>))" arbitrary: eps_run)
        case 0
        hence "eps_run \<noteq> []" by auto
        hence "last eps_run \<in> set eps_run" using assm 0 by auto
        thus ?case using assms existence_shorter_eps_runs 0 by fastforce
      next
        case (Suc n)
        hence props: "eps_run_well_defined eps_run \<A> s' \<and> length eps_run = Suc (card (states \<A>)) + Suc n \<and> length eps_run > 1" using assms unfolding run_well_defined_def by linarith
        have "eps_run \<noteq> []" using Suc by force
        then obtain eps_run' where eps_run': "eps_run = eps_run' @ [last eps_run]" using append_butlast_last_id by metis
        hence well_def: "eps_run_well_defined eps_run' \<A> s' \<and> (last eps_run', Inr(), last eps_run) \<in> transitions \<A>" using assms props eps_run_well_defined_extension by metis
        have "length (eps_run' @ [last eps_run]) = Suc (card (states \<A>)) + Suc n \<and> length (eps_run' @ [last eps_run]) > 1" using eps_run' props by argo
        hence len: "length eps_run' = Suc (card (states \<A>)) + n \<and> length eps_run' \<ge> Suc (card (states \<A>))" by auto
        hence "\<exists> eps_run'' . eps_run_well_defined eps_run'' \<A> s' \<and> last eps_run'' = (last eps_run') \<and> length eps_run'' \<le> card (states \<A>)" using well_def Suc by auto
        then obtain eps_run'' where eps_run'': "eps_run_well_defined eps_run'' \<A> s' \<and> last eps_run'' = last eps_run' \<and> length eps_run'' \<le> card (states \<A>)" by blast
        then consider (case3) "length eps_run'' < card (states \<A>)" | (case4) "length eps_run'' = card (states \<A>)" by linarith
        thus ?case
        proof cases
          case case3 
          hence length: "length (eps_run'' @ [last eps_run]) < Suc (card (states \<A>))" by auto
          have "eps_run_well_defined (eps_run'' @ [last eps_run]) \<A> s'" using eps_run_well_defined_extension assms eps_run'' well_def by metis
          thus ?thesis using length by auto
        next
          case case4
          hence length: "length (eps_run'' @ [last eps_run]) = Suc (card (states \<A>)) \<and> last eps_run \<in> set (eps_run'' @ [last eps_run])" by auto
          have "eps_run_well_defined (eps_run'' @ [last eps_run]) \<A> s'" using eps_run_well_defined_extension assms eps_run'' well_def by metis
          hence "\<exists> eps_run2 . eps_run_well_defined eps_run2 \<A> s' \<and> length eps_run2 < length (eps_run'' @ [last eps_run]) \<and> last eps_run2 = last eps_run" using length existence_shorter_eps_runs assms by fast
          thus ?thesis using length by auto
        qed
      qed
    }
    thus ?thesis by fastforce
  qed
qed

lemma equivalence_epsilon_closure_iter_left:
  assumes "auto_well_defined \<A>" "s \<in> epsilon_closure_iterativ s' \<A>" "s' \<in> states \<A>"
  shows "\<exists> eps_run . eps_run_well_defined eps_run \<A> s' \<and> last eps_run = s \<and> length eps_run \<le> card (states \<A>)"
proof -
  have "epsilon_connected s' \<A> s" using assms eps_clos_states_are_in_epsilon_closure by fast
  hence "\<exists> eps_run . eps_run_well_defined eps_run \<A> s' \<and> last eps_run = s" unfolding epsilon_connected_def by auto
  then obtain eps_run where "eps_run_well_defined eps_run \<A> s' \<and> last eps_run = s" by auto
  thus ?thesis using existence_sub_eps_runs assms by fast
qed

lemma equivalence_epsilon_closure_iter_right_helper:
  assumes "auto_well_defined \<A>"
  shows "eps_run_well_defined eps_run \<A> s' \<and> length eps_run \<le> Suc n \<Longrightarrow> last eps_run \<in> epsilon_closure_iter n \<A> {s'}"
proof(induction n arbitrary: eps_run s')
  case 0
  hence "length eps_run = 1 \<and> eps_run ! 0 = s'" unfolding eps_run_well_defined_def by linarith
  hence "last eps_run = s'" using list_with_one_element by metis  
  thus ?case by auto
next
  case (Suc n)
  hence props: "eps_run_well_defined eps_run \<A> s' \<and> length eps_run \<le> Suc (Suc n)" by auto
  consider (case1) "length eps_run = 1" | (case2) "length eps_run > 1" using Suc unfolding eps_run_well_defined_def by linarith
  thus ?case
  proof cases
    case case1
    hence "length eps_run = 1 \<and> eps_run ! 0 = s'" using props unfolding eps_run_well_defined_def by linarith
    hence "last eps_run = s'" using list_with_one_element by metis
    thus ?thesis by auto
  next
    case case2
    hence "eps_run \<noteq> []" by force
    then obtain eps_run' where eps_run': "eps_run = eps_run' @ [last eps_run]" using append_butlast_last_id by metis
    hence well_def: "eps_run_well_defined eps_run' \<A> s' \<and> (last eps_run', Inr(), last eps_run) \<in> transitions \<A>" using case2 eps_run_well_defined_extension assms Suc by metis
    have "length (eps_run' @ [last eps_run]) \<le> Suc (Suc n)" using eps_run' props by auto
    hence "length eps_run' \<le> Suc n" by auto
    hence "last eps_run' \<in> epsilon_closure_iter n \<A> {s'} \<and> (last eps_run', Inr(), last eps_run) \<in> transitions \<A>" using well_def Suc by blast
    thus ?thesis using eps_clos_inheritance_general assms by fast
  qed
qed

lemma equivalence_epsilon_closure_iter_right:
  assumes "auto_well_defined \<A>" "eps_run_well_defined eps_run \<A> s'" "length eps_run \<le> card (states \<A>)"
  shows "last eps_run \<in> epsilon_closure_iterativ s' \<A>"
  using assms equivalence_epsilon_closure_iter_right_helper unfolding epsilon_closure_iterativ_def by fastforce

proposition equivalence_epsilon_closure_iterativ:
  assumes "auto_well_defined \<A>" "s' \<in> states \<A>"
  shows "s \<in> epsilon_closure_iterativ s' \<A> \<longleftrightarrow> (\<exists> eps_run . eps_run_well_defined eps_run \<A> s' \<and> last eps_run = s \<and> length eps_run \<le> card (states \<A>))"
  using assms equivalence_epsilon_closure_iter_right equivalence_epsilon_closure_iter_left by fast

text \<open>Main Theorem for iterativ epsilon closure\<close>
theorem equivalence_of_epsilon_closure:
  assumes "auto_well_defined \<A>" "s' \<in> states \<A>"
  shows "epsilon_closure s' \<A> = epsilon_closure_iterativ s' \<A>"
proof -
  {
    fix s assume "s \<in> epsilon_closure s' \<A>"
    hence "epsilon_connected s' \<A> s" unfolding epsilon_closure_def by auto
    hence "\<exists> eps_run . eps_run_well_defined eps_run \<A> s' \<and> last eps_run = s" unfolding epsilon_connected_def by auto
    hence "\<exists> eps_run . eps_run_well_defined eps_run \<A> s' \<and> last eps_run = s \<and> length eps_run \<le> card (states \<A>)" using assms existence_sub_eps_runs by fast
    hence "s \<in> epsilon_closure_iterativ s' \<A>" using assms equivalence_epsilon_closure_iterativ by fast
  }
  hence left: "epsilon_closure s' \<A> \<subseteq> epsilon_closure_iterativ s' \<A>" by auto
  {
    fix s assume "s \<in> epsilon_closure_iterativ s' \<A>"
    hence "\<exists> eps_run . eps_run_well_defined eps_run \<A> s' \<and> last eps_run = s" using assms equivalence_epsilon_closure_iterativ by fast
    hence "s \<in> epsilon_closure s' \<A>" unfolding epsilon_closure_def epsilon_connected_def by auto
  }
  hence "epsilon_closure_iterativ s' \<A> \<subseteq> epsilon_closure s' \<A>" by auto
  thus ?thesis using left by auto
qed

end