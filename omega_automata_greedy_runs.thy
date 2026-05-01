theory omega_automata_greedy_runs

imports Main omega_automata_omega_power

begin

text \<open>Author: Benno Thalmann, last update: 1.5.2026, Addition to masterarbeit_benno_thalmann\<close>

fun acc_sum :: "('s, 'a) automaton \<Rightarrow> 's run \<Rightarrow> nat" where
  "acc_sum \<A> [] = 0" |
  "acc_sum \<A> (s # run) = (if s \<in> accepting_states \<A> then (2 ^ length run + acc_sum \<A> run) else acc_sum \<A> run)"

proposition acc_sum_bounded: "acc_sum \<A> list \<ge> 0 \<and> acc_sum \<A> list \<le> 2 ^ (length list) - 1"
  by(induction list) auto

proposition acc_sum_snoc: "acc_sum \<A> (list @ [x]) = 2 * acc_sum \<A> list + acc_sum \<A> [x]"
  by(induction list) auto

lemma acc_sum_last_equal:
  assumes "2 * acc_sum \<A> list1 + acc_sum \<A> [x1] = 2 * acc_sum \<A> list2 + acc_sum \<A> [x2]"
  shows "acc_sum \<A> [x1] = acc_sum \<A> [x2] \<and> acc_sum \<A> list1 = acc_sum \<A> list2"
proof -
  have mod2: "(2 * acc_sum \<A> list1 + acc_sum \<A> [x1]) mod 2  = acc_sum \<A> [x1]" by force
  have "(2 * acc_sum \<A> list2 + acc_sum \<A> [x2]) mod 2  = acc_sum \<A> [x2]" by force
  hence x_equi: "acc_sum \<A> [x1] = acc_sum \<A> [x2]" using mod2 assms by argo
  hence "2 * acc_sum \<A> list1 = 2 * acc_sum \<A> list2" using assms by auto
  thus ?thesis using x_equi by simp
qed

lemma same_acc_sum_same_acc_sum_left: "length alpha = length beta \<and> length alpha' = length beta' \<and> acc_sum \<A> (alpha @ alpha') = acc_sum \<A> (beta @ beta') \<Longrightarrow> acc_sum \<A> alpha = acc_sum \<A> beta \<and> acc_sum \<A> alpha' = acc_sum \<A> beta'"
proof(induction alpha' arbitrary: alpha beta beta' rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc a alpha')
  hence "length (alpha' @ [a]) = length beta'" by blast
  hence "beta' \<noteq> []" by auto
  then obtain b beta'' where b: "beta' = beta'' @ [b]" using append_butlast_last_id by metis
  hence "length alpha = length beta \<and> length (alpha' @ [a]) = length (beta'' @ [b]) \<and> acc_sum \<A> (alpha @ alpha' @ [a]) = acc_sum \<A> (beta @ beta'' @ [b])" using snoc by blast
  hence props: "length alpha = length beta \<and> length alpha' = length beta'' \<and> acc_sum \<A> (alpha @ alpha' @ [a]) = acc_sum \<A> (beta @ beta'' @ [b])" by simp
  have "acc_sum \<A> (alpha @ alpha' @ [a]) = acc_sum \<A> ((alpha @ alpha') @ [a]) \<and> acc_sum \<A> (beta @ beta'' @ [b]) = acc_sum \<A> ((beta @ beta'') @ [b])" by auto
  hence "length alpha = length beta \<and> length alpha' = length beta'' \<and> acc_sum \<A> (alpha @ alpha') = acc_sum \<A> (beta @ beta'') \<and> acc_sum \<A> [a] = acc_sum \<A> [b]" using props acc_sum_snoc acc_sum_last_equal by metis
  hence more_props: "length alpha = length beta \<and> length alpha' = length beta'' \<and> acc_sum \<A> alpha = acc_sum \<A> beta \<and> acc_sum \<A> alpha' = acc_sum \<A> beta'' \<and> acc_sum \<A> [a] = acc_sum \<A> [b]" using snoc by blast
  thus ?case using acc_sum_snoc b by metis
qed

lemma same_acc_sum_same_acc_sum_right: "length alpha = length beta \<and> length alpha' = length beta' \<and> acc_sum \<A> alpha = acc_sum \<A> beta \<and> acc_sum \<A> alpha' = acc_sum \<A> beta' \<Longrightarrow> acc_sum \<A> (alpha @ alpha') = acc_sum \<A> (beta @ beta')"
proof(induction alpha' arbitrary: alpha beta beta' rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc a alpha')
  hence "length (alpha' @ [a]) = length beta'" by blast
  hence "beta' \<noteq> []" by auto
  then obtain b beta'' where b: "beta' = beta'' @ [b]" using append_butlast_last_id by metis
  hence "length alpha = length beta \<and> length (alpha' @ [a]) = length (beta'' @ [b]) \<and> acc_sum \<A> alpha = acc_sum \<A> beta \<and> acc_sum \<A> (alpha' @ [a]) = acc_sum \<A> (beta'' @ [b])" using snoc by blast
  hence "length alpha = length beta \<and> length alpha' = length beta'' \<and> acc_sum \<A> alpha = acc_sum \<A> beta \<and> acc_sum \<A> (alpha' @ [a]) = acc_sum \<A> (beta'' @ [b])" by force
  hence props: "length alpha = length beta \<and> length alpha' = length beta'' \<and> acc_sum \<A> alpha = acc_sum \<A> beta \<and> acc_sum \<A> alpha' = acc_sum \<A> beta'' \<and> acc_sum \<A> [a] = acc_sum \<A> [b]" using acc_sum_snoc acc_sum_last_equal by metis
  hence "length (alpha @ alpha') = length (beta @ beta'') \<and> acc_sum \<A> (alpha @ alpha') = acc_sum \<A> (beta @ beta'') \<and> acc_sum \<A> [a] = acc_sum \<A> [b]" using snoc by simp
  hence "2 * acc_sum \<A> (alpha @ alpha') + acc_sum \<A> [a] = 2 * acc_sum \<A> (beta @ beta'') + acc_sum \<A> [b]" using acc_sum_last_equal by argo
  hence "acc_sum \<A> ((alpha @ alpha') @ [a]) = acc_sum \<A> ((beta @ beta'') @ [b])" using acc_sum_snoc by metis
  thus ?case using b by simp
qed

proposition same_acc_sum_same_acc_sum: 
  assumes "length alpha = length beta \<and> length alpha' = length beta'"
  shows "acc_sum \<A> alpha = acc_sum \<A> beta \<and> acc_sum \<A> alpha' = acc_sum \<A> beta' \<longleftrightarrow> acc_sum \<A> (alpha @ alpha') = acc_sum \<A> (beta @ beta')"
  using assms same_acc_sum_same_acc_sum_right same_acc_sum_same_acc_sum_left by blast

definition greedy_run :: "'s run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a word \<Rightarrow> bool" where "greedy_run run \<A> word = (run_well_defined run \<A> word \<and> (\<nexists> run' . run_well_defined run' \<A> word \<and> last run' = last run \<and> (acc_sum \<A> run') > (acc_sum \<A> run)))"

proposition greedy_run_snoc:
  assumes "greedy_run (run @ [s]) \<A> (word @ [a])"
  shows "greedy_run run \<A> word"
proof(rule ccontr)
  assume assm: "\<not> greedy_run run \<A> word"
  have trans: "run_well_defined run \<A> word \<and> (last run, a, s) \<in> transitions \<A>" using assms prun_well_defined_extension_snoc unfolding greedy_run_def run_well_defined_def by fast
  hence "\<exists> run' . run_well_defined run' \<A> word \<and> last run' = last run \<and> (acc_sum \<A> run') > (acc_sum \<A> run)" using assm unfolding greedy_run_def by blast
  then obtain run' where run': "run_well_defined run' \<A> word \<and> last run' = last run \<and> (acc_sum \<A> run') > (acc_sum \<A> run)" by blast
  hence well_def: "run_well_defined (run' @ [s]) \<A> (word @ [a])" using trans prun_well_defined_extension_snoc unfolding run_well_defined_def by metis
  have acc: "acc_sum \<A> (run' @ [s]) = 2 * acc_sum \<A> run' + acc_sum \<A> [s]" using acc_sum_snoc by fast
  have "acc_sum \<A> (run @ [s]) = 2 * acc_sum \<A> run + acc_sum \<A> [s]" using acc_sum_snoc by fast
  hence acc_less: "acc_sum \<A> (run' @ [s]) > acc_sum \<A> (run @ [s])" using run' acc by simp
  have "last (run @ [s]) = last (run' @ [s])" by simp
  thus False using run' assms acc_less well_def unfolding greedy_run_def by force
qed

lemma greedy_run_take: "greedy_run run \<A> word \<and> m \<le> length word \<Longrightarrow> greedy_run (take (m + 1) run) \<A> (take m word)"
proof (induction "length word - m" arbitrary: run word m rule: nat_less_induct)
  case 1 thus ?case
  proof (cases "m = length word")
    case True
    have gr: "greedy_run run \<A> word" using 1 by simp
    hence "run_well_defined run \<A> word" unfolding greedy_run_def by simp
    hence "length run = length word + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by simp
    hence take: "take (m + 1) run = run" using True by simp
    have "take m word = word" using True by simp
    thus ?thesis using gr take by simp
  next
    case False
    hence mlt: "m < length word" using 1 by simp
    hence "word \<noteq> []" by force
    then obtain word' a where word: "word = word' @ [a]" using append_butlast_last_id by metis
    have gr: "greedy_run run \<A> word" using 1 by simp
    hence "run_well_defined run \<A> word" unfolding greedy_run_def by simp
    hence len: "length run = length word + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by simp
    hence "run \<noteq> []" by auto
    then obtain run' s where run: "run = run' @ [s]" using append_butlast_last_id by metis
    hence gr': "greedy_run run' \<A> word'" using gr greedy_run_snoc word by fast
    have mle': "m \<le> length word'" using mlt unfolding word by simp
    hence "length word' - m < length word - m" unfolding word by (simp add: diff_less_mono mle')
    hence IH: "greedy_run (take (m + 1) run') \<A> (take m word')" using 1 gr' mle' by blast
    have take: "take (m + 1) run = take (m + 1) run'" using mle' len run word by simp
    have "take m word = take m word'" using mle' word by simp
    thus ?thesis using IH take by simp
  qed
qed

definition runs_with_end :: "('s, 'a) automaton \<Rightarrow> 'a word \<Rightarrow> 's state \<Rightarrow> 's run set" where "runs_with_end \<A> word s = {run . run_well_defined run \<A> word \<and> last run = s}"

lemma finite_runs_with_end:
  assumes "auto_well_defined \<A>"
  shows "finite (runs_with_end \<A> word s)"
proof -
  have "\<forall> run . run \<in> runs_with_end \<A> word s \<longrightarrow> length run = length word + 1 \<and> prun_states run \<A>" using assms well_def_implies_prun_states unfolding runs_with_end_def run_well_defined_def pseudo_run_well_defined_def by fast
  hence runs_sub: "runs_with_end \<A> word s \<subseteq> {run . prun_states run \<A> \<and> length run = length word + 1}" by fast
  have "finite {run . prun_states run \<A> \<and> length run = length word + 1}" using assms finite_lists_length_eq unfolding auto_well_defined_def prun_states_def by blast
  thus ?thesis using finite_subset runs_sub by blast
qed

lemma greedy_run_exists:
  assumes "auto_well_defined \<A>" "\<exists> run . run_well_defined run \<A> word \<and> last run = s"
  shows "\<exists> run . greedy_run run \<A> word \<and> last run = s"
proof -
  obtain run where run: "run_well_defined run \<A> word \<and> last run = s" using assms by blast
  have fin: "finite (runs_with_end \<A> word s)" using assms finite_runs_with_end by fast
  have nonempty: "runs_with_end \<A> word s \<noteq> {}" using run unfolding runs_with_end_def by blast
  then obtain run' where run': "run' \<in> (runs_with_end \<A> word s) \<and> acc_sum \<A> run' = Max (image (acc_sum \<A>) (runs_with_end \<A> word s))" using fin Max_in finite_imageI image_iff image_is_empty by (metis (no_types, lifting))
  {
    fix r assume "r \<in> (runs_with_end \<A> word s)"
    hence "acc_sum \<A> r \<in> image (acc_sum \<A>) (runs_with_end \<A> word s)" by auto
    hence "acc_sum \<A> r \<le> Max (image (acc_sum \<A>) (runs_with_end \<A> word s))" using fin nonempty Max_ge by auto
    hence "acc_sum \<A> r \<le> acc_sum \<A> run'" using run' by simp
  }
  hence "\<forall> run . run \<in> (runs_with_end \<A> word s) \<longrightarrow> acc_sum \<A> run \<le> acc_sum \<A> run'" by simp
  hence "\<forall> run . run_well_defined run \<A> word \<and> last run = s \<longrightarrow> acc_sum \<A> run \<le> acc_sum \<A> run'" unfolding runs_with_end_def by blast
  thus ?thesis using run' unfolding runs_with_end_def greedy_run_def by force
qed

theorem greedy_run_iff_finite_case:
  assumes "auto_well_defined \<A>"
  shows "(\<exists> run . run_well_defined run \<A> word \<and> last run s) \<longleftrightarrow> (\<exists> run . greedy_run run \<A> word \<and> last run s)"
  using assms greedy_run_exists unfolding greedy_run_def by fastforce

definition omega_greedy_run :: "'s omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> bool" where "omega_greedy_run omega_run \<A> omega_word = (omega_run_well_defined omega_run \<A> omega_word \<and> (\<forall> n . greedy_run (pre_omega_run omega_run n) \<A> (pre_omega_word omega_word n)))"

fun pos_i :: "nat \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 's omega_run \<Rightarrow> nat" where
  "pos_i 0 \<A> omega_run = (LEAST i . omega_run i \<in> accepting_states \<A>)" |
  "pos_i (Suc i) \<A> omega_run = (LEAST n . n > (pos_i i \<A> omega_run) \<and> (omega_run n \<in> accepting_states \<A>))"

lemma pos_i_0_acc:
  assumes "omega_run_accepting omega_run \<A> omega_word"
  shows "omega_run (pos_i 0 \<A> omega_run) \<in> accepting_states \<A>"
proof -
  have "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>" using assms unfolding omega_run_accepting_def by blast
  hence "\<exists> k . omega_run k \<in> accepting_states \<A>" by blast
  thus ?thesis using LeastI_ex by force
qed

lemma pos_i_Suc_gt_and_acc:
  assumes "omega_run_accepting omega_run \<A> omega_word"
  shows "pos_i (Suc i) \<A> omega_run > pos_i i \<A> omega_run \<and> omega_run (pos_i (Suc i) \<A> omega_run) \<in> accepting_states \<A>"
proof -
  have "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>" using assms unfolding omega_run_accepting_def by blast
  hence ex: "\<exists> n . n > pos_i i \<A> omega_run \<and> omega_run n \<in> accepting_states \<A>" by blast
  obtain n where n: "n = (LEAST n . n > pos_i i \<A> omega_run \<and> omega_run n \<in> accepting_states \<A>)" by simp
  hence props: "n > pos_i i \<A> omega_run \<and> omega_run n \<in> accepting_states \<A>" using ex LeastI_ex by simp
  have "n = pos_i (Suc i) \<A> omega_run" using n by simp
  thus ?thesis using props by blast
qed

lemma pos_i_gt_and_acc:
  assumes "omega_run_accepting omega_run \<A> omega_word"
  shows "\<forall> i . pos_i (Suc i) \<A> omega_run > pos_i i \<A> omega_run \<and> omega_run (pos_i i \<A> omega_run) \<in> accepting_states \<A>"
proof - 
  {
    fix i
    have "pos_i (Suc i) \<A> omega_run > pos_i i \<A> omega_run \<and> omega_run (pos_i i \<A> omega_run) \<in> accepting_states \<A>"
    proof(cases i)
      case 0 thus ?thesis using assms pos_i_Suc_gt_and_acc pos_i_0_acc by blast
    next
      case (Suc nat) thus ?thesis using assms pos_i_Suc_gt_and_acc by blast
    qed
  }
  thus ?thesis by blast
qed

lemma pos_i_ge_index:
  assumes "omega_run_accepting omega_run \<A> omega_word"
  shows "pos_i i \<A> omega_run \<ge> i"
proof (induction i)
  case 0 show ?case by simp
next
  case (Suc i)
  have "pos_i (Suc i) \<A> omega_run > pos_i i \<A> omega_run" using pos_i_gt_and_acc assms by blast
  hence "pos_i (Suc i) \<A> omega_run \<ge> pos_i i \<A> omega_run + 1" by linarith
  hence "pos_i (Suc i) \<A> omega_run \<ge> i + 1" using Suc by force
  thus ?case by force
qed

definition all_acc_omega_runs :: "('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> 's omega_run set" where "all_acc_omega_runs \<A> omega_word = {omega_run . omega_run_accepting omega_run \<A> omega_word}"

fun R_i :: "nat \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> 's omega_run set" where
  "R_i 0 \<A> omega_word = all_acc_omega_runs \<A> omega_word" |
  "R_i (Suc i) \<A> omega_word = {omega_run \<in> R_i i \<A> omega_word . pos_i i \<A> omega_run = (LEAST n . n \<in> (image (pos_i i \<A>) (R_i i \<A> omega_word)))}"

lemma R_i_empty_step:
  assumes "R_i i \<A> omega_word = {}"
  shows "R_i (Suc i) \<A> omega_word = {}"
  using assms by auto

lemma R_i_not_empty_step:
  assumes "R_i i \<A> omega_word \<noteq> {}"
  shows "R_i (Suc i) \<A> omega_word \<noteq> {}"
proof -
  have "image (pos_i i \<A>) (R_i i \<A> omega_word) \<noteq> {}" using assms by auto
  hence "\<exists> n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word)" by blast
  hence "(LEAST n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word)) \<in> image (pos_i i \<A>) (R_i i \<A> omega_word)" by (rule LeastI_ex)
  then obtain omega_run where "omega_run \<in> R_i i \<A> omega_word \<and> pos_i i \<A> omega_run = (LEAST n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word))" by auto
  hence "omega_run \<in> R_i (Suc i) \<A> omega_word" by simp
  thus ?thesis by blast
qed

theorem R_i_not_empty_iff: "R_i i \<A> omega_word \<noteq> {} \<longleftrightarrow> R_i (Suc i) \<A> omega_word \<noteq> {}"
  using R_i_empty_step R_i_not_empty_step by metis

lemma cor_3_1_4_left:
  assumes "omega_word \<in> omega_language_auto \<A>"
  shows "R_i i \<A> omega_word \<noteq> {}"
proof(induction i)
  case 0
  then obtain omega_run where "omega_run_accepting omega_run \<A> omega_word" using assms unfolding omega_language_auto_def by force
  hence "omega_run \<in> all_acc_omega_runs \<A> omega_word" unfolding all_acc_omega_runs_def by fast
  hence "omega_run \<in> R_i 0 \<A> omega_word" by auto
  thus ?case by blast
next
  case (Suc i)
  thus ?case using R_i_not_empty_iff by blast
qed

lemma cor_3_1_4_right:
  assumes "\<forall> i . R_i i \<A> omega_word \<noteq> {}"
  shows "omega_word \<in> omega_language_auto \<A>"
proof -
  have "R_i 0 \<A> omega_word \<noteq> {}" using assms by blast
  hence "all_acc_omega_runs \<A> omega_word \<noteq> {}" by simp
  hence "\<exists> omega_run . omega_run \<in> all_acc_omega_runs \<A> omega_word" by auto
  hence "\<exists> omega_run . omega_run_accepting omega_run \<A> omega_word" unfolding all_acc_omega_runs_def by simp
  thus ?thesis unfolding omega_language_auto_def by auto
qed

corollary cor_3_1_4: "(\<forall> i . R_i i \<A> omega_word \<noteq> {}) \<longleftrightarrow> omega_word \<in> omega_language_auto \<A>"
  using cor_3_1_4_left cor_3_1_4_right by blast

lemma claim_3_1_5: "R_i (Suc i) \<A> omega_word \<subseteq> R_i i \<A> omega_word"
  by auto

fun R_tilde :: "nat \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> 's run set" where
  "R_tilde 0 \<A> omega_word = {[]}" |
  "R_tilde (Suc i) \<A> omega_word = {pre_omega_run omega_run (pos_i i \<A> omega_run) | omega_run . omega_run \<in> R_i (Suc i) \<A> omega_word}"

lemma R_tilde_not_empty:
  assumes "R_i i \<A> omega_word \<noteq> {}"
  shows "R_tilde i \<A> omega_word \<noteq> {}"
  using assms by (induction i) auto

lemma R_i_subset_all_acc: "R_i i \<A> omega_word \<subseteq> all_acc_omega_runs \<A> omega_word"
  by (induction i) auto

lemma R_i_mem_accepting:
  assumes "omega_run \<in> R_i i \<A> omega_word"
  shows "omega_run_accepting omega_run \<A> omega_word"
  using assms R_i_subset_all_acc unfolding all_acc_omega_runs_def by blast

lemma pre_omega_run_states:
  assumes "auto_well_defined \<A>" "omega_run_well_defined omega_run \<A> omega_word"
  shows "prun_states (pre_omega_run omega_run n) \<A>"
  using assms omega_run_implies_pre_states_and_word_well_def unfolding omega_run_well_defined_def by fast

lemma finite_R_tilde_0: "finite (R_tilde 0 \<A> omega_word)"
  by auto

lemma finite_R_tilde_Suc:
  assumes "auto_well_defined \<A>"
  shows "finite (R_tilde (Suc i) \<A> omega_word)"
proof -
  let ?k = "(LEAST n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word))"
  {
    fix run assume "run \<in> R_tilde (Suc i) \<A> omega_word"
    then obtain omega_run where omega_run: "omega_run \<in> R_i (Suc i) \<A> omega_word \<and> run = pre_omega_run omega_run (pos_i i \<A> omega_run)" by auto
    hence "omega_run_well_defined omega_run \<A> omega_word" using R_i_mem_accepting unfolding omega_run_accepting_def by blast
    hence in_set: "set run \<subseteq> states \<A>" using assms omega_run pre_omega_run_states unfolding prun_states_def by fast
    have "length run = Suc ?k" using omega_run pre_omega_run_length by auto
    hence "run \<in> {run . set run \<subseteq> states \<A> \<and> length run = Suc ?k}" using in_set by blast
  }
  hence sub: "R_tilde (Suc i) \<A> omega_word \<subseteq> {run . set run \<subseteq> states \<A> \<and> length run = Suc ?k}" by blast
  have "finite {run . set run \<subseteq> states \<A> \<and> length run = Suc ?k}" using assms finite_lists_length_eq unfolding auto_well_defined_def by blast
  thus ?thesis using sub finite_subset by blast
qed

proposition finite_R_tilde:
  assumes "auto_well_defined \<A>"
  shows "finite (R_tilde i \<A> omega_word)"
  using assms finite_R_tilde_Suc finite_R_tilde_0 by(cases i) auto

lemma claim_3_1_6:
  assumes "auto_well_defined \<A>" "omega_word \<in> omega_language_auto \<A>"
  shows "R_tilde i \<A> omega_word \<noteq> {} \<and> finite (R_tilde i \<A> omega_word)"
proof -
  have "R_i i \<A> omega_word \<noteq> {}" using cor_3_1_4 assms by blast
  hence nonempty_tilde: "R_tilde i \<A> omega_word \<noteq> {}" using R_tilde_not_empty by blast
  have "finite (R_tilde i \<A> omega_word)" using assms finite_R_tilde by blast
  thus ?thesis using nonempty_tilde by blast
qed

lemma R_tilde_length_const:
  assumes "run \<in> R_tilde (Suc i) \<A> omega_word"
  shows "length run = Suc ((LEAST n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word)))"
  using assms pre_omega_run_length by force

lemma k_strict_mono:
  assumes "omega_word \<in> omega_language_auto \<A>"
  shows "(LEAST n . n \<in> image (pos_i (Suc i) \<A>) (R_i (Suc i) \<A> omega_word)) > (LEAST n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word))"
proof -
  let ?k  = "(LEAST n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word))"
  let ?kS = "(LEAST n . n \<in> image (pos_i (Suc i) \<A>) (R_i (Suc i) \<A> omega_word))"
  have not_empty: "R_i i \<A> omega_word \<noteq> {} \<and> R_i (Suc i) \<A> omega_word \<noteq> {}" using cor_3_1_4 assms by blast
  {
    fix m assume "m \<in> image (pos_i (Suc i) \<A>) (R_i (Suc i) \<A> omega_word)"
    then obtain omega_run where omega_run: "omega_run \<in> R_i (Suc i) \<A> omega_word \<and> m = pos_i (Suc i) \<A> omega_run" by blast
    hence acc: "omega_run_accepting omega_run \<A> omega_word" using R_i_mem_accepting by blast
    have pos_i_eq_k: "pos_i i \<A> omega_run = ?k" using omega_run by auto
    have "pos_i (Suc i) \<A> omega_run > pos_i i \<A> omega_run" using pos_i_gt_and_acc acc by blast
    hence "m > ?k" using omega_run pos_i_eq_k by argo
  }
  hence all_gt: "\<forall> m \<in> image (pos_i (Suc i) \<A>) (R_i (Suc i) \<A> omega_word) . m > ?k" by blast
  have "\<exists> n . n \<in> image (pos_i (Suc i) \<A>) (R_i (Suc i) \<A> omega_word)" using not_empty by blast
  hence "?kS \<in> image (pos_i (Suc i) \<A>) (R_i (Suc i) \<A> omega_word)" by (rule LeastI_ex)
  thus ?thesis using all_gt by blast
qed

lemma R_tilde_disjoint_step:
  assumes "omega_word \<in> omega_language_auto \<A>"
  shows "R_tilde (Suc i) \<A> omega_word \<inter> R_tilde (Suc (Suc i)) \<A> omega_word = {}"
proof -
  have len_i: "\<forall> run . run \<in> R_tilde (Suc i) \<A> omega_word \<longrightarrow> length run = Suc (LEAST n. n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word))" using R_tilde_length_const by blast
  have len_Si: "\<forall> run . run \<in> R_tilde (Suc (Suc i)) \<A> omega_word \<longrightarrow> length run = Suc (LEAST n. n \<in> image (pos_i (Suc i) \<A>) (R_i (Suc i) \<A> omega_word))" using R_tilde_length_const by blast
  have lt: "Suc (LEAST n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word)) < Suc (LEAST n . n \<in> image (pos_i (Suc i) \<A>) (R_i (Suc i) \<A> omega_word))" using assms k_strict_mono by blast
  {
    fix run assume "run \<in> R_tilde (Suc i) \<A> omega_word \<inter> R_tilde (Suc (Suc i)) \<A> omega_word"
    hence "run \<in> R_tilde (Suc i) \<A> omega_word \<and> run \<in> R_tilde (Suc (Suc i)) \<A> omega_word" by fast
    hence "length run = Suc (LEAST n. n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word)) \<and> length run = Suc (LEAST n. n \<in> image (pos_i (Suc i) \<A>) (R_i (Suc i) \<A> omega_word))" using len_i len_Si by blast 
    hence False using lt by linarith
  }
  thus ?thesis by blast
qed

lemma epsilon_not_in_R_tilde_1: "[] \<notin> R_tilde (Suc 0) \<A> omega_word"
proof(rule ccontr)
  assume "\<not> [] \<notin> R_tilde (Suc 0) \<A> omega_word"
  hence "[] \<in> R_tilde 1 \<A> omega_word" by auto
  then obtain omega_run where "omega_run \<in> R_i 1 \<A> omega_word \<and> [] = pre_omega_run omega_run (pos_i 0 \<A> omega_run)" by auto
  hence "length [] = length (pre_omega_run omega_run (pos_i 0 \<A> omega_run))" by force
  hence "0 = Suc (pos_i 0 \<A> omega_run)" using pre_omega_run_length list.size(3) by metis
  thus False by blast
qed

lemma R_tilde_disjoint_step_0: "R_tilde 0 \<A> omega_word \<inter> R_tilde (Suc 0) \<A> omega_word = {}"
  using epsilon_not_in_R_tilde_1 by auto

proposition R_tilde_disjoint_step_all: 
  assumes "omega_word \<in> omega_language_auto \<A>"
  shows "R_tilde i \<A> omega_word \<inter> R_tilde (Suc i) \<A> omega_word = {}"
proof(cases i)
  case 0 thus ?thesis using R_tilde_disjoint_step_0 by blast
next
  case (Suc nat) thus ?thesis using assms R_tilde_disjoint_step by blast
qed

lemma strict_mono_kfun:
  assumes "omega_word \<in> omega_language_auto \<A>"
  shows "strict_mono (\<lambda>i . (LEAST n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word)))"
proof (rule strict_monoI)
  fix i j :: nat assume assm: "i < j"
  let ?k = "\<lambda>t. (LEAST n . n \<in> image (pos_i t \<A>) (R_i t \<A> omega_word))"
  obtain d where jd: "j = i + Suc d"  using assm less_iff_Suc_add by fastforce
  have step: "\<forall> t . ?k t < ?k (Suc t)" using k_strict_mono assms by blast
  have "?k i < ?k (i + Suc d)"
  proof (induction d)
    case 0 thus ?case using step by force
  next
    case (Suc d)
    have "?k (i + Suc d) < ?k (Suc (i + Suc d))" using step by blast
    hence less: "?k i < ?k (Suc (i + Suc d))" using Suc less_trans by blast
    have "Suc (i + Suc d) = i + Suc (Suc d)" by simp
    thus ?case using less by presburger
  qed
  thus "?k i < ?k j" using jd by blast
qed

corollary cor_3_1_7:
  assumes "auto_well_defined \<A>" "omega_word \<in> omega_language_auto \<A>"
  shows "infinite (\<Union> i . R_tilde i \<A> omega_word)"
proof -
  let ?pick = "\<lambda>i . (SOME run . run \<in> R_tilde (Suc i) \<A> omega_word)"
  {
    fix i
    have "R_tilde (Suc i) \<A> omega_word \<noteq> {}" using claim_3_1_6 assms by blast
    hence "?pick i \<in> R_tilde (Suc i) \<A> omega_word" using someI_ex by fast
  }
  hence pick_mem: "\<forall> i . ?pick i \<in> R_tilde (Suc i) \<A> omega_word" by blast
  have pick_inj: "inj ?pick"
  proof (rule injI)
    fix i j assume assm: "?pick i = ?pick j"
    have li: "length (?pick i) = Suc (LEAST n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word))" using R_tilde_length_const pick_mem by blast
    have "length (?pick j) = Suc (LEAST n . n \<in> image (pos_i j \<A>) (R_i j \<A> omega_word))" using R_tilde_length_const pick_mem by blast
    hence "Suc (LEAST n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word)) = Suc (LEAST n . n \<in> image (pos_i j \<A>) (R_i j \<A> omega_word))" using assm li by argo
    thus "i = j" using strict_mono_kfun assms strict_mono_eq by blast
  qed
  have "range ?pick \<subseteq> (\<Union> i . R_tilde (Suc i) \<A> omega_word)" using pick_mem by blast
  hence range_sub: "range ?pick \<subseteq> (\<Union> i . R_tilde i \<A> omega_word)" by blast
  have "infinite (range ?pick)" using pick_inj finite_image_iff by blast
  thus ?thesis using infinite_super range_sub by blast
qed

definition proper_prefix :: "'s run \<Rightarrow> 's run \<Rightarrow> bool" (infix "\<prec>" 50) where "a \<prec> b = (\<exists> d . d \<noteq> [] \<and> a @ d = b)"

lemma pre_omega_run_proper_prefix:
  assumes "m < n"
  shows "pre_omega_run omega_run m \<prec> pre_omega_run omega_run n"
proof -
  have "pre_omega_run omega_run m = take (Suc m) (pre_omega_run omega_run n)" using assms unfolding pre_omega_run_def by (simp add: take_map)
  hence concat: "pre_omega_run omega_run m @ drop (Suc m) (pre_omega_run omega_run n) = pre_omega_run omega_run n" by (simp add: take_drop)
  have "drop (Suc m) (pre_omega_run omega_run n) \<noteq> []" using assms by (simp add: pre_omega_run_length)
  thus ?thesis using concat unfolding proper_prefix_def by blast
qed

lemma lemma_3_1_8:
  assumes "omega_word \<in> omega_language_auto \<A>" "ri \<in> R_tilde (Suc i) \<A> omega_word"
  shows "\<exists> ri_prev \<in> R_tilde i \<A> omega_word . ri_prev \<prec> ri"
proof(cases i)
  case 0
  hence empty_list: "[] \<in> R_tilde 0 \<A> omega_word" by auto
  have "ri \<noteq> []" using 0 assms epsilon_not_in_R_tilde_1 by blast
  hence "[] \<prec> ri" unfolding proper_prefix_def by blast
  thus ?thesis using empty_list 0 by blast
next
  case (Suc nat)
  obtain omega_run where "omega_run \<in> R_i (Suc i) \<A> omega_word \<and> ri = pre_omega_run omega_run (pos_i i \<A> omega_run)" using assms by auto
  hence omega_run: "omega_run \<in> R_i (Suc (Suc nat)) \<A> omega_word \<and> ri = pre_omega_run omega_run (pos_i (Suc nat) \<A> omega_run)" using Suc by blast
  let ?ri_prev = "pre_omega_run omega_run (pos_i nat \<A> omega_run)"
  have "omega_run \<in> R_i (Suc nat) \<A> omega_word" using omega_run claim_3_1_5 by blast
  hence ri_prev: "?ri_prev \<in> R_tilde (Suc nat) \<A> omega_word" by force
  have "omega_run_accepting omega_run \<A> omega_word" using R_i_mem_accepting omega_run by blast
  hence "pos_i nat \<A> omega_run < pos_i (Suc nat) \<A> omega_run" using pos_i_gt_and_acc by blast
  hence "?ri_prev \<prec> ri" using pre_omega_run_proper_prefix omega_run by blast
  thus ?thesis using ri_prev Suc by blast
qed

definition children :: "nat \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> 's run \<Rightarrow> 's run set" where "children i \<A> omega_word run = {run' \<in> R_tilde (Suc i) \<A> omega_word . run \<prec> run'}"

definition prefixeq :: "'s run \<Rightarrow> 's run \<Rightarrow> bool" (infix "\<preceq>" 50) where "a \<preceq> b = (\<exists> d . a @ d = b)"

lemma prefixeq_transitiv:
  assumes "a \<preceq> b" "b \<preceq> c"
  shows "a \<preceq> c"
  using assms unfolding prefixeq_def by auto

lemma prefixeq_take:
  assumes "a \<preceq> c"
  shows "take (length a) c = a"
  using assms unfolding prefixeq_def by force

definition descendants :: "nat \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> 's run \<Rightarrow> 's run set" where "descendants i \<A> omega_word run = {run' . \<exists> j \<ge> i . run' \<in> R_tilde j \<A> omega_word \<and> run \<preceq> run'}"

lemma descendant_has_child:
  assumes "omega_word \<in> omega_language_auto \<A>" "r \<in> R_tilde i \<A> omega_word" "t \<in> descendants i \<A> omega_word r" "t \<notin> R_tilde i \<A> omega_word"
  shows "\<exists> c \<in> children i \<A> omega_word r . t \<in> descendants (Suc i) \<A> omega_word c"
proof -
  obtain j where j: "j \<ge> i \<and> t \<in> R_tilde j \<A> omega_word \<and> r \<preceq> t" using assms unfolding descendants_def by blast
  hence "j > i" using assms le_neq_implies_less by blast
  hence sucji: "Suc i \<le> j" by simp
  then obtain d where d: "j = Suc i + d" using le_iff_add by metis
  have "\<exists> c \<in> R_tilde (Suc i) \<A> omega_word . c \<preceq> t"
  proof (cases d)
    case 0 thus ?thesis using d j unfolding prefixeq_def by auto
  next
    case (Suc d')
    hence "j = Suc (Suc i + d')" using d by simp
    hence "t \<in> R_tilde (Suc (Suc i + d')) \<A> omega_word" using j by blast
    then obtain p where p_in: "p \<in> R_tilde (Suc i + d') \<A> omega_word \<and> p \<prec> t" using lemma_3_1_8 assms by blast
    hence p_pre: "p \<in> R_tilde (Suc i + d') \<A> omega_word \<and> p \<preceq> t" unfolding proper_prefix_def prefixeq_def by blast
    hence "\<exists> c \<in> R_tilde (Suc i) \<A> omega_word . c \<preceq> p"
    proof (induction d' arbitrary: p t)
      case 0 thus ?case unfolding prefixeq_def by auto
    next
      case (Suc d'')
      hence "Suc (Suc i + d'') = Suc i + Suc d''" by presburger
      hence "p \<in> R_tilde (Suc (Suc i + d'')) \<A> omega_word" using Suc by presburger
      then obtain q where "q \<in> R_tilde (Suc i + d'') \<A> omega_word \<and> q \<prec> p" using lemma_3_1_8 assms by blast
      hence q_pre: "q \<in> R_tilde (Suc i + d'') \<A> omega_word \<and> q \<preceq> p" unfolding proper_prefix_def prefixeq_def by blast
      then obtain c where c_in: "c \<in> R_tilde (Suc i) \<A> omega_word \<and> c \<preceq> q" using Suc by blast
      hence "c \<preceq> p" using prefixeq_transitiv q_pre by blast
      thus ?case using c_in by blast
    qed
    then obtain c where "c \<in> R_tilde (Suc i) \<A> omega_word \<and> c \<preceq> p" by blast
    hence "c \<in> R_tilde (Suc i) \<A> omega_word \<and> c \<preceq> t" using prefixeq_transitiv p_pre by fast
    thus ?thesis by blast
  qed
  then obtain c where c: "c \<in> R_tilde (Suc i) \<A> omega_word \<and> c \<preceq> t" by blast
  let ?L = "\<lambda>k . (LEAST n . n \<in> image (pos_i k \<A>) (R_i k \<A> omega_word))"
  have sm: "strict_mono (\<lambda>k . ?L k)" using assms strict_mono_kfun by blast
  hence "?L i < ?L (Suc i)" using strict_monoD by blast
  hence len_lt: "length r < length c"
  proof (cases i)
    case 0
    hence not_empty: "r = []" using assms by auto
    have "length c \<noteq> 0" using c 0 pre_omega_run_length epsilon_not_in_R_tilde_1 by blast
    thus ?thesis using not_empty by force
  next
    case (Suc i')
    hence lr: "length r = Suc (?L i')" using R_tilde_length_const assms by blast
    have lc: "length c = Suc (?L (Suc i'))"  using R_tilde_length_const c Suc by blast
    have "?L i' < ?L (Suc i')" using strict_monoD sm by blast
    thus ?thesis using lr lc by linarith
  qed
  have r: "r = take (length r) t" using prefixeq_take j by metis
  have "take (length c) t = c" using prefixeq_take c by blast
  hence "take (length r) c = r" using r c len_lt unfolding prefixeq_def by force
  hence "r \<preceq> c" using append_take_drop_id unfolding prefixeq_def by metis
  hence "r \<prec> c" using len_lt unfolding prefixeq_def proper_prefix_def by force
  hence c_child: "c \<in> children i \<A> omega_word r" using c unfolding children_def by blast
  have "t \<in> descendants (Suc i) \<A> omega_word c" unfolding descendants_def using j c sucji by blast
  thus ?thesis using c_child by blast
qed

lemma infinite_descendants_choose_child:
  assumes "auto_well_defined \<A>" "omega_word \<in> omega_language_auto \<A>" "r \<in> R_tilde i \<A> omega_word" "infinite (descendants i \<A> omega_word r)"
  shows "\<exists> c \<in> children i \<A> omega_word r . infinite (descendants (Suc i) \<A> omega_word c)"
proof -
  let ?Ch = "children i \<A> omega_word r"
  have fin: "finite (R_tilde (Suc i) \<A> omega_word)" using finite_R_tilde assms by blast
  have "?Ch \<subseteq> R_tilde (Suc i) \<A> omega_word" unfolding children_def by auto   
  hence finCh: "finite ?Ch" using fin finite_subset by blast
  let ?B = "{t . t \<in> R_tilde i \<A> omega_word \<and> r \<preceq> t}"
  have finB: "finite ?B" using finite_R_tilde assms by fastforce
  {
    fix t assume assm: "t \<in> descendants i \<A> omega_word r"
    hence "t \<in> ?B \<union> (\<Union> c \<in> ?Ch . descendants (Suc i) \<A> omega_word c)"
    proof (cases "t \<in> R_tilde i \<A> omega_word")
      case True thus ?thesis using assm unfolding descendants_def by blast
    next
      case False thus ?thesis using descendant_has_child assms assm by fast
    qed
  }
  hence sub: "descendants i \<A> omega_word r \<subseteq> ?B \<union> (\<Union> c \<in> ?Ch . descendants (Suc i) \<A> omega_word c)" by blast
  have "infinite (\<Union> c\<in> ?Ch . descendants (Suc i) \<A> omega_word c)"
  proof (rule ccontr)
    assume "\<not> infinite (\<Union> c \<in> ?Ch . descendants (Suc i) \<A> omega_word c)"
    hence "finite (\<Union> c \<in> ?Ch . descendants (Suc i) \<A> omega_word c)" by blast
    hence "finite (?B \<union> (\<Union>c\<in>?Ch. descendants (Suc i) \<A> omega_word c))" using finB by simp
    hence "finite (descendants i \<A> omega_word r)" using assms sub finite_subset by blast
    thus False using assms by blast
  qed
  thus ?thesis using finCh by blast
qed

lemma infinite_descendants_0:
  assumes "infinite (\<Union> i . R_tilde i \<A> omega_word)"
  shows "infinite (descendants 0 \<A> omega_word [])"
proof -
  {
    fix t assume "t \<in> (\<Union> i . R_tilde i \<A> omega_word)"
    then obtain j where "t \<in> R_tilde j \<A> omega_word" by fast
    hence "t \<in> descendants 0 \<A> omega_word []" unfolding prefixeq_def descendants_def by blast
  }
  hence sub: "(\<Union> i . R_tilde i \<A> omega_word) \<subseteq> descendants 0 \<A> omega_word []" by blast   
  thus ?thesis using assms infinite_super by fast
qed

lemma lemma_3_1_9:
  assumes "auto_well_defined \<A>" "omega_word \<in> omega_language_auto \<A>"
  shows "\<exists> rseq . (\<forall> i . rseq i \<in> R_tilde i \<A> omega_word \<and> rseq i \<prec> rseq (Suc i))"
proof -
  have "infinite (\<Union> i . R_tilde i \<A> omega_word)" using assms cor_3_1_7 by blast
  hence Inf0: "infinite (descendants 0 \<A> omega_word [])" using infinite_descendants_0 by blast
  define rseq where "rseq = rec_nat [] (\<lambda>i ri . (SOME c . c \<in> children i \<A> omega_word ri \<and> infinite (descendants (Suc i) \<A> omega_word c)))"
  hence rseq0: "rseq 0 = []" by simp
  {
    fix i
    have step_all: "rseq i \<in> R_tilde i \<A> omega_word \<and> infinite (descendants i \<A> omega_word (rseq i))"
    proof (induction i)
      case 0 thus ?case using Inf0 rseq0 by force
    next
      case (Suc i)
      hence "\<exists> c \<in> children i \<A> omega_word (rseq i) . infinite (descendants (Suc i) \<A> omega_word c)" using infinite_descendants_choose_child assms by blast
      hence some_mem: "(SOME c . c \<in> children i \<A> omega_word (rseq i) \<and> infinite (descendants (Suc i) \<A> omega_word c)) \<in> children i \<A> omega_word (rseq i) \<and> infinite (descendants (Suc i) \<A> omega_word (SOME c . c \<in> children i \<A> omega_word (rseq i) \<and> infinite (descendants (Suc i) \<A> omega_word c)))" by (rule someI2_bex) auto
      hence "rseq (Suc i) \<in> children i \<A> omega_word (rseq i)" unfolding rseq_def by auto
      hence inNext: "rseq (Suc i) \<in> R_tilde (Suc i) \<A> omega_word" unfolding children_def by blast
      have "infinite (descendants (Suc i) \<A> omega_word (rseq (Suc i)))" using some_mem unfolding rseq_def by auto
      thus ?case using inNext by blast
    qed
    hence "\<exists> c \<in> children i \<A> omega_word (rseq i) . infinite (descendants (Suc i) \<A> omega_word c)" using infinite_descendants_choose_child assms by blast
    hence some_mem: "(SOME c . c \<in> children i \<A> omega_word (rseq i) \<and>  infinite (descendants (Suc i) \<A> omega_word c)) \<in> children i \<A> omega_word (rseq i)" by (rule someI2_bex) auto
    hence "rseq (Suc i) \<in> children i \<A> omega_word (rseq i)" unfolding rseq_def by auto
    hence "rseq i \<prec> rseq (Suc i)" unfolding children_def by blast
    hence "rseq i \<in> R_tilde i \<A> omega_word \<and> infinite (descendants i \<A> omega_word (rseq i)) \<and> rseq i \<prec> rseq (Suc i)" using step_all by blast
  }
  thus ?thesis by blast
qed

definition rho_from_chain :: "'s omega_run_list \<Rightarrow> 's omega_run" where "rho_from_chain rseq = (\<lambda>n . (rseq (Suc n)) ! n)"

lemma proper_prefix_length_lt:
  assumes "a \<prec> b"
  shows "length a < length b"
  using assms unfolding proper_prefix_def by auto

lemma chain_len_ge:
  assumes "\<forall> i . rseq i \<prec> rseq (Suc i)"
  shows "n < length (rseq (Suc n))"
proof (induction n)
  case 0
  have "rseq 0 \<prec> rseq (Suc 0)" using assms by blast
  hence "length (rseq 0) < length (rseq (Suc 0))" using proper_prefix_length_lt by blast
  thus ?case by force
next
  case (Suc n)
  have "rseq (Suc n) \<prec> rseq (Suc (Suc n))" using assms by blast
  hence "length (rseq (Suc n)) < length (rseq (Suc (Suc n)))" using proper_prefix_length_lt by blast
  thus ?case using Suc by auto
qed

lemma chain_nth_stable:
  assumes "\<forall> i . rseq i \<prec> rseq (Suc i) \<and> rseq i \<in> R_tilde i \<A> omega_word" 
  shows "(rseq (Suc (Suc n))) ! n = (rseq (Suc n)) ! n"
proof -
  have "rseq (Suc n) \<prec> rseq (Suc (Suc n))" using assms by blast
  hence "rseq (Suc n) \<preceq> rseq (Suc (Suc n))" unfolding proper_prefix_def prefixeq_def by blast
  then obtain d where app: "rseq (Suc n) @ d = rseq (Suc (Suc n))" unfolding prefixeq_def by blast
  have "n < length (rseq (Suc n))" using assms chain_len_ge by blast
  thus ?thesis using app nth_append by metis
qed

lemma R_tilde_witness:
  assumes "ri \<in> R_tilde (Suc i) \<A> omega_word"
  shows "\<exists> omega_run \<in> R_i (Suc i) \<A> omega_word . ri = pre_omega_run omega_run (pos_i i \<A> omega_run)"
  using assms by auto

lemma rho_well_defined:
  assumes "auto_well_defined \<A>" "\<forall> i . rseq i \<in> R_tilde i \<A> omega_word \<and> rseq i \<prec> rseq (Suc i)"
  shows "omega_run_well_defined (rho_from_chain rseq) \<A> omega_word"
proof -
  let ?rho = "rho_from_chain rseq"
  have "rseq 1 \<in> R_tilde 1 \<A> omega_word" using assms by blast
  then obtain omega_run1 where or1: "omega_run1 \<in> R_i 1 \<A> omega_word \<and> rseq 1 = pre_omega_run omega_run1 (pos_i 0 \<A> omega_run1)" using R_tilde_witness by auto
  hence "omega_run_accepting omega_run1 \<A> omega_word" using R_i_mem_accepting by fast
  hence or1_well_def: "omega_run_well_defined omega_run1 \<A> omega_word" unfolding omega_run_accepting_def by auto
  have rho0: "?rho 0 = (rseq 1) ! 0" unfolding rho_from_chain_def by simp   
  have "0 < Suc (pos_i 0 \<A> omega_run1)" by simp
  hence "(pre_omega_run omega_run1 (pos_i 0 \<A> omega_run1)) ! 0 = omega_run1 0" using pre_omega_run_nth by blast
  hence "?rho 0 = omega_run1 0" using rho0 or1 by presburger
  hence "?rho 0 = initial_state \<A>" using or1_well_def unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
  hence init: "?rho 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  {
    fix n
    have "rseq (Suc (Suc n)) \<in> R_tilde (Suc (Suc n)) \<A> omega_word" using assms by blast
    then obtain omega_run where omega_run: "omega_run \<in> R_i (Suc (Suc n)) \<A> omega_word \<and> rseq (Suc (Suc n)) = pre_omega_run omega_run (pos_i (Suc n) \<A> omega_run)" using R_tilde_witness by blast   
    hence "omega_run_accepting omega_run \<A> omega_word" using R_i_mem_accepting by blast
    hence omega_run_well_def: "omega_run_well_defined omega_run \<A> omega_word" unfolding omega_run_accepting_def by auto
    have n_leq: "n < pos_i (Suc n) \<A> omega_run" using assms chain_len_ge Suc_less_eq omega_run pre_omega_run_length by metis
    hence "n < Suc (pos_i (Suc n) \<A> omega_run)" by auto
    hence "(pre_omega_run omega_run (pos_i (Suc n) \<A> omega_run)) ! n = omega_run n" using pre_omega_run_nth by blast
    hence "(rseq (Suc (Suc n))) ! n = omega_run n" using omega_run by argo
    hence rho_n: "?rho n = omega_run n" using chain_nth_stable assms unfolding rho_from_chain_def by metis
    have "n + 1 < Suc (pos_i (Suc n) \<A> omega_run)" using n_leq by simp
    hence "(pre_omega_run omega_run (pos_i (Suc n) \<A> omega_run)) ! (n + 1) = omega_run (n + 1)" using pre_omega_run_nth by blast
    hence "(rseq (Suc (Suc n))) ! (n + 1) = omega_run (n + 1)" using omega_run by argo
    hence rho_np1: "?rho (n + 1) = omega_run (n + 1)" unfolding rho_from_chain_def by simp
    have "(omega_run n, omega_word n, omega_run (n+1)) \<in> transitions \<A>" using omega_run_well_def unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
    hence "(?rho n, omega_word n, ?rho (n + 1)) \<in> transitions \<A>" using rho_n rho_np1 by auto
  }
  hence "\<forall> n . (?rho n, omega_word n, ?rho (n + 1)) \<in> transitions \<A>" by blast
  thus ?thesis unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def using init trans by blast
qed

text \<open>Intermezzo: same Approach with Chain argument for a general omega_run\<close>
definition Rpref :: "nat \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> 's run set" where "Rpref n \<A> omega_word = {run . greedy_run run \<A> (pre_omega_word omega_word n)}"

lemma Rpref_length_const:
  assumes "r \<in> Rpref n \<A> omega_word"
  shows "length r = n + 1"
  using assms pre_omega_word_length unfolding Rpref_def greedy_run_def run_well_defined_def pseudo_run_well_defined_def by auto

lemma pre_omega_word_take:
  assumes "m \<le> n"
  shows "take m (pre_omega_word omega_word n) = pre_omega_word omega_word m"
  using assms unfolding pre_omega_word_def by (simp add: take_map)

lemma run_well_defined_take:
  assumes "run_well_defined run \<A> word" "m \<le> length word"
  shows "run_well_defined (take (m + 1) run) \<A> (take m word)"
proof -
  have props: "pseudo_run_well_defined run \<A> (initial_state \<A>) word" using assms unfolding run_well_defined_def by simp
  hence len: "length run = length word + 1" unfolding pseudo_run_well_defined_def by auto
  hence take_len: "length (take (m + 1) run) = length (take m word) + 1" using len assms by simp
  have init: "(take (m + 1) run) ! 0 = initial_state \<A>" using props assms unfolding pseudo_run_well_defined_def by force
  have init_in: "initial_state \<A> \<in> states \<A>" using props unfolding pseudo_run_well_defined_def by auto
  {
    fix i assume "i < length (take (m + 1) run) - 1"
    hence i: "i < m" by simp
    hence "i < length run - 1" using len assms by force
    hence step: "(run ! i, word ! i, run ! (i + 1)) \<in> transitions \<A>" using props unfolding pseudo_run_well_defined_def by blast
    have run_i: "(take (m + 1) run) ! i = run ! i" using i len assms by force
    have word_i: "(take m word) ! i = word ! i" using i assms by simp
    have "(take (m + 1) run) ! (i + 1) = run ! (i + 1)" using i len assms by force
    hence "((take (m + 1) run) ! i, (take m word) ! i, (take (m + 1) run) ! (i + 1)) \<in> transitions \<A>" using step run_i word_i by presburger
  }
  hence "\<forall> i < length (take (m + 1) run) - 1 . ((take (m + 1) run) ! i, (take m word) ! i, (take (m + 1) run) ! (i + 1)) \<in> transitions \<A>" by blast
  thus ?thesis using take_len init init_in unfolding run_well_defined_def pseudo_run_well_defined_def by blast
qed

lemma Rpref_finite:
  assumes "auto_well_defined \<A>"
  shows "finite (Rpref n \<A> omega_word)"
proof -
  {
    fix r assume "r \<in> Rpref n \<A> omega_word"
    hence "run_well_defined r \<A> (pre_omega_word omega_word n)" unfolding Rpref_def greedy_run_def by blast
    hence well_def: "pseudo_run_well_defined r \<A> (initial_state \<A>) (pre_omega_word omega_word n)" unfolding run_well_defined_def by blast
    hence len: "length r = n + 1" unfolding pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
    have "prun_states r \<A>" using assms well_def well_def_implies_prun_states by fast
    hence "r \<in> {run . prun_states run \<A> \<and> length run = n + 1}" using len by blast
  }  
  hence sub: "Rpref n \<A> omega_word \<subseteq> {run . prun_states run \<A> \<and> length run = n + 1}" by blast
  have "finite {run . prun_states run \<A> \<and> length run = n + 1}" using assms finite_lists_length_eq unfolding auto_well_defined_def prun_states_def by blast
  thus ?thesis using finite_subset sub by blast
qed

definition children_pref :: "nat \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> 's run \<Rightarrow> 's run set" where "children_pref i \<A> omega_word r = {r' \<in> Rpref (Suc i) \<A> omega_word . r \<prec> r'}"

definition descendants_pref :: "nat \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> 's run \<Rightarrow> 's run set" where "descendants_pref i \<A> omega_word r = {t . \<exists> j \<ge> i . t \<in> Rpref j \<A> omega_word \<and> r \<preceq> t}"

lemma descendant_has_child_pref:
  assumes "auto_well_defined \<A>" "r \<in> Rpref i \<A> omega_word" "t \<in> descendants_pref i \<A> omega_word r" "t \<notin> Rpref i \<A> omega_word"
  shows "\<exists> c \<in> children_pref i \<A> omega_word r . t \<in> descendants_pref (Suc i) \<A> omega_word c"
proof -
  obtain j where j: "j \<ge> i \<and> t \<in> Rpref j \<A> omega_word \<and> r \<preceq> t" using assms unfolding descendants_pref_def by blast
  hence j_gt: "j > i" using assms le_neq_implies_less by blast
  have len_r: "length r = i + 1" using assms Rpref_length_const by blast
  have len_t: "length t = j + 1" using j Rpref_length_const by blast
  define c where "c = take (Suc i + 1) t"
  hence c_len: "length c = Suc i + 1" using len_t j_gt by force
  hence leq: "length r < length c" using assms Rpref_length_const by force
  have "take (length r) t = r" using j unfolding prefixeq_def by force
  hence "take (length r) c = r" using len_r j_gt c_def leq Suc_eq_plus1 add_less_cancel_left c_len le_refl len_t new_butlast_equi2 plus_1_eq_Suc take_all by metis
  hence "r \<preceq> c" using append_take_drop_id unfolding prefixeq_def by metis
  then obtain d where d: "r @ d = c" unfolding prefixeq_def by blast
  hence "d \<noteq> []" using leq len_r by force
  hence r_proper_c: "r \<prec> c" using d unfolding proper_prefix_def by blast
  have "length (pre_omega_word omega_word j) = j" using pre_omega_word_length by auto
  hence len_suc: "length (pre_omega_word omega_word j) \<ge> Suc i \<and> j \<ge> Suc i" using j_gt by linarith
  have "greedy_run t \<A> (pre_omega_word omega_word j)" using j unfolding Rpref_def by auto
  hence run_take: "greedy_run (take ((Suc i) + 1) t) \<A> (take (Suc i) (pre_omega_word omega_word j))" using greedy_run_take len_suc by blast    
  have "take (Suc i) (pre_omega_word omega_word j) = pre_omega_word omega_word (Suc i)" using pre_omega_word_take len_suc by fast
  hence "c \<in> Rpref (Suc i) \<A> omega_word" using run_take unfolding c_def Rpref_def by auto
  hence c_child: "c \<in> children_pref i \<A> omega_word r" using r_proper_c unfolding children_pref_def by blast
  have "c \<preceq> t" using append_take_drop_id unfolding prefixeq_def c_def by blast
  hence "t \<in> descendants_pref (Suc i) \<A> omega_word c" using j len_suc unfolding descendants_pref_def by blast
  thus ?thesis using c_child by blast
qed

lemma infinite_descendants_choose_child_pref:
  assumes "auto_well_defined \<A>" "r \<in> Rpref i \<A> omega_word" "infinite (descendants_pref i \<A> omega_word r)"
  shows "\<exists> c \<in> children_pref i \<A> omega_word r . infinite (descendants_pref (Suc i) \<A> omega_word c)"
proof -
  let ?Ch = "children_pref i \<A> omega_word r"
  have "finite (Rpref (Suc i) \<A> omega_word)" using Rpref_finite assms by blast
  hence finCh: "finite ?Ch" using finite_subset unfolding children_pref_def by auto
  let ?B = "{t . t \<in> Rpref i \<A> omega_word \<and> r \<preceq> t}"
  have "finite (Rpref i \<A> omega_word)" using Rpref_finite assms by auto
  hence finB: "finite ?B" using finite_subset by auto  
  {
    fix t assume assm: "t \<in> descendants_pref i \<A> omega_word r"
    have "t \<in> ?B \<union> (\<Union> c \<in> ?Ch . descendants_pref (Suc i) \<A> omega_word c)"
    proof (cases "t \<in> Rpref i \<A> omega_word")
      case True thus ?thesis using assm unfolding descendants_pref_def by blast
    next
      case False
      then obtain c where "c \<in> children_pref i \<A> omega_word r \<and> t \<in> descendants_pref (Suc i) \<A> omega_word c" using descendant_has_child_pref assms assm by blast
      thus ?thesis by blast
    qed
  }
  hence sub: "descendants_pref i \<A> omega_word r \<subseteq> ?B \<union> (\<Union> c \<in> ?Ch . descendants_pref (Suc i) \<A> omega_word c)" by blast
  have "infinite (\<Union> c \<in> ?Ch . descendants_pref (Suc i) \<A> omega_word c)"
  proof (rule ccontr)
    assume "\<not> infinite (\<Union> c \<in> ?Ch . descendants_pref (Suc i) \<A> omega_word c)"
    hence "finite (\<Union> c \<in> ?Ch . descendants_pref (Suc i) \<A> omega_word c)" by blast
    hence "finite (?B \<union> (\<Union> c \<in> ?Ch . descendants_pref (Suc i) \<A> omega_word c))" using finB by blast
    hence "finite (descendants_pref i \<A> omega_word r)" using sub finite_subset by fast
    thus False using assms by auto
  qed
  thus ?thesis using finCh by blast
qed

lemma infinite_descendants_0_pref:
  assumes "infinite (\<Union> n . Rpref n \<A> omega_word)"
  shows "infinite (descendants_pref 0 \<A> omega_word [initial_state \<A>])"
proof -
  {
    fix t assume "t \<in> (\<Union> n . Rpref n \<A> omega_word)"
    then obtain j where j: "t \<in> Rpref j \<A> omega_word" by blast
    hence "run_well_defined t \<A> (pre_omega_word omega_word j)" unfolding Rpref_def greedy_run_def by blast
    hence "t \<noteq> [] \<and> t ! 0 = initial_state \<A>" unfolding run_well_defined_def pseudo_run_well_defined_def by force
    then obtain t' where "t = [initial_state \<A>] @ t'" by(induction t) auto
    hence "[initial_state \<A>] \<preceq> t" unfolding prefixeq_def by auto
    hence "t \<in> descendants_pref 0 \<A> omega_word [initial_state \<A>]" using j unfolding descendants_pref_def by fast 
  }  
  hence "(\<Union> n . Rpref n \<A> omega_word) \<subseteq> descendants_pref 0 \<A> omega_word [initial_state \<A>]" by blast
  thus ?thesis using assms infinite_super by fast
qed

lemma initial_greedy_pref0:
  assumes "auto_well_defined \<A>"
  shows "[initial_state \<A>] \<in> Rpref 0 \<A> omega_word"
proof -
  have rwd: "run_well_defined [initial_state \<A>] \<A> (pre_omega_word omega_word 0)" using assms pre_omega_word_0 unfolding run_well_defined_def pseudo_run_well_defined_def auto_well_defined_def by auto
  have "greedy_run [initial_state \<A>] \<A> (pre_omega_word omega_word 0)" 
  proof(rule ccontr)
    assume "\<not> greedy_run [initial_state \<A>] \<A> (pre_omega_word omega_word 0)"
    hence "\<exists> run' . run_well_defined run' \<A> (pre_omega_word omega_word 0) \<and> last run' = last [initial_state \<A>] \<and> (acc_sum \<A> run') > (acc_sum \<A> [initial_state \<A>])" using rwd unfolding greedy_run_def by fast
    then obtain run' where run': "run_well_defined run' \<A> (pre_omega_word omega_word 0) \<and> last run' = last [initial_state \<A>] \<and> acc_sum \<A> run' > acc_sum \<A> [initial_state \<A>]" by blast
    hence len: "length run' = 1" unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_0)
    have init: "run' ! 0 = initial_state \<A>" using run' unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_0)
    hence "run' = [initial_state \<A>]" using len by (cases run') auto
    thus False using run' by simp
  qed
  thus ?thesis unfolding Rpref_def by simp
qed

lemma chain_exists_Rpref:
  assumes "auto_well_defined \<A>" "infinite (\<Union> n . Rpref n \<A> omega_word)"
  shows "\<exists> rseq . (\<forall> i . rseq i \<in> Rpref i \<A> omega_word \<and> rseq i \<prec> rseq (Suc i))"
proof -
  have Inf0: "infinite (descendants_pref 0 \<A> omega_word [initial_state \<A>])" using infinite_descendants_0_pref assms by blast
  have "run_well_defined [initial_state \<A>] \<A> (pre_omega_word omega_word 0)" using assms pre_omega_word_0 unfolding run_well_defined_def pseudo_run_well_defined_def auto_well_defined_def by auto
  hence r0_in: "[initial_state \<A>] \<in> Rpref 0 \<A> omega_word" using assms initial_greedy_pref0 by fast
  define rseq where "rseq = rec_nat [initial_state \<A>] (\<lambda>i ri . (SOME c . c \<in> children_pref i \<A> omega_word ri \<and> infinite (descendants_pref (Suc i) \<A> omega_word c)))"
  have rseq0: "rseq 0 = [initial_state \<A>]" unfolding rseq_def by simp
  {
    fix i
    have "rseq i \<in> Rpref i \<A> omega_word \<and> infinite (descendants_pref i \<A> omega_word (rseq i))"
    proof (induction i)
      case 0 thus ?case using rseq0 r0_in Inf0 by auto
    next
      case (Suc i)
      hence "\<exists> c \<in> children_pref i \<A> omega_word (rseq i) . infinite (descendants_pref (Suc i) \<A> omega_word c)" using infinite_descendants_choose_child_pref assms by blast
      hence some_mem: "(SOME c . c \<in> children_pref i \<A> omega_word (rseq i) \<and> infinite (descendants_pref (Suc i) \<A> omega_word c)) \<in> children_pref i \<A> omega_word (rseq i) \<and> infinite (descendants_pref (Suc i) \<A> omega_word (SOME c . c \<in> children_pref i \<A> omega_word (rseq i) \<and> infinite (descendants_pref (Suc i) \<A> omega_word c)))" by (rule someI2_bex) auto
      hence "rseq (Suc i) \<in> children_pref i \<A> omega_word (rseq i)" unfolding rseq_def by simp
      hence inR: "rseq (Suc i) \<in> Rpref (Suc i) \<A> omega_word" unfolding children_pref_def by simp
      have "infinite (descendants_pref (Suc i) \<A> omega_word (rseq (Suc i)))" using some_mem unfolding rseq_def by simp
      thus ?case using inR by simp
    qed
  }
  hence step_all: "\<forall> i . rseq i \<in> Rpref i \<A> omega_word \<and> infinite (descendants_pref i \<A> omega_word (rseq i))" by auto
  {
    fix i
    have props: "rseq i \<in> Rpref i \<A> omega_word \<and> infinite (descendants_pref i \<A> omega_word (rseq i))" using step_all by simp
    hence "\<exists> c \<in> children_pref i \<A> omega_word (rseq i) . infinite (descendants_pref (Suc i) \<A> omega_word c)" using infinite_descendants_choose_child_pref assms by blast
    hence "(SOME c . c \<in> children_pref i \<A> omega_word (rseq i) \<and> infinite (descendants_pref (Suc i) \<A> omega_word c)) \<in> children_pref i \<A> omega_word (rseq i)" by (rule someI2_bex) auto
    hence "rseq (Suc i) \<in> children_pref i \<A> omega_word (rseq i)"  unfolding rseq_def by auto
    hence "rseq i \<prec> rseq (Suc i)" unfolding children_pref_def by auto
    hence "rseq i \<prec> rseq (Suc i) \<and> rseq i \<in> Rpref i \<A> omega_word" using props by blast
  }
  hence "\<forall> i . rseq i \<prec> rseq (Suc i) \<and> rseq i \<in> Rpref i \<A> omega_word" by auto
  thus ?thesis by blast
qed

lemma chain_nth_stable_Rpref:
  assumes "\<forall> i . rseq i \<prec> rseq (Suc i) \<and> rseq i \<in> Rpref i \<A> omega_word" 
  shows "(rseq (Suc (Suc n))) ! n = (rseq (Suc n)) ! n"
proof -
  have "rseq (Suc n) \<prec> rseq (Suc (Suc n))" using assms by blast
  hence "rseq (Suc n) \<preceq> rseq (Suc (Suc n))" unfolding proper_prefix_def prefixeq_def by blast
  then obtain d where app: "rseq (Suc n) @ d = rseq (Suc (Suc n))" unfolding prefixeq_def by blast
  have "n < length (rseq (Suc n))" using assms chain_len_ge by blast
  thus ?thesis using app nth_append by metis
qed

lemma chain_nth_stable_iter_Rpref: "i \<le> n \<and> (\<forall> i . rseq i \<in> Rpref i \<A> omega_word \<and> rseq i \<prec> rseq (Suc i)) \<Longrightarrow> (rseq (Suc n)) ! i = (rseq (Suc i)) ! i"
proof (induction "n - i" arbitrary: n)
  case 0 thus ?case by simp
next
  case (Suc k)
  hence "i < n" by simp
  then obtain n' where n: "n = Suc n'" by (cases n) auto
  hence i_le_n': "i \<le> n'" using Suc by simp
  hence IH: "(rseq (Suc n')) ! i = (rseq (Suc i)) ! i" using Suc Suc_diff_le Suc_inject n by metis
  have "rseq (Suc n') \<prec> rseq (Suc (Suc n'))" using Suc by blast
  hence "rseq (Suc n') \<preceq> rseq (Suc (Suc n'))" unfolding proper_prefix_def prefixeq_def by auto
  then obtain d where app: "rseq (Suc n') @ d = rseq (Suc (Suc n'))" unfolding prefixeq_def by blast
  have "length (rseq (Suc n')) = Suc n' + 1" using Suc Rpref_length_const by blast
  hence "i < length (rseq (Suc n'))" using i_le_n' by simp
  hence "(rseq (Suc (Suc n'))) ! i = (rseq (Suc n')) ! i" using app nth_append by metis
  thus ?case using IH n by simp
qed

lemma pre_omega_run_rho_from_chain:
  assumes "\<forall> i . rseq i \<in> Rpref i \<A> omega_word \<and> rseq i \<prec> rseq (Suc i)"
  shows "pre_omega_run (rho_from_chain rseq) n = rseq n"
proof (rule nth_equalityI)
  show "length (pre_omega_run (rho_from_chain rseq) n) = length (rseq n)" using assms Rpref_length_const add.commute diff_zero length_map length_upt plus_1_eq_Suc unfolding pre_omega_run_def by metis
next
  fix i assume i: "i < length (pre_omega_run (rho_from_chain rseq) n)"
  hence i_lt: "i < n + 1" unfolding pre_omega_run_def by auto
  hence i_le: "i \<le> n" by simp
  have lhs: "(pre_omega_run (rho_from_chain rseq) n) ! i = (rho_from_chain rseq) i" using i pre_omega_run_length pre_omega_run_nth unfolding pre_omega_run_def by metis
  have rho_i: "(rho_from_chain rseq) i = (rseq (Suc i)) ! i" unfolding rho_from_chain_def by auto
  have stab: "(rseq (Suc n)) ! i = (rseq (Suc i)) ! i" using chain_nth_stable_iter_Rpref assms i_le by blast
  have "rseq n \<prec> rseq (Suc n)" using assms by blast
  hence "rseq n \<preceq> rseq (Suc n)" unfolding proper_prefix_def prefixeq_def by blast
  then obtain d where app: "rseq n @ d = rseq (Suc n)" unfolding prefixeq_def by blast
  have "length (rseq n) = n + 1" using assms Rpref_length_const by blast
  hence "i < length (rseq n)" using i_lt by simp
  hence "(rseq (Suc n)) ! i = (rseq n) ! i" using app nth_append by metis
  thus "(pre_omega_run (rho_from_chain rseq) n) ! i = (rseq n) ! i" using lhs rho_i stab by simp
qed

lemma rho_well_defined_Rpref:
  assumes "auto_well_defined \<A>" "\<forall> i . rseq i \<in> Rpref i \<A> omega_word \<and> rseq i \<prec> rseq (Suc i)"
  shows "omega_run_well_defined (rho_from_chain rseq) \<A> omega_word"
proof -
  let ?rho = "rho_from_chain rseq"
  have "rseq 1 \<in> Rpref 1 \<A> omega_word" using assms by auto
  hence r1: "run_well_defined (rseq 1) \<A> (pre_omega_word omega_word 1)" unfolding Rpref_def greedy_run_def by auto
  have "?rho 0 = (rseq 1) ! 0" unfolding rho_from_chain_def by auto
  hence init: "?rho 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using r1 unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  {
    fix n
    have "rseq (Suc (Suc n)) \<in> Rpref (Suc (Suc n)) \<A> omega_word" using assms by blast
    hence pr: "pseudo_run_well_defined (rseq (Suc (Suc n))) \<A> (initial_state \<A>) (pre_omega_word omega_word (Suc (Suc n)))" unfolding Rpref_def greedy_run_def run_well_defined_def by simp
    hence "n < length (rseq (Suc (Suc n))) - 1" unfolding pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
    hence trans: "((rseq (Suc (Suc n))) ! n, (pre_omega_word omega_word (Suc (Suc n))) ! n, (rseq (Suc (Suc n))) ! (n + 1)) \<in> transitions \<A>" using pr unfolding pseudo_run_well_defined_def by blast
    have w_n: "(pre_omega_word omega_word (Suc (Suc n))) ! n = omega_word n" by (simp add: pre_omega_word_nth)
    have "(rseq (Suc (Suc n))) ! n = (rseq (Suc n)) ! n" using assms chain_nth_stable_Rpref by blast
    hence rho_n: "?rho n = (rseq (Suc (Suc n))) ! n" unfolding rho_from_chain_def by auto
    have "?rho (n + 1) = (rseq (Suc (Suc n))) ! (n + 1)" unfolding rho_from_chain_def by auto
    hence "(?rho n, omega_word n, ?rho (n + 1)) \<in> transitions \<A>" using trans w_n rho_n by argo
  }
  hence "\<forall> n . (?rho n, omega_word n, ?rho (n + 1)) \<in> transitions \<A>" by blast
  thus ?thesis using init unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
qed

lemma rho_greedy_Rpref:
  assumes "auto_well_defined \<A>" "\<forall> i . rseq i \<in> Rpref i \<A> omega_word \<and> rseq i \<prec> rseq (Suc i)"
  shows "omega_greedy_run (rho_from_chain rseq) \<A> omega_word"
proof -
  have wd: "omega_run_well_defined (rho_from_chain rseq) \<A> omega_word" using rho_well_defined_Rpref assms by blast
  {
    fix n
    have "rseq n \<in> Rpref n \<A> omega_word" using assms by blast
    hence greedy: "greedy_run (rseq n) \<A> (pre_omega_word omega_word n)" unfolding Rpref_def by blast
    have "pre_omega_run (rho_from_chain rseq) n = rseq n" using pre_omega_run_rho_from_chain assms by blast
    hence "greedy_run (pre_omega_run (rho_from_chain rseq) n) \<A> (pre_omega_word omega_word n)" using greedy by simp
  }
  hence "\<forall> n . greedy_run (pre_omega_run (rho_from_chain rseq) n) \<A> (pre_omega_word omega_word n)" by auto
  thus ?thesis using wd unfolding omega_greedy_run_def by blast
qed

theorem omega_run_exists_if_all_prefix_runs:
  assumes "auto_well_defined \<A>" "\<forall> n . \<exists> run . run_well_defined run \<A> (pre_omega_word omega_word (Suc n))"
  shows "\<exists> omega_run . omega_greedy_run omega_run \<A> omega_word"
proof -
  let ?pick = "\<lambda>n. (SOME r . r \<in> Rpref (Suc n) \<A> omega_word)"
  have "\<forall> n . {run . run_well_defined run \<A> (pre_omega_word omega_word (Suc n))} \<noteq> {}" using assms by blast
  have "\<forall> n . Rpref (Suc n) \<A> omega_word \<noteq> {}" using assms greedy_run_exists unfolding Rpref_def by fast
  hence pick_mem: "\<forall> n . ?pick n \<in> Rpref (Suc n) \<A> omega_word" using someI_ex by fast
  {
    fix i j assume assm: "?pick i = ?pick j"
    have li: "length (?pick i) = (Suc i) + 1" using pick_mem Rpref_length_const by blast
    have "length (?pick j) = (Suc j) + 1" using pick_mem Rpref_length_const by blast
    hence "i = j" using assm li by presburger
  }
  hence "inj ?pick" by (rule injI) auto
  hence inf: "infinite (range ?pick)" using finite_image_iff by blast
  have "range ?pick \<subseteq> (\<Union> n . Rpref n \<A> omega_word)" using pick_mem by blast
  hence "infinite (\<Union> n . Rpref n \<A> omega_word)" using inf infinite_super by blast
  then obtain rseq where "\<forall> i . rseq i \<in> Rpref i \<A> omega_word \<and> rseq i \<prec> rseq (Suc i)" using chain_exists_Rpref assms by blast
  thus ?thesis using rho_greedy_Rpref assms by blast
qed

proposition maximal_prefix_omega_run:
  assumes "auto_well_defined \<A>" "\<nexists> omega_run . omega_run_well_defined omega_run \<A> omega_word"
  shows "\<exists> n . (\<exists> run . run_well_defined run \<A> (pre_omega_word omega_word n)) \<and> (\<forall> run . run_well_defined run \<A> (pre_omega_word omega_word n) \<longrightarrow> (\<nexists> s . s \<in> states \<A> \<and> (last run, omega_word n, s) \<in> transitions \<A>))"
proof -
  have base: "run_well_defined [initial_state \<A>] \<A> (pre_omega_word omega_word 0)" using assms pre_omega_word_0 unfolding run_well_defined_def pseudo_run_well_defined_def auto_well_defined_def by force
  define Bad where "Bad = {n . (\<nexists> run . run_well_defined run \<A> (pre_omega_word omega_word (Suc n)))}"
  obtain n where n: "n = (LEAST m . m \<in> Bad)" by blast
  have "Bad \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> Bad \<noteq> {}"
    hence "Bad = {}" by simp
    hence "\<forall> n . \<exists> run . run_well_defined run \<A> (pre_omega_word omega_word (Suc n))" unfolding Bad_def by blast
    hence "\<exists> omega_run . omega_run_well_defined omega_run \<A> omega_word" using omega_run_exists_if_all_prefix_runs assms unfolding omega_greedy_run_def by blast
    thus False using assms by auto
  qed
  hence n_props: "n \<in> Bad \<and> (\<forall> m < n . m \<notin> Bad)" using n LeastI all_not_in_conv not_less_Least by metis
  have prefix_exists: "\<exists> run . run_well_defined run \<A> (pre_omega_word omega_word n)"
  proof (cases n)
    case 0 thus ?thesis using base by blast
  next
    case (Suc m)
    hence "m < n" by auto
    hence "m \<notin> Bad" using n_props by blast
    thus ?thesis unfolding Bad_def Suc by blast
  qed
  {
    fix run assume assm: "run_well_defined run \<A> (pre_omega_word omega_word n)"
    have "\<nexists> s . s \<in> states \<A> \<and> (last run, omega_word n, s) \<in> transitions \<A>"
    proof(rule ccontr)
      assume "\<not> (\<nexists> s . s \<in> states \<A> \<and> (last run, omega_word n, s) \<in> transitions \<A>)"
      hence "\<exists> s \<in> states \<A> . (last run, omega_word n, s) \<in> transitions \<A>" by blast
      then obtain s where s: "s \<in> states \<A> \<and> (last run, omega_word n, s) \<in> transitions \<A>" by blast
      hence well_def: "run_well_defined (run @ [s]) \<A> ((pre_omega_word omega_word n) @ [omega_word n])" using assm prun_well_defined_extension_snoc unfolding run_well_defined_def by fast
      have "(pre_omega_word omega_word n) @ [omega_word n] = pre_omega_word omega_word (Suc n)" unfolding pre_omega_word_def by simp
      hence "run_well_defined (run @ [s]) \<A> (pre_omega_word omega_word (Suc n))" using well_def by argo
      thus False using n_props unfolding Bad_def by blast
    qed
  }
  thus ?thesis using prefix_exists by blast
qed

lemma chain_prefixeq:
  assumes "\<forall> i . rseq i \<prec> rseq (Suc i)"
  shows "i \<le> j \<Longrightarrow> rseq i \<preceq> rseq j"
proof (induction j arbitrary: i)
  case 0 thus ?case using prefixeq_def by blast
next
  case (Suc j)
  thus ?case
  proof (cases "i = Suc j")
    case True thus ?thesis using assms unfolding proper_prefix_def prefixeq_def by blast
  next
    case False
    hence "rseq i \<preceq> rseq j \<and> rseq j \<prec> rseq (Suc j)" using Suc assms by force
    then obtain d1 d2 where "rseq i @ d1 = rseq j \<and> rseq j @ d2 = rseq (Suc j)" unfolding proper_prefix_def prefixeq_def by blast
    hence "rseq i @ d1 @ d2 = rseq (Suc j)" using append.assoc by metis
    thus ?thesis unfolding prefixeq_def by metis
  qed
qed

lemma nth_prefixeq:
  assumes "a \<preceq> b" "k < length a"
  shows "b ! k = a ! k"
  using assms nth_append unfolding prefixeq_def by metis

lemma rho_accepting:
  assumes "auto_well_defined \<A>" "omega_word \<in> omega_language_auto \<A>" "\<forall> i . rseq i \<in> R_tilde i \<A> omega_word \<and> rseq i \<prec> rseq (Suc i)"
  shows "omega_run_accepting (rho_from_chain rseq) \<A> omega_word"
proof -
  let ?rho = "rho_from_chain rseq"
  have rho_well_def: "omega_run_well_defined ?rho \<A> omega_word" using rho_well_defined assms by blast
  {
    fix n
    have "rseq (Suc (Suc n)) \<in> R_tilde (Suc (Suc n)) \<A> omega_word" using assms by blast
    then obtain omega_run where omega_run: "omega_run \<in> R_i (Suc (Suc n)) \<A> omega_word \<and> rseq (Suc (Suc n)) = pre_omega_run omega_run (pos_i (Suc n) \<A> omega_run)" using R_tilde_witness by blast
    hence acc_run: "omega_run_accepting omega_run \<A> omega_word" using R_i_mem_accepting by blast    
    let ?N = "pos_i (Suc n) \<A> omega_run"
    have "?N \<ge> Suc n" using pos_i_ge_index acc_run by blast
    hence Ngt: "?N > n" by auto   
    have "length (rseq (Suc (Suc n))) = Suc ?N" using omega_run pre_omega_run_length by metis
    hence Nlt_len: "?N < length (rseq (Suc (Suc n)))" by simp
    have "rseq (Suc (Suc n)) \<preceq> rseq (Suc ?N)" using chain_prefixeq assms Ngt by fastforce
    hence nth_eq: "rseq (Suc ?N) ! ?N = rseq (Suc (Suc n)) ! ?N" using nth_prefixeq Nlt_len by blast
    have "?N < Suc (pos_i (Suc n) \<A> omega_run)" by blast
    hence "(pre_omega_run omega_run (pos_i (Suc n) \<A> omega_run)) ! ?N = omega_run ?N" using pre_omega_run_nth by blast
    hence "rseq (Suc (Suc n)) ! ?N = omega_run ?N" using omega_run by argo
    hence "rseq (Suc ?N) ! ?N = omega_run ?N" using nth_eq by argo    
    hence "?rho ?N = omega_run ?N" unfolding rho_from_chain_def by blast
    hence "?rho ?N \<in> accepting_states \<A>" using pos_i_gt_and_acc acc_run by metis
    hence "\<exists> N > n . ?rho N \<in> accepting_states \<A>" using Ngt by blast
  }
  thus ?thesis using rho_well_def unfolding omega_run_accepting_def by blast
qed

lemma not_omega_greedy_ex_min_bad_prefix:
  assumes "omega_run_well_defined rho \<A> omega_word" "\<not> omega_greedy_run rho \<A> omega_word"
  shows "\<exists> n . (\<not> greedy_run (pre_omega_run rho n) \<A> (pre_omega_word omega_word n)) \<and> (\<forall> m < n . greedy_run (pre_omega_run rho m) \<A> (pre_omega_word omega_word m))"
proof -
  have ex: "\<exists> n . \<not> greedy_run (pre_omega_run rho n) \<A> (pre_omega_word omega_word n)" using assms unfolding omega_greedy_run_def by auto
  then obtain n where n: "n = (LEAST n . \<not> greedy_run (pre_omega_run rho n) \<A> (pre_omega_word omega_word n))" by blast
  thus ?thesis using ex not_less_Least LeastI by (metis (no_types, lifting))
qed

definition splice_omega_run :: "'s run \<Rightarrow> 's omega_run \<Rightarrow> 's omega_run" where "splice_omega_run beta rho = (\<lambda>k . if k < length beta then beta ! k else rho k)"

lemma splice_omega_run_well_defined:
  assumes "omega_run_well_defined rho \<A> omega_word" "run_well_defined beta \<A> (pre_omega_word omega_word (length beta - 1))" "last beta = rho (length beta - 1)"
  shows "omega_run_well_defined (splice_omega_run beta rho) \<A> omega_word"
proof -
  let ?r = "splice_omega_run beta rho"
  have props: "beta \<noteq> [] \<and> beta ! 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce  
  hence init: "?r 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" unfolding splice_omega_run_def by auto
  {
    fix n
    consider (case1) "n < length beta - 1" | (case2) "n = length beta - 1" | (case3) "n > length beta - 1" by linarith
    hence "(?r n, omega_word n, ?r (n + 1)) \<in> transitions \<A>"
    proof cases
      case case1
      hence trans: "(beta ! n, (pre_omega_word omega_word (length beta - 1)) ! n, beta ! (n + 1)) \<in> transitions \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast     
      hence r_n: "?r n = beta ! n" using case1 unfolding splice_omega_run_def by auto
      have ow_n: "omega_word n = (pre_omega_word omega_word (length beta - 1)) ! n" using case1 unfolding pre_omega_word_def by auto
      have "?r (n + 1) = beta ! (n + 1)" using case1 unfolding splice_omega_run_def by auto
      thus ?thesis using r_n ow_n trans by simp
    next
      case case2
      have trans: "(rho n, omega_word n, rho (n + 1)) \<in> transitions \<A>" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
      have "last beta = rho n \<and> beta \<noteq> []" using case2 assms props by blast
      hence r_n: "?r n = rho n" using case2 last_conv_nth unfolding splice_omega_run_def by metis
      have "?r (n + 1) = rho (n + 1)" using case2 unfolding splice_omega_run_def by auto
      thus ?thesis using trans r_n by argo
    next
      case case3 thus ?thesis using assms unfolding splice_omega_run_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by force
    qed
  }   
  thus ?thesis using init unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
qed

lemma splice_preserves_accepting:
  assumes "omega_run_accepting rho \<A> omega_word" "run_well_defined beta \<A> (pre_omega_word omega_word (length beta - 1))" "last beta = rho (length beta - 1)"
  shows "omega_run_accepting (splice_omega_run beta rho) \<A> omega_word"
proof -
  let ?r = "splice_omega_run beta rho"
  have props: "omega_run_well_defined rho \<A> omega_word \<and> (\<forall> n . \<exists> N > n . rho N \<in> accepting_states \<A>)" using assms unfolding omega_run_accepting_def by auto
  hence omega_run: "omega_run_well_defined (splice_omega_run beta rho) \<A> omega_word" using assms splice_omega_run_well_defined by blast
  {
    fix n
    obtain N where N: "N = n + length beta + 1" by simp
    then obtain N' where N': "N' > N \<and> rho N' \<in> accepting_states \<A>" using props by blast
    hence acc: "?r N' \<in> accepting_states \<A>" using N unfolding splice_omega_run_def by auto
    have "N' > n" using N' N by simp
    hence "\<exists> N > n . ?r N \<in> accepting_states \<A>" using acc by blast
  }
  thus ?thesis using omega_run  unfolding omega_run_accepting_def by blast
qed

lemma rho_agrees_with_level:
  assumes "\<forall> k . rseq k \<prec> rseq (Suc k)" "k < length (rseq (Suc i))"
  shows "rho_from_chain rseq k = (rseq (Suc i)) ! k"
proof (cases "k < i")
  case True
  hence pre: "rseq (Suc k) \<preceq> rseq (Suc i)" using chain_prefixeq assms by fastforce
  have "k < length (rseq (Suc k))"  using chain_len_ge assms by blast
  hence "(rseq (Suc i)) ! k = (rseq (Suc k)) ! k"  using nth_prefixeq pre by blast
  thus ?thesis unfolding rho_from_chain_def by simp
next
  case False
  hence pre: "rseq (Suc i) \<preceq> rseq (Suc k)" using chain_prefixeq assms by fastforce
  hence "(rseq (Suc k)) ! k = (rseq (Suc i)) ! k" using assms nth_prefixeq by blast
  thus ?thesis unfolding rho_from_chain_def by simp
qed

lemma pos_i_eq_if_eq_upto:
  assumes "omega_run_accepting r1 \<A> omega_word" "omega_run_accepting r2 \<A> omega_word"
  shows "\<forall> k \<le> pos_i i \<A> r1 . r2 k = r1 k \<Longrightarrow> pos_i i \<A> r2 = pos_i i \<A> r1"
proof (induction i)
  case 0
  let ?p = "pos_i 0 \<A> r1"
  have "r1 ?p = r2 ?p \<and> r1 ?p \<in> accepting_states \<A>" using 0 assms pos_i_0_acc by auto  
  hence Pp: "r2 ?p \<in> accepting_states \<A>" by argo
  hence exP: "\<exists> k . r2 k \<in> accepting_states \<A>" by blast
  {
    fix m assume assm: "m < ?p"
    hence "r1 m \<notin> accepting_states \<A>" using exP not_less_Least unfolding pos_i.simps by blast
    hence "r2 m \<notin> accepting_states \<A>" using assms assm 0 by simp
  }
  hence "\<forall> m < ?p . r2 m \<notin> accepting_states \<A>" by blast
  thus ?case using leI Least_equality Pp unfolding pos_i.simps by metis
next
  case (Suc i)
  let ?p1 = "pos_i i \<A> r1"
  let ?p2 = "pos_i (Suc i) \<A> r1"
  have leq: "?p1 < ?p2 \<and> r1 ?p2 \<in> accepting_states \<A>" using assms pos_i_Suc_gt_and_acc by auto
  hence equi: "pos_i i \<A> r2 = ?p1" using Suc by auto
  have "r2 ?p2 = r1 ?p2" using Suc by blast
  hence props: "pos_i i \<A> r2 < ?p2 \<and> r2 ?p2 \<in> accepting_states \<A>" using equi leq by argo
  {
    fix m assume assm: "m < ?p2"
    have "\<not> (m > pos_i i \<A> r2 \<and> r2 m \<in> accepting_states \<A>)"
    proof(rule ccontr)
      assume "\<not> \<not> (m > pos_i i \<A> r2 \<and> r2 m \<in> accepting_states \<A>)"
      hence "m > pos_i i \<A> r2 \<and> r2 m \<in> accepting_states \<A>" by blast
      hence bad: "m > ?p1 \<and> r2 m \<in> accepting_states \<A>" using equi by force
      have "r2 m = r1 m" using Suc assm by force
      hence "r1 m \<in> accepting_states \<A>" using bad by auto
      hence "\<not> (m < ?p2)" using not_less_Least bad unfolding pos_i.simps by blast
      thus False using assm by blast
    qed
  }
  hence "\<forall> m < ?p2 . \<not> (m > pos_i i \<A> r2 \<and> r2 m \<in> accepting_states \<A>)" by blast
  thus ?case using leI props Least_equality[of "\<lambda>n . n > pos_i i \<A> r2 \<and> r2 n \<in> accepting_states \<A>" ?p2] unfolding pos_i.simps by blast
qed

lemma rho_pos_is_Least:
  assumes "\<forall> i . rseq i \<in> R_tilde i \<A> omega_word \<and> rseq i \<prec> rseq (Suc i)" "omega_run_accepting (rho_from_chain rseq) \<A> omega_word"
  shows "pos_i i \<A> (rho_from_chain rseq) = (LEAST n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word))"
proof -
  let ?rho = "rho_from_chain rseq"
  let ?L = "(LEAST n . n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word))"
  have chain: "\<forall> k . rseq k \<prec> rseq (Suc k)" using assms by blast
  have "rseq (Suc i) \<in> R_tilde (Suc i) \<A> omega_word" using assms by blast
  then obtain omega_run where omega_run: "omega_run \<in> R_i (Suc i) \<A> omega_word \<and> rseq (Suc i) = pre_omega_run omega_run (pos_i i \<A> omega_run)" using R_tilde_witness by fast
  hence omega_in: "omega_run_accepting omega_run \<A> omega_word \<and> omega_run \<in> R_i i \<A> omega_word \<and> pos_i i \<A> omega_run = ?L" using R_i_mem_accepting by auto
  {
    fix k assume k: "k \<le> pos_i i \<A> omega_run"
    have "length (rseq (Suc i)) = Suc (pos_i i \<A> omega_run)" using omega_run pre_omega_run_length by simp
    hence "k < length (rseq (Suc i))" using k by simp
    hence equi: "?rho k = (rseq (Suc i)) ! k" using chain rho_agrees_with_level by blast    
    have "k < Suc (pos_i i \<A> omega_run)" using k by simp
    hence "(pre_omega_run omega_run (pos_i i \<A> omega_run)) ! k = omega_run k" using pre_omega_run_nth by blast   
    hence "?rho k = omega_run k" using equi omega_run by presburger
  }
  hence "\<forall> k \<le> pos_i i \<A> omega_run . ?rho k = omega_run k" by blast
  thus ?thesis using assms pos_i_eq_if_eq_upto omega_in by metis
qed

lemma rho_in_all_Ri:
  assumes "\<forall> i . rseq i \<in> R_tilde i \<A> omega_word \<and> rseq i \<prec> rseq (Suc i)" "omega_run_accepting (rho_from_chain rseq) \<A> omega_word"
  shows "\<forall> i . (rho_from_chain rseq) \<in> R_i i \<A> omega_word"
proof - 
  {
    fix i
    have "(rho_from_chain rseq) \<in> R_i i \<A> omega_word"
    proof (induction i)
      case 0
      have "(rho_from_chain rseq) \<in> all_acc_omega_runs \<A> omega_word" using assms unfolding all_acc_omega_runs_def by blast
      thus ?case by auto
    next
      case (Suc i)
      have "pos_i i \<A> (rho_from_chain rseq) = (LEAST n. n \<in> image (pos_i i \<A>) (R_i i \<A> omega_word))" using rho_pos_is_Least assms by blast
      thus ?case using Suc by auto
    qed
  }
  thus ?thesis by blast
qed

lemma acc_sum_gt_ex_first_accept_diff_left: "length alpha = length beta \<and> acc_sum \<A> beta > acc_sum \<A> alpha \<Longrightarrow> \<exists> k < length alpha . beta ! k \<in> accepting_states \<A> \<and> alpha ! k \<notin> accepting_states \<A> \<and> (\<forall> l < k . (beta ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>))"
proof (induction alpha arbitrary: beta)
  case Nil thus ?case by force
next
  case (Cons a alpha)
  then obtain b beta' where beta: "beta = b # beta'" by (cases beta) auto
  hence len: "length alpha = length beta'" using Cons by simp
  have gt0: "acc_sum \<A> (b # beta') > acc_sum \<A> (a # alpha)"  using Cons beta by simp
  consider (case1) "b \<in> accepting_states \<A> \<and> a \<in> accepting_states \<A>" | (case2) "b \<in> accepting_states \<A> \<and> a \<notin> accepting_states \<A>" | (case3) "b \<notin> accepting_states \<A> \<and> a \<in> accepting_states \<A>" | (case4) "b \<notin> accepting_states \<A> \<and> a \<notin> accepting_states \<A>" by blast 
  thus ?case
  proof cases
    case case1
    hence "acc_sum \<A> beta' > acc_sum \<A> alpha" using gt0 beta Cons by force
    then obtain k where kprops: "k < length alpha \<and> beta' ! k \<in> accepting_states \<A> \<and> alpha ! k \<notin> accepting_states \<A> \<and> (\<forall> l < k . ((beta' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>)))" using Cons len by presburger
    hence K_lt: "Suc k < length (a # alpha)" by simp
    have nth_beta: "(b # beta') ! Suc k = beta' ! k" by simp
    have nth_alpha: "(a # alpha) ! Suc k = alpha ! k" by simp
    {
      fix l assume assm: "l < Suc k"
      hence "(((b # beta') ! l \<in> accepting_states \<A>) \<longleftrightarrow> ((a # alpha) ! l \<in> accepting_states \<A>))"
      proof (cases l)
        case 0 thus ?thesis using case1 by simp
      next
        case (Suc l')
        hence "l' < k" using assm by blast
        hence "((beta' ! l' \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l' \<in> accepting_states \<A>))" using kprops by blast
        thus ?thesis using Suc by simp
      qed
    }
    hence "\<forall> l < Suc k . (((b # beta') ! l \<in> accepting_states \<A>) \<longleftrightarrow> ((a # alpha) ! l \<in> accepting_states \<A>))" by blast
    thus ?thesis using beta kprops Cons nth_beta nth_alpha K_lt by metis
  next
    case case2 thus ?thesis using beta by auto
  next
    case case3
    hence bsum: "acc_sum \<A> (b # beta') = acc_sum \<A> beta'" by simp
    have asum: "acc_sum \<A> (a # alpha) = (2 ^ length alpha) + acc_sum \<A> alpha" using case3 by simp
    have "acc_sum \<A> beta' \<le> 2 ^ length beta' - 1" using acc_sum_bounded by blast
    hence "acc_sum \<A> beta' \<le> 2 ^ length alpha - 1"  using len by argo
    hence "acc_sum \<A> beta' < 2 ^ length alpha" using Nat.le_diff_conv2 by force
    hence "False" using bsum asum gt0 by force
    thus ?thesis by blast
  next
    case case4
    hence "acc_sum \<A> beta' > acc_sum \<A> alpha" using gt0 beta Cons by force
    then obtain k where kprops: "k < length alpha \<and> beta' ! k \<in> accepting_states \<A> \<and> alpha ! k \<notin> accepting_states \<A> \<and> (\<forall> l < k . ((beta' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>)))" using Cons len by presburger
    hence K_lt: "Suc k < length (a # alpha)" by simp
    have nth_beta: "(b # beta') ! Suc k = beta' ! k" by simp
    have nth_alpha: "(a # alpha) ! Suc k = alpha ! k" by simp
    {
      fix l assume assm: "l < Suc k"
      hence "(((b # beta') ! l \<in> accepting_states \<A>) \<longleftrightarrow> ((a # alpha) ! l \<in> accepting_states \<A>))"
      proof (cases l)
        case 0 thus ?thesis using case4 by simp
      next
        case (Suc l')
        hence "l' < k" using assm by blast
        hence "((beta' ! l' \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l' \<in> accepting_states \<A>))" using kprops by blast
        thus ?thesis using Suc by simp
      qed
    }
    hence "\<forall> l < Suc k . (((b # beta') ! l \<in> accepting_states \<A>) \<longleftrightarrow> ((a # alpha) ! l \<in> accepting_states \<A>))" by blast
    thus ?thesis using beta kprops Cons nth_beta nth_alpha K_lt by metis
  qed
qed

lemma acc_sum_append: "length alpha = length beta \<and> acc_sum \<A> beta > acc_sum \<A> alpha \<Longrightarrow> acc_sum \<A> (beta @ [b]) > acc_sum \<A> (alpha @ [a])"
proof (induction alpha arbitrary: beta)
  case Nil thus ?case by fastforce
next
  case (Cons a' alpha)
  hence not_empty: "beta \<noteq> []" by force
  then obtain beta' where beta: "beta = (beta ! 0) # beta'" using list_properties_not_empty by fast
  hence "length beta' = length beta - 1" using length_tl list.sel(3) by metis
  hence length: "length alpha = length beta'" using Cons by force
  hence len: "length (alpha @ [a]) = length (beta' @ [b])" by auto
  consider (case1) "(beta ! 0) \<in> accepting_states \<A> \<and> a' \<in> accepting_states \<A>" | (case2) "(beta ! 0) \<in> accepting_states \<A> \<and> a' \<notin> accepting_states \<A>" | (case3) "(beta ! 0) \<notin> accepting_states \<A> \<and> a' \<in> accepting_states \<A>" | (case4) "(beta ! 0) \<notin> accepting_states \<A> \<and> a' \<notin> accepting_states \<A>" by argo
  thus ?case
  proof cases
    case case1
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence acc_b: "acc_sum \<A> beta = 2 ^ length beta' + acc_sum \<A> beta'" using case1 by simp
    have "acc_sum \<A> (a' # alpha) = 2 ^ length alpha + acc_sum \<A> alpha" using case1 by simp
    hence "acc_sum \<A> beta' > acc_sum \<A> alpha" using acc_b Cons length by simp
    hence less: "acc_sum \<A> (alpha @ [a]) < acc_sum \<A> (beta' @ [b])" using Cons length by blast
    have "a' # (alpha @ [a]) = (a' # alpha) @ [a] \<and> (beta !0) # (beta' @ [b]) = ((beta ! 0) # beta') @ [b]" by auto
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = 2 ^ length (alpha @ [a]) + acc_sum \<A> (alpha @ [a]) \<and> acc_sum \<A> (((beta ! 0) # beta') @ [b]) = 2 ^ length (beta' @ [b]) + acc_sum \<A> (beta' @ [b])" using case1 by simp
    hence "acc_sum \<A> ((a' # alpha) @ [a]) < acc_sum \<A> (((beta ! 0) # beta') @ [b])" using less len by auto
    thus ?thesis using beta by simp
  next
    case case2
    have "a' # (alpha @ [a]) = (a' # alpha) @ [a] \<and> (beta !0) # (beta' @ [b]) = ((beta ! 0) # beta') @ [b]" by auto
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = acc_sum \<A> (alpha @ [a]) \<and> acc_sum \<A> (((beta ! 0) # beta') @ [b]) = 2 ^ length (beta' @ [b]) + acc_sum \<A> (beta' @ [b])" using case2 by auto
    hence "acc_sum \<A> ((a' # alpha) @ [a]) \<le> 2 ^ length (alpha @ [a]) - 1 \<and> acc_sum \<A> (((beta ! 0) # beta') @ [b]) \<ge> 2 ^ length (beta' @ [b])" using acc_sum_bounded le_add1 by metis
    hence less: "acc_sum \<A> ((a' # alpha) @ [a]) \<le> 2 ^ length (alpha @ [a]) - 1 \<and> acc_sum \<A> (beta @ [b]) \<ge> 2 ^ length (alpha @ [a])" using length beta by simp
    have "2 ^ length (alpha @ [a]) > (0 :: nat)" by auto
    thus ?thesis using less by linarith
  next
    case case3
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence "acc_sum \<A> beta = acc_sum \<A> beta'" using case3 by simp
    hence acc_b: "acc_sum \<A> beta \<le> 2 ^ length beta' - 1" using acc_sum_bounded by auto
    have "acc_sum \<A> (a' # alpha) = 2 ^ length alpha + acc_sum \<A> alpha" using case3 by simp
    hence "acc_sum \<A> beta \<le> 2 ^ length beta' - 1 \<and> acc_sum \<A> (a' # alpha) \<ge> 2 ^ length alpha" using acc_b le_add1 by metis
    hence less: "acc_sum \<A> beta \<le> 2 ^ length alpha - 1 \<and> acc_sum \<A> (a' # alpha) \<ge> 2 ^ length alpha" using length by argo
    have "2 ^ length alpha > (0 :: nat)" by auto
    hence "acc_sum \<A> (a' # alpha) > acc_sum \<A> beta" using less by linarith
    thus ?thesis using Cons by linarith
  next
    case case4
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence acc_b: "acc_sum \<A> beta = acc_sum \<A> beta'" using case4 by simp
    have "acc_sum \<A> (a' # alpha) = acc_sum \<A> alpha" using case4 by simp
    hence "acc_sum \<A> beta' > acc_sum \<A> alpha" using acc_b Cons length by simp
    hence less: "acc_sum \<A> (alpha @ [a]) < acc_sum \<A> (beta' @ [b])" using Cons length by blast
    have "a' # (alpha @ [a]) = (a' # alpha) @ [a] \<and> (beta !0) # (beta' @ [b]) = ((beta ! 0) # beta') @ [b]" by auto
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = acc_sum \<A> (alpha @ [a]) \<and> acc_sum \<A> (((beta ! 0) # beta') @ [b]) = acc_sum \<A> (beta' @ [b])" using case4 by simp
    hence "acc_sum \<A> ((a' # alpha) @ [a]) < acc_sum \<A> (((beta ! 0) # beta') @ [b])" using less len by auto
    thus ?thesis using beta by simp
  qed
qed

lemma acc_sum_append_equi_leq: "length alpha = length beta \<and> acc_sum \<A> beta = acc_sum \<A> alpha \<and> b \<in> accepting_states \<A> \<and> a \<notin> accepting_states \<A> \<Longrightarrow> acc_sum \<A> (beta @ [b]) > acc_sum \<A> (alpha @ [a])"
proof (induction alpha arbitrary: beta)
  case Nil thus ?case by auto
next
  case (Cons a' alpha)
  hence not_empty: "beta \<noteq> []" by force
  then obtain beta' where beta: "beta = (beta ! 0) # beta'" using list_properties_not_empty by fast
  hence "length beta' = length beta - 1" using length_tl list.sel(3) by metis
  hence length: "length alpha = length beta'" using Cons by force
  hence len: "length (alpha @ [a]) = length (beta' @ [b])" by auto
  consider (case1) "(beta ! 0) \<in> accepting_states \<A> \<and> a' \<in> accepting_states \<A>" | (case2) "(beta ! 0) \<in> accepting_states \<A> \<and> a' \<notin> accepting_states \<A>" | (case3) "(beta ! 0) \<notin> accepting_states \<A> \<and> a' \<in> accepting_states \<A>" | (case4) "(beta ! 0) \<notin> accepting_states \<A> \<and> a' \<notin> accepting_states \<A>" by argo
  thus ?case
  proof cases
    case case1
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence acc_b: "acc_sum \<A> beta = 2 ^ length beta' + acc_sum \<A> beta'" using case1 by simp
    have "acc_sum \<A> (a' # alpha) = 2 ^ length alpha + acc_sum \<A> alpha" using case1 by simp
    hence "acc_sum \<A> beta' = acc_sum \<A> alpha" using acc_b Cons length by simp
    hence less: "acc_sum \<A> (alpha @ [a]) < acc_sum \<A> (beta' @ [b])" using Cons length by blast
    have "a' # (alpha @ [a]) = (a' # alpha) @ [a] \<and> (beta !0) # (beta' @ [b]) = ((beta ! 0) # beta') @ [b]" by auto
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = 2 ^ length (alpha @ [a]) + acc_sum \<A> (alpha @ [a]) \<and> acc_sum \<A> (((beta ! 0) # beta') @ [b]) = 2 ^ length (beta' @ [b]) + acc_sum \<A> (beta' @ [b])" using case1 by simp
    hence "acc_sum \<A> ((a' # alpha) @ [a]) < acc_sum \<A> (((beta ! 0) # beta') @ [b])" using less len by auto
    thus ?thesis using beta by simp
  next
    case case2
    have "a' # (alpha @ [a]) = (a' # alpha) @ [a] \<and> (beta !0) # (beta' @ [b]) = ((beta ! 0) # beta') @ [b]" by auto
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = acc_sum \<A> (alpha @ [a]) \<and> acc_sum \<A> (((beta ! 0) # beta') @ [b]) = 2 ^ length (beta' @ [b]) + acc_sum \<A> (beta' @ [b])" using case2 by auto
    hence "acc_sum \<A> ((a' # alpha) @ [a]) \<le> 2 ^ length (alpha @ [a]) - 1 \<and> acc_sum \<A> (((beta ! 0) # beta') @ [b]) \<ge> 2 ^ length (beta' @ [b])" using acc_sum_bounded le_add1 by metis
    hence less: "acc_sum \<A> ((a' # alpha) @ [a]) \<le> 2 ^ length (alpha @ [a]) - 1 \<and> acc_sum \<A> (beta @ [b]) \<ge> 2 ^ length (alpha @ [a])" using length beta by simp
    have "2 ^ length (alpha @ [a]) > (0 :: nat)" by auto
    thus ?thesis using less by linarith
  next
    case case3
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence "acc_sum \<A> beta = acc_sum \<A> beta'" using case3 by simp
    hence acc_b: "acc_sum \<A> beta \<le> 2 ^ length beta' - 1" using acc_sum_bounded by auto
    have "acc_sum \<A> (a' # alpha) = 2 ^ length alpha + acc_sum \<A> alpha" using case3 by simp
    hence "acc_sum \<A> beta \<le> 2 ^ length beta' - 1 \<and> acc_sum \<A> (a' # alpha) \<ge> 2 ^ length alpha" using acc_b le_add1 by metis
    hence less: "acc_sum \<A> beta \<le> 2 ^ length alpha - 1 \<and> acc_sum \<A> (a' # alpha) \<ge> 2 ^ length alpha" using length by argo
    have "2 ^ length alpha > (0 :: nat)" by auto
    hence "acc_sum \<A> (a' # alpha) > acc_sum \<A> beta" using less by linarith
    thus ?thesis using Cons by linarith
  next
    case case4
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence acc_b: "acc_sum \<A> beta = acc_sum \<A> beta'" using case4 by simp
    have "acc_sum \<A> (a' # alpha) = acc_sum \<A> alpha" using case4 by simp
    hence "acc_sum \<A> beta' = acc_sum \<A> alpha" using acc_b Cons length by simp
    hence less: "acc_sum \<A> (alpha @ [a]) < acc_sum \<A> (beta' @ [b])" using Cons length by blast
    have "a' # (alpha @ [a]) = (a' # alpha) @ [a] \<and> (beta !0) # (beta' @ [b]) = ((beta ! 0) # beta') @ [b]" by auto
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = acc_sum \<A> (alpha @ [a]) \<and> acc_sum \<A> (((beta ! 0) # beta') @ [b]) = acc_sum \<A> (beta' @ [b])" using case4 by simp
    hence "acc_sum \<A> ((a' # alpha) @ [a]) < acc_sum \<A> (((beta ! 0) # beta') @ [b])" using less len by auto
    thus ?thesis using beta by simp
  qed
qed

lemma acc_sum_append_equi_in: "length alpha = length beta \<and> acc_sum \<A> beta = acc_sum \<A> alpha \<and> b \<in> accepting_states \<A> \<and> a \<in> accepting_states \<A> \<Longrightarrow> acc_sum \<A> (beta @ [b]) = acc_sum \<A> (alpha @ [a])"
proof (induction alpha arbitrary: beta)
  case Nil thus ?case by auto
next
  case (Cons a' alpha)
  hence not_empty: "beta \<noteq> []" by force
  then obtain beta' where beta: "beta = (beta ! 0) # beta'" using list_properties_not_empty by fast
  hence "length beta' = length beta - 1" using length_tl list.sel(3) by metis
  hence length: "length alpha = length beta'" using Cons by force
  hence len: "length (alpha @ [a]) = length (beta' @ [b])" by auto
  consider (case1) "(beta ! 0) \<in> accepting_states \<A> \<and> a' \<in> accepting_states \<A>" | (case2) "(beta ! 0) \<in> accepting_states \<A> \<and> a' \<notin> accepting_states \<A>" | (case3) "(beta ! 0) \<notin> accepting_states \<A> \<and> a' \<in> accepting_states \<A>" | (case4) "(beta ! 0) \<notin> accepting_states \<A> \<and> a' \<notin> accepting_states \<A>" by argo
  thus ?case
  proof cases
    case case1
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence acc_b: "acc_sum \<A> beta = 2 ^ length beta' + acc_sum \<A> beta'" using case1 by simp
    have "acc_sum \<A> (a' # alpha) = 2 ^ length alpha + acc_sum \<A> alpha" using case1 by simp
    hence "acc_sum \<A> beta' = acc_sum \<A> alpha" using acc_b Cons length by simp
    hence less: "acc_sum \<A> (alpha @ [a]) = acc_sum \<A> (beta' @ [b])" using Cons length by presburger
    have "a' # (alpha @ [a]) = (a' # alpha) @ [a] \<and> (beta !0) # (beta' @ [b]) = ((beta ! 0) # beta') @ [b]" by auto
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = 2 ^ length (alpha @ [a]) + acc_sum \<A> (alpha @ [a]) \<and> acc_sum \<A> (((beta ! 0) # beta') @ [b]) = 2 ^ length (beta' @ [b]) + acc_sum \<A> (beta' @ [b])" using case1 by simp
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = acc_sum \<A> (((beta ! 0) # beta') @ [b])" using less len by auto
    thus ?thesis using beta by simp
  next
    case case2
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence "acc_sum \<A> beta = 2 ^ length beta' + acc_sum \<A> beta'" using case2 by simp
    hence acc_b: "acc_sum \<A> beta \<ge> 2 ^ length beta'" using acc_sum_bounded by auto
    have "acc_sum \<A> (a' # alpha) = acc_sum \<A> alpha" using case2 by simp
    hence "acc_sum \<A> (a' # alpha) \<le> 2 ^ length alpha - 1" using acc_sum_bounded by auto
    hence "acc_sum \<A> beta \<ge> 2 ^ length beta' \<and> acc_sum \<A> (a' # alpha) \<le> 2 ^ length alpha - 1" using acc_b by metis
    hence less: "acc_sum \<A> beta \<ge> 2 ^ length alpha \<and> acc_sum \<A> (a' # alpha) \<le> 2 ^ length alpha - 1" using length by argo
    have "2 ^ length alpha > (0 :: nat)" by auto
    hence "acc_sum \<A> (a' # alpha) < acc_sum \<A> beta" using less by linarith
    thus ?thesis using Cons by linarith
  next
    case case3
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence "acc_sum \<A> beta = acc_sum \<A> beta'" using case3 by simp
    hence acc_b: "acc_sum \<A> beta \<le> 2 ^ length beta' - 1" using acc_sum_bounded by auto
    have "acc_sum \<A> (a' # alpha) = 2 ^ length alpha + acc_sum \<A> alpha" using case3 by simp
    hence "acc_sum \<A> beta \<le> 2 ^ length beta' - 1 \<and> acc_sum \<A> (a' # alpha) \<ge> 2 ^ length alpha" using acc_b le_add1 by metis
    hence less: "acc_sum \<A> beta \<le> 2 ^ length alpha - 1 \<and> acc_sum \<A> (a' # alpha) \<ge> 2 ^ length alpha" using length by argo
    have "2 ^ length alpha > (0 :: nat)" by auto
    hence "acc_sum \<A> (a' # alpha) > acc_sum \<A> beta" using less by linarith
    thus ?thesis using Cons by linarith
  next
    case case4
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence acc_b: "acc_sum \<A> beta = acc_sum \<A> beta'" using case4 by simp
    have "acc_sum \<A> (a' # alpha) = acc_sum \<A> alpha" using case4 by simp
    hence "acc_sum \<A> beta' = acc_sum \<A> alpha" using acc_b Cons length by simp
    hence less: "acc_sum \<A> (alpha @ [a]) = acc_sum \<A> (beta' @ [b])" using Cons length by presburger
    have "a' # (alpha @ [a]) = (a' # alpha) @ [a] \<and> (beta !0) # (beta' @ [b]) = ((beta ! 0) # beta') @ [b]" by auto
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = acc_sum \<A> (alpha @ [a]) \<and> acc_sum \<A> (((beta ! 0) # beta') @ [b]) = acc_sum \<A> (beta' @ [b])" using case4 by simp
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = acc_sum \<A> (((beta ! 0) # beta') @ [b])" using less len by auto
    thus ?thesis using beta by simp
  qed
qed

lemma acc_sum_append_equi_notin: "length alpha = length beta \<and> acc_sum \<A> beta = acc_sum \<A> alpha \<and> b \<notin> accepting_states \<A> \<and> a \<notin> accepting_states \<A> \<Longrightarrow> acc_sum \<A> (beta @ [b]) = acc_sum \<A> (alpha @ [a])"
proof (induction alpha arbitrary: beta)
  case Nil thus ?case by auto
next
  case (Cons a' alpha)
  hence not_empty: "beta \<noteq> []" by force
  then obtain beta' where beta: "beta = (beta ! 0) # beta'" using list_properties_not_empty by fast
  hence "length beta' = length beta - 1" using length_tl list.sel(3) by metis
  hence length: "length alpha = length beta'" using Cons by force
  hence len: "length (alpha @ [a]) = length (beta' @ [b])" by auto
  consider (case1) "(beta ! 0) \<in> accepting_states \<A> \<and> a' \<in> accepting_states \<A>" | (case2) "(beta ! 0) \<in> accepting_states \<A> \<and> a' \<notin> accepting_states \<A>" | (case3) "(beta ! 0) \<notin> accepting_states \<A> \<and> a' \<in> accepting_states \<A>" | (case4) "(beta ! 0) \<notin> accepting_states \<A> \<and> a' \<notin> accepting_states \<A>" by argo
  thus ?case
  proof cases
    case case1
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence acc_b: "acc_sum \<A> beta = 2 ^ length beta' + acc_sum \<A> beta'" using case1 by simp
    have "acc_sum \<A> (a' # alpha) = 2 ^ length alpha + acc_sum \<A> alpha" using case1 by simp
    hence "acc_sum \<A> beta' = acc_sum \<A> alpha" using acc_b Cons length by simp
    hence less: "acc_sum \<A> (alpha @ [a]) = acc_sum \<A> (beta' @ [b])" using Cons length by presburger
    have "a' # (alpha @ [a]) = (a' # alpha) @ [a] \<and> (beta !0) # (beta' @ [b]) = ((beta ! 0) # beta') @ [b]" by auto
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = 2 ^ length (alpha @ [a]) + acc_sum \<A> (alpha @ [a]) \<and> acc_sum \<A> (((beta ! 0) # beta') @ [b]) = 2 ^ length (beta' @ [b]) + acc_sum \<A> (beta' @ [b])" using case1 by simp
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = acc_sum \<A> (((beta ! 0) # beta') @ [b])" using less len by auto
    thus ?thesis using beta by simp
  next
    case case2
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence "acc_sum \<A> beta = 2 ^ length beta' + acc_sum \<A> beta'" using case2 by simp
    hence acc_b: "acc_sum \<A> beta \<ge> 2 ^ length beta'" using acc_sum_bounded by auto
    have "acc_sum \<A> (a' # alpha) = acc_sum \<A> alpha" using case2 by simp
    hence "acc_sum \<A> (a' # alpha) \<le> 2 ^ length alpha - 1" using acc_sum_bounded by auto
    hence "acc_sum \<A> beta \<ge> 2 ^ length beta' \<and> acc_sum \<A> (a' # alpha) \<le> 2 ^ length alpha - 1" using acc_b by metis
    hence less: "acc_sum \<A> beta \<ge> 2 ^ length alpha \<and> acc_sum \<A> (a' # alpha) \<le> 2 ^ length alpha - 1" using length by argo
    have "2 ^ length alpha > (0 :: nat)" by auto
    hence "acc_sum \<A> (a' # alpha) < acc_sum \<A> beta" using less by linarith
    thus ?thesis using Cons by linarith
  next
    case case3
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence "acc_sum \<A> beta = acc_sum \<A> beta'" using case3 by simp
    hence acc_b: "acc_sum \<A> beta \<le> 2 ^ length beta' - 1" using acc_sum_bounded by auto
    have "acc_sum \<A> (a' # alpha) = 2 ^ length alpha + acc_sum \<A> alpha" using case3 by simp
    hence "acc_sum \<A> beta \<le> 2 ^ length beta' - 1 \<and> acc_sum \<A> (a' # alpha) \<ge> 2 ^ length alpha" using acc_b le_add1 by metis
    hence less: "acc_sum \<A> beta \<le> 2 ^ length alpha - 1 \<and> acc_sum \<A> (a' # alpha) \<ge> 2 ^ length alpha" using length by argo
    have "2 ^ length alpha > (0 :: nat)" by auto
    hence "acc_sum \<A> (a' # alpha) > acc_sum \<A> beta" using less by linarith
    thus ?thesis using Cons by linarith
  next
    case case4
    have "acc_sum \<A> beta = acc_sum \<A> ((beta ! 0) # beta')" using beta by simp
    hence acc_b: "acc_sum \<A> beta = acc_sum \<A> beta'" using case4 by simp
    have "acc_sum \<A> (a' # alpha) = acc_sum \<A> alpha" using case4 by simp
    hence "acc_sum \<A> beta' = acc_sum \<A> alpha" using acc_b Cons length by simp
    hence less: "acc_sum \<A> (alpha @ [a]) = acc_sum \<A> (beta' @ [b])" using Cons length by presburger
    have "a' # (alpha @ [a]) = (a' # alpha) @ [a] \<and> (beta !0) # (beta' @ [b]) = ((beta ! 0) # beta') @ [b]" by auto
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = acc_sum \<A> (alpha @ [a]) \<and> acc_sum \<A> (((beta ! 0) # beta') @ [b]) = acc_sum \<A> (beta' @ [b])" using case4 by simp
    hence "acc_sum \<A> ((a' # alpha) @ [a]) = acc_sum \<A> (((beta ! 0) # beta') @ [b])" using less len by auto
    thus ?thesis using beta by simp
  qed
qed

lemma same_acc_states_equals_same_acc_sum: "length alpha = length beta \<and> (\<forall> l < length alpha . (beta ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>)) \<Longrightarrow> acc_sum \<A> beta = acc_sum \<A> alpha"
proof(induction alpha arbitrary: beta rule: rev_induct)
  case Nil thus ?case by force
next
  case (snoc a alpha)
  hence not_empty: "beta \<noteq> [] \<and> (alpha @ [a]) \<noteq> []" by auto
  then obtain beta' where beta: "beta = beta' @ [last beta]" using append_butlast_last_id by metis
  hence "length beta' = length beta - 1" using butlast_snoc length_butlast by metis
  hence length: "length alpha = length beta'" using snoc by force
  hence len: "length (alpha @ [a]) = length (beta' @ [last beta])" by auto
  {
    fix l assume assm: "l < length (alpha @ [a]) - 1"
    hence "l < length alpha \<and> l < length beta'" using length by simp
    hence "beta' ! l = (beta' @ [last beta]) ! l \<and> alpha ! l = (alpha @ [a]) ! l" using list_properties_length by fast
    hence "(beta' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>)" using snoc assm beta by force
  }
  hence "\<forall> l < length (alpha @ [a]) - 1 . (beta' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>)" by blast  
  hence "\<forall> l < length alpha . (beta' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>)" by simp
  hence equi: "acc_sum \<A> beta' = acc_sum \<A> alpha" using length snoc by blast
  have "(beta ! (length (alpha @ [a]) - 1) \<in> accepting_states \<A>) \<longleftrightarrow> ((alpha @ [a]) ! (length (alpha @ [a]) - 1) \<in> accepting_states \<A>)" using snoc by force
  hence "(last beta \<in> accepting_states \<A>) \<longleftrightarrow> (last (alpha @ [a]) \<in> accepting_states \<A>)" using not_empty len beta list_properties_not_empty by metis
  hence "(last beta \<in> accepting_states \<A>) \<longleftrightarrow> (a \<in> accepting_states \<A>)" by simp
  thus ?case using equi acc_sum_append_equi_in acc_sum_append_equi_notin length beta by metis
qed

lemma same_acc_states_equals_same_acc_sum_right: "length alpha = length beta \<and> acc_sum \<A> beta = acc_sum \<A> alpha \<Longrightarrow> (\<forall> l < length alpha . (beta ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>))"
proof(induction alpha arbitrary: beta rule: rev_induct)
  case Nil thus ?case by force
next
  case (snoc a alpha)
  hence not_empty: "beta \<noteq> [] \<and> (alpha @ [a]) \<noteq> []" by auto
  then obtain beta' where beta: "beta = beta' @ [last beta]" using append_butlast_last_id by metis
  hence "length beta' = length beta - 1" using butlast_snoc length_butlast by metis
  hence length: "length alpha = length beta'" using snoc by force
  hence len: "length (alpha @ [a]) = length (beta' @ [last beta])" by auto
  have acc_alpha: "acc_sum \<A> (alpha @ [a]) = 2 * acc_sum \<A> alpha + acc_sum \<A> [a]" using acc_sum_snoc by fast
  have "acc_sum \<A> (beta' @ [last beta]) = 2 * acc_sum \<A> beta' + acc_sum \<A> [last beta]" using acc_sum_snoc by fast
  hence a: "acc_sum \<A> alpha = acc_sum \<A> beta' \<and> acc_sum \<A> [a] = acc_sum \<A> [last beta]" using acc_sum_last_equal acc_alpha snoc beta by metis
  hence up_to_l: "\<forall> l < length alpha . (beta' ! l \<in> accepting_states \<A>) = (alpha ! l \<in> accepting_states \<A>)" using snoc length by metis
  consider (case1) "a \<in> accepting_states \<A>" | (case2) "a \<notin> accepting_states \<A>" by blast
  hence last: "(last beta \<in> accepting_states \<A>) \<longleftrightarrow> (a \<in> accepting_states \<A>)"
  proof cases
    case case1
    hence "acc_sum \<A> [a] = 1" by simp
    hence "acc_sum \<A> [last beta] = 1" using a by argo
    hence "last beta \<in> accepting_states \<A>" using acc_sum_append_equi_leq by fastforce
    thus ?thesis using case1 by blast
  next
    case case2
    hence "acc_sum \<A> [a] = 0" by simp
    hence "acc_sum \<A> [last beta] = 0" using a by argo
    hence "last beta \<notin> accepting_states \<A>" by force
    thus ?thesis using case2 by blast
  qed
  {
    fix l assume "l < length (alpha @ [a])"
    then consider (case1) "l < length (alpha @ [a]) - 1" | (case2) "l = length (alpha @ [a]) - 1" by fastforce
    hence "((beta' @ [last beta]) ! l \<in> accepting_states \<A>) = ((alpha @ [a]) ! l \<in> accepting_states \<A>)"
    proof cases
      case case1
      hence l_lt: "l < length alpha" by simp
      hence beta_l: "(beta' @ [last beta]) ! l = beta' ! l" using case1 nth_append length by metis
      have "(alpha @ [a]) ! l = alpha ! l" using case1 nth_append l_lt length by metis
      thus ?thesis using up_to_l l_lt beta_l by presburger
    next
      case case2
      hence l_eq: "l = length alpha"  by simp
      hence beta_l: "(beta' @ [last beta]) ! l = last beta" using case2 nth_append length by simp
      have "(alpha @ [a]) ! l = a" using case2  length l_eq by (simp add: nth_append)
      thus?thesis using last beta_l by simp
    qed
  }
  thus ?case using beta by simp
qed

lemma acc_sum_gt_ex_first_accept_diff_right: "length alpha = length beta \<and> (\<exists> k < length alpha . beta ! k \<in> accepting_states \<A> \<and> alpha ! k \<notin> accepting_states \<A> \<and> (\<forall> l < k . (beta ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>))) \<Longrightarrow> acc_sum \<A> beta > acc_sum \<A> alpha"
proof (induction alpha arbitrary: beta rule: rev_induct)
  case Nil thus ?case by auto
next
  case (snoc a alpha)
  hence not_empty: "beta \<noteq> []" by force
  then obtain beta' where beta: "beta = beta' @ [last beta]" using append_butlast_last_id by metis
  then obtain k where k: "k < length (alpha @ [a]) \<and> (beta' @ [last beta]) ! k \<in> accepting_states \<A> \<and> (alpha @ [a]) ! k \<notin> accepting_states \<A> \<and> (\<forall> l < k . ((beta' @ [last beta]) ! l \<in> accepting_states \<A>) \<longleftrightarrow> ((alpha @ [a]) ! l \<in> accepting_states \<A>))" using snoc by force
  have "length beta' = length beta - 1" using beta not_empty butlast_snoc length_butlast by metis
  hence length: "length alpha = length beta'" using snoc by force
  consider (case1) "k < length (alpha @ [a]) - 1" | (case2) "k = length (alpha @ [a]) - 1" using k by linarith
  thus ?case
  proof cases
    case case1
    hence less: "k < length alpha \<and> k < length beta'" using length by simp
    hence first: "k < length alpha \<and> beta' ! k \<in> accepting_states \<A> \<and> alpha ! k \<notin> accepting_states \<A>" using k list_properties_length by metis
    {
      fix l assume assm: "l < k"
      hence "l < length alpha \<and> l < length beta'" using less by auto
      hence "beta' ! l = (beta' @ [last beta]) ! l \<and> alpha ! l = (alpha @ [a]) ! l" using less list_properties_length by fast
      hence "(beta' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>)" using k assm by simp
    }
    hence "length alpha = length beta' \<and> (\<exists> k < length alpha . beta' ! k \<in> accepting_states \<A> \<and> alpha ! k \<notin> accepting_states \<A> \<and> (\<forall> l < k . (beta' ! l \<in> accepting_states \<A>) = (alpha ! l \<in> accepting_states \<A>)))" using length first by blast
    hence "acc_sum \<A> beta' > acc_sum \<A> alpha" using snoc by blast
    thus ?thesis using beta length acc_sum_append by metis
  next
    case case2
    have "beta \<noteq> [] \<and> (alpha @ [a]) \<noteq> []" using not_empty by auto
    hence kth: "beta ! k = last beta \<and> (alpha @ [a]) ! k = last (alpha @ [a])" using list_properties_not_empty case2 snoc by metis
    have "last (alpha @ [a]) = a" by simp
    hence states: "last beta \<in> accepting_states \<A> \<and> a \<notin> accepting_states \<A>" using k kth beta by argo    
    {
      fix l assume assm: "l < length (alpha @ [a]) - 1"
      hence "l < length alpha \<and> l < length beta'" using length by simp
      hence "beta' ! l = (beta' @ [last beta]) ! l \<and> alpha ! l = (alpha @ [a]) ! l" using list_properties_length by fast
      hence "(beta' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>)" using k assm case2 by simp
    }
    hence "\<forall> l < length (alpha @ [a]) - 1 . (beta' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>)" by blast
    hence "\<forall> l < length alpha . (beta' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>)" by simp
    hence "acc_sum \<A> beta' = acc_sum \<A> alpha" using length same_acc_states_equals_same_acc_sum by blast
    hence "acc_sum \<A> (beta' @ [last beta]) > acc_sum \<A> (alpha @ [a])" using states acc_sum_append_equi_leq length by fast
    thus ?thesis using beta by auto
  qed
qed

lemma acc_sum_gt_ex_first_accept_diff:
  assumes "length alpha = length beta"
  shows "acc_sum \<A> beta > acc_sum \<A> alpha \<longleftrightarrow> (\<exists> k < length alpha . beta ! k \<in> accepting_states \<A> \<and> alpha ! k \<notin> accepting_states \<A> \<and> (\<forall> l < k . (beta ! l \<in> accepting_states \<A>) \<longleftrightarrow> (alpha ! l \<in> accepting_states \<A>)))"
  using assms acc_sum_gt_ex_first_accept_diff_left acc_sum_gt_ex_first_accept_diff_right by blast

lemma pos_i_unbounded:
  assumes "omega_run_accepting omega_run \<A> omega_word"
  shows "\<forall> n . \<exists> i . pos_i i \<A> omega_run > n"
  using assms pos_i_ge_index Suc_le_eq by blast

lemma acc_index_ex_pos_i:
  assumes "omega_run_accepting omega_run \<A> omega_word" "omega_run n \<in> accepting_states \<A>"
  shows "\<exists> i . pos_i i \<A> omega_run = n"
proof -
  let ?P = "\<lambda>i . pos_i i \<A> omega_run \<ge> n"
  let ?i = "(LEAST i . ?P i)"
  have "\<exists> i . pos_i i \<A> omega_run > n" using assms pos_i_unbounded by blast
  hence "\<exists> i . ?P i"  using nat_less_le by auto
  hence Pi: "?P ?i" by (rule LeastI_ex)
  {
    fix m assume assm: "m < ?i" 
    have "\<not> ?P m"
    proof(rule ccontr)
      assume "\<not> \<not> ?P m"
      hence "?P m" by blast
      hence "(LEAST i . ?P i) \<le> m" by (rule Least_le)
      thus False using assm by simp
    qed
  }
  hence minP: "\<forall> m < ?i . \<not> ?P m" by blast
  show ?thesis
  proof (cases ?i)
    case 0
    have "n \<in> {t . omega_run t \<in> accepting_states \<A>}" using assms by blast
    hence "(LEAST t . omega_run t \<in> accepting_states \<A>) \<le> n" using Least_le by fastforce
    hence le_n: "pos_i 0 \<A> omega_run \<le> n" by auto
    have "pos_i 0 \<A> omega_run \<ge> n" using Pi 0 by argo
    hence "pos_i 0 \<A> omega_run = n" using le_n by force
    thus ?thesis by blast
  next
    case (Suc j)
    hence "\<not> ?P j" using minP by fastforce
    hence "pos_i j \<A> omega_run < n" by (simp add: not_le)
    hence "n \<in> {t . t > pos_i j \<A> omega_run \<and> omega_run t \<in> accepting_states \<A>}" using assms by auto
    hence "(LEAST t . t > pos_i j \<A> omega_run \<and> omega_run t \<in> accepting_states \<A>) \<le> n" using Least_le by(rule Set.CollectE) auto
    hence le_n: "pos_i (Suc j) \<A> omega_run \<le> n" by force
    have "pos_i (Suc j) \<A> omega_run \<ge> n" using Pi Suc by simp
    hence "pos_i (Suc j) \<A> omega_run = n" using le_n by force
    thus ?thesis by blast
  qed
qed

lemma chain_pos:
  assumes "omega_run_accepting omega_run \<A> omega_word"
  shows "i < j \<Longrightarrow> pos_i i \<A> omega_run < pos_i j \<A> omega_run"
proof (induction j arbitrary: i)
  case 0 thus ?case by blast
next
  case (Suc j)
  thus ?case
  proof (cases "i = j")
    case True thus ?thesis using assms pos_i_gt_and_acc by blast
  next
    case False
    hence pos_i: "pos_i i \<A> omega_run < pos_i j \<A> omega_run" using Suc by force
    have "pos_i j \<A> omega_run < pos_i (Suc j) \<A> omega_run" using assms pos_i_gt_and_acc by blast
    thus ?thesis using pos_i by force
  qed
qed

lemma lemma_3_1_10:
  assumes "auto_well_defined \<A>" "omega_word \<in> omega_language_auto \<A>"
    shows "\<exists> rho . omega_run_accepting rho \<A> omega_word \<and> omega_greedy_run rho \<A> omega_word"
proof -
  obtain rseq where rseq: "\<forall> i . rseq i \<in> R_tilde i \<A> omega_word \<and> rseq i \<prec> rseq (Suc i)" using lemma_3_1_9 assms by blast
  let ?rho = "rho_from_chain rseq"
  have rho_acc: "omega_run_accepting ?rho \<A> omega_word" using rho_accepting assms rseq by blast
  hence rho_in_Ri: "\<forall> i . ?rho \<in> R_i i \<A> omega_word" using rho_in_all_Ri rseq by blast
  have rho_omega_greedy: "omega_greedy_run ?rho \<A> omega_word"
  proof (rule ccontr)
    assume "\<not> omega_greedy_run ?rho \<A> omega_word"
    then obtain n where nbad: "(\<not> greedy_run (pre_omega_run ?rho n) \<A> (pre_omega_word omega_word n)) \<and> (\<forall> m < n . greedy_run (pre_omega_run ?rho m) \<A> (pre_omega_word omega_word m))" using not_omega_greedy_ex_min_bad_prefix rho_acc unfolding omega_run_accepting_def by blast
    let ?alpha = "pre_omega_run ?rho n"
    let ?v = "pre_omega_word omega_word n"
    have alpha: "run_well_defined ?alpha \<A> ?v" using rho_acc omega_run_implies_pre_run_well_def unfolding omega_run_accepting_def omega_run_well_defined_def run_well_defined_def by metis
    then obtain beta where beta: "run_well_defined beta \<A> ?v \<and> last beta = last ?alpha \<and> acc_sum \<A> beta > acc_sum \<A> ?alpha" using nbad unfolding greedy_run_def by blast
    hence len_equi: "length ?alpha = length beta" using alpha unfolding run_well_defined_def pseudo_run_well_defined_def by argo
    then obtain k where k: "k < length ?alpha \<and> beta ! k \<in> accepting_states \<A> \<and> ?alpha ! k \<notin> accepting_states \<A> \<and> (\<forall> l < k . (beta ! l \<in> accepting_states \<A>) \<longleftrightarrow> (?alpha ! l \<in> accepting_states \<A>))" using acc_sum_gt_ex_first_accept_diff beta by blast
    have ge0: "length ?alpha = Suc n" using pre_omega_run_length by blast
    hence n_equi: "length beta - 1 = n" using len_equi by auto
    hence "last beta = ?rho (length beta - 1)" using beta ge0 pre_omega_run_nth Zero_not_Suc last_conv_nth len_equi length_0_conv lessI by metis
    hence splice_acc: "omega_run_accepting (splice_omega_run beta ?rho) \<A> omega_word" using rho_acc n_equi beta splice_preserves_accepting by blast
    have "(splice_omega_run beta ?rho) k = beta ! k" using k len_equi unfolding splice_omega_run_def by auto
    hence rho'_k_acc: "(splice_omega_run beta ?rho) k \<in> accepting_states \<A>" using k by argo
    then obtain i where i: "pos_i i \<A> (splice_omega_run beta ?rho) = k" using splice_acc acc_index_ex_pos_i by blast
    have rho_k_not_acc: "?rho k \<notin> accepting_states \<A>" using k ge0 pre_omega_run_nth by metis
    {
      fix l assume assm: "l < k"
      hence equi_l: "(splice_omega_run beta ?rho) l = beta ! l" using k len_equi unfolding splice_omega_run_def by auto
      have "l < Suc n" using assm k ge0 by force
      hence equi_l': "?rho l = ?alpha ! l" using pre_omega_run_nth by metis
      have "(beta ! l \<in> accepting_states \<A>) \<longleftrightarrow> (?alpha ! l \<in> accepting_states \<A>)" using k assm by blast
      hence "((splice_omega_run beta ?rho) l \<in> accepting_states \<A>) \<longleftrightarrow> (?rho l \<in> accepting_states \<A>)" using equi_l equi_l' by simp
    }
    hence rho'_agree_lt_k: "\<forall> l < k . ((splice_omega_run beta ?rho) l \<in> accepting_states \<A>) \<longleftrightarrow> (?rho l \<in> accepting_states \<A>)" by blast
    have pos_lt_k_rho': "\<forall> j < i . pos_i j \<A> (splice_omega_run beta ?rho) < k" using splice_acc chain_pos i by blast
    {
      fix j assume "j < i"
      hence "pos_i j \<A> (splice_omega_run beta ?rho) = pos_i j \<A> ?rho"
      proof (induction j)
        case 0
        hence i_pos: "pos_i 0 \<A> (splice_omega_run beta ?rho) < k" using pos_lt_k_rho' by blast
        have "(splice_omega_run beta ?rho) (pos_i 0 \<A> (splice_omega_run beta ?rho)) \<in> accepting_states \<A>" using pos_i_gt_and_acc splice_acc 0 by blast
        hence "?rho (pos_i 0 \<A> (splice_omega_run beta ?rho)) \<in> accepting_states \<A>"  using rho'_agree_lt_k i_pos by blast
        hence rho_pos0: "?rho (pos_i 0 \<A> (splice_omega_run beta ?rho)) \<in> accepting_states \<A>" by blast
        {    
          fix m assume assm: "m < pos_i 0 \<A> (splice_omega_run beta ?rho)"
          hence mlt_k: "m < k" using i_pos by linarith
          have "(splice_omega_run beta ?rho) m \<notin> accepting_states \<A>" using assm not_less_Least by auto
          hence "?rho m \<notin> accepting_states \<A>" using rho'_agree_lt_k mlt_k by blast
        }
        hence "\<forall> m . m < pos_i 0 \<A> (splice_omega_run beta ?rho) \<longrightarrow> ?rho m \<notin> accepting_states \<A>" by blast
        hence "(LEAST n . ?rho n \<in> accepting_states \<A>) = pos_i 0 \<A> (splice_omega_run beta ?rho)" using leI rho_pos0 Least_equality by metis
        thus ?case by auto
      next
        case (Suc j)
        have rho'_posSuc_acc: "(splice_omega_run beta ?rho) (pos_i (Suc j) \<A> (splice_omega_run beta ?rho)) \<in> accepting_states \<A>" using pos_i_gt_and_acc splice_acc by blast
        have "pos_i (Suc j) \<A> (splice_omega_run beta ?rho) < k" using pos_lt_k_rho' Suc by blast
        hence rho_acc_at_rho'_posSuc: "?rho (pos_i (Suc j) \<A> (splice_omega_run beta ?rho)) \<in> accepting_states \<A>" using rho'_posSuc_acc rho'_agree_lt_k by blast
        have "\<forall> j . pos_i (Suc j) \<A> (splice_omega_run beta ?rho) > pos_i j \<A> (splice_omega_run beta ?rho)" using pos_i_gt_and_acc splice_acc by blast
        hence "pos_i (Suc j) \<A> (splice_omega_run beta ?rho) > pos_i j \<A> (splice_omega_run beta ?rho)" by blast
        hence rho_posj: "pos_i (Suc j) \<A> (splice_omega_run beta ?rho) > pos_i j \<A> ?rho \<and> ?rho (pos_i (Suc j) \<A> (splice_omega_run beta ?rho)) \<in> accepting_states \<A>"  using Suc rho_acc_at_rho'_posSuc by auto
        {
          fix m assume assm: "m < pos_i (Suc j) \<A> (splice_omega_run beta ?rho)"
          hence mlt_k: "m < k" using pos_lt_k_rho' Suc by force
          have rho'_m_not: "\<not> (m > pos_i j \<A> (splice_omega_run beta ?rho) \<and> (splice_omega_run beta ?rho) m \<in> accepting_states \<A>)" using assm not_less_Least by auto
          have "\<not> (m > pos_i j \<A> ?rho \<and> ?rho m \<in> accepting_states \<A>)"
          proof(rule ccontr)
            assume "\<not> \<not> (m > pos_i j \<A> ?rho \<and> ?rho m \<in> accepting_states \<A>)"
            hence "m > pos_i j \<A> ?rho \<and> ?rho m \<in> accepting_states \<A>" by blast
            hence contra: "m > pos_i j \<A> (splice_omega_run beta ?rho) \<and> ?rho m \<in> accepting_states \<A>" using Suc by simp
            hence "(splice_omega_run beta ?rho) m \<in> accepting_states \<A>" using rho'_agree_lt_k mlt_k by blast
            thus False using rho'_m_not contra by blast
          qed
        }
        hence "\<forall> m < pos_i (Suc j) \<A> (splice_omega_run beta ?rho) . \<not> (m > pos_i j \<A> ?rho \<and> ?rho m \<in> accepting_states \<A>)" by blast
        hence "(LEAST n . n > pos_i j \<A> ?rho \<and> ?rho n \<in> accepting_states \<A>) = pos_i (Suc j) \<A> (splice_omega_run beta ?rho)" using leI rho_posj Least_equality[of "\<lambda>n . n > pos_i j \<A> ?rho \<and> ?rho n \<in> accepting_states \<A>" "pos_i (Suc j) \<A> (splice_omega_run beta ?rho)"] by blast
        thus ?case by simp
      qed
    }
    hence pos_eq_lt_i: "\<forall> j < i . pos_i j \<A> (splice_omega_run beta ?rho) = pos_i j \<A> ?rho" by blast
    have "pos_i i \<A> ?rho > k"
    proof (cases i)
      case 0
      {    
        fix m assume assm: "m \<le> k"
        hence "?rho m \<notin> accepting_states \<A>"
        proof (cases "m < k")
          case True
          hence iff: "(splice_omega_run beta ?rho) m \<in> accepting_states \<A> \<longleftrightarrow> ?rho m \<in> accepting_states \<A>" using rho'_agree_lt_k by blast        
          have "\<forall>j . pos_i (Suc j) \<A> (splice_omega_run beta ?rho) > pos_i j \<A> (splice_omega_run beta ?rho)" using pos_i_gt_and_acc splice_acc by blast         
          hence "(splice_omega_run beta ?rho) m \<notin> accepting_states \<A>" using 0 i True not_less_Least by auto
          thus ?thesis using iff by blast
        next
          case False
          hence "m = k" using assm by auto
          thus ?thesis using rho_k_not_acc by blast
        qed
      }
      thus ?thesis using 0 leI pos_i_0_acc rho_acc by metis
    next
      case (Suc i')
      have "pos_i (Suc i') \<A> ?rho > k"
      proof (rule ccontr)
        assume assm: "\<not> pos_i (Suc i') \<A> ?rho > k"
        have lt_k: "pos_i (Suc i') \<A> ?rho < k"
        proof (cases "pos_i (Suc i') \<A> ?rho = k")
          case True thus ?thesis using rho_k_not_acc pos_i_gt_and_acc rho_acc by blast
        next
          case False thus ?thesis using assm by linarith
        qed
        hence "(splice_omega_run beta ?rho) (pos_i (Suc i') \<A> ?rho) \<in> accepting_states \<A>" using rho'_agree_lt_k pos_i_gt_and_acc rho_acc by blast
        hence "pos_i (Suc i') \<A> ?rho > pos_i i' \<A> (splice_omega_run beta ?rho) \<and> (splice_omega_run beta ?rho) (pos_i (Suc i') \<A> ?rho) \<in> accepting_states \<A>" using pos_i_gt_and_acc rho_acc pos_eq_lt_i Suc by auto      
        hence "(LEAST n . n > pos_i i' \<A> (splice_omega_run beta ?rho) \<and> (splice_omega_run beta ?rho) n \<in> accepting_states \<A>) \<le> pos_i (Suc i') \<A> ?rho" by (rule Least_le)
        hence "k \<le> pos_i (Suc i') \<A> ?rho" using i Suc by auto
        thus False using lt_k by linarith
      qed
      thus ?thesis using Suc by blast
    qed
    hence "pos_i i \<A> (splice_omega_run beta ?rho) < pos_i i \<A> ?rho" using i by blast
    hence "splice_omega_run beta ?rho \<in> R_i i \<A> omega_word \<and> ?rho \<in> R_i i \<A> omega_word \<Longrightarrow> pos_i i \<A> ?rho \<noteq> (LEAST n . n \<in> (image (pos_i i \<A>) (R_i i \<A> omega_word)))" using not_less_Least rev_image_eqI by metis
    hence "splice_omega_run beta ?rho \<in> R_i i \<A> omega_word \<and> ?rho \<in> R_i i \<A> omega_word \<Longrightarrow> ?rho \<notin>  R_i (Suc i) \<A> omega_word" by auto
    hence False: "splice_omega_run beta ?rho \<in> R_i i \<A> omega_word \<and> ?rho \<in> R_i i \<A> omega_word \<Longrightarrow> False" using rho_in_Ri by blast
    {
      fix t assume "t \<le> i"
      hence rho'_in_Ri_i: "(splice_omega_run beta ?rho) \<in> R_i t \<A> omega_word"
      proof (induction t)
        case 0 thus ?case using splice_acc R_i.simps unfolding all_acc_omega_runs_def by blast
      next
        case (Suc t)
        hence pos_eq_t: "pos_i t \<A> (splice_omega_run beta ?rho) = pos_i t \<A> ?rho" using pos_eq_lt_i Suc by auto
        have "?rho \<in> R_i (Suc t) \<A> omega_word" using rho_in_Ri by blast
        hence "pos_i t \<A> (splice_omega_run beta ?rho) = (LEAST n . n \<in> image (pos_i t \<A>) (R_i t \<A> omega_word))" using rho_in_Ri pos_eq_t by simp
        thus ?case using Suc by auto
      qed
    }
    hence "\<forall> t \<le> i . (splice_omega_run beta ?rho) \<in> R_i t \<A> omega_word" by blast
    thus False using rho_in_Ri False by blast
  qed
  thus ?thesis using rho_acc by blast
qed

corollary cor_3_1_11:
  assumes "auto_well_defined \<A>"
  shows "(\<exists> omega_run . omega_run_accepting omega_run \<A> omega_word) \<longleftrightarrow> (\<exists> omega_run . omega_run_accepting omega_run \<A> omega_word \<and> omega_greedy_run omega_run \<A> omega_word)"
  using assms lemma_3_1_10 unfolding omega_language_auto_def by blast

end