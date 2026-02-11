theory omega_automata_omega_power

imports Main omega_automata_concatenation

begin

text \<open>Author: Benno Thalmann, last update: 11.2.2026, Addition to masterarbeit_benno_thalmann\<close>

type_synonym 'a omega_word_list = "nat \<Rightarrow> 'a word"

fun prefix_concat :: "'a omega_word_list \<Rightarrow> nat \<Rightarrow> 'a word" where
  "prefix_concat inf_word_list 0 = []" |
  "prefix_concat inf_word_list (Suc n) = prefix_concat inf_word_list n @ inf_word_list n"

lemma length_prefix_concat:
  assumes "\<forall> n . inf_word_list n \<noteq> []"
  shows "length (prefix_concat inf_word_list n) = 0 \<Longrightarrow> n = 0"
  using assms by (induction n) auto

lemma length_prefix_concat_equi: 
  assumes "\<forall> i . length (inf_word_list i) = length (inf_run_list i)"
  shows "length (prefix_concat inf_word_list n) = length (prefix_concat inf_run_list n)"
  using assms by (induction n) auto

definition omega_power_language :: "'a language \<Rightarrow> 'a omega_language" where "omega_power_language L = {omega_word . \<exists> inf_word_list . (\<forall> n . inf_word_list n \<in> L \<and> inf_word_list n \<noteq> [] \<and> (\<forall> k . k < length (inf_word_list n) \<longrightarrow> omega_word (length (prefix_concat inf_word_list n) + k) = (inf_word_list n) ! k))}"

theorem omega_power_of_empty_lan:
  assumes "L = {}"
  shows "omega_power_language L = {}"
  using assms unfolding omega_power_language_def by fast

theorem omega_power_of_lan_with_empty_word:
  assumes "L = {[]}"
  shows "omega_power_language L = {}"
  using assms unfolding omega_power_language_def by fast

definition return_index_start :: "'a omega_word_list \<Rightarrow> nat \<Rightarrow> nat" where "return_index_start inf_word_list n = length (prefix_concat inf_word_list n)"

lemma return_index_start_strict_mono:
  assumes "\<forall> n . inf_word_list n \<noteq> []"
  shows "strict_mono (return_index_start inf_word_list)"
proof -
  {
    fix n
    have props: "return_index_start inf_word_list (Suc n) = return_index_start inf_word_list n + length (inf_word_list n)" unfolding return_index_start_def by simp
    have "length (inf_word_list n) > 0" using assms by simp
    hence "return_index_start inf_word_list n < return_index_start inf_word_list (Suc n)" using props by auto
  }
  thus ?thesis by (simp add: lift_Suc_mono_less strict_monoI)
qed

lemma return_index_start_ge:
  assumes "\<forall> n . inf_word_list n \<noteq> []"
  shows "return_index_start inf_word_list n \<ge> n"
  apply (induction n) apply simp using assms return_index_start_strict_mono strict_mono_imp_increasing unfolding return_index_start_def by metis

lemma exists_unique_block_index:
  assumes "\<forall> n . inf_word_list n \<noteq> []"
  shows "\<exists>! n . return_index_start inf_word_list n \<le> i \<and> i < return_index_start inf_word_list (Suc n)"
proof -
  have sm: "strict_mono (return_index_start inf_word_list)" using return_index_start_strict_mono assms by blast
  have "i < return_index_start inf_word_list (Suc i)" using assms return_index_start_ge Suc_le_lessD by blast
  hence exP: "\<exists> n . i < return_index_start inf_word_list (Suc n)" by blast
  let ?P = "\<lambda>n . i < return_index_start inf_word_list (Suc n)"
  let ?n = "LEAST n . ?P n"
  have high: "i < return_index_start inf_word_list (Suc ?n)" using exP LeastI_ex by metis
  have low: "return_index_start inf_word_list ?n \<le> i"
  proof (cases "?n = 0")
    case True thus ?thesis unfolding return_index_start_def by simp
  next
    case False thus ?thesis using Least_le[of ?P "?n - 1"] by force
  qed
  {
    fix m assume assm: "return_index_start inf_word_list m \<le> i \<and> i < return_index_start inf_word_list (Suc m)"
    have less: "m \<le> ?n" 
    proof (rule ccontr)
      assume "\<not> m \<le> ?n"
      hence "?n < m" by auto
      hence "return_index_start inf_word_list (Suc ?n) \<le> return_index_start inf_word_list m" using sm by (simp add: strict_mono_less_eq)
      hence "return_index_start inf_word_list (Suc ?n) \<le> i" using assm by simp
      thus False using high by simp
    qed
    have greater: "?n \<le> m"
    proof (rule ccontr)
      assume "\<not> ?n \<le> m"
      hence "m < ?n" by simp
      hence "return_index_start inf_word_list (Suc m) \<le> return_index_start inf_word_list ?n" using sm by (simp add: strict_mono_less_eq)
      hence "i < return_index_start inf_word_list ?n" using assm by simp
      thus False using low by simp
    qed
    hence "m = ?n" using less greater by simp
  }
  thus ?thesis using low high by blast
qed

lemma exists_unique_decomposition:
  assumes "\<forall> n . inf_word_list n \<noteq> []"
  shows "\<exists>! n . \<exists>! k . i = length (prefix_concat inf_word_list n) + k \<and> k < length (inf_word_list n)"
proof -
  have "\<exists>! n . return_index_start inf_word_list n \<le> i \<and> i < return_index_start inf_word_list (Suc n)" using exists_unique_block_index assms by blast
  then obtain n where n: "return_index_start inf_word_list n \<le> i \<and> i < return_index_start inf_word_list (Suc n) \<and> (\<forall> m . return_index_start inf_word_list m \<le> i \<and> i < return_index_start inf_word_list (Suc m) \<longrightarrow> m = n)" by auto
  let ?k = "i - return_index_start inf_word_list n"
  have eqi: "i = return_index_start inf_word_list n + ?k" using n by simp
  have "return_index_start inf_word_list (Suc n) =  return_index_start inf_word_list n + length (inf_word_list n)" unfolding return_index_start_def by simp
  hence less: "?k < length (inf_word_list n)" using n eqi by linarith
  show ?thesis
  proof (rule ex1I[of _ n])
    show "\<exists>! k. i = length (prefix_concat inf_word_list n) + k \<and> k < length (inf_word_list n)" using less eqi unfolding return_index_start_def by auto
  next
    fix m assume assm: "\<exists>! k . i = length (prefix_concat inf_word_list m) + k \<and> k < length (inf_word_list m)"
    then obtain k where k: "i = return_index_start inf_word_list m + k \<and> k < length (inf_word_list m)" unfolding return_index_start_def by blast
    hence less: "return_index_start inf_word_list m \<le> i" by auto
    have "i < return_index_start inf_word_list (Suc m)" using k unfolding return_index_start_def by simp
    thus "m = n" using less n by blast
  qed
qed

lemma exists_unique_decomposition_forall:
  assumes "\<forall> n . inf_word_list n \<noteq> []"
  shows "\<forall> i . \<exists>! n . \<exists>! k . i = length (prefix_concat inf_word_list n) + k \<and> k < length (inf_word_list n)"
 using assms by (intro allI) (rule exists_unique_decomposition)

proposition omega_power_well_defined:
  assumes "language_well_defined L \<Sigma>"
  shows "omega_language_well_defined (omega_power_language L) \<Sigma>"
proof - 
  {
    fix omega_word assume "omega_word \<in> omega_power_language L"
    then obtain inf_word_list where n: "\<forall> n . inf_word_list n \<in> L \<and> inf_word_list n \<noteq> [] \<and> (\<forall> k . k < length (inf_word_list n) \<longrightarrow> omega_word (length (prefix_concat inf_word_list n) + k) = (inf_word_list n) ! k)" unfolding omega_power_language_def by blast
    hence not_empty: "\<forall> n . inf_word_list n \<noteq> []" by blast
    {
      fix i
      obtain n k where i: "i = length (prefix_concat inf_word_list n) + k \<and> k < length (inf_word_list n)" using not_empty exists_unique_decomposition by metis
      have "inf_word_list n \<in> L \<and> inf_word_list n \<noteq> [] \<and> (\<forall> k . k < length (inf_word_list n) \<longrightarrow> omega_word (length (prefix_concat inf_word_list n) + k) = (inf_word_list n) ! k)" using n by simp
      hence "word_well_defined (inf_word_list n) \<Sigma>" using assms unfolding language_well_defined_def by simp
      hence "\<forall> k < length (inf_word_list n) . (inf_word_list n) ! k \<in> \<Sigma>" unfolding word_well_defined_def by force
      hence "\<forall> k < length (inf_word_list n) . omega_word (length (prefix_concat inf_word_list n) + k) \<in> \<Sigma>" using n by simp
      hence "omega_word i \<in> \<Sigma>" using i by simp
    }
    hence "omega_word_well_defined omega_word \<Sigma>" unfolding omega_word_well_defined_def by blast
  }
  thus ?thesis unfolding omega_language_well_defined_def by blast
qed

lemma omega_power_word_decompose:
  assumes "omega_word \<in> omega_power_language L"
  shows "\<exists> word omega_word_shift . word \<in> L \<and> omega_word_shift \<in> omega_power_language L \<and> omega_word = merge_lists_fun word omega_word_shift"
proof - 
  obtain inf_word_list where n: "\<forall> n . inf_word_list n \<in> L \<and> inf_word_list n \<noteq> [] \<and> (\<forall> k . k < length (inf_word_list n) \<longrightarrow> omega_word (length (prefix_concat inf_word_list n) + k) = (inf_word_list n) ! k)" using assms unfolding omega_power_language_def by blast
  then obtain word where word: "word = inf_word_list 0 \<and> word \<in> L \<and> word \<noteq> []" by auto
  hence equi: "\<forall> n < length word . word ! n = omega_word n" using n list.size plus_nat.add_0 prefix_concat.simps by force
  define new_inf_list where "new_inf_list = (\<lambda>n . inf_word_list (Suc n))"
  define omega_word_shift where "omega_word_shift =  (\<lambda>n . omega_word (n + length word))"
  have merge: "omega_word = merge_lists_fun word omega_word_shift" using equi unfolding merge_lists_fun_def omega_word_shift_def by auto
  {
    fix n
    have props: "new_inf_list n \<in> L \<and> new_inf_list n \<noteq> []" using n unfolding new_inf_list_def by simp
    {
      fix k assume "k < length (new_inf_list n)"
      hence "k < length (inf_word_list (Suc n))" unfolding new_inf_list_def by simp
      hence "omega_word (length (prefix_concat inf_word_list (Suc n)) + k) = (inf_word_list (Suc n)) ! k" using n by blast
      hence equi_new: "omega_word (length (prefix_concat inf_word_list (Suc n)) + k) = (new_inf_list n) ! k" unfolding new_inf_list_def by auto
      have "prefix_concat inf_word_list (Suc n) = inf_word_list 0 @ prefix_concat new_inf_list n" unfolding new_inf_list_def by (induction n) auto
      hence "length (prefix_concat inf_word_list (Suc n)) = length word + length (prefix_concat new_inf_list n)" using word by simp
      hence "omega_word_shift (length (prefix_concat new_inf_list n) + k) = omega_word (length (prefix_concat inf_word_list (Suc n)) + k)" using add.assoc add.commute unfolding omega_word_shift_def by metis 
      hence "omega_word_shift (length (prefix_concat new_inf_list n) + k) = (new_inf_list n) ! k" using equi_new by simp
    }
  hence "new_inf_list n \<in> L \<and> new_inf_list n \<noteq> [] \<and> (\<forall> k . k < length (new_inf_list n) \<longrightarrow> omega_word_shift (length (prefix_concat new_inf_list n) + k) = (new_inf_list n) ! k)" using props by blast
  }
  thus ?thesis using merge word unfolding omega_power_language_def by blast
qed

proposition omega_power_is_closed: "concatenation_omega_language L (omega_power_language L) = omega_power_language L"
proof -
  {
    fix omega_word assume "omega_word \<in> omega_power_language L"
    then obtain word omega_word_shift where "word \<in> L \<and> omega_word_shift \<in> omega_power_language L \<and> omega_word = merge_lists_fun word omega_word_shift" using omega_power_word_decompose by blast
    hence "omega_word \<in> concatenation_omega_language L (omega_power_language L)" unfolding concatenation_omega_language_def by blast
  }
  hence sub: "omega_power_language L \<subseteq> concatenation_omega_language L (omega_power_language L)" by auto
  {
    fix omega_word assume "omega_word \<in> concatenation_omega_language L (omega_power_language L)"
    then obtain word omega_word_shift where props: "omega_word = merge_lists_fun word omega_word_shift \<and> word \<in> L \<and> omega_word_shift \<in> omega_power_language L" unfolding concatenation_omega_language_def by blast
    hence "omega_word \<in> omega_power_language L"
    proof(cases word)
      case Nil thus ?thesis using props unfolding merge_lists_fun_def by simp
    next
      case (Cons a list)
      hence not_empty: "word \<noteq> []" by simp
      obtain inf_word_list where n: "\<forall> n . inf_word_list n \<in> L \<and> inf_word_list n \<noteq> [] \<and> (\<forall> k . k < length (inf_word_list n) \<longrightarrow> omega_word_shift (length (prefix_concat inf_word_list n) + k) = (inf_word_list n) ! k)" using props unfolding omega_power_language_def by blast 
      define new_inf_list where "new_inf_list = (\<lambda>n . if n = 0 then word else inf_word_list (n - 1))"
      have in_L: "\<forall> n . new_inf_list n \<in> L \<and> new_inf_list n \<noteq> []" using not_empty props n unfolding new_inf_list_def by simp
      {
        fix n k assume assm: "k < length (new_inf_list n)"
        hence "omega_word (length (prefix_concat new_inf_list n) + k) = (new_inf_list n) ! k"
        proof(cases n)
          case 0 thus ?thesis using props assm unfolding merge_lists_fun_def new_inf_list_def by auto
        next
          case (Suc nat)
          hence "k < length (inf_word_list nat)" using assm unfolding new_inf_list_def by simp
          hence "omega_word_shift (length (prefix_concat inf_word_list nat) + k) = (inf_word_list nat) ! k" using n by auto
          hence equi_new: "omega_word_shift (length (prefix_concat inf_word_list nat) + k) = (new_inf_list n) ! k" unfolding new_inf_list_def Suc by auto
          have "prefix_concat new_inf_list (Suc nat) = word @ prefix_concat inf_word_list nat" unfolding new_inf_list_def by (induction nat) auto
          hence "length (prefix_concat new_inf_list (Suc nat)) =  length word + length (prefix_concat inf_word_list nat)" by simp
          hence "omega_word (length (prefix_concat new_inf_list (Suc nat)) + k) = omega_word_shift (length (prefix_concat inf_word_list nat) + k)" using props unfolding merge_lists_fun_def by auto
          thus ?thesis using equi_new Suc by simp
        qed
      }
      thus ?thesis using in_L unfolding omega_power_language_def by blast
    qed
  }
  thus ?thesis using sub by blast
qed




text \<open>Automaton construction for omega_power_language language\<close>
definition omega_power_auto :: "('s, 'a) automaton \<Rightarrow> ('s + unit, 'a) automaton" where
  "omega_power_auto \<A> = Automaton
    (image Inl (states \<A>) \<union> {Inr()})
    (alphabet \<A>)
    (image (\<lambda>(s1, a, s2) . (Inl s1, a, Inl s2)) (transitions \<A>) \<union> {(Inr(), a, Inl s) | s a . (initial_state \<A>, a, s) \<in> transitions \<A>} \<union> {(Inr(), a, Inr()) | s a . (initial_state \<A>, a, s) \<in> transitions \<A> \<and> s \<in> accepting_states \<A>} \<union> {(Inl s1, a, Inr()) | s1 a s2 . (s1, a, s2) \<in> transitions \<A> \<and> s2 \<in> accepting_states \<A>})
    (Inr())
    ({Inr()})"

proposition omega_power_alphabet: "alphabet (omega_power_auto \<A>) = alphabet \<A>" unfolding omega_power_auto_def by auto

proposition omega_power_auto_well_defined:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (omega_power_auto \<A>)"
  using assms unfolding auto_well_defined_def omega_power_auto_def by auto

corollary language_well_def_omega_power_auto:
  assumes "auto_well_defined \<A>"
  shows "omega_language_well_defined (omega_language_auto (omega_power_auto \<A>)) (alphabet (omega_power_auto \<A>))"
  using omega_power_auto_well_defined assms automata_omega_language_are_well_defined by blast

proposition prun_omega_power_auto: "pseudo_run_well_defined prun \<A> s word \<Longrightarrow> pseudo_run_well_defined (map Inl prun) (omega_power_auto \<A>) (Inl s) word"
proof(induction word arbitrary: prun rule: rev_induct)
  case Nil thus ?case unfolding omega_power_auto_def pseudo_run_well_defined_def by force
next
  case (snoc a word)
  hence "prun \<noteq> []" unfolding pseudo_run_well_defined_def by force
  then obtain prun' where prun': "prun = prun' @ [last prun]" using append_butlast_last_id by metis
  hence "pseudo_run_well_defined prun' \<A> s word \<and> (last prun', a, last prun) \<in> transitions \<A>" using prun_well_defined_extension_snoc snoc by metis
  hence "pseudo_run_well_defined (map Inl prun') (omega_power_auto \<A>) (Inl s) word \<and> (last prun', a, last prun) \<in> transitions \<A>" using snoc by blast
  hence prun: "pseudo_run_well_defined (map Inl prun') (omega_power_auto \<A>) (Inl s) word \<and> (Inl (last prun'), a, Inl (last prun)) \<in> transitions (omega_power_auto \<A>)" unfolding omega_power_auto_def by force
  hence "map Inl prun' \<noteq> []" unfolding pseudo_run_well_defined_def by force
  hence "last (map Inl prun') = Inl (last prun')" using last_map by blast
  hence step: "pseudo_run_well_defined ((map Inl prun') @ [Inl (last prun)]) (omega_power_auto \<A>) (Inl s) (word @ [a])" using prun_well_defined_extension_snoc prun by metis
  have "((map Inl prun') @ [Inl (last prun)]) = map Inl (prun' @ [last prun])" by auto
  hence "((map Inl prun') @ [Inl (last prun)]) = map Inl prun" using prun' by auto
  thus ?case using step by metis
qed

lemma run_well_defined_omega_power_auto:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word"
  shows "run_well_defined (run_transformation run) (omega_power_auto \<A>) word"
proof(cases word)
  case Nil
  hence "length run = 1 \<and> run ! 0 = initial_state \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence "run = [initial_state \<A>]" by (simp add: list_with_one_element)
  hence "run_transformation run = [Inr()]" unfolding run_transformation_def by simp
  hence props: "length (run_transformation run) = 1 \<and> run_transformation run ! 0 = initial_state (omega_power_auto \<A>)" unfolding omega_power_auto_def by simp
  have "auto_well_defined (omega_power_auto \<A>)" using assms omega_power_auto_well_defined by auto
  hence "initial_state (omega_power_auto \<A>) \<in> states (omega_power_auto \<A>)" unfolding auto_well_defined_def by blast
  thus ?thesis using Nil props unfolding run_well_defined_def pseudo_run_well_defined_def by simp
next
  case (Cons a list)
  let ?\<A> = "omega_power_auto \<A>"
  have well_def: "auto_well_defined ?\<A>" using assms omega_power_auto_well_defined by auto
  have "word \<noteq> []" using Cons by blast
  hence len: "run \<noteq> [] \<and> length run > 1 \<and> run ! 0 = initial_state \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "run = (initial_state \<A>) # tl run" using list_properties_not_empty by metis
  hence "pseudo_run_well_defined ((initial_state \<A>) # tl run) \<A> (initial_state \<A>) (a # list)" using assms Cons unfolding run_well_defined_def by simp
  hence "pseudo_run_well_defined (tl run) \<A> ((tl run) ! 0) list \<and> (initial_state \<A>, a, (tl run) ! 0) \<in> transitions \<A>" using assms prun_well_defined_cons by fast  
  hence prun: "pseudo_run_well_defined (map Inl (tl run)) ?\<A> (Inl ((tl run) ! 0)) list \<and> (Inr(), a, Inl ((tl run) ! 0)) \<in> transitions ?\<A>" using prun_omega_power_auto unfolding omega_power_auto_def by fastforce
  have "Inl ((tl run) ! 0) = (map Inl (tl run)) ! 0" using len by simp
  hence "pseudo_run_well_defined (Inr() # (map Inl (tl run))) ?\<A> (Inr()) (a # list)" using well_def prun_well_defined_induction_cons prun by fast
  hence run: "pseudo_run_well_defined (run_transformation run) ?\<A> (Inr()) word" using Cons unfolding run_transformation_def by blast  
  have "Inr() = initial_state ?\<A> \<and> Inr() \<in> states ?\<A>" using well_def unfolding omega_power_auto_def auto_well_defined_def by force
  thus ?thesis using run unfolding run_well_defined_def by auto
qed

proposition run_accepting_omega_power_auto:
  assumes "auto_well_defined \<A>" "run_accepting run \<A> word"
  shows "run_accepting (butlast (run_transformation run) @ [Inr()]) (omega_power_auto \<A>) word"
proof(cases word)
  case Nil
  hence "length run = 1" using assms unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by auto
  hence "(butlast (run_transformation run) @ [Inr()]) = [Inr()]" using tl_Nil tl_empty unfolding run_transformation_def by auto
  hence props: "length (butlast (run_transformation run) @ [Inr()]) = 1 \<and> (butlast (run_transformation run) @ [Inr()]) ! 0 = initial_state (omega_power_auto \<A>) \<and> last (butlast (run_transformation run) @ [Inr()]) \<in> accepting_states (omega_power_auto \<A>)" unfolding omega_power_auto_def by simp
  have "auto_well_defined (omega_power_auto \<A>)" using assms omega_power_auto_well_defined by auto
  hence "initial_state (omega_power_auto \<A>) \<in> states (omega_power_auto \<A>)" unfolding auto_well_defined_def by blast
  thus ?thesis using Nil props unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by simp
next
  case (Cons a list)
  let ?\<A> = "omega_power_auto \<A>"
  have well_def: "auto_well_defined ?\<A>" using assms omega_power_auto_well_defined by auto
  have props: "run_well_defined run \<A> word \<and> last run \<in> accepting_states \<A>" using assms unfolding run_accepting_def by blast
  hence not_empty: "run ! 0 = initial_state \<A> \<and> word \<noteq> [] \<and> run \<noteq> [] \<and> length run > 1" using Cons unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  then consider (case1) "length run = 2" | (case2) "length run > 2" by linarith
  thus ?thesis
  proof cases
    case case1
    hence run: "run ! 0 = initial_state \<A> \<and> run ! 1 = last run" using not_empty props list_properties_not_empty by force
    hence "run = [initial_state \<A>, last run]" using case1 list_with_two_elements by metis
    hence "run_transformation run = [Inr(), Inl (last run)]" using list.sel(3) list.simps(8) list.simps(9) unfolding run_transformation_def by metis
    hence equi: "(butlast (run_transformation run) @ [Inr()]) = [Inr(), Inr()]" by simp
    have "(initial_state \<A>, word ! 0, last run) \<in> transitions \<A> \<and> last run \<in> accepting_states \<A>" using run props case1 unfolding run_well_defined_def pseudo_run_well_defined_def by force
    hence trans: "(Inr(), word ! 0, Inr()) \<in> transitions ?\<A>" unfolding omega_power_auto_def by auto
    have len: "length (butlast (run_transformation run) @ [Inr()]) = 2" using equi by simp
    have "length word + 1 = length run" using props unfolding run_well_defined_def pseudo_run_well_defined_def by auto
    hence length: "length word + 1 = length (butlast (run_transformation run) @ [Inr()])" using case1 len by argo
    have "Inr() = initial_state ?\<A> \<and> initial_state ?\<A> \<in> states ?\<A>" using well_def unfolding omega_power_auto_def auto_well_defined_def by force
    thus ?thesis using equi trans case1 length unfolding pseudo_run_well_defined_def run_well_defined_def run_accepting_def omega_power_auto_def by auto
  next
    case case2
    obtain b where b: "run = butlast run @ [last run] \<and> word = (butlast word) @ [b]" using not_empty append_butlast_last_id by metis
    hence "run_well_defined (butlast run @ [last run]) \<A> ((butlast word) @ [b])" using props by simp
    hence "run_well_defined (butlast run) \<A> (butlast word) \<and> (last (butlast run), b, last run) \<in> transitions \<A>" using prun_well_defined_snoc unfolding run_well_defined_def by fast
    hence run: "run_well_defined (run_transformation (butlast run)) ?\<A> (butlast word) \<and> (Inl (last (butlast run)), b, Inr()) \<in> transitions ?\<A>" using props assms run_well_defined_omega_power_auto unfolding omega_power_auto_def by auto
    have "length (butlast run) > 1" using case2 by force
    hence equi: "last (run_transformation (butlast run)) = Inl (last (butlast run))" using last.simps last_map last_tl map_is_Nil_conv tl_more_elements unfolding run_transformation_def by metis
    hence almost: "run_well_defined (run_transformation (butlast run) @ [Inr()]) ?\<A> (butlast word @ [b])" using run prun_well_defined_induction_snoc unfolding run_well_defined_def by metis
    have "run_transformation (butlast run) = butlast (run_transformation run)" using equi map_butlast unfolding run_transformation_def by(induction run) auto
    hence "run_well_defined (butlast (run_transformation run) @ [Inr()]) ?\<A> word" using almost b by simp
    thus ?thesis unfolding run_accepting_def omega_power_auto_def by force
  qed
qed

corollary originial_language_in_lang_omega_power_auto:
  assumes "auto_well_defined \<A>"
  shows "language_auto \<A> \<subseteq> language_auto (omega_power_auto \<A>)"
  using assms run_accepting_omega_power_auto unfolding language_auto_def by blast

corollary omega_power_lang_sub_omega_power_auto:
  assumes "auto_well_defined \<A>"
  shows "omega_power_language (language_auto \<A>) \<subseteq> omega_power_language (language_auto (omega_power_auto \<A>))"
  using assms originial_language_in_lang_omega_power_auto unfolding omega_power_language_def by blast

type_synonym 's omega_run_list = "nat \<Rightarrow> 's run"

definition omega_run_from_blocks :: "'s omega_run_list \<Rightarrow> 's omega_run" where "omega_run_from_blocks inf_run_list i = (THE s . \<exists> n k . i = length (prefix_concat inf_run_list n) + k \<and> k < length (inf_run_list n) \<and> s = (inf_run_list n) ! k)"

theorem omega_power_omega_power_auto_in_omega_lang:
  assumes "auto_well_defined \<A>"
  shows "omega_power_language (language_auto (omega_power_auto \<A>)) \<subseteq> omega_language_auto (omega_power_auto \<A>)"
proof - 
  let ?\<A> = "omega_power_auto \<A>"
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
    have "auto_well_defined ?\<A>" using assms omega_power_auto_well_defined by blast
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
        have last: "last ?run_n = Inr()" using run_acc unfolding run_accepting_def omega_power_auto_def by simp
        have "length (butlast ?run_n) > 0" using inf_run_list_n not_empty by force
        hence ge1: "length ?run_n > 1" using length_butlast by simp
        hence "?run_n \<noteq> []" by force
        hence last_inr: "?run_n ! (length ?run_n - 1) = Inr()" using list_properties_not_empty last by fastforce
        have k_len: "k = length ?run_n - 2" using kend unfolding inf_run_list_n by force
        hence equi_k: "(inf_run_list n) ! k = ?run_n ! (length ?run_n - 2)" using inf_run_list_n kless by (simp add: nth_butlast)
        have "length ?run_n - 1 = length ?run_n - 2 + 1" using ge1 simple_math by force
        hence "(?run_n ! (length ?run_n - 2), (inf_word_list n) ! (length ?run_n - 2), ?run_n ! (length ?run_n - 1)) \<in> transitions ?\<A>" using prun less_add_one by force
        hence trans: "((inf_run_list n) ! k, (inf_word_list n) ! k, Inr()) \<in> transitions ?\<A>" using k_len equi_k last_inr by argo
        have "run_accepting (SOME run. run_accepting run ?\<A> (inf_word_list (n + 1)) \<and> butlast run \<noteq> []) ?\<A> (inf_word_list (n + 1))" using tfl_some existence by (metis (mono_tags, lifting))
        hence "(SOME run. run_accepting run ?\<A> (inf_word_list (n + 1)) \<and> butlast run \<noteq> []) ! 0 = initial_state ?\<A>" unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by blast
        hence "(inf_run_list (n + 1)) ! 0 = initial_state ?\<A>" using Eps_cong length_greater_0_conv not_empty nth_butlast unfolding inf_run_list_def by (metis (no_types, lifting))
        hence sucn_inr: "(inf_run_list (n + 1)) ! 0 = Inr()" unfolding omega_power_auto_def by auto
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
        hence "omega_run (i + 1) = Inr()" using sucn_inr by simp
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
      hence "omega_run ?i \<in> accepting_states ?\<A>" unfolding omega_power_auto_def by force
      hence "\<exists> N > l . omega_run N \<in> accepting_states ?\<A>" using m by blast 
    }
    hence "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states ?\<A>" by argo
    hence "omega_run_accepting omega_run ?\<A> omega_word" using init step unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
    hence "omega_word \<in> omega_language_auto ?\<A>" unfolding omega_language_auto_def by blast
  }
  thus ?thesis by blast
qed

corollary omega_power_in_omega_lang_power_auto:
  assumes "auto_well_defined \<A>"
  shows "omega_power_language (language_auto \<A>) \<subseteq> omega_language_auto (omega_power_auto \<A>)"
  using assms omega_power_lang_sub_omega_power_auto omega_power_omega_power_auto_in_omega_lang by blast

lemma existence_of_run_on_original_auto:
  assumes "auto_well_defined \<A>"
  shows "length run > 1 \<and> run_well_defined run (omega_power_auto \<A>) word \<and> (\<forall> i < length run . i \<noteq> 0 \<longrightarrow> run ! i \<noteq> Inr()) \<Longrightarrow> \<exists> run_inl . run_well_defined run_inl \<A> word \<and> Inl (last run_inl) = last run"
proof(induction word arbitrary: run rule: rev_induct)
  case Nil thus ?case unfolding run_well_defined_def pseudo_run_well_defined_def by force
next
  case (snoc a word)
  then consider (case1) "length run = 2" | (case2) "length run > 2" by linarith
  thus ?case
  proof cases
    case case1
    have init_is_state: "initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
    have props: "length run = length (word @ [a]) + 1 \<and> run ! 0 = initial_state (omega_power_auto \<A>) \<and> (\<forall> i < length run - 1 . (run ! i, (word @ [a]) ! i, run ! (i + 1)) \<in> transitions (omega_power_auto \<A>))" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by blast
    hence "run \<noteq> [] \<and> run ! 0 = Inr()" unfolding omega_power_auto_def by force
    hence equi: "run ! 0 = Inr() \<and> run ! 1 = last run" using case1 list_properties_not_empty by fastforce
    hence run: "run = [Inr(), last run]" using case1 list_with_two_elements by metis
    have "length (word @ [a]) = 1 \<and> (run ! 0, (word @ [a]) ! 0, run ! 1) \<in> transitions (omega_power_auto \<A>)" using case1 props by force
    hence trans: "word @ [a] = [a] \<and> (Inr(), a, last run) \<in> transitions (omega_power_auto \<A>)" using equi by force
    have "last run \<noteq> Inr()" using snoc equi by force
    then obtain s where s: "Inl s = last run" using unique_existence by blast
    hence "(initial_state \<A>, a, s) \<in> transitions \<A>" using trans unfolding omega_power_auto_def by auto
    hence "run_well_defined [initial_state \<A>, s] \<A> (word @ [a])" using init_is_state trans unfolding run_well_defined_def pseudo_run_well_defined_def by auto
    thus ?thesis using s by auto
  next
    case case2
    have not_empty: "run \<noteq> []" using snoc unfolding pseudo_run_well_defined_def run_well_defined_def by force
    then obtain run' where run: "run = run' @ [last run]" using append_butlast_last_id by metis
    hence "run_well_defined (run' @ [last run]) (omega_power_auto \<A>) (word @ [a])" using snoc by argo
    hence props: "run_well_defined run' (omega_power_auto \<A>) word \<and> (last run', a, last run) \<in> transitions (omega_power_auto \<A>)" using prun_well_defined_snoc unfolding run_well_defined_def by fast
    have len: "length run' > 1" using case2 run Suc_1 Suc_less_eq length_append_singleton by metis
    have "\<forall> i < length run' . i \<noteq> 0 \<longrightarrow> run' ! i \<noteq> Inr()" using run snoc length_append list_properties_length trans_less_add1 by metis
    then obtain run_inl where run_inl: "run_well_defined run_inl \<A> word \<and> Inl (last run_inl) = last run'" using snoc props len by blast
    have "last run = run ! (length run - 1)" using not_empty list_properties_not_empty by metis
    hence "last run \<noteq> Inr()" using snoc by auto
    then obtain s where s: "Inl s = last run" using unique_existence by blast
    hence "(last run_inl, a, s) \<in> transitions \<A>" using run_inl props unfolding omega_power_auto_def by force
    hence "run_well_defined (run_inl @ [s]) \<A> (word @ [a])" using run_inl prun_well_defined_induction_snoc unfolding run_well_defined_def by fast
    thus ?thesis using s by force
  qed
qed

lemma existence_of_accepting_run_on_original_auto:
  assumes "auto_well_defined \<A>" "run_accepting run (omega_power_auto \<A>) word" "length run > 2" "\<forall> i < length run . i \<noteq> 0 \<and> i \<noteq> length run - 1 \<longrightarrow> run ! i \<noteq> Inr()"
  shows "\<exists> run_inl . run_accepting run_inl \<A> word"
proof -
  have props: "run_well_defined run (omega_power_auto \<A>) word \<and> last run \<in> accepting_states (omega_power_auto \<A>)" using assms unfolding run_accepting_def by blast
  hence not_empty: "run \<noteq> [] \<and> last run = Inr()" using assms unfolding omega_power_auto_def by force
  then obtain run' where run: "run = run' @ [Inr()]" using append_butlast_last_id by metis
  have "word \<noteq> []" using props assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain word' where word: "word = word' @ [last word]" using append_butlast_last_id by metis
  hence run': "run_well_defined run' (omega_power_auto \<A>) word' \<and> (last run', last word, Inr()) \<in> transitions (omega_power_auto \<A>)" using props prun_well_defined_snoc run unfolding run_well_defined_def by metis
  have len: "length run' > 1" using assms run by simp
  have not_inr: "\<forall> i < length run' . i \<noteq> 0 \<longrightarrow> run' ! i \<noteq> Inr()" using assms run butlast_snoc length_append length_butlast list_properties_length nat_neq_iff trans_less_add1 by metis
  have "\<exists> run_inl . run_well_defined run_inl \<A> word' \<and> Inl (last run_inl) = last run'" using not_inr run' len assms existence_of_run_on_original_auto by blast
  then obtain run_inl where run_inl: "run_well_defined run_inl \<A> word' \<and> Inl (last run_inl) = last run'" by blast
  then obtain s2 where "(last run_inl, last word, s2) \<in> transitions \<A> \<and> s2 \<in> accepting_states \<A>" using run' unfolding omega_power_auto_def by auto
  hence "run_well_defined (run_inl @ [s2]) \<A> (word' @ [last word]) \<and> s2 \<in> accepting_states \<A>" using run_inl prun_well_defined_induction_snoc unfolding run_well_defined_def by fast
  hence "run_accepting (run_inl @ [s2]) \<A> word" using word unfolding run_accepting_def by auto
  thus ?thesis by blast
qed

lemma existence_of_accepting_run_on_original_auto_length2:
  assumes "auto_well_defined \<A>" "run_accepting run (omega_power_auto \<A>) word" "length run = 2"
  shows "\<exists> run_inl . run_accepting run_inl \<A> word"
proof - 
  have "run ! 0 = Inr() \<and> last run = Inr()" using assms unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def omega_power_auto_def by force
  hence "run = [Inr(), Inr()]" using assms list_with_two_elements by force
  hence word: "(Inr(), word ! 0, Inr()) \<in> transitions (omega_power_auto \<A>) \<and> length word = 1" using assms unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by auto
  then obtain s where "(initial_state \<A>, word ! 0, s) \<in> transitions \<A> \<and> s \<in> accepting_states \<A>" unfolding omega_power_auto_def by auto
  hence trans: "(\<forall> i < length [initial_state \<A>, s] - 1 . ([initial_state \<A>, s] ! i, word ! i, [initial_state \<A>, s] ! (i + 1)) \<in> transitions \<A>) \<and> s \<in> accepting_states \<A>" by auto
  have length: "length [initial_state \<A>, s] = length word + 1 \<and> [initial_state \<A>, s] ! 0 = initial_state \<A>" using word by auto
  have "last [initial_state \<A>, s] \<in> accepting_states \<A> \<and> initial_state \<A> \<in> states \<A>" using assms trans unfolding auto_well_defined_def by simp
  hence "run_accepting [initial_state \<A>, s] \<A> word" using length trans unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by blast
  thus ?thesis by blast
qed

fun cut_omega_run :: "('s + unit) omega_run \<Rightarrow> nat \<Rightarrow> nat" where
  "cut_omega_run omega_run 0 = 0" |
  "cut_omega_run omega_run (Suc n) = (LEAST i . i > cut_omega_run omega_run n \<and> omega_run i = Inr())"

lemma cut_hits_Inr:
  assumes "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (omega_power_auto \<A>)"
  shows "omega_run (cut_omega_run omega_run (Suc j)) = Inr() \<and> cut_omega_run omega_run (Suc j) > cut_omega_run omega_run j"
proof - 
  have existence: "\<forall> n . \<exists> N > n . omega_run N = Inr()" using assms unfolding omega_power_auto_def by simp
  {
    fix j
    obtain n where n: "cut_omega_run omega_run j = n" by simp
    have equi: "cut_omega_run omega_run (Suc j) = (LEAST i . i > n \<and> omega_run i = Inr())" using n by simp
    hence mono: "cut_omega_run omega_run (Suc j) > cut_omega_run omega_run j" using n existence LeastI_ex by (metis (mono_tags, lifting))
    have "omega_run (cut_omega_run omega_run (Suc j)) = Inr()" using equi existence LeastI_ex by (metis (mono_tags, lifting))
    hence "omega_run (cut_omega_run omega_run (Suc j)) = Inr() \<and> cut_omega_run omega_run (Suc j) > cut_omega_run omega_run j" using mono by blast
  }
  thus ?thesis by blast
qed

corollary omega_run_cut_j_is_Inr:
  assumes "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (omega_power_auto \<A>)" "omega_run 0 = Inr()"
  shows "omega_run (cut_omega_run omega_run j) = Inr()"
proof(cases j)
  case 0 thus ?thesis using assms by simp
next
  case (Suc nat) thus ?thesis using assms cut_hits_Inr by blast
qed

lemma no_Inr_between_cuts: "cut_omega_run omega_run j < t \<and> t < cut_omega_run omega_run (Suc j) \<Longrightarrow> omega_run t \<noteq> Inr()"
  using not_less_Least by auto

definition block_run :: "('s + unit) omega_run \<Rightarrow> nat \<Rightarrow> ('s + unit) run" where "block_run omega_run j = map omega_run [cut_omega_run omega_run j ..< cut_omega_run omega_run (Suc j) + 1]"

definition block_word :: "'a omega_word \<Rightarrow> ('s + unit) omega_run \<Rightarrow> nat \<Rightarrow> 'a word" where "block_word omega_word omega_run j = map omega_word [cut_omega_run omega_run j ..< cut_omega_run omega_run (Suc j)]"

lemma not_empty_block_word:
  assumes "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states (omega_power_auto \<A>)"
  shows "block_word omega_word omega_run j \<noteq> []"
proof - 
  have "cut_omega_run omega_run (Suc j) > cut_omega_run omega_run j" using assms cut_hits_Inr by blast
  hence "[cut_omega_run omega_run j ..< cut_omega_run omega_run (Suc j)] \<noteq> []" by simp
  thus ?thesis unfolding block_word_def by blast
qed

lemma block_run_accepting_in_power_auto:
  assumes "omega_run_accepting omega_run (omega_power_auto \<A>) omega_word"
  shows "run_accepting (block_run omega_run j) (omega_power_auto \<A>) (block_word omega_word omega_run j)"
proof - 
  let ?\<A> = "omega_power_auto \<A>"
  have props: "\<forall> n . (omega_run n, omega_word n, omega_run (n + 1)) \<in> transitions ?\<A> \<and> omega_run 0 = initial_state ?\<A> \<and> initial_state ?\<A> \<in> states ?\<A> \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states ?\<A>)" using assms unfolding omega_run_accepting_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
  {
    fix k assume assm: "k < length (block_run omega_run j) - 1"
    hence "k < length (block_run omega_run j)" by force
    hence equik: "(block_run omega_run j) ! k = omega_run (cut_omega_run omega_run j + k)" using length_map length_upt nth_map_upt unfolding block_run_def by metis
    have "k + 1 < length (block_run omega_run j)" using assm by force
    hence equik1: "(block_run omega_run j) ! (k + 1) = omega_run (cut_omega_run omega_run j + k + 1)" using add.assoc length_map length_upt nth_map_upt unfolding block_run_def by metis
    have "k < length (block_word omega_word omega_run j)" using assm diff_add_inverse2 diff_commute length_map length_upt unfolding block_word_def block_run_def by metis
    hence equiw: "(block_word omega_word omega_run j) ! k = omega_word (cut_omega_run omega_run j + k)" using assm unfolding block_word_def by force
    have "(omega_run (cut_omega_run omega_run j + k), omega_word (cut_omega_run omega_run j + k), omega_run (cut_omega_run omega_run j + k + 1)) \<in> transitions ?\<A>" using props by blast
    hence "(block_run omega_run j ! k, block_word omega_word omega_run j ! k, block_run omega_run j ! (k + 1)) \<in> transitions ?\<A>" using equik equik1 equiw by auto
  }
  hence trans: "\<forall> k < length (block_run omega_run j) - 1 . (block_run omega_run j ! k, block_word omega_word omega_run j ! k, block_run omega_run j ! (k + 1)) \<in> transitions ?\<A>" by blast
  have "cut_omega_run omega_run (Suc j) > cut_omega_run omega_run j" using props cut_hits_Inr by blast
  hence len: "length [cut_omega_run omega_run j ..< cut_omega_run omega_run (Suc j) + 1] = length [cut_omega_run omega_run j ..< cut_omega_run omega_run (Suc j)] + 1" by auto
  hence length: "length (block_run omega_run j) = length (block_word omega_word omega_run j) + 1" unfolding block_word_def block_run_def by auto
  have "(block_run omega_run j) ! 0 = omega_run (cut_omega_run omega_run j)" using Nat.add_0_right len add_gr_0 length_upt less_numeral_extra(1) nth_map_upt unfolding block_run_def by metis
  hence init: "(block_run omega_run j) ! 0 = initial_state ?\<A> \<and> initial_state ?\<A> \<in> states ?\<A>" using props omega_run_cut_j_is_Inr unfolding omega_power_auto_def by auto
  have "block_run omega_run j \<noteq> []" using length by auto
  hence "last (block_run omega_run j) = omega_run (cut_omega_run omega_run (Suc j))" unfolding block_run_def by auto
  hence "last (block_run omega_run j) = Inr()" using props cut_hits_Inr by auto
  hence "last (block_run omega_run j) \<in> accepting_states ?\<A>" unfolding omega_power_auto_def by auto
  thus ?thesis using length init trans unfolding pseudo_run_well_defined_def run_well_defined_def run_accepting_def by blast
qed

lemma no_Inr_inside_block:
  assumes "run_accepting (block_run omega_run j) (omega_power_auto \<A>) (block_word omega_word omega_run j)"
  shows "\<forall> i < length (block_run omega_run j) . i \<noteq> 0 \<and> i \<noteq> length (block_run omega_run j) - 1 \<longrightarrow> (block_run omega_run j) ! i \<noteq> Inr()"
proof - 
  {
    fix i assume assm: "i < length (block_run omega_run j) \<and> i \<noteq> 0 \<and> i \<noteq> length (block_run omega_run j) - 1"
    hence equi: "(block_run omega_run j) ! i = omega_run ((cut_omega_run omega_run j) + i)" using length_map length_upt nth_map_upt unfolding block_run_def by metis
    then obtain t where t: "t = (cut_omega_run omega_run j) + i" by blast
    hence between: "cut_omega_run omega_run j < t \<and> t < (cut_omega_run omega_run j) + length (block_run omega_run j) - 1" using assm by auto
    have "block_run omega_run j \<noteq> []" using assms unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by auto
    hence len: "length (block_run omega_run j) = cut_omega_run omega_run (Suc j) - cut_omega_run omega_run j + 1" unfolding block_run_def by force
    hence "cut_omega_run omega_run j < t \<and> t < cut_omega_run omega_run (Suc j)" using between by force
    hence "omega_run t \<noteq> Inr()" using no_Inr_between_cuts by blast
    hence "(block_run omega_run j) ! i \<noteq> Inr()" using t equi by auto
  }
  thus ?thesis by blast
qed

theorem omega_lang_power_auto_in_omega_power:
  assumes "auto_well_defined \<A>"
  shows "omega_language_auto (omega_power_auto \<A>) \<subseteq> omega_power_language (language_auto \<A>)"
proof -
  let ?\<A> = "omega_power_auto \<A>"
  {
    fix omega_word assume "omega_word \<in> omega_language_auto ?\<A>"
    then obtain omega_run where acc: "omega_run_accepting omega_run ?\<A> omega_word" unfolding omega_language_auto_def by blast
    hence inf: "\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states ?\<A>" unfolding omega_run_accepting_def by blast
    define inf_word_list where "inf_word_list = (\<lambda>n . (block_word omega_word omega_run n))"
    {
      fix j
      have run: "run_accepting (block_run omega_run j) ?\<A> (block_word omega_word omega_run j)" using acc block_run_accepting_in_power_auto by blast
      have not_empty: "block_word omega_word omega_run j \<noteq> []" using inf not_empty_block_word by blast
      hence "length (block_run omega_run j) > 1" using run unfolding run_accepting_def run_well_defined_def pseudo_run_well_defined_def by auto
      then consider (case1) "length (block_run omega_run j) = 2" | (case2) "length (block_run omega_run j) > 2" by linarith
      hence "\<exists> run_inl . run_accepting run_inl \<A> (block_word omega_word omega_run j)"
      proof cases
        case case1 thus ?thesis using assms run existence_of_accepting_run_on_original_auto_length2 by blast
      next
        case case2
        thus ?thesis using assms run no_Inr_inside_block existence_of_accepting_run_on_original_auto by fast
      qed
      hence first_prop: "(block_word omega_word omega_run j) \<in> language_auto \<A> \<and> block_word omega_word omega_run j \<noteq> []" using not_empty unfolding language_auto_def by blast
      {
        fix k assume k: "k < length (inf_word_list j)"
        have  "inf_word_list j = block_word omega_word omega_run j" unfolding inf_word_list_def by simp
        hence index: "(inf_word_list j) ! k = omega_word (cut_omega_run omega_run j + k)" using k unfolding block_word_def by auto
        have "length (prefix_concat inf_word_list j) = cut_omega_run omega_run j" unfolding inf_word_list_def
        proof (induction j)
          case 0 thus ?case by simp
        next
          case (Suc j)
          have ge: "cut_omega_run omega_run (Suc j) > cut_omega_run omega_run j" using inf cut_hits_Inr by blast   
          have "prefix_concat inf_word_list (Suc j)  = prefix_concat inf_word_list j @ inf_word_list j" by simp
          hence "length (prefix_concat inf_word_list (Suc j)) = length (prefix_concat inf_word_list j) + length (inf_word_list j)" by simp
          thus ?case using Suc ge unfolding inf_word_list_def block_word_def by force
        qed
        hence "omega_word (length (prefix_concat inf_word_list j) + k) = (inf_word_list j) ! k" using index by simp
      }
      hence "\<forall> k . k < length (inf_word_list j) \<longrightarrow> omega_word (length (prefix_concat inf_word_list j) + k) = (inf_word_list j) ! k" by blast
      hence "inf_word_list j \<in> language_auto \<A> \<and> inf_word_list j \<noteq> [] \<and> (\<forall> k . k < length (inf_word_list j) \<longrightarrow> omega_word (length (prefix_concat inf_word_list j) + k) = (inf_word_list j) ! k)" using first_prop unfolding inf_word_list_def by blast
    }
    hence "omega_word \<in> omega_power_language (language_auto \<A>)" unfolding omega_power_language_def by blast
  }
  thus ?thesis by blast
qed

theorem omega_power_language_correctness:
  assumes "auto_well_defined \<A>"
  shows "omega_language_auto (omega_power_auto \<A>) = omega_power_language (language_auto \<A>)"
  using assms omega_lang_power_auto_in_omega_power omega_power_in_omega_lang_power_auto by blast

corollary omega_power_main:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)"
  shows "\<exists> omega_power_\<A> :: ('s + unit, 'a) automaton . auto_well_defined omega_power_\<A> \<and> alphabet omega_power_\<A> = alphabet \<A> \<and> omega_language_auto omega_power_\<A> = omega_power_language (language_auto \<A>)"
  using assms omega_power_language_correctness omega_power_auto_well_defined omega_power_alphabet by metis

theorem existence_of_omega_power_same_type:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> omega_power_\<A> :: ('s, 'a) automaton . auto_well_defined omega_power_\<A> \<and> alphabet omega_power_\<A> = alphabet \<A> \<and> omega_language_auto omega_power_\<A> = omega_power_language (language_auto \<A>)"
  using assms omega_power_main existence_soft_iso_auto_omega_lang by metis

end