theory omega_automata_complementation

imports Main omega_automata_greedy_runs

begin

text \<open>Author: Benno Thalmann, last update: 1.5.2026, Addition to masterarbeit_benno_thalmann\<close>

definition upper_states :: "('s, 'a) automaton \<Rightarrow> ('s states list) states" where "upper_states \<A> = {S . 1 \<le> length S \<and> length S \<le> card (states \<A>) \<and> distinct S \<and> pairwise (\<lambda> S_i S_j . S_i \<inter> S_j = {}) (set S) \<and> (\<forall> S_m \<in> set S . S_m \<subseteq> (states \<A>) \<and> S_m \<noteq> {})}"

definition post_set :: "('s, 'a) automaton \<Rightarrow> 's states \<Rightarrow> 'a symbol \<Rightarrow> 's states" where "post_set \<A> S_m a = {s2 . \<exists> s1 \<in> S_m . (s1, a, s2) \<in> transitions \<A>}"

fun upper_step :: "('s, 'a) automaton \<Rightarrow> 'a symbol \<Rightarrow> 's states list \<Rightarrow> ('s states list \<times> 's states)" where
  "upper_step \<A> a [] = ([], {})" |
  "upper_step \<A> a (S_m # S) = (((post_set \<A> S_m a - snd (upper_step \<A> a S)) - accepting_states \<A>) # ((post_set \<A> S_m a - snd (upper_step \<A> a S)) \<inter> accepting_states \<A>) # fst (upper_step \<A> a S), (snd (upper_step \<A> a S) \<union> post_set \<A> S_m a))"

definition upper_transitions :: "('s, 'a) automaton \<Rightarrow> ('s states list, 'a) transitions" where "upper_transitions \<A> = {(S, a, S') . S \<in> upper_states \<A> \<and> a \<in> alphabet \<A> \<and> S' = filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a S)) \<and> S' \<noteq> []}"

lemma upper_step_fst_subset_states:
  assumes "auto_well_defined \<A>"
  shows "\<forall> S_m \<in> set (fst (upper_step \<A> a S)) . S_m \<subseteq> states \<A>"
proof (induction S)
  case Nil thus ?case by auto
next
  case (Cons S_m S)
  have ps: "post_set \<A> S_m a \<subseteq> states \<A>" using assms unfolding auto_well_defined_def post_set_def by fast
  hence sub: "(post_set \<A> S_m a - snd (upper_step \<A> a S)) - accepting_states \<A> \<subseteq> states \<A>" by blast
  have "(post_set \<A> S_m a - snd (upper_step \<A> a S)) \<inter> accepting_states \<A> \<subseteq> states \<A>" using ps by blast
  thus ?case using Cons sub by auto
qed

lemma upper_step_fst_subset_snd: "\<forall> S_m \<in> set (fst (upper_step \<A> a S)) . S_m \<subseteq> snd (upper_step \<A> a S)"
proof (induction S)
  case Nil thus ?case by simp
next
  case (Cons S_m S)
  let ?L = "post_set \<A> S_m a - snd (upper_step \<A> a S) - accepting_states \<A>"
  let ?R = "(post_set \<A> S_m a - snd (upper_step \<A> a S)) \<inter> accepting_states \<A>"
  have Lsub: "?L \<subseteq> (snd (upper_step \<A> a (S_m # S)))" by force
  have Rsub: "?R \<subseteq> (snd (upper_step \<A> a (S_m # S)))" by force
  have Usub: "snd (upper_step \<A> a S) \<subseteq> snd (upper_step \<A> a (S_m # S))" by simp
  {
    fix S_k assume "S_k \<in> set (fst (upper_step \<A> a (S_m # S)))"
    hence "S_k = ?L \<or> S_k = ?R \<or> S_k \<in> set (fst (upper_step \<A> a S))" by simp
    then consider (case1) "S_k = ?L" | (case2) "S_k = ?R" | (case3) "S_k \<in> set (fst (upper_step \<A> a S))" by fast
    hence "S_k \<subseteq> snd (upper_step \<A> a (S_m # S))"
    proof cases
      case case1 thus ?thesis using Lsub by blast
    next
      case case2 thus ?thesis using Rsub by blast
    next
      case case3 thus ?thesis using Cons Usub by blast
    qed
  }  
  thus ?case by blast
qed

definition pairwise_list :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> bool" where "pairwise_list R list = (\<forall> i < length list . \<forall> j < length list . i < j \<longrightarrow> R (list ! i) (list ! j))"

lemma upper_step_fst_pairwise_list: "pairwise_list (\<lambda> S_i S_j . S_i \<inter> S_j = {}) (fst (upper_step \<A> a S))"
proof (induction S)
  case Nil thus ?case unfolding pairwise_list_def by auto
next
  case (Cons S_m S)
  let ?L = "(post_set \<A> S_m a - (snd (upper_step \<A> a S))) - accepting_states \<A>"
  let ?R = "(post_set \<A> S_m a - (snd (upper_step \<A> a S))) \<inter> accepting_states \<A>"
  have LR: "?L \<inter> ?R = {}" by auto
  {
    fix j assume "j < length (fst (upper_step \<A> a S))"
    hence "(fst (upper_step \<A> a S)) ! j \<in> set (fst (upper_step \<A> a S))" by auto
    hence "(fst (upper_step \<A> a S)) ! j \<subseteq> (snd (upper_step \<A> a S))" using upper_step_fst_subset_snd by fast
    hence "?L \<inter> ((fst (upper_step \<A> a S)) ! j) = {}" by blast
  }
  hence L_rest: "\<forall> j < length (fst (upper_step \<A> a S)) . ?L \<inter> ((fst (upper_step \<A> a S)) ! j) = {}" by blast
  {
    fix j assume "j < length (fst (upper_step \<A> a S))"
    hence "(fst (upper_step \<A> a S)) ! j \<in> set (fst (upper_step \<A> a S))" by auto
    hence "(fst (upper_step \<A> a S)) ! j \<subseteq> (snd (upper_step \<A> a S))" using upper_step_fst_subset_snd by fast
    hence "?R \<inter> ((fst (upper_step \<A> a S)) ! j) = {}" by blast
  }
  hence R_rest: "\<forall>j < length (fst (upper_step \<A> a S)) . ?R \<inter> ((fst (upper_step \<A> a S)) ! j) = {}" by blast
  {
    fix i j assume assm: "i < length (?L # ?R # (fst (upper_step \<A> a S))) \<and> j < length (?L # ?R # (fst (upper_step \<A> a S))) \<and> i < j"
    hence "((?L # ?R # (fst (upper_step \<A> a S))) ! i) \<inter> ((?L # ?R # (fst (upper_step \<A> a S))) ! j) = {}"
    proof (cases i)
      case 0
      thus ?thesis
      proof (cases j)
        case 0 thus ?thesis using assm by blast
      next
        case (Suc j')
        hence j: "j = Suc j'" by blast
        thus ?thesis
        proof (cases j')
          case 0 thus ?thesis using assm Suc LR by force
        next
          case (Suc t) thus ?thesis using L_rest assm 0 j by auto
        qed
      qed
    next
      case (Suc i')
      hence i: "i = Suc i'" by blast
      thus ?thesis
      proof (cases i')
        case 0
        thus ?thesis
        proof (cases j)
          case 0 thus ?thesis using assm by blast
        next
          case (Suc j')
          hence j: "j = Suc j'" by blast
          thus ?thesis
          proof (cases j')
            case 0 thus ?thesis using assm Suc LR by auto
          next
            case (Suc t) thus ?thesis using R_rest assm 0 j i by auto
          qed
        qed
      next
        case (Suc i2)
        hence i2lt: "i2 < length (fst (upper_step \<A> a S))" using i assm by simp
        have "\<exists> j2 . j = Suc (Suc j2)" using assm Suc i by presburger
        then obtain j2 where j2: "j = Suc (Suc j2)" by blast
        hence j2lt: "j2 < length (fst (upper_step \<A> a S))" using assm by simp
        have "i2 < j2" using assm Suc j2 i by blast
        hence "((fst (upper_step \<A> a S)) ! i2) \<inter> ((fst (upper_step \<A> a S)) ! j2) = {}" using Cons unfolding pairwise_list_def using i2lt j2lt by blast
        thus ?thesis using Suc assm j2 i by simp
      qed
    qed
  }
  hence "pairwise_list (\<lambda> S_i S_j . S_i \<inter> S_j = {}) (?L # ?R # (fst (upper_step \<A> a S)))" unfolding pairwise_list_def by blast
  thus ?case by simp
qed

lemma distinct_of_pairwise_list_disjoint_nonempty:
  assumes "pairwise_list (\<lambda> S_i S_j . S_i \<inter> S_j = {}) S" "\<forall> S_m \<in> set S . S_m \<noteq> {}"
  shows "distinct S"
proof -
  {
    fix i j assume assm: "i < length S \<and> j < length S \<and> i \<noteq> j"
    hence "S ! i \<noteq> S ! j"
    proof(cases "i < j")
      case True
      hence disj: "(S ! i) \<inter> (S ! j) = {}" using assms assm unfolding pairwise_list_def by blast
      have "S ! i \<noteq> {}" using assms assm by auto
      thus ?thesis using disj by blast
    next
      case False
      hence "j < i" using assm by linarith
      hence disj: "(S ! i) \<inter> (S ! j) = {}" using assms assm unfolding pairwise_list_def by blast
      have "S ! j \<noteq> {}" using assms assm by auto
      thus ?thesis using disj by blast
    qed
  }
  thus ?thesis by (simp add: distinct_conv_nth)
qed

lemma pairwise_list_disjoint_imp_pairwise:
  assumes "pairwise_list (\<lambda> A B . A \<inter> B = {}) list"
  shows "pairwise (\<lambda> A B . A \<inter> B = {}) (set list)"
proof -
  {
    fix x y assume assm: "x \<in> set list \<and> y \<in> set list \<and> x \<noteq> y"
    then obtain i j  where var: "i < length list \<and> list ! i = x \<and> j < length list \<and> list ! j = y" using in_set_conv_nth by metis
    hence "i \<noteq> j" using assm by blast
    hence or: "i < j \<or> j < i" using linorder_neqE_nat by blast
    hence "x \<inter> y = {}"
    proof(cases "i < j")
      case True thus ?thesis using assms var unfolding pairwise_list_def by blast
    next
      case False
      hence "j < i" using or by blast
      thus ?thesis using assms var unfolding pairwise_list_def by blast
    qed
  }
  hence "\<forall> x \<in> set list . \<forall> y \<in> set list . x \<noteq> y \<longrightarrow> (x \<inter> y = {})" by blast
  thus ?thesis unfolding pairwise_def by blast
qed

lemma length_le_card_states_of_pairwise_disjoint_nonempty:
  assumes "auto_well_defined \<A>" "\<forall> S_m \<in> set S . S_m \<subseteq> states \<A> \<and> S_m \<noteq> {}" "pairwise_list (\<lambda> S_i S_j . S_i \<inter> S_j = {}) S"
  shows "length S \<le> card (states \<A>)"
proof -
  have fin: "finite (states \<A>)" using assms unfolding auto_well_defined_def by blast
  have dist: "distinct S" using assms distinct_of_pairwise_list_disjoint_nonempty by fast
  have pairwise: "pairwise (\<lambda> S_i S_j . S_i \<inter> S_j = {}) (set S)" using assms pairwise_list_disjoint_imp_pairwise by auto
  let ?pick = "\<lambda> S_m . (SOME x . x \<in> S_m)"
  {
    fix S_m assume "S_m \<in> set S"
    hence "\<exists> x . x \<in> S_m" using assms by auto
    hence "?pick S_m \<in> S_m" by (rule someI_ex)
  }
  hence pick_in: "\<forall> S_m \<in> set S . ?pick S_m \<in> S_m" by blast
  hence pick_in_states: "\<forall> S_m \<in> set S . ?pick S_m \<in> states \<A>" using assms by blast
  {
    fix S_i S_j assume assm: "S_i \<in> set S \<and> S_j \<in> set S \<and> ?pick S_i = ?pick S_j"
    hence "S_i = S_j"
    proof (cases "S_i = S_j")
      case True thus ?thesis by blast
    next
      case False
      hence disj: "S_i \<inter> S_j = {}" using assm pairwise by (auto dest: pairwiseD)
      have pick: "?pick S_i \<in> S_i" using pick_in assm by blast
      have "?pick S_j \<in> S_j" using pick_in assm by blast
      hence "?pick S_i \<in> S_i \<inter> S_j" using pick assm by auto
      thus ?thesis using disj by auto
    qed
  }
  hence "inj_on ?pick (set S)" by (rule inj_onI) auto
  hence "card (set S) \<le> card (states \<A>)" using fin pick_in_states card_inj_on_le by blast
  thus ?thesis using dist distinct_card by metis
qed

lemma pairwise_list_tl:
  assumes "pairwise_list R (x # xs)"
  shows "pairwise_list R xs"
proof(rule ccontr)
  assume "\<not> pairwise_list R xs"
  then obtain i j where "i < length xs \<and> j < length xs \<and> i < j \<and> \<not> R (xs ! i) (xs ! j)" unfolding pairwise_list_def by blast
  hence "Suc i < length (x # xs) \<and> Suc j < length (x # xs) \<and> Suc i < Suc j \<and> \<not> R ((x # xs) ! (Suc i)) ((x # xs) ! (Suc j))" by simp
  thus False using assms unfolding pairwise_list_def by blast
qed

lemma pairwise_list_hd_nth:
  assumes "pairwise_list R (x # xs)" "j < length xs"
  shows "R x (xs ! j)"
  using assms unfolding pairwise_list_def by fastforce

lemma pairwise_list_hd_set:
  assumes "pairwise_list R (x # xs)"
  shows "\<forall> y \<in> set xs . R x y"
  using assms in_set_conv_nth pairwise_list_hd_nth by metis

lemma pairwise_list_filter: "pairwise_list R list \<Longrightarrow> pairwise_list R (filter P list)"
proof(induction list)
  case Nil thus ?case unfolding pairwise_list_def by auto
next
  case (Cons x xs)
  hence IH: "pairwise_list R (filter P xs)" using pairwise_list_tl by fast
  thus ?case
  proof (cases "P x")
    case True
    {
      fix y assume "y \<in> set (filter P xs)"
      hence yxs: "y \<in> set xs" by auto
      have "\<forall> y \<in> set xs . R x y"
      proof (cases xs)
        case Nil thus ?thesis using yxs by auto
      next
        case (Cons z zs) thus ?thesis using pairwise_list_hd_set Cons.prems by fast
      qed
      hence "R x y" using yxs by blast
    }
    hence hx: "\<forall>y \<in> set (filter P xs). R x y" by blast
    {
      fix i j assume assm: "i < length (x # filter P xs) \<and> j < length (x # filter P xs) \<and> i < j"
      hence "R ((x # filter P xs) ! i) ((x # filter P xs) ! j)"
      proof (cases i)
        case 0 thus ?thesis
        proof (cases j)
          case 0 thus ?thesis using assm by blast
        next
          case (Suc j') thus ?thesis using hx 0 assm nth_mem by force
        qed
      next
        case (Suc i')
        hence i': "i' < length (filter P xs)" using assm by simp
        obtain j' where j': "j = Suc j'" using assm by (cases j) auto
        hence j'' : "j' < length (filter P xs)" using assm by simp
        have "i' < j'" using assm Suc j' by blast
        hence "R ((filter P xs) ! i') ((filter P xs) ! j')" using IH i' j'' unfolding pairwise_list_def by blast
        thus ?thesis using Suc j' by simp
      qed
    }
    hence "pairwise_list R (x # filter P xs)" unfolding pairwise_list_def by blast
    thus ?thesis using True by force
  next
    case False thus ?thesis using IH by simp
  qed
qed

lemma upper_transitions_target_in_upper_states:
  assumes "auto_well_defined \<A>" "(S, a, S') \<in> upper_transitions \<A>"
  shows "S \<in> upper_states \<A> \<and> a \<in> alphabet \<A> \<and> S' \<in> upper_states \<A>"
proof -
  have S'def: "S \<in> upper_states \<A> \<and> a \<in> alphabet \<A> \<and> S' = filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a S)) \<and> S' \<noteq> []" using assms unfolding upper_transitions_def by auto
  have fin: "finite (states \<A>)" using assms unfolding auto_well_defined_def by auto

  have sub_fst: "\<forall> S_m \<in> set (fst (upper_step \<A> a S)) . S_m \<subseteq> states \<A>" using upper_step_fst_subset_states assms by fast
  {
    fix S_m assume assm: "S_m \<in> set S'"
    hence "S_m \<in> set (fst (upper_step \<A> a S))" using S'def by auto
    hence S_m: "S_m \<subseteq> states \<A>" using sub_fst by blast
    have "S_m \<noteq> {}" using assm S'def by auto
    hence "S_m \<subseteq> states \<A> \<and> S_m \<noteq> {}" using S_m by blast
  }
  hence S_m: "\<forall> S_m \<in> set S' . S_m \<subseteq> states \<A> \<and> S_m \<noteq> {}" by blast
  have "pairwise_list (\<lambda> S_i S_j . S_i \<inter> S_j = {}) (fst (upper_step \<A> a S))" using upper_step_fst_pairwise_list by fast
  hence "pairwise_list (\<lambda> S_i S_j . S_i \<inter> S_j = {}) (filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a S)))" using pairwise_list_filter by blast
  hence pwlS': "pairwise_list (\<lambda> S_i S_j . S_i \<inter> S_j = {}) S'" using S'def by simp
  hence distS': "distinct S'" using distinct_of_pairwise_list_disjoint_nonempty S_m by blast
  have pwS': "pairwise (\<lambda>S_i S_j. S_i \<inter> S_j = {}) (set S')" using pairwise_list_disjoint_imp_pairwise pwlS' by blast
  have "S' \<noteq> []" using S'def by blast
  hence "0 < length S'" by blast
  hence lenS': "1 \<le> length S'" by linarith
  have "length S' \<le> card (states \<A>)" using length_le_card_states_of_pairwise_disjoint_nonempty assms S_m pwlS' by blast
  hence "S' \<in> upper_states \<A>" using lenS' distS' pwS' S_m unfolding upper_states_def by blast
  thus ?thesis using assms unfolding upper_transitions_def by fast
qed

definition upper_part_pure :: "('s, 'a) automaton \<Rightarrow> ('s states list, 'a) automaton" where
  "upper_part_pure \<A> = Automaton
     (upper_states \<A> \<union> {[]})
     (alphabet \<A>)
     (upper_transitions \<A> \<union> {(s1, a, s2) . s1 \<in> upper_states \<A> \<and> s2 = [] \<and> a \<in> alphabet \<A> \<and> (\<nexists> s . (s1, a, s) \<in> upper_transitions \<A>)} \<union> {(s1, a, s2) . s1 = [] \<and> s2 = [] \<and> a \<in> alphabet \<A>})
     ([{initial_state \<A>}])
     {[]}"

lemma finite_upper_states:
  assumes "auto_well_defined \<A>"
  shows "finite (upper_states \<A>)"
proof -
  have "finite (states \<A>)" using assms unfolding auto_well_defined_def by auto
  hence finPow: "finite (Pow (states \<A>))" by simp
  have sub: "upper_states \<A> \<subseteq> {S . set S \<subseteq> Pow (states \<A>) \<and> length S \<le> card (states \<A>)}" unfolding upper_states_def by auto
  have "finite {S . set S \<subseteq> Pow (states \<A>) \<and> length S \<le> card (states \<A>)}" using finPow by (rule finite_lists_length_le)
  thus ?thesis using finite_subset sub by blast
qed

theorem well_def_upper_part_pure:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (upper_part_pure \<A>)"
proof - 
  let ?\<A> = "upper_part_pure \<A>"
  have fin_s: "finite (states ?\<A>)" using assms finite_upper_states unfolding upper_part_pure_def by auto
  have fin_a: "finite (alphabet ?\<A>)" using assms unfolding auto_well_defined_def upper_part_pure_def by auto
  have card: "card (states \<A>) \<ge> 1" using assms at_least_one_state by force
  have "initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  hence "1 \<le> length [{initial_state \<A>}] \<and> length [{initial_state \<A>}] \<le> card (states \<A>) \<and> distinct [{initial_state \<A>}] \<and> pairwise (\<lambda> S_i S_j . S_i \<inter> S_j = {}) (set [{initial_state \<A>}]) \<and> (\<forall> S_m \<in> set [{initial_state \<A>}] . S_m \<subseteq> (states \<A>) \<and> S_m \<noteq> {})" using card by force 
  hence init: "initial_state ?\<A> \<in> states ?\<A>" unfolding upper_states_def upper_part_pure_def by simp
  have "\<forall> (s1, a, s2) \<in> transitions ?\<A> . s1 \<in> states ?\<A> \<and> a \<in> alphabet ?\<A> \<and> s2 \<in> states ?\<A>" using assms upper_transitions_target_in_upper_states unfolding upper_part_pure_def by force
  thus ?thesis using fin_s fin_a init unfolding auto_well_defined_def upper_part_pure_def by force
qed

proposition DFA_property_upper_part_pure:
  assumes "auto_well_defined \<A>"
  shows "DFA_property (upper_part_pure \<A>)"
proof - 
  let ?\<A> = "upper_part_pure \<A>"
  have unique: "\<forall> s1 s2 s3 a . (s1, a, s2) \<in> upper_transitions \<A> \<and> (s1, a, s3) \<in> upper_transitions \<A> \<longrightarrow> s2 = s3" using assms unfolding upper_transitions_def by fast
  {
    fix s1 a assume assm: "s1 \<in> states ?\<A> \<and> a \<in> alphabet ?\<A>"
    then consider (case1) "s1 = []" | (case2) "s1 \<noteq> []" by auto
    hence "\<exists>! s2 . (s1, a, s2) \<in> transitions ?\<A>"
    proof cases
      case case1
      hence exi: "(s1, a, []) \<in> transitions ?\<A>" using assm unfolding upper_part_pure_def by auto
      {
        fix s2 assume "(s1, a, s2) \<in> transitions ?\<A>"
        hence "s2 = []" using case1 unfolding upper_part_pure_def upper_transitions_def by auto
      }
      thus ?thesis using exi by auto
    next
      case case2
      hence s1: "s1 \<in> upper_states \<A>" using assm unfolding upper_part_pure_def by auto
      thus ?thesis
      proof (cases "\<exists> s . (s1, a, s) \<in> upper_transitions \<A>")
        case True
        then obtain s2 where s2: "(s1, a, s2) \<in> upper_transitions \<A>" by auto
        hence trans: "(s1, a, s2) \<in> transitions ?\<A>" unfolding upper_part_pure_def by auto
        {
          fix s3 assume s3: "(s1, a, s3) \<in> transitions ?\<A>"
          hence "(s1, a, s3) \<in> upper_transitions \<A> \<or> (s1, a, s3) \<in> {(x, b, y) . x \<in> upper_states \<A> \<and> y = [] \<and> b \<in> alphabet \<A> \<and> (\<nexists> s . (x, b, s) \<in> upper_transitions \<A>)} \<or> (s1, a, s3) \<in> {(x, b, y) . x = [] \<and> y = [] \<and> b \<in> alphabet \<A>}" unfolding upper_part_pure_def by force
          then consider (case3) "(s1, a, s3) \<in> upper_transitions \<A>" | (case4) "(s1, a, s3) \<in> {(x, b, y) . x \<in> upper_states \<A> \<and> y = [] \<and> b \<in> alphabet \<A> \<and> (\<nexists> s . (x, b, s) \<in> upper_transitions \<A>)}" | (case5) "(s1, a, s3) \<in> {(x, b, y) . x = [] \<and> y = [] \<and> b \<in> alphabet \<A>}" by argo 
          hence "s3 = s2"
          proof cases
            case case3 thus ?thesis using s2 unique by blast
          next
            case case4 thus ?thesis using True by fast
          next
            case case5 thus ?thesis using case2 by fast
          qed
        }
        thus ?thesis using trans by blast
      next
        case False
        hence trans: "(s1, a, []) \<in> transitions ?\<A>" using assm unfolding upper_part_pure_def by auto
        {
          fix s3 assume s3: "(s1, a, s3) \<in> transitions ?\<A>"
          hence "(s1, a, s3) \<in> upper_transitions \<A> \<or> (s1, a, s3) \<in> {(x, b, y) . x \<in> upper_states \<A> \<and> y = [] \<and> b \<in> alphabet \<A> \<and> (\<nexists> s . (x, b, s) \<in> upper_transitions \<A>)} \<or> (s1, a, s3) \<in> {(x, b, y) . x = [] \<and> y = [] \<and> b \<in> alphabet \<A>}" unfolding upper_part_pure_def by force
          then consider (case3) "(s1, a, s3) \<in> upper_transitions \<A>" | (case4) "(s1, a, s3) \<in> {(x, b, y) . x \<in> upper_states \<A> \<and> y = [] \<and> b \<in> alphabet \<A> \<and> (\<nexists> s . (x, b, s) \<in> upper_transitions \<A>)}" | (case5) "(s1, a, s3) \<in> {(x, b, y) . x = [] \<and> y = [] \<and> b \<in> alphabet \<A>}" by argo 
          hence "s3 = []"
          proof cases
            case case3 thus ?thesis using False by blast
          next
            case case4 thus ?thesis by fast
          next
            case case5 thus ?thesis using case2 by fast
          qed
        }
        thus ?thesis using trans by blast
      qed
    qed
  }
  thus ?thesis using assms well_def_trans_components well_def_upper_part_pure unfolding DFA_property_def by fast
qed

text \<open>Proof of correctness\<close>
lemma lemma_3_4_8:
  assumes "p \<in> upper_states \<A>" "j < k" "k < length p"
  shows "p ! j \<noteq> {} \<and> p ! k \<noteq> {} \<and> (p ! j) \<inter> (p ! k) = {}"
proof -
  have jlt: "j < length p" using assms by auto
  have nonempty: "\<forall> S_m \<in> set p . S_m \<noteq> {}" using assms unfolding upper_states_def by blast
  hence pj_ne: "p ! j \<noteq> {}" using nth_mem jlt by auto
  have pk_ne: "p ! k \<noteq> {}" using nonempty nth_mem assms by auto
  have "distinct p \<and> pairwise (\<lambda> S_i S_j . S_i \<inter> S_j = {}) (set p)" using assms unfolding upper_states_def by blast
  hence "(p ! j) \<inter> (p ! k) = {}" using nth_mem jlt assms pairwiseD inf.strict_order_iff nth_eq_iff_index_eq by (metis (mono_tags, lifting))
  thus ?thesis using pj_ne pk_ne by blast
qed

lemma snd_upper_step_eq_post_set_Union: "snd (upper_step \<A> a S) = post_set \<A> (\<Union> (set S)) a"
proof (induction S)
  case Nil thus ?case unfolding post_set_def by simp
next
  case (Cons S_m S) 
  have "\<forall> A B . post_set \<A> (A \<union> B) a = post_set \<A> A a \<union> post_set \<A> B a" unfolding post_set_def by blast
  thus ?case using Cons by force
qed

lemma Union_fst_upper_step_eq_snd: "\<Union> (set (fst (upper_step \<A> a S))) = snd (upper_step \<A> a S)"
  by (induction S) auto

lemma Union_filter_nonempty: "\<Union> (set (filter (\<lambda>S_m . S_m \<noteq> {}) list)) = \<Union> (set list)"
  by (induction list) auto

lemma lemma_3_4_10:
  assumes "(s1, a, s2) \<in> upper_transitions \<A>"
  shows "post_set \<A> (\<Union> (set s1)) a = \<Union> (set s2)"
proof -
  have def: "s2 = filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a s1))" using assms unfolding upper_transitions_def by fast
  have "post_set \<A> (\<Union> (set s1)) a = snd (upper_step \<A> a s1)" using snd_upper_step_eq_post_set_Union by fast
  hence "post_set \<A> (\<Union> (set s1)) a = \<Union> (set (fst (upper_step \<A> a s1)))" using Union_fst_upper_step_eq_snd by fast
  hence "post_set \<A> (\<Union> (set s1)) a = \<Union> (set (filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a s1))))" using Union_filter_nonempty by fast
  thus ?thesis using def by argo
qed

lemma run_on_upper:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined run \<A> word \<Longrightarrow> \<exists> Run . run_well_defined Run (upper_part_pure \<A>) word \<and> (\<forall> i < length run . run ! i \<in> \<Union> (set (Run ! i)))"
proof(induction word arbitrary: run rule: rev_induct)
  case Nil
  hence "run = [initial_state \<A>]" using list_with_one_element unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence last_run: "run ! 0 = initial_state \<A> \<and> length run = 1" by auto
  have "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by auto
  hence "initial_state (upper_part_pure \<A>) \<in> states (upper_part_pure \<A>)" using assms unfolding auto_well_defined_def by blast
  hence "run_well_defined [initial_state (upper_part_pure \<A>)] (upper_part_pure \<A>) []" unfolding pseudo_run_well_defined_def run_well_defined_def by simp
  thus ?case using Nil last_run unfolding upper_part_pure_def by auto
next
  have well_def: "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
  case (snoc a word)
  hence "run \<noteq> []" unfolding pseudo_run_well_defined_def run_well_defined_def by force
  then obtain run' where var: "run = run' @ [last run]" using append_butlast_last_id by metis
  hence "run_well_defined (run' @ [last run]) \<A> (word @ [a])" using snoc by simp
  hence run': "run_well_defined run' \<A> word \<and> (last run', a, last run) \<in> transitions \<A>" using prun_well_defined_extension_snoc unfolding run_well_defined_def by fast
  then obtain Run where Run: "run_well_defined Run (upper_part_pure \<A>) word \<and> (\<forall> i < length run' . run' ! i \<in> \<Union> (set (Run ! i))) \<and> (last run', a, last run) \<in> transitions \<A>" using snoc by blast
  let ?S' = "filter (\<lambda>Sm . Sm \<noteq> {}) (fst (upper_step \<A> a (last Run)))"
  have "run' \<noteq> []" using run' unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "length run' - 1 < length run' \<and> run' ! (length run' - 1) = last run'" using list_properties_not_empty by fastforce
  hence in_set: "last run' \<in> \<Union> (set (Run ! (length run' - 1)))" using Run by metis
  have "length Run = length run' \<and> Run \<noteq> []" using Run run' unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "Run ! (length run' - 1) = last Run" using list_properties_not_empty by metis
  hence not_empty: "last run' \<in> \<Union> (set (last Run)) \<and> last Run \<noteq> []" using in_set by force
  have "last Run \<in> states (upper_part_pure \<A>)" using Run well_def last_of_prun_is_state unfolding run_well_defined_def by fast
  hence S_in_upper: "last Run \<in> upper_states \<A>" using not_empty unfolding upper_part_pure_def by force
  have a_in_alpha: "a \<in> alphabet \<A>" using assms Run well_def_trans_components by fast
  obtain Sm where Sm: "Sm \<in> set (last Run) \<and> last run' \<in> Sm" using not_empty by blast
  hence "last run \<in> post_set \<A> (\<Union> (set (last Run))) a" using Sm Run unfolding post_set_def by fast
  hence "last run \<in> snd (upper_step \<A> a (last Run))" using snd_upper_step_eq_post_set_Union by fast
  hence "last run \<in> \<Union> (set (fst (upper_step \<A> a (last Run))))" using Union_fst_upper_step_eq_snd by fast
  hence last_in_union_S': "last run \<in> \<Union> (set ?S')" using Union_filter_nonempty by fast
  hence "?S' \<noteq> []" by force
  hence "(last Run, a, ?S') \<in> transitions (upper_part_pure \<A>)" using S_in_upper a_in_alpha unfolding upper_part_pure_def upper_transitions_def by simp
  hence Run_ext: "run_well_defined (Run @ [?S']) (upper_part_pure \<A>) (word @ [a])" using Run prun_well_defined_extension_snoc unfolding run_well_defined_def by fast
  {
    fix i assume "i < length run"
    then consider "i < length run - 1" | "i = length run - 1" by linarith
    hence "run ! i \<in> \<Union> (set ((Run @ [?S']) ! i))"
    proof cases
      case 1
      have "run \<noteq> []" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by force
      hence i_less: "i < length run'" using var 1 add_diff_cancel_right' length_append list.distinct(1) list.sel(3) tl_empty by metis
      hence idx: "run ! i = run' ! i" using list_properties_length var by metis
      have not_empty: "(Run @ [?S']) \<noteq> []" by fast
      have "length Run = length run'" using Run run' unfolding run_well_defined_def pseudo_run_well_defined_def by force
      hence "i < length Run" using i_less by auto
      hence "(Run @ [?S']) ! i = Run ! i" using list_properties_length by metis
      thus ?thesis using Run idx i_less by presburger
    next
      case 2
      have "length (Run @ [?S']) = length run" using Run_ext snoc unfolding run_well_defined_def pseudo_run_well_defined_def by force
      hence equi: "length (Run @ [?S']) - 1 = length run - 1" by argo
      have "(Run @ [?S']) \<noteq> []" using Run_ext unfolding run_well_defined_def pseudo_run_well_defined_def by force
      hence "(Run @ [?S']) ! (length (Run @ [?S']) - 1) = last (Run @ [?S'])" using list_properties_not_empty by simp
      hence last: "(Run @ [?S']) ! (length run - 1) = last (Run @ [?S'])" using equi by argo
      have "run \<noteq> []" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by force
      hence "run ! (length run - 1) = last run" using list_properties_not_empty by fast
      hence "(Run @ [?S']) ! i = last (Run @ [?S']) \<and> run ! i = last run" using 2 last by blast
      hence "(Run @ [?S']) ! i = ?S' \<and> run ! i = last run" by force
      thus ?thesis using last_in_union_S' by argo
    qed
  }
  thus ?case using Run_ext by metis
qed

corollary run_on_upper_last:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word"
  shows "\<exists> Run . run_well_defined Run (upper_part_pure \<A>) word \<and> last run \<in> \<Union> (set (last Run))"
proof -
  obtain Run where Run: "run_well_defined Run (upper_part_pure \<A>) word \<and> (\<forall> i < length run . run ! i \<in> \<Union> (set (Run ! i)))" using assms run_on_upper by blast
  hence "length Run = length run" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence equi: "length Run - 1 = length run - 1" by argo
  have "Run \<noteq> []" using Run unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "Run ! (length Run - 1) = last Run" using list_properties_not_empty by fast
  hence lastR: "Run ! (length run - 1) = last Run" using equi by argo
  have not_empty: "run \<noteq> []" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence lastr: "run ! (length run - 1) = last run" using list_properties_not_empty by fast
  have "length run - 1 < length run" using not_empty by auto
  thus ?thesis using Run lastR lastr by metis
qed

lemma upper_run_reaches_all:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined Run (upper_part_pure \<A>) word \<Longrightarrow> (\<forall> s \<in> \<Union> (set (last Run)) . \<exists> run . run_well_defined run \<A> word \<and> last run = s \<and> (\<forall> i < length run . run ! i \<in> \<Union> (set (Run ! i))))"
proof (induction word arbitrary: Run rule: rev_induct)
  case Nil
  hence Run0: "Run = [initial_state (upper_part_pure \<A>)]" using list_with_one_element unfolding run_well_defined_def pseudo_run_well_defined_def by force
  have "initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  hence "run_well_defined [initial_state \<A>] \<A> []" unfolding run_well_defined_def pseudo_run_well_defined_def by simp
  thus ?case using Run0 unfolding upper_part_pure_def by auto
next
  case (snoc a word)
  have "Run \<noteq> []" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain Run' where "Run = Run' @ [last Run]" using append_butlast_last_id by metis
  hence Run_ext: "run_well_defined Run' (upper_part_pure \<A>) word \<and> (last Run', a, last Run) \<in> transitions (upper_part_pure \<A>)" using snoc prun_well_defined_extension_snoc unfolding run_well_defined_def by metis
  hence IH: "\<forall> s \<in> \<Union> (set (last Run')) . \<exists> run . run_well_defined run \<A> word \<and> last run = s \<and> (\<forall> i < length run . run ! i \<in> \<Union> (set (Run' ! i)))" using snoc by presburger
  {
    fix s assume s: "s \<in> \<Union> (set (last Run))"
    hence "\<exists> run . run_well_defined run \<A> (word @ [a]) \<and> last run = s"
    proof (cases "last Run = []")
      case True thus ?thesis using s by simp
    next
      case False
      have "(last Run', a, last Run) \<in> upper_transitions \<A> \<or> (last Run' \<in> upper_states \<A> \<and> last Run = [] \<and> a \<in> alphabet \<A> \<and> (\<nexists>t. (last Run', a, t) \<in> upper_transitions \<A>)) \<or> (last Run' = [] \<and> last Run = [] \<and> a \<in> alphabet \<A>)" using Run_ext unfolding upper_part_pure_def by simp
      then consider (U) "(last Run', a, last Run) \<in> upper_transitions \<A>" | (SINKU) "last Run' \<in> upper_states \<A> \<and> last Run = [] \<and> a \<in> alphabet \<A> \<and> (\<nexists> t . (last Run', a, t) \<in> upper_transitions \<A>)" | (SINK0) "last Run' = [] \<and> last Run = [] \<and> a \<in> alphabet \<A>" by blast
      hence "(last Run', a, last Run) \<in> upper_transitions \<A>"
      proof cases
        case U thus ?thesis by auto
      next
        case SINKU thus ?thesis using False by simp
      next
        case SINK0 thus ?thesis using False by simp
      qed
      hence "post_set \<A> (\<Union> (set (last Run'))) a = \<Union> (set (last Run))" using lemma_3_4_10 by metis
      hence "s \<in> post_set \<A> (\<Union> (set (last Run'))) a" using s by blast
      then obtain s1 where s1: "s1 \<in> (\<Union> (set (last Run'))) \<and> (s1, a, s) \<in> transitions \<A>" unfolding post_set_def by blast
      then obtain run1 where "run_well_defined run1 \<A> word \<and> last run1 = s1" using IH by fast
      hence run: "run_well_defined (run1 @ [s]) \<A> (word @ [a])" using s1 prun_well_defined_extension_snoc unfolding run_well_defined_def by fast
      have "last (run1 @ [s]) = s" by simp
      thus ?thesis using run by blast
    qed
    then obtain run where run: "run_well_defined run \<A> (word @ [a]) \<and> last run = s" by auto
    then obtain Run'' where Run'': "run_well_defined Run'' (upper_part_pure \<A>) (word @ [a]) \<and> last run = s \<and> (\<forall> i < length run . run ! i \<in> \<Union> (set (Run'' ! i)))" using assms run_on_upper by blast
    have well_def: "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
    hence "word_well_defined (word @ [a]) (alphabet (upper_part_pure \<A>))" using Run'' well_def_implies_word_well_defined unfolding run_well_defined_def by fast
    hence "Run'' = Run" using snoc Run'' well_def exists_only_one_run_for_DFA DFA_property_upper_part_pure assms by metis
    hence "\<exists> run . run_well_defined run \<A> (word @ [a]) \<and> last run = s \<and> (\<forall> i < length run . run ! i \<in> \<Union> (set (Run ! i)))" using Run'' run by blast
  }
  thus ?case by blast
qed

lemma no_run_on_upper:
  assumes "auto_well_defined \<A>"
  shows "word_well_defined word (alphabet \<A>) \<and> (\<nexists> run . run_well_defined run \<A> word) \<Longrightarrow> \<exists> Run . run_well_defined Run (upper_part_pure \<A>) word \<and> last Run = []"
proof(induction word rule: rev_induct)
  case Nil
  have "initial_state \<A> \<in> states \<A>" using assms unfolding auto_well_defined_def by blast
  hence "run_well_defined [initial_state \<A>] \<A> []" unfolding pseudo_run_well_defined_def run_well_defined_def by simp
  thus ?case using Nil by auto
next
  case (snoc a word)
  hence word_well: "word_well_defined word (alphabet \<A>) \<and> a \<in> alphabet \<A>" using word_well_def_snoc by metis
  thus ?case
  proof(cases "\<exists> run . run_well_defined run \<A> word")
    case True
    have well_def: "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
    have DFA: "DFA_property (upper_part_pure \<A>)" using assms DFA_property_upper_part_pure by fast
    have alpha: "alphabet (upper_part_pure \<A>) = alphabet \<A>" unfolding upper_part_pure_def by auto
    then obtain Run2 where Run2: "run_well_defined Run2 (upper_part_pure \<A>) (word @ [a])" using exists_only_one_run_for_DFA well_def DFA snoc by metis
    show ?thesis
    proof (cases "last Run2 = []")
      case True thus ?thesis using Run2 by blast
    next
      case False
      have "last Run2 \<in> states (upper_part_pure \<A>)" using Run2 last_of_prun_is_state well_def unfolding run_well_defined_def by fast
      hence "last Run2 \<in> upper_states \<A>" using False unfolding upper_part_pure_def by simp
      hence len_pos: "1 \<le> length (last Run2) \<and> (\<forall> S_m \<in> set (last Run2) . S_m \<noteq> {})" unfolding upper_states_def by fast
      hence  "\<exists> S_m . S_m \<in> set (last Run2)" by (cases "last Run2") auto
      then obtain S_m where "S_m \<in> set (last Run2) \<and> S_m \<noteq> {}" using len_pos by blast
      hence "\<Union> (set (last Run2)) \<noteq> {}" by blast
      then obtain s where s: "s \<in> \<Union> (set (last Run2))" by blast
      have "\<forall> t \<in> \<Union> (set (last Run2)) . \<exists> r . run_well_defined r \<A> (word @ [a]) \<and> last r = t" using upper_run_reaches_all assms snoc Run2 by blast
      then obtain r where "run_well_defined r \<A> (word @ [a])" using s by fast
      hence "\<exists> r . run_well_defined r \<A> (word @ [a])" by blast
      thus ?thesis using snoc by blast
    qed
  next
    case False
    hence "\<exists> Run . run_well_defined Run (upper_part_pure \<A>) word \<and> last Run = []" using snoc word_well by blast
    then obtain Run where Run: "run_well_defined Run (upper_part_pure \<A>) word \<and> last Run = []" by blast
    hence "(last Run, a, []) \<in> transitions (upper_part_pure \<A>)" using word_well unfolding upper_part_pure_def by simp
    hence Run': "run_well_defined (Run @ [[]]) (upper_part_pure \<A>) (word @ [a])" using Run prun_well_defined_extension_snoc unfolding run_well_defined_def by fast
    have "last (Run @ [[]]) = []" by auto
    thus ?thesis using Run' by fast
  qed
qed

lemma last_not_empty_run:
  assumes "auto_well_defined \<A>" "run_well_defined r \<A> word" "run_well_defined Run (upper_part_pure \<A>) word"
  shows "last Run \<noteq> []"
proof - 
  obtain Run' where Run': "run_well_defined Run' (upper_part_pure \<A>) word \<and> (last r) \<in> \<Union> (set (last Run'))" using assms run_on_upper_last by metis
  have well_def: "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
  have DFA: "DFA_property (upper_part_pure \<A>)" using assms DFA_property_upper_part_pure by blast
  have word: "word_well_defined word (alphabet (upper_part_pure \<A>))" using well_def well_def_implies_word_well_defined Run' unfolding run_well_defined_def by fast
  hence "Run = Run'" using assms exists_only_one_run_for_DFA well_def DFA word Run' by fast
  hence "last r \<in> \<Union> (set (last Run))" using Run' by argo
  hence "last Run \<noteq> []" by auto
  thus ?thesis by blast
qed

proposition not_empty_run:
  assumes "auto_well_defined \<A>" "run_well_defined r \<A> word" "run_well_defined Run (upper_part_pure \<A>) word"
  shows "\<forall> n < length Run . Run ! n \<noteq> []"
proof -
  have not_empty: "Run \<noteq> []" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  {
    fix n assume n: "n < length Run"
    have "Run ! n \<noteq> []"
    proof(rule ccontr)
      assume "\<not> Run ! n \<noteq> []"
      hence empty: "Run ! n = []" by blast
      {
        fix m assume assm: "n \<le> m \<and> m < length Run"
        hence "Run ! m = []"
        proof (induction m)
          case 0 thus ?case using empty n by blast
        next
          case (Suc m) thus ?case
          proof (cases "n \<le> m")
            case True
            hence ih: "Run ! m = []" using Suc by linarith
            have "(Run ! m, word ! m, Run ! Suc m) \<in> transitions (upper_part_pure \<A>)" using Suc assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
            thus ?thesis using ih unfolding upper_part_pure_def upper_transitions_def by auto
          next
            case False
            hence "n = Suc m" using Suc by simp
            thus ?thesis using empty by blast
          qed
        qed
      }
      hence prop_empty: "\<forall> m . n \<le> m \<and> m < length Run \<longrightarrow> Run ! m = []" by blast
      hence "Run ! (length Run - 1) = []" using n less_eq_Suc_le by force
      hence "last Run = []" using not_empty list_properties_not_empty by metis
      thus False using last_not_empty_run assms by blast
    qed
  }
  thus ?thesis by blast
qed

proposition no_run_means_accepting_run_on_upper_part_pure:
  assumes "auto_well_defined \<A>" "\<nexists> omega_run . omega_run_well_defined omega_run \<A> omega_word" "omega_word_well_defined omega_word (alphabet \<A>)"
  shows "omega_word \<in> omega_language_auto (upper_part_pure \<A>)"
proof -
  have "\<not> (\<forall> n . \<exists> run . run_well_defined run \<A> (pre_omega_word omega_word (Suc n)))" using omega_run_exists_if_all_prefix_runs assms unfolding omega_greedy_run_def by blast
  then obtain n where no_run: "\<nexists> run . run_well_defined run \<A> (pre_omega_word omega_word (Suc n))" by blast
  have "word_well_defined (pre_omega_word omega_word (Suc n)) (alphabet \<A>)" using assms unfolding omega_word_well_defined_def word_well_defined_def pre_omega_word_def by auto
  then obtain Run where Run: "run_well_defined Run (upper_part_pure \<A>) (pre_omega_word omega_word (Suc n)) \<and> last Run = []" using no_run_on_upper assms no_run by blast
  hence not_empty: "Run \<noteq> [] \<and> length Run = (Suc n) + 1" using pre_omega_word_length unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  define omega_Run where "omega_Run = merge_lists_fun Run (\<lambda>n . [])"
  have well_def: "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by auto
  have "omega_Run 0 = Run ! 0" using not_empty unfolding merge_lists_fun_def omega_Run_def by auto
  hence init: "omega_Run 0 = initial_state (upper_part_pure \<A>) \<and> initial_state (upper_part_pure \<A>) \<in> states (upper_part_pure \<A>)" using Run unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  {
    fix i
    consider "i < Suc n" | "i = Suc n" | "i > Suc n" by linarith
    hence "(omega_Run i, omega_word i, omega_Run (i + 1)) \<in> transitions (upper_part_pure \<A>)"
    proof cases
      case 1
      hence trans: "(Run ! i, (pre_omega_word omega_word (Suc n)) ! i, Run ! (i + 1)) \<in> transitions (upper_part_pure \<A>)" using Run not_empty unfolding run_well_defined_def pseudo_run_well_defined_def by force
      have i: "omega_Run i = Run ! i" using 1 not_empty unfolding merge_lists_fun_def omega_Run_def by auto
      have Suci: "omega_Run (i + 1) = Run ! (i + 1)" using 1 not_empty unfolding merge_lists_fun_def omega_Run_def by simp
      have "omega_word i = (pre_omega_word omega_word (Suc n)) ! i" using 1 by (simp add: pre_omega_word_nth)
      thus ?thesis using i Suci trans by simp
    next
      case 2
      hence "omega_Run i = Run ! i" using not_empty unfolding merge_lists_fun_def omega_Run_def by auto
      hence i: "omega_Run i = []" using 2 not_empty list_properties_not_empty Run by fastforce
      have Suci: "omega_Run (i + 1) = []" using 2 not_empty unfolding merge_lists_fun_def omega_Run_def by simp
      have "omega_word i \<in> alphabet \<A>" using assms unfolding omega_word_well_defined_def by blast
      thus ?thesis using i Suci unfolding upper_part_pure_def by force
    next
      case 3
      hence i: "omega_Run i = []" using not_empty unfolding merge_lists_fun_def omega_Run_def by auto
      have Suci: "omega_Run (i + 1) = []" using 3 not_empty unfolding merge_lists_fun_def omega_Run_def by simp
      have "omega_word i \<in> alphabet \<A>" using assms unfolding omega_word_well_defined_def by blast
      thus ?thesis using i Suci unfolding upper_part_pure_def by simp
    qed
  }
  hence "\<forall> n . (omega_Run n, omega_word n, omega_Run (n + 1)) \<in> transitions (upper_part_pure \<A>)" by blast
  hence omega_run: "omega_run_well_defined omega_Run (upper_part_pure \<A>) omega_word" using init unfolding omega_pseudo_run_well_defined_def omega_run_well_defined_def by blast
  {
    fix i
    have ge: "i + (Suc n) + 1 > i"  by simp
    have "omega_Run (i + (Suc n) + 1) = []" using not_empty unfolding merge_lists_fun_def omega_Run_def by simp
    hence "omega_Run (i + (Suc n) + 1) \<in> accepting_states (upper_part_pure \<A>)" unfolding upper_part_pure_def by force
    hence "\<exists> N > i . omega_Run N \<in> accepting_states (upper_part_pure \<A>)" using ge by blast
  }
  hence "\<forall> i . \<exists> N > i . omega_Run N \<in> accepting_states (upper_part_pure \<A>)" by blast
  thus ?thesis using omega_run unfolding omega_run_accepting_def omega_language_auto_def by blast
qed

lemma exists_max_index:
  assumes "\<exists> k \<le> (n :: nat) . P k"
  shows "\<exists> m \<le> n . P m \<and> (\<forall> k . m < k \<and> k \<le> n \<longrightarrow> \<not> P k)"
proof -
  define S where "S = {k. k \<le> n \<and> P k}"
  have fin: "finite S" unfolding S_def by fast
  have "S \<noteq> {}" using assms unfolding S_def by blast
  then obtain m where m: "m \<in> S \<and> (\<forall> k \<in> S . k \<le> m)" using fin eq_Max_iff by metis
  hence props: "m \<le> n \<and> P m" unfolding S_def by auto
  {
    fix k assume assm: "m < k \<and> k \<le> n"
    hence "k \<notin> S" using m unfolding S_def by auto
    hence "\<not> P k" unfolding S_def using assm by blast
  }
  hence "\<forall> k . m < k \<and> k \<le> n \<longrightarrow> \<not> P k" by auto
  thus ?thesis using m props by blast
qed

definition stolen_at :: "('s, 'a) automaton \<Rightarrow> 's run \<Rightarrow> ('s states list) run \<Rightarrow> 'a word \<Rightarrow> nat \<Rightarrow> bool" where "stolen_at \<A> run Run word k = (\<exists> m n . m < n \<and> m < length (Run ! k) \<and> n < length (Run ! k) \<and> run ! k \<in> (Run ! k) ! m \<and> run ! (Suc k) \<in> post_set \<A> ((Run ! k) ! n) (word ! k))"

lemma stolen_at_lower_place:
  assumes "k < length run - 1" "stolen_at \<A> (run @ [s]) (Run @ [S]) (word @ [a]) k" "length run = length Run" "length run = length word + 1"
  shows "stolen_at \<A> run Run word k"
proof -
  obtain m n where mn: "m < n \<and> m < length ((Run @ [S]) ! k) \<and> n < length ((Run @ [S]) ! k) \<and> (run @ [s]) ! k \<in> ((Run @ [S]) ! k) ! m \<and> (run @ [s]) ! (Suc k) \<in> post_set \<A> (((Run @ [S]) ! k) ! n) ((word @ [a]) ! k)" using assms unfolding stolen_at_def by blast
  have "run ! k = (run @ [s]) ! k \<and> Run ! k = (Run @ [S]) ! k \<and> word ! k = (word @ [a]) ! k" using assms list_properties_length add_diff_cancel_right' by metis
  thus ?thesis using mn Suc_eq_plus1 assms less_diff_conv nth_append unfolding stolen_at_def by metis
qed

lemma stolen_at_lower_place_iff:
  assumes "k < length run - 1" "length run = length Run" "length run = length word + 1"
  shows "stolen_at \<A> (run @ [s]) (Run @ [S]) (word @ [a]) k \<longleftrightarrow> stolen_at \<A> run Run word k"
proof -
  have left: "stolen_at \<A> (run @ [s]) (Run @ [S]) (word @ [a]) k \<Longrightarrow> stolen_at \<A> run Run word k" using assms stolen_at_lower_place by fast
  {
    assume "stolen_at \<A> run Run word k"
    then obtain m n where mn: "m < n \<and> m < length (Run ! k) \<and> n < length (Run ! k) \<and> run ! k \<in> (Run ! k) ! m \<and>run ! Suc k \<in> post_set \<A> ((Run ! k) ! n) (word ! k)" unfolding stolen_at_def by blast
    have nths: "(run @ [s]) ! k = run ! k \<and> (Run @ [S]) ! k = Run ! k \<and> (word @ [a]) ! k = word ! k \<and> (run @ [s]) ! Suc k = run ! Suc k" using assms list_properties_length Suc_eq_plus1 diff_add_inverse2 by metis
    hence "stolen_at \<A> (run @ [s]) (Run @ [S]) (word @ [a]) k" using mn nths unfolding stolen_at_def by auto
  }
  thus ?thesis using left by blast
qed

lemma unique_component_upper_state:
  assumes "p \<in> upper_states \<A>" "i < length p" "j < length p" "x \<in> p ! i" "x \<in> p ! j"
  shows "i = j"
proof (rule ccontr)
  assume "i \<noteq> j"
  then consider "i < j" | "j < i" by linarith
  thus False
  proof cases
    case 1 thus False using assms lemma_3_4_8 by blast
  next
    case 2 thus False using assms lemma_3_4_8 by blast
  qed
qed

proposition existence_of_run_without_stealing:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined run \<A> word \<and> run_well_defined Run (upper_part_pure \<A>) word \<and> (\<exists> k < length run - 1 . stolen_at \<A> run Run word k) \<Longrightarrow> \<exists> run' . run_well_defined run' \<A> word \<and> last run = last run' \<and> (\<nexists> k . k < length run' - 1 \<and> stolen_at \<A> run' Run word k)"
proof(induction word arbitrary: run Run rule: rev_induct)
  case Nil
  hence list1: "run = [initial_state \<A>]" using list_with_one_element unfolding run_well_defined_def pseudo_run_well_defined_def greedy_run_def by force
  have "Run = [initial_state (upper_part_pure \<A>)]" using Nil list_with_one_element unfolding run_well_defined_def pseudo_run_well_defined_def by fastforce  
  hence Run: "Run = [[{initial_state \<A>}]]" unfolding upper_part_pure_def by simp
  {
    fix k assume "k < length run - 1"
    hence "k < 0" using list1 by simp
  }
  thus ?case using Nil by blast
next
  case (snoc a word)
  hence run_ge_1: "length run > 1" unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence "\<forall> k . (k < length run - 1 \<longleftrightarrow> k \<le> length run - 2)" by auto
  hence "\<exists> m \<le> length run - 2 . stolen_at \<A> run Run (word @ [a]) m \<and> (\<forall> k . m < k \<and> k \<le> length run - 2 \<longrightarrow> \<not> stolen_at \<A> run Run (word @ [a]) k)" using exists_max_index snoc by presburger 
  then obtain m where m: "m \<le> length run - 2 \<and> stolen_at \<A> run Run (word @ [a]) m \<and> (\<forall> k . m < k \<and> k \<le> length run - 2 \<longrightarrow> \<not> stolen_at \<A> run Run (word @ [a]) k)" by presburger
  then consider (case1) "m < length run - 2" | (case2) "m = length run - 2" by linarith
  thus ?case
  proof cases
    case case1
    hence not_empty: "Run \<noteq> [] \<and> run \<noteq> []" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by force
    then obtain Run' run' where var: "Run = Run' @ [last Run] \<and> run = run' @ [last run]" using append_butlast_last_id by metis
    hence runs': "run_well_defined Run' (upper_part_pure \<A>) word \<and> run_well_defined run' \<A> word \<and> (last run', a, last run) \<in> transitions \<A>" using snoc prun_well_defined_extension_snoc unfolding run_well_defined_def by metis
    hence length: "length run' = length Run' \<and> length run' = length word + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by argo
    have "m < length (run' @ [last run]) - 2" using case1 var by argo
    hence "m < length run' + 1 - 2" by simp
    hence m': "m < length run' - 1" by simp
    hence "stolen_at \<A> run' Run' word m" using m stolen_at_lower_place var length by metis
    hence "\<exists> k < length run' - 1 . stolen_at \<A> run' Run' word k" using m' by blast
    then obtain run'' where run'': "run_well_defined run'' \<A> word \<and> last run' = last run'' \<and> (\<nexists> k . k < length run'' - 1 \<and> stolen_at \<A> run'' Run' word k)" using runs' m' snoc by blast
    hence well_def: "run_well_defined (run'' @ [last run]) \<A> (word @ [a])" using runs' prun_well_defined_extension_snoc unfolding run_well_defined_def by metis
    hence len: "length run'' = length Run' \<and> length run'' = length word + 1" using length unfolding run_well_defined_def pseudo_run_well_defined_def by force
    have no_steal_prefix: "\<nexists> k . k < length run'' - 1 \<and> stolen_at \<A> run'' Run' word k" using run'' by blast
    have "\<nexists> k . k < length (run'' @ [last run]) - 1 \<and> stolen_at \<A> (run'' @ [last run]) (Run' @ [last Run]) (word @ [a]) k"
    proof(rule ccontr)
      assume "\<not> (\<nexists> k . k < length (run'' @ [last run]) - 1 \<and> stolen_at \<A> (run'' @ [last run]) (Run' @ [last Run]) (word @ [a]) k)"
      hence "\<exists> k . k < length (run'' @ [last run]) - 1 \<and> stolen_at \<A> (run'' @ [last run]) (Run' @ [last Run]) (word @ [a]) k" by blast
      then obtain k where k: "k < length (run'' @ [last run]) - 1 \<and> stolen_at \<A> (run'' @ [last run]) (Run' @ [last Run]) (word @ [a]) k" by blast
      then consider (old) "k < length run'' - 1" | (last) "k = length run'' - 1" by fastforce
      thus False
      proof cases
        case old
        hence "stolen_at \<A> run'' Run' word k" using stolen_at_lower_place_iff len no_steal_prefix k by fast
        thus ?thesis using run'' old by blast
      next
        case last
        have "length run = length (word @ [a]) + 1" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by blast
        hence le: "k = length run - 2" using last len by force
        have last_index: "k = length run'' - 1" using last by blast
        {
          assume st: "stolen_at \<A> (run'' @ [last run]) (Run' @ [last Run]) (word @ [a]) (length run'' - 1)"
          then obtain p q where pq: "p < q \<and> p < length ((Run' @ [last Run]) ! (length run'' - 1)) \<and> q < length ((Run' @ [last Run]) ! (length run'' - 1)) \<and> (run'' @ [last run]) ! (length run'' - 1) \<in> ((Run' @ [last Run]) ! (length run'' - 1)) ! p \<and> (run'' @ [last run]) ! Suc (length run'' - 1) \<in> post_set \<A> (((Run' @ [last Run]) ! (length run'' - 1)) ! q) ((word @ [a]) ! (length run'' - 1))" unfolding stolen_at_def by blast
          have "length run'' - 1 < length Run'" using len by auto
          hence idx1: "(Run' @ [last Run]) ! (length run'' - 1) = Run' ! (length run'' - 1)" using list_properties_length by metis
          have run''_not_empty: "length run'' - 1 < length run'' \<and> run'' \<noteq> []"  using len by auto
          hence "(run'' @ [last run]) ! (length run'' - 1) = run'' ! (length run'' - 1) \<and> run'' \<noteq> []" using list_properties_length by metis
          hence idx2: "(run'' @ [last run]) ! (length run'' - 1) = last run''" using list_properties_not_empty by fast
          have "Suc (length run'' - 1) = length (run'' @ [last run]) - 1"  using len by force
          hence idx3: "(run'' @ [last run]) ! Suc (length run'' - 1) = last run" using list_properties_not_empty by force
          have idx4: "(word @ [a]) ! (length run'' - 1) = a" using diff_add_inverse2 len nth_append_length by metis
          hence props: "p < q \<and> p < length (Run' ! (length run'' - 1)) \<and> q < length (Run' ! (length run'' - 1)) \<and> last run' \<in> (Run' ! (length run'' - 1)) ! p \<and> last run \<in> post_set \<A> (Run' ! (length run'' - 1) ! q) a" using pq idx1 idx2 idx3 idx4 run'' by argo
          have len_eq: "length run' = length run'' \<and> run' \<noteq> []" using len length by force
          hence idx_run'1: "(run' @ [last run]) ! (length run'' - 1) = last run'" using list_properties_not_empty by metis
          have "Suc (length run'' - 1) = length run'" using len_eq run''_not_empty by force
          hence idx_run'2: "(run' @ [last run]) ! Suc (length run'' - 1) = last run" by auto
          have idx_Run': "((Run' @ [last Run]) ! (length run'' - 1)) = Run' ! (length run'' - 1)" using idx1 by simp
          have "((word @ [a]) ! (length run'' - 1)) = a" using idx4 by simp
          hence stolen: "stolen_at \<A> (run' @ [last run]) (Run' @ [last Run]) (word @ [a]) (length run'' - 1)" using props idx_run'1 idx_run'2 idx_Run' unfolding stolen_at_def by auto
          have "length run'' - 1 = length run - 2" using last_index le by blast
          hence steal_last_old: "stolen_at \<A> run Run (word @ [a]) (length run - 2)" using var run'' runs' length stolen unfolding stolen_at_def by presburger
          have "\<not> stolen_at \<A> run Run (word @ [a]) (length run - 2)" using m case1 by blast
          hence False using steal_last_old by blast
        }
        thus ?thesis using k last_index by blast
      qed
    qed
    hence "\<nexists> k . k < length (run'' @ [last run]) - 1 \<and>  stolen_at \<A> (run'' @ [last run]) Run (word @ [a]) k" using var by simp
    thus ?thesis using well_def by auto
  next
    case case2
    hence not_empty: "Run \<noteq> [] \<and> run \<noteq> []" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by force
    then obtain Run' run' where var: "Run = Run' @ [last Run] \<and> run = run' @ [last run]" using append_butlast_last_id by metis
    hence runs': "run_well_defined Run' (upper_part_pure \<A>) word \<and> run_well_defined run' \<A> word \<and> (last run', a, last run) \<in> transitions \<A>" using snoc prun_well_defined_extension_snoc unfolding run_well_defined_def by metis
    hence length: "length run' = length Run' \<and> length run' = length word + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by argo
    have len_run: "length run = length (word @ [a]) + 1" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by blast
    hence a: "(word @ [a]) ! (length run - 2) = a" using list_properties_not_empty by auto
    have Suc: "Suc (length run - 2) = length run - 1" using run_ge_1 by fastforce
    have "stolen_at \<A> run Run (word @ [a]) (length run - 2)" using m case2 by blast
    then obtain p q where pq: "p < q \<and> p < length (Run ! (length run - 2)) \<and> q < length (Run ! (length run - 2)) \<and> run ! (length run - 2) \<in> (Run ! (length run - 2)) ! p \<and> run ! (length run - 1) \<in> post_set \<A> ((Run ! (length run - 2)) ! q) a" using Suc a unfolding stolen_at_def by metis
    have run'_not_empty: "run' \<noteq> [] \<and> Run' \<noteq> []" using length by auto
    have idx_last: "length run - 2 = length run' - 1" using var run_ge_1 Suc_1 diff_Suc_Suc length_append_singleton by metis
    hence "length run - 2 = length Run' - 1" using length by argo
    hence equi: "Run ! (length run - 2) = Run ! (length Run' - 1)" by argo
    have "length Run' - 1 < length Run'" using run'_not_empty by simp
    hence "Run ! (length run - 2) = Run' ! (length Run' - 1)" using var list_properties_length equi by metis
    hence Run_idx: "Run ! (length run - 2) = last Run'" using run'_not_empty list_properties_not_empty by metis
    have "run ! (length run - 1) = last run" using var not_empty list_properties_not_empty by metis
    hence "\<exists> n \<le> length (last Run') - 1 . last run \<in> post_set \<A> ((last Run') ! n) a" using pq Run_idx Suc_leI diff_Suc_1 diff_le_mono by metis
    then obtain n where n: "n \<le> length (last Run') - 1 \<and> last run \<in> post_set \<A> ((last Run') ! n) a \<and> (\<forall> j . n < j \<and> j \<le> length (last Run') - 1 \<longrightarrow> last run \<notin> post_set \<A> ((last Run') ! j) a)" using exists_max_index by presburger
    then obtain s_higher where s_higher: "s_higher \<in> (last Run') ! n \<and> (s_higher, a, last run) \<in> transitions \<A>" unfolding post_set_def by blast
    have "last Run' = Run' ! (length Run' - 1)" using run'_not_empty list_properties_not_empty by metis
    hence "last Run' \<noteq> []" using assms runs' last_not_empty_run by blast
    hence "n + 1 \<le> length (last Run')" using n Nat.le_diff_conv2 leI length_0_conv less_one by metis
    hence n_less: "n < length (last Run')" by simp
    hence "s_higher \<in> \<Union> (set (last Run'))" using s_higher by fastforce
    then obtain run_higher where run_higher: "run_well_defined run_higher \<A> word \<and> last run_higher = s_higher" using upper_run_reaches_all assms runs' by blast
    consider "\<nexists> k . k < length run_higher - 1 \<and> stolen_at \<A> run_higher Run' word k" | "\<exists> k < length run_higher - 1 . stolen_at \<A> run_higher Run' word k" by blast
    hence "\<exists> run . run_well_defined run \<A> word \<and> last run = s_higher \<and> (\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run Run' word k)"
    proof cases
      case 1 thus ?thesis using run_higher by blast
    next
      case 2
      then obtain r where "run_well_defined r \<A> word \<and> last run_higher = last r \<and> (\<nexists> k . k < length r - 1 \<and> stolen_at \<A> r Run' word k)" using snoc run_higher runs' by blast
      thus ?thesis using run_higher by auto
    qed
    then obtain r_clean where r_clean: "run_well_defined r_clean \<A> word \<and> last r_clean = s_higher \<and> (\<nexists> k . k < length r_clean - 1 \<and> stolen_at \<A> r_clean Run' word k)" by blast
    hence well_def_final: "run_well_defined (r_clean @ [last run]) \<A> (word @ [a])" using s_higher runs' prun_well_defined_extension_snoc unfolding run_well_defined_def by fast
    hence "length (r_clean @ [last run]) = length (word @ [a]) + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by blast
    hence le_r: "length r_clean = length word + 1" by simp
    have last_eq_final: "last (r_clean @ [last run]) = last run"  by simp
    have no_steal_before_last: "\<nexists> k . k < length (r_clean @ [last run]) - 1 \<and> k < length r_clean - 1 \<and> stolen_at \<A> (r_clean @ [last run]) (Run' @ [last Run]) (word @ [a]) k"
    proof(rule ccontr)
      assume " \<not> (\<nexists> k . k < length (r_clean @ [last run]) - 1 \<and> k < length r_clean - 1 \<and> stolen_at \<A> (r_clean @ [last run]) (Run' @ [last Run]) (word @ [a]) k)"
      hence "\<exists> k . k < length (r_clean @ [last run]) - 1 \<and> k < length r_clean - 1 \<and> stolen_at \<A> (r_clean @ [last run]) (Run' @ [last Run]) (word @ [a]) k" by blast
      then obtain k where k: "k < length (r_clean @ [last run]) - 1 \<and> k < length r_clean - 1 \<and> stolen_at \<A> (r_clean @ [last run]) (Run' @ [last Run]) (word @ [a]) k" by blast
      hence "stolen_at \<A> r_clean Run' word k" using stolen_at_lower_place_iff r_clean le_r length by metis
      thus False using r_clean k by blast
    qed
    have not_stolen: "\<not> stolen_at \<A> (r_clean @ [last run]) (Run' @ [last Run]) (word @ [a]) (length r_clean - 1)"
    proof(rule ccontr)
      assume "\<not> \<not> stolen_at \<A> (r_clean @ [last run]) (Run' @ [last Run]) (word @ [a]) (length r_clean - 1)"
      hence "stolen_at \<A> (r_clean @ [last run]) (Run' @ [last Run]) (word @ [a]) (length r_clean - 1)" by blast
      then obtain p j where pj: "p < j \<and> p < length ((Run' @ [last Run]) ! (length r_clean - 1)) \<and> j < length ((Run' @ [last Run]) ! (length r_clean - 1)) \<and> (r_clean @ [last run]) ! (length r_clean - 1) \<in> ((Run' @ [last Run]) ! (length r_clean - 1)) ! p \<and> (r_clean @ [last run]) ! Suc (length r_clean - 1) \<in> post_set \<A> (((Run' @ [last Run]) ! (length r_clean - 1)) ! j) ((word @ [a]) ! (length r_clean - 1))" unfolding stolen_at_def by blast
      have rc_not_empty: "r_clean \<noteq> [] \<and> Run' \<noteq> []" using le_r run'_not_empty by auto
      have length_clean: "length run - 2 = length r_clean - 1" using idx_last le_r length by argo
      hence idxR: "((Run' @ [last Run]) ! (length r_clean - 1)) = last Run'" using Run_idx var by argo
      have idxr1: "(r_clean @ [last run]) ! (length r_clean - 1) = last r_clean" using rc_not_empty list_properties_not_empty by fast
      have idxr2: "(r_clean @ [last run]) ! Suc (length r_clean - 1) = last run" using Suc_eq_plus1 diff_add_inverse2 le_r nth_append_length by metis
      have "((word @ [a]) ! (length r_clean - 1)) = a" using nth_append_length length_clean a by argo
      hence last_post: "last run \<in> post_set \<A> ((last Run') ! j) a" using pj idxR idxr2 by argo
      have "last r_clean = s_higher" using r_clean by blast
      hence in_n: "last r_clean \<in> (last Run') ! n" using s_higher by blast
      have in_p: "last r_clean \<in> (last Run') ! p" using pj idxR idxr1 by auto
      have "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
      hence "last Run' \<in> states (upper_part_pure \<A>)" using runs' last_of_prun_is_state unfolding run_well_defined_def by fast
      hence lastRun'_upper: "last Run' \<in> upper_states \<A>" using assms runs' last_not_empty_run unfolding upper_part_pure_def by auto
      have "p < length (last Run')" using pj idxR by argo
      hence "n = p" using unique_component_upper_state lastRun'_upper n_less in_n in_p by metis
      hence "n < j \<and> j \<le> length (last Run') - 1" using pj idxR by force
      thus False using n last_post by blast
    qed
    have "\<nexists> k . k < length (r_clean @ [last run]) - 1 \<and> stolen_at \<A> (r_clean @ [last run]) (Run' @ [last Run]) (word @ [a]) k"
    proof(rule ccontr)
      assume "\<not> (\<nexists> k . k < length (r_clean @ [last run]) - 1 \<and> stolen_at \<A> (r_clean @ [last run]) (Run' @ [last Run]) (word @ [a]) k)"
      hence "\<exists> k . k < length (r_clean @ [last run]) - 1 \<and> stolen_at \<A> (r_clean @ [last run]) (Run' @ [last Run]) (word @ [a]) k" by blast
      then obtain k where k: "k < length (r_clean @ [last run]) - 1 \<and> stolen_at \<A> (r_clean @ [last run]) (Run' @ [last Run]) (word @ [a]) k" by blast
      then consider "k < length r_clean - 1" | "k = length r_clean - 1" by fastforce
      thus False
      proof cases
        case 1 thus False using no_steal_before_last k by blast
      next
        case 2 thus False using k not_stolen by blast
      qed
    qed
    hence "\<nexists> k . k < length (r_clean @ [last run]) - 1 \<and> stolen_at \<A> (r_clean @ [last run]) Run (word @ [a]) k" using var by simp
    thus ?thesis using well_def_final last_eq_final by metis
  qed
qed

corollary existence_of_run_without_stealing_cor:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word" "run_well_defined Run (upper_part_pure \<A>) word"
  shows "\<exists> run' . run_well_defined run' \<A> word \<and> last run = last run' \<and> (\<nexists> k . k < length run' - 1 \<and> stolen_at \<A> run' Run word k)"
proof(cases "\<exists> k < length run - 1 . stolen_at \<A> run Run word k")
  case True thus ?thesis using assms existence_of_run_without_stealing by blast
next
  case False thus ?thesis using assms by blast
qed

lemma no_steal_implies_not_in_right_snd:
  assumes "run_well_defined run \<A> word" "run_well_defined Run (upper_part_pure \<A>) word" "i < length word" "m < length (Run ! i)" "run ! i \<in> (Run ! i) ! m" "\<not> stolen_at \<A> run Run word i"
  shows "run ! Suc i \<in> post_set \<A> ((Run ! i) ! m) (word ! i) \<and> run ! Suc i \<notin> snd (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))"
proof -
  have "(run ! i, word ! i, run ! Suc i) \<in> transitions \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "run ! Suc i \<in> post_set \<A> ((Run ! i) ! m) (word ! i)" using assms unfolding post_set_def by blast
  hence first: "run ! Suc i \<in> post_set \<A> ((Run ! i) ! m) (word ! i)" by blast
  have "run ! Suc i \<notin> snd (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))"
  proof(rule ccontr)
    assume "\<not> run ! Suc i \<notin> snd (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))"
    hence h: "run ! Suc i \<in> snd (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))" by blast
    have "snd (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))) = post_set \<A> (\<Union> (set (drop (Suc m) (Run ! i)))) (word ! i)" using snd_upper_step_eq_post_set_Union by fast
    hence "run ! Suc i \<in> post_set \<A> (\<Union> (set (drop (Suc m) (Run ! i)))) (word ! i)" using h by blast
    then obtain s where s: "s \<in> \<Union> (set (drop (Suc m) (Run ! i))) \<and> (s, word ! i, run ! Suc i) \<in> transitions \<A>" unfolding post_set_def by blast
    then obtain n where n: "n < length (drop (Suc m) (Run ! i)) \<and> s \<in> drop (Suc m) (Run ! i) ! n" using UnionE maximal_index_for_element by metis
    hence idx: "m < Suc m + n \<and> Suc m + n < length (Run ! i) \<and> s \<in> (Run ! i) ! (Suc m + n)" using assms by force
    hence "run ! Suc i \<in> post_set \<A> ((Run ! i) ! (Suc m + n)) (word ! i)" using s unfolding post_set_def by blast
    hence "m < Suc m + n \<and> m < length (Run ! i) \<and> Suc m + n < length (Run ! i) \<and> run ! i \<in> Run ! i ! m \<and> run ! Suc i \<in> post_set \<A> ((Run ! i) ! (Suc m + n)) (word ! i)" using idx assms by blast    
    hence "\<exists> m n . m < n \<and> m < length (Run ! i) \<and> n < length (Run ! i) \<and> run ! i \<in> (Run ! i) ! m \<and> run ! (Suc i) \<in> post_set \<A> ((Run ! i) ! n) (word ! i)" by blast
    hence "stolen_at \<A> run Run word i" unfolding stolen_at_def by blast
    thus False using assms by blast
  qed
  thus ?thesis using first by blast
qed

lemma right_run_succ_in_right_snd:
  assumes "run_well_defined run' \<A> word" "i < length word" "m < n" "n < length (Run ! i)" "run' ! i \<in> (Run ! i) ! n"
  shows "run' ! Suc i \<in> snd (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))"
proof -
  have "(run' ! i, word ! i, run' ! Suc i) \<in> transitions \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence post_n: "run' ! Suc i \<in> post_set \<A> ((Run ! i) ! n) (word ! i)" using assms unfolding post_set_def by blast
  have n_drop: "n - Suc m < length (drop (Suc m) (Run ! i))" using assms by auto
  have "drop (Suc m) (Run ! i) ! (n - Suc m) = (Run ! i) ! n" using assms by force
  hence "(Run ! i) ! n \<in> set (drop (Suc m) (Run ! i))" using n_drop nth_mem by metis
  hence "run' ! Suc i \<in> post_set \<A> (\<Union> (set (drop (Suc m) (Run ! i)))) (word ! i)" using post_n unfolding post_set_def by blast
  thus ?thesis using snd_upper_step_eq_post_set_Union by fast
qed

lemma no_steal_succ_in_head_pair:
  assumes "run_well_defined run \<A> word" "run_well_defined Run (upper_part_pure \<A>) word" "i < length word" "m < length (Run ! i)" "run ! i \<in> (Run ! i) ! m" "\<not> stolen_at \<A> run Run word i"
  defines "R \<equiv> snd (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))"
  defines "L \<equiv> (post_set \<A> ((Run ! i) ! m) (word ! i) - R) - accepting_states \<A>"
  defines "A \<equiv> (post_set \<A> ((Run ! i) ! m) (word ! i) - R) \<inter> accepting_states \<A>"
  shows "run ! Suc i \<in> L \<union> A"
proof -
  have "run ! Suc i \<in> post_set \<A> ((Run ! i) ! m) (word ! i) \<and> run ! Suc i \<notin> R" using no_steal_implies_not_in_right_snd assms unfolding R_def by fast
  thus ?thesis unfolding L_def A_def by blast
qed

lemma filter_head_pair_before_tail:
  assumes "x \<in> L \<union> A" "y \<in> \<Union> (set (fst (upper_step \<A> a T)))" "L \<noteq> {} \<or> A \<noteq> {}"
  shows "\<exists> p q . p < q \<and> p < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) \<and> q < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) \<and> x \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) ! p \<and> y \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) ! q"
proof -
  consider (Lcase) "x \<in> L" | (Acase) "x \<in> A" using assms by blast
  thus ?thesis
  proof cases
    case Lcase
    have "y \<in> \<Union> (set (filter (\<lambda>X . X \<noteq> {}) (A # fst (upper_step \<A> a T))))" using assms Union_filter_nonempty[of "A # fst (upper_step \<A> a T)"] by simp
    then obtain q where q: "q < length (filter (\<lambda>X . X \<noteq> {}) (A # fst (upper_step \<A> a T))) \<and> y \<in> (filter (\<lambda>X . X \<noteq> {}) (A # fst (upper_step \<A> a T))) ! q" using maximal_index_for_element by fast
    have p0: "0 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) \<and> x \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) ! 0" using Lcase by auto
    have "Suc q < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) \<and>  y \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) ! Suc q" using q Lcase by force
    thus ?thesis using p0 by blast
   next
    case Acase
    have "y \<in> \<Union> (set (filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> a T))))" using assms Union_filter_nonempty[of "fst (upper_step \<A> a T)"] by simp
    then obtain q where q: "q < length (filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> a T))) \<and> y \<in> (filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> a T))) ! q" using maximal_index_for_element by fast
    thus ?thesis
    proof (cases "L = {}")
      case True
      have px: "0 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) \<and> x \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) ! 0" using Acase assms True by simp
      have "Suc q < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) \<and> y \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) ! Suc q" using q True Acase by force
      thus ?thesis using px by blast
    next
      case False
      have px: "1 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) \<and> x \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) ! 1" using Acase False by force
      have qy: "Suc (Suc q) < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) \<and> y \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> a T))) ! Suc (Suc q)" using q False Acase by force
      have "1 < Suc (Suc q)" by simp
      thus ?thesis using px qy by blast
    qed
  qed
qed

lemma upper_step_fst_append: "fst (upper_step \<A> a (X @ Y)) = map (\<lambda>S_m . S_m - snd (upper_step \<A> a Y)) (fst (upper_step \<A> a X)) @ fst (upper_step \<A> a Y)"
proof (induction X)
  case Nil thus ?case by simp
next
  case (Cons x X)
  let ?SX = "snd (upper_step \<A> a X)"
  let ?FX = "fst (upper_step \<A> a X)"
  let ?SY = "snd (upper_step \<A> a Y)"
  let ?FY = "fst (upper_step \<A> a Y)"
  have snd_split: "snd (upper_step \<A> a (X @ Y)) = ?SX \<union> ?SY" by (induction X) auto
  have "fst (upper_step \<A> a ((x # X) @ Y)) = (((post_set \<A> x a - snd (upper_step \<A> a (X @ Y))) - accepting_states \<A>) # ((post_set \<A> x a - snd (upper_step \<A> a (X @ Y))) \<inter> accepting_states \<A>) # fst (upper_step \<A> a (X @ Y)))" by simp
  have "fst (upper_step \<A> a ((x # X) @ Y)) = (((post_set \<A> x a - (?SX \<union> ?SY)) - accepting_states \<A>) # ((post_set \<A> x a - (?SX \<union> ?SY)) \<inter> accepting_states \<A>) # map (\<lambda>S_m . S_m - ?SY) ?FX @ ?FY)" using Cons snd_split by auto
  thus ?case by force
qed

lemma RunSuc_prefix_decomp:
  assumes "m < length (Run ! i)" "run_well_defined Run (upper_part_pure \<A>) word"
  defines "R \<equiv> snd (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))"
  defines "L \<equiv> (post_set \<A> ((Run ! i) ! m) (word ! i) - R) - accepting_states \<A>"
  defines "A \<equiv> (post_set \<A> ((Run ! i) ! m) (word ! i) - R) \<inter> accepting_states \<A>"
  shows "\<exists> P . filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (word ! i) (Run ! i))) = P @ filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))"
proof -
  let ?Pref = "take m (Run ! i)"
  let ?Mid = "(Run ! i) ! m"
  let ?Suf = "drop (Suc m) (Run ! i)"
  have "Run ! i = ?Pref @ [?Mid] @ ?Suf" using assms by (simp add: Cons_nth_drop_Suc) 
  hence fst_split: "fst (upper_step \<A> (word ! i) (Run ! i)) = map (\<lambda>S_m . S_m - snd (upper_step \<A> (word ! i) ([?Mid] @ ?Suf))) (fst (upper_step \<A> (word ! i) ?Pref)) @ fst (upper_step \<A> (word ! i) ([?Mid] @ ?Suf))" using upper_step_fst_append by metis
  have fst_mid: "fst (upper_step \<A> (word ! i) ([?Mid] @ ?Suf)) = [((post_set \<A> ?Mid (word ! i) - snd (upper_step \<A> (word ! i) ?Suf)) - accepting_states \<A>), ((post_set \<A> ?Mid (word ! i) - snd (upper_step \<A> (word ! i) ?Suf)) \<inter> accepting_states \<A>)] @ fst (upper_step \<A> (word ! i) ?Suf)" by simp
  let ?P = "filter (\<lambda>X . X \<noteq> {}) (map (\<lambda>S_m . S_m - snd (upper_step \<A> (word ! i) ([?Mid] @ ?Suf))) (fst (upper_step \<A> (word ! i) ?Pref)))"
  have "filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (word ! i) (Run ! i))) = filter (\<lambda>X . X \<noteq> {}) (map (\<lambda>S_m . S_m - snd (upper_step \<A> (word ! i) ([?Mid] @ ?Suf))) (fst (upper_step \<A> (word ! i) ?Pref)) @ fst (upper_step \<A> (word ! i) ([?Mid] @ ?Suf)))" using fst_split by simp
  hence filter: "filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (word ! i) (Run ! i))) = ?P @ filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (word ! i) ([?Mid] @ ?Suf)))" by force
  have "R = snd (upper_step \<A> (word ! i) ?Suf)" using assms by simp
  hence "[((post_set \<A> ?Mid (word ! i) - snd (upper_step \<A> (word ! i) ?Suf)) - accepting_states \<A>),((post_set \<A> ?Mid (word ! i) - snd (upper_step \<A> (word ! i) ?Suf)) \<inter> accepting_states \<A>)] = [L, A]" using assms by argo
  hence "fst (upper_step \<A> (word ! i) ([?Mid] @ ?Suf)) = [L, A] @ fst (upper_step \<A> (word ! i) ?Suf)" using fst_mid by simp
  hence "filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (word ! i) (Run ! i))) = ?P @ filter (\<lambda>X . X \<noteq> {}) ([L, A] @ fst (upper_step \<A> (word ! i) ?Suf))" using filter by argo
  thus ?thesis by force
qed

lemma no_steal_preserves_left_order:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word" "run_well_defined run' \<A> word" "run_well_defined Run (upper_part_pure \<A>) word" "i < length word" "m < n" "m < length (Run ! i)" "n < length (Run ! i)" "run ! i \<in> (Run ! i) ! m" "run' ! i \<in> (Run ! i) ! n" "\<not> stolen_at \<A> run Run word i" "run ! Suc i \<in> (Run ! Suc i) ! m'" "run' ! Suc i \<in> (Run ! Suc i) ! n'" "m' < length (Run ! Suc i)" "n' < length (Run ! Suc i)"
  shows "m' < n'"
proof (rule ccontr)
  assume "\<not> m' < n'"
  hence ge: "n' \<le> m'" using assms by linarith
  define R where "R = snd (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))"
  define L where "L = (post_set \<A> ((Run ! i) ! m) (word ! i) - R) - accepting_states \<A>"
  define A where "A = (post_set \<A> ((Run ! i) ! m) (word ! i) - R) \<inter> accepting_states \<A>"
  have left_head: "run ! Suc i \<in> L \<union> A" using no_steal_succ_in_head_pair assms unfolding A_def L_def R_def  by blast
  have right_tail: "run' ! Suc i \<in> R" using right_run_succ_in_right_snd assms unfolding R_def by blast
  have RunSuc_nonempty: "Run ! Suc i \<noteq> []" using assms by force
  have trans_Run: "(Run ! i, word ! i, Run ! Suc i) \<in> transitions (upper_part_pure \<A>)" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence RunSuc_eq: "Run ! Suc i = filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (word ! i) (Run ! i)))" using RunSuc_nonempty unfolding upper_part_pure_def upper_transitions_def by force
  obtain P where P: "filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (word ! i) (Run ! i))) = P @ filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))" using RunSuc_prefix_decomp assms unfolding R_def L_def A_def by blast
  have right_tail_union: "run' ! Suc i \<in> \<Union> (set (fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))))" using right_tail Union_fst_upper_step_eq_snd unfolding R_def by fast
  have nz: "L \<noteq> {} \<or> A \<noteq> {}" using left_head by blast
  obtain p q where pq: "p < q \<and> p < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> q < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> run ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! p \<and> run' ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! q" using filter_head_pair_before_tail[OF left_head right_tail_union nz] by blast
  hence run_suc_in_big: "run ! Suc i \<in> (P @ filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! (length P + p)"by auto
  have run'_suc_in_big: "run' ! Suc i \<in> (P @ filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! (length P + q)" using pq by simp
  have pq_len: "length P + p < length (Run ! Suc i) \<and> length P + q < length (Run ! Suc i)" using pq P RunSuc_eq by force
  have pq_order: "length P + p < length P + q" using pq by linarith
  have "(Run ! i, word ! i, Run ! Suc i) \<in> upper_transitions \<A>" using trans_Run RunSuc_nonempty unfolding upper_part_pure_def by simp
  hence RunSuc_upper: "Run ! Suc i \<in> upper_states \<A>" using assms upper_transitions_target_in_upper_states by fast  
  hence mm': "m' = length P + p" using unique_component_upper_state assms pq_len run_suc_in_big P RunSuc_eq by metis
  have "n' = length P + q" using unique_component_upper_state RunSuc_upper assms pq_len run'_suc_in_big P RunSuc_eq by metis
  hence "m' < n'" using pq_order mm' by blast
  thus False using ge by auto
qed

lemma run_state_in_upper_component:
  assumes "auto_well_defined \<A>" "run_well_defined run \<A> word" "run_well_defined Run (upper_part_pure \<A>) word"
  shows "\<forall> k < length run . \<exists> i < length (Run ! k) . run ! k \<in> (Run ! k) ! i"
proof - 
  obtain Run' where Run': "run_well_defined Run' (upper_part_pure \<A>) word \<and> (\<forall> i < length run . run ! i \<in> \<Union> (set (Run' ! i)))" using assms run_on_upper by metis
  have well_def: "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
  have DFA: "DFA_property (upper_part_pure \<A>)" using assms DFA_property_upper_part_pure by blast
  have word: "word_well_defined word (alphabet (upper_part_pure \<A>))" using well_def well_def_implies_word_well_defined Run' unfolding run_well_defined_def by fast
  hence "Run = Run'" using assms exists_only_one_run_for_DFA well_def DFA word Run' by fast
  hence "\<forall> k < length run . run ! k \<in> \<Union> (set (Run ! k))" using Run' by blast
  thus ?thesis using Union_iff minimal_index_for_element by fast
qed

definition leftgap :: "'s run \<Rightarrow> 's run \<Rightarrow> ('s states list) run \<Rightarrow> nat \<Rightarrow> bool" where "leftgap run run' Run k = (\<exists> m n . m < n \<and> n < length (Run ! k) \<and> m < length (Run ! k) \<and> run ! k \<in> (Run ! k) ! m \<and> run' ! k \<in> (Run ! k) ! n)"

definition rightgap :: "'s run \<Rightarrow> 's run \<Rightarrow> ('s states list) run \<Rightarrow> nat \<Rightarrow> bool" where "rightgap run run' Run k = (\<exists> m n . n < m \<and> n < length (Run ! k) \<and> m < length (Run ! k) \<and> run ! k \<in> (Run ! k) ! m \<and> run' ! k \<in> (Run ! k) ! n)"

definition samelevel :: "'s run \<Rightarrow> 's run \<Rightarrow> ('s states list) run \<Rightarrow> nat \<Rightarrow> bool" where "samelevel run run' Run k = (\<exists> i . i < length (Run ! k) \<and> run ! k \<in> (Run ! k) ! i \<and> run' ! k \<in> (Run ! k) ! i)"

proposition leftgap_rightgap_iff: "leftgap alpha beta Run k \<longleftrightarrow> rightgap beta alpha Run k"
  unfolding leftgap_def rightgap_def by blast

lemma samelevel_nonacc_acc_step_gives_leftgap_local:
  assumes "auto_well_defined \<A>" "run_well_defined Run (upper_part_pure \<A>) word" "run_well_defined alpha \<A> word" "run_well_defined beta \<A> word" "Suc k < length alpha" "samelevel alpha beta Run k" "alpha ! Suc k \<notin> accepting_states \<A>" "beta ! Suc k \<in> accepting_states \<A>" "\<not> stolen_at \<A> alpha Run word k"
  shows "leftgap alpha beta Run (Suc k)"
proof -
  have "length alpha = length word + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  hence k_word: "k < length word" using assms by simp
  obtain i where i: "i < length (Run ! k) \<and> alpha ! k \<in> (Run ! k) ! i \<and> beta ! k \<in> (Run ! k) ! i" using assms unfolding samelevel_def by blast
  have trans_Run: "(Run ! k, word ! k, Run ! Suc k) \<in> transitions (upper_part_pure \<A>)" using assms k_word unfolding run_well_defined_def pseudo_run_well_defined_def by force
  have "(alpha ! k, word ! k, alpha ! Suc k) \<in> transitions \<A>" using assms k_word unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence alpha_post: "alpha ! Suc k \<in> post_set \<A> ((Run ! k) ! i) (word ! k)" using i unfolding post_set_def by blast
  have "(beta ! k, word ! k, beta ! Suc k) \<in> transitions \<A>" using assms k_word unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence beta_post: "beta ! Suc k \<in> post_set \<A> ((Run ! k) ! i) (word ! k)" using i unfolding post_set_def by blast
  define R where "R = snd (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k)))"
  define L where "L = (post_set \<A> ((Run ! k) ! i) (word ! k) - R) - accepting_states \<A>"
  define A where "A = (post_set \<A> ((Run ! k) ! i) (word ! k) - R) \<inter> accepting_states \<A>"
  have "alpha ! Suc k \<in> post_set \<A> ((Run ! k) ! i) (word ! k) \<and> alpha ! Suc k \<notin> snd (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k)))" using no_steal_implies_not_in_right_snd[OF assms(3) assms(2), of k i] assms i k_word by blast
  hence "alpha ! Suc k \<notin> R" unfolding R_def by blast
  hence alpha_in_L: "alpha ! Suc k \<in> L" using alpha_post assms unfolding L_def A_def by auto
  have beta_in_A_or_R: "beta ! Suc k \<in> A \<or> beta ! Suc k \<in> R" using beta_post assms unfolding A_def R_def by auto
  have RunSuc: "Run ! Suc k = filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (word ! k) (Run ! k)))" using trans_Run unfolding upper_part_pure_def upper_transitions_def by auto
  obtain P where P: "filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (word ! k) (Run ! k))) = P @ filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))" using RunSuc_prefix_decomp[where m=i and Run=Run and word=word and i=k and \<A>=\<A>] assms i unfolding R_def L_def A_def by blast
  have tail_gap: "\<exists> p q . p < q \<and> p < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))) \<and> q < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))) \<and> alpha ! Suc k \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))) ! p \<and> beta ! Suc k \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))) ! q"
  proof (cases "beta ! Suc k \<in> A")
    case True
    have L_ne: "L \<noteq> {}" using alpha_in_L by auto
    have A_ne: "A \<noteq> {}" using True by auto
    have p0: "0 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))) \<and> alpha ! Suc k \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))) ! 0" using alpha_in_L L_ne by simp
    have "1 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))) \<and> beta ! Suc k \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))) ! 1" using True L_ne A_ne by simp
    thus ?thesis using p0 by blast
  next
    case False
    hence beta_tail: "beta ! Suc k \<in> \<Union> (set (fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k)))))" using beta_in_A_or_R Union_fst_upper_step_eq_snd unfolding R_def by fast
    thus ?thesis using filter_head_pair_before_tail[OF _ beta_tail] alpha_in_L by blast
  qed
  then obtain p q where pq: "p < q \<and> p < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))) \<and> q < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))) \<and> alpha ! Suc k \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))) ! p \<and> beta ! Suc k \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))) ! q" by blast
  have RunSuc': "Run ! Suc k = P @ filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! k) (drop (Suc i) (Run ! k))))" using RunSuc P by argo
  have m_lt: "length P + p < length (Run ! Suc k)" using pq RunSuc' by auto
  have n_lt: "length P + q < length (Run ! Suc k)" using pq RunSuc' by auto
  have a_in: "alpha ! Suc k \<in> (Run ! Suc k) ! (length P + p)" using pq RunSuc' by auto
  have b_in: "beta ! Suc k \<in> (Run ! Suc k) ! (length P + q)" using pq RunSuc' by auto
  have "length P + p < length P + q" using pq by simp
  thus ?thesis using m_lt n_lt a_in b_in unfolding leftgap_def by blast
qed

lemma samelevel_sameacc_step_not_rightgap_local:
  assumes "auto_well_defined \<A>" "run_well_defined Run (upper_part_pure \<A>) word" "run_well_defined alpha \<A> word" "run_well_defined beta \<A> word" "i < length word" "samelevel alpha beta Run i" "((alpha ! Suc i \<in> accepting_states \<A>) \<longleftrightarrow> (beta ! Suc i \<in> accepting_states \<A>))" "\<not> stolen_at \<A> alpha Run word i"
  shows "\<not> rightgap alpha beta Run (Suc i)"
proof(rule ccontr)
  assume "\<not> \<not> rightgap alpha beta Run (Suc i)"
  hence rg: "rightgap alpha beta Run (Suc i)" by simp
  obtain m where m: "m < length (Run ! i) \<and> alpha ! i \<in> (Run ! i) ! m \<and> beta ! i \<in> (Run ! i) ! m" using assms unfolding samelevel_def by blast
  define R where "R = snd (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))"
  define L where "L = (post_set \<A> ((Run ! i) ! m) (word ! i) - R) - accepting_states \<A>"
  define A where "A = (post_set \<A> ((Run ! i) ! m) (word ! i) - R) \<inter> accepting_states \<A>"
  have m_lt: "m < length (Run ! i)" using m by blast
  have m_in: "alpha ! i \<in> (Run ! i) ! m" using m by blast
  have alpha_head: "alpha ! Suc i \<in> L \<union> A" using no_steal_succ_in_head_pair[OF assms(3) assms(2) assms(5) m_lt m_in assms(8)] unfolding R_def L_def A_def by blast
  have "(beta ! i, word ! i, beta ! Suc i) \<in> transitions \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "beta ! Suc i \<in> post_set \<A> ((Run ! i) ! m) (word ! i)" using m unfolding post_set_def by blast
  hence beta_cases_all: "beta ! Suc i \<in> L \<or> beta ! Suc i \<in> A \<or> beta ! Suc i \<in> R" unfolding L_def A_def R_def by blast
  have alpha_L_or_A: "alpha ! Suc i \<in> L \<or> alpha ! Suc i \<in> A" using alpha_head by blast
  {
    assume hL: "alpha ! Suc i \<in> L"
    hence "alpha ! Suc i \<notin> accepting_states \<A>" unfolding L_def by blast
    hence "beta ! Suc i \<notin> accepting_states \<A>" using assms by blast
    hence "beta ! Suc i \<in> L \<or> beta ! Suc i \<in> R" using beta_cases_all unfolding A_def by blast
    hence "(alpha ! Suc i \<in> L \<and> beta ! Suc i \<in> L) \<or> (beta ! Suc i \<in> R)" using hL by blast
  }
  hence imp1: "alpha ! Suc i \<in> L \<Longrightarrow> (alpha ! Suc i \<in> L \<and> beta ! Suc i \<in> L) \<or> (beta ! Suc i \<in> R)" by auto
  {
    assume hA: "alpha ! Suc i \<in> A"
    hence "alpha ! Suc i \<in> accepting_states \<A>" unfolding A_def by blast
    hence "beta ! Suc i \<in> accepting_states \<A>" using assms by blast
    hence "beta ! Suc i \<in> A \<or> beta ! Suc i \<in> R" using beta_cases_all unfolding A_def L_def by blast
    hence "(alpha ! Suc i \<in> A \<and> beta ! Suc i \<in> A) \<or> (beta ! Suc i \<in> R)" using hA by blast
  }
  hence "alpha ! Suc i \<in> A \<Longrightarrow> (alpha ! Suc i \<in> A \<and> beta ! Suc i \<in> A) \<or> (beta ! Suc i \<in> R)" by blast
  hence acc_split: "(alpha ! Suc i \<in> L \<and> beta ! Suc i \<in> L) \<or> (alpha ! Suc i \<in> A \<and> beta ! Suc i \<in> A) \<or> (beta ! Suc i \<in> R)" using alpha_L_or_A imp1 by blast
  obtain p q where pq: "q < p \<and> q < length (Run ! Suc i) \<and> p < length (Run ! Suc i) \<and> alpha ! Suc i \<in> (Run ! Suc i) ! p \<and> beta ! Suc i \<in> (Run ! Suc i) ! q" using rg unfolding rightgap_def by blast
  hence RunSuc_ne: "Run ! Suc i \<noteq> []" by auto
  have trans_Run: "(Run ! i, word ! i, Run ! Suc i) \<in> transitions (upper_part_pure \<A>)" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  hence RunSuc_eq: "Run ! Suc i = filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (word ! i) (Run ! i)))" using RunSuc_ne unfolding upper_part_pure_def upper_transitions_def by auto
  have "(Run ! i, word ! i, Run ! Suc i) \<in> upper_transitions \<A>" using trans_Run RunSuc_ne unfolding upper_part_pure_def by auto
  hence RunSuc_upper: "Run ! Suc i \<in> upper_states \<A>" using assms upper_transitions_target_in_upper_states by fast
  obtain P where "filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (word ! i) (Run ! i))) = P @ filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))" using RunSuc_prefix_decomp[where m=m and Run=Run and word=word and i=i and \<A>=\<A>] assms m unfolding R_def L_def A_def by blast
  hence RunSuc_split: "Run ! Suc i = P @ filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))" using RunSuc_eq by simp
  have beta_tail_if_R: "beta ! Suc i \<in> R \<Longrightarrow> beta ! Suc i \<in> \<Union> (set (fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))))" unfolding R_def using Union_fst_upper_step_eq_snd by fast
  thus False
  proof (cases "beta ! Suc i \<in> R")
    case True
    hence beta_tail: "beta ! Suc i \<in> \<Union> (set (fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))))" using beta_tail_if_R by blast
    have alpha_first: "alpha ! Suc i \<in> L \<or> alpha ! Suc i \<in> A" using alpha_head by blast
    have "\<exists> t . t < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! t \<and> (\<forall> u < t . alpha ! Suc i \<notin> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! u)"
    proof (cases "alpha ! Suc i \<in> L")
      case True
      hence L_ne: "L \<noteq> {}" by auto
      hence 1: "0 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))))" using True by simp
      have 2: "alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0" using True L_ne by simp
      have "\<forall> u < 0 . alpha ! Suc i \<notin> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! u" by simp
      thus ?thesis using 1 2 by blast
    next
      case False
      hence alpha_suc: "alpha ! Suc i \<in> A" using alpha_head by blast
      thus ?thesis
      proof (cases "L = {}")
        case True thus ?thesis using alpha_suc by force
      next
        case False 
        hence L_ne: "L \<noteq> {}"  by simp
        have A_ne: "A \<noteq> {}" using alpha_suc by auto
        have 1: "1 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))))" using L_ne A_ne by simp
        have 2: "alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 1" using alpha_suc L_ne by auto
        {
          fix u :: nat assume "u < 1"
          hence u0: "u = 0" by simp
          have "(filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0 = L" using L_ne by simp
          hence "alpha ! Suc i \<notin> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! u" using alpha_suc u0 unfolding A_def L_def by blast
        }
        hence 3: "\<forall> u < 1 . alpha ! Suc i \<notin> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! u" by auto
        thus ?thesis using 1 2 by blast
      qed
    qed
    then obtain t where t: "t < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! t \<and> (\<forall> u < t . alpha ! Suc i \<notin> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! u)" by blast
    have LA_ne: "L \<noteq> {} \<or> A \<noteq> {}" using alpha_head by blast
    obtain p' q' where pq': "p' < q' \<and> p' < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> q' < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! p' \<and> beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! q'" using filter_head_pair_before_tail[OF alpha_head beta_tail LA_ne] by blast
    let ?Suf = "filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))"
    have p'_lt: "length P + p' < length (Run ! Suc i)" using pq' RunSuc_split by auto
    have t_lt: "length P + t < length (Run ! Suc i)" using t RunSuc_split by auto
    have alpha_in_p': "alpha ! Suc i \<in> (Run ! Suc i) ! (length P + p')" using pq' RunSuc_split by auto
    have alpha_in_t: "alpha ! Suc i \<in> (Run ! Suc i) ! (length P + t)" using t RunSuc_split by auto
    have "length P + p' = length P + t" using unique_component_upper_state[OF RunSuc_upper p'_lt t_lt alpha_in_p' alpha_in_t] by blast
    hence "p' = t" by simp
    hence "\<exists> s . s < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! s \<and> t < s" using pq' by blast
    then obtain s where s: "s < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! s \<and> t < s" by blast
    have beta_in_s: "beta ! Suc i \<in> (Run ! Suc i) ! (length P + s)" using s RunSuc_split by auto
    have beta_q: "beta ! Suc i \<in> (Run ! Suc i) ! q" using pq by blast
    have q_lt: "q < length (Run ! Suc i)" using pq by blast
    have s_lt: "length P + s < length (Run ! Suc i)" using s RunSuc_split by auto
    have q_eq: "q = length P + s" using unique_component_upper_state[OF RunSuc_upper q_lt s_lt beta_q beta_in_s] by blast
    have alpha_p: "alpha ! Suc i \<in> (Run ! Suc i) ! p" using pq by blast
    have p_lt: "p < length (Run ! Suc i)" using pq by blast
    have t_whole_lt: "length P + t < length (Run ! Suc i)" using t RunSuc_split by auto
    have alpha_t_whole: "alpha ! Suc i \<in> (Run ! Suc i) ! (length P + t)" using t RunSuc_split by auto
    have p_eq: "p = length P + t" using unique_component_upper_state[OF RunSuc_upper p_lt t_whole_lt alpha_p alpha_t_whole] by blast
    have "length P + t < length P + s" using s by simp
    hence "p < q" using p_eq q_eq by simp
    thus False using pq by linarith
  next
    case False
    hence same_bucket: "(alpha ! Suc i \<in> L \<and> beta ! Suc i \<in> L) \<or> (alpha ! Suc i \<in> A \<and> beta ! Suc i \<in> A)" using acc_split by blast
    {
      assume hL: "alpha ! Suc i \<in> L \<and> beta ! Suc i \<in> L"
      hence 1: "0 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))))" by auto
      have 2: "alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0" using hL by auto
      have "beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0" using hL by auto
      hence "0 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0 \<and> beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0" using 1 2 by blast
    }
    hence imp1: "alpha ! Suc i \<in> L \<and> beta ! Suc i \<in> L \<Longrightarrow> 0 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0 \<and> beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0" by blast
    {
      assume hA: "alpha ! Suc i \<in> A \<and> beta ! Suc i \<in> A \<and> L = {}"
      hence 1: "0 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))))" by auto
      have 2: "alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0" using hA by auto
      have "beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0" using hA by auto
      hence "0 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0 \<and> beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0" using 1 2 by blast
    }
    hence imp2: "alpha ! Suc i \<in> A \<and> beta ! Suc i \<in> A \<and> L = {} \<Longrightarrow> 0 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0 \<and> beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 0" by blast
    {
      assume hA: "alpha ! Suc i \<in> A \<and> beta ! Suc i \<in> A \<and> L \<noteq> {}"
      hence 1: "1 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i)))))" by auto
      have 2: "alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 1" using hA by auto
      have "beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 1" using hA by auto
      hence "1 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 1 \<and> beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 1" using 1 2 by blast
    }
    hence "alpha ! Suc i \<in> A \<and> beta ! Suc i \<in> A \<and> L \<noteq> {} \<Longrightarrow> 1 < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 1 \<and> beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! 1" by blast
    then obtain r where r: "r < length (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) \<and> alpha ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! r \<and> beta ! Suc i \<in> (filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (word ! i) (drop (Suc m) (Run ! i))))) ! r" using imp1 imp2 same_bucket by blast
    hence r_lt: "length P + r < length (Run ! Suc i)" using RunSuc_split by auto
    have alpha_r: "alpha ! Suc i \<in> (Run ! Suc i) ! (length P + r)" using r RunSuc_split by auto
    have beta_r: "beta ! Suc i \<in> (Run ! Suc i) ! (length P + r)" using r RunSuc_split by auto
    have p_le: "p < length (Run ! Suc i)" using pq by blast
    have q_le: "q < length (Run ! Suc i)" using pq by blast
    have alpha_suc_p: "alpha ! Suc i \<in> (Run ! Suc i) ! p" using pq by blast
    have beta_suc_q: "beta ! Suc i \<in> (Run ! Suc i) ! q" using pq by blast
    have p_eq: "p = length P + r" using unique_component_upper_state[OF RunSuc_upper p_le r_lt alpha_suc_p alpha_r] pq by blast
    have q_eq: "q = length P + r" using unique_component_upper_state[OF RunSuc_upper q_le r_lt beta_suc_q beta_r] pq by blast
    hence "q = p" using p_eq by simp
    thus False using pq by blast
  qed
qed

lemma no_rightgap_at_start:
  assumes "auto_well_defined \<A>" "run_well_defined Run (upper_part_pure \<A>) word"
  shows "\<not> rightgap run run' Run 0"
proof -
  have "Run ! 0 = [{initial_state \<A>}]" using assms unfolding run_well_defined_def pseudo_run_well_defined_def upper_part_pure_def by force
  thus ?thesis unfolding rightgap_def by auto
qed

lemma samelevel_or_leftgap_or_rightgap:
  assumes "auto_well_defined \<A>" "k < length run" "run_well_defined Run (upper_part_pure \<A>) word" "run_well_defined run \<A> word" "run_well_defined run' \<A> word"
  shows "samelevel run run' Run k \<or> leftgap run run' Run k \<or> rightgap run run' Run k"
proof -
  have "length run = length run'" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  then obtain j where j: "j < length (Run ! k) \<and> run' ! k \<in> (Run ! k) ! j" using run_state_in_upper_component assms by metis
  obtain i where i: "i < length (Run ! k) \<and> run ! k \<in> (Run ! k) ! i" using run_state_in_upper_component assms by blast
  consider "i = j" | "i < j" | "j < i" by linarith
  thus ?thesis
  proof cases
    case 1 thus ?thesis using i j unfolding samelevel_def by blast
  next
    case 2 thus ?thesis using i j unfolding leftgap_def by blast
  next
    case 3 thus ?thesis using i j unfolding rightgap_def by blast
  qed
qed

lemma rightgap_backprop_step:
  assumes "auto_well_defined \<A>" "run_well_defined Run (upper_part_pure \<A>) word" "run_well_defined run \<A> word" "run_well_defined run' \<A> word" "0 < k" "k < length run" "rightgap run run' Run k" "\<nexists> j . j \<le> k - 1 \<and> leftgap run run' Run j" "((run ! k \<in> accepting_states \<A>) \<longleftrightarrow> (run' ! k \<in> accepting_states \<A>))" "\<not> stolen_at \<A> run Run word (k - 1)"
  shows "rightgap run run' Run (k - 1)"
proof -
  have km1_lt: "k - 1 < length run" using assms by linarith
  have cases: "samelevel run run' Run (k - 1) \<or> leftgap run run' Run (k - 1) \<or> rightgap run run' Run (k - 1)"  using samelevel_or_leftgap_or_rightgap[OF assms(1) km1_lt assms(2-4)] .
  then consider "samelevel run run' Run (k - 1)" | "leftgap run run' Run (k - 1)" | "rightgap run run' Run (k - 1)" by blast
  thus ?thesis
  proof cases
    case 1
    have km1_word: "k - 1 < length word" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by simp
    have "\<not> rightgap run run' Run (Suc (k - 1))" using samelevel_sameacc_step_not_rightgap_local[OF assms(1-4) km1_word 1] assms by simp
    hence "\<not> rightgap run run' Run k" using assms by simp
    thus ?thesis using assms by blast
  next
    case 2 thus ?thesis using assms by blast
  next
    case 3 thus ?thesis by blast
  qed
qed

lemma rightgap_no_leftgap_impossible:
  assumes "auto_well_defined \<A>" "run_well_defined Run (upper_part_pure \<A>) word" "run_well_defined run \<A> word" "run_well_defined run' \<A> word" "x < length run" "rightgap run run' Run x" "\<nexists> j . j \<le> x \<and> leftgap run run' Run j" "\<forall> l \<le> x . (run ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run' ! l \<in> accepting_states \<A>)" "\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run Run word k"
  shows False
proof -
  {
    fix d assume "d \<le> x"
    have "d \<le> x \<Longrightarrow> rightgap run run' Run (x - d)"
    proof (induction d)
      case 0 thus ?case using assms by simp
    next
      case (Suc d)
      hence dlt: "d < x" by simp
      hence IH: "rightgap run run' Run (x - d)" using Suc by linarith
      have kgt: "0 < x - d" using dlt by force
      have klt: "x - d < length run" using assms dlt by auto
      have no_left_small: "\<nexists> j .  j \<le> x - d - 1 \<and> leftgap run run' Run j" using assms by auto
      have acc_eq_k: "((run ! (x - d) \<in> accepting_states \<A>) \<longleftrightarrow> (run' ! (x - d) \<in> accepting_states \<A>))" using assms dlt by force
      have no_steal_km1: "\<not> stolen_at \<A> run Run word (x - d - 1)"
      proof(rule ccontr)
        assume "\<not> \<not> stolen_at \<A> run Run word (x - d - 1)"
        hence st: "stolen_at \<A> run Run word (x - d - 1)" by blast
        have "x - d - 1 < length run - 1" using assms dlt by auto
        hence "\<exists> k . k < length run - 1 \<and> stolen_at \<A> run Run word k" using st by blast
        thus False using assms by argo
      qed
      have "rightgap run run' Run (x - Suc d)" using rightgap_backprop_step[OF assms(1-4) kgt klt IH no_left_small acc_eq_k no_steal_km1] by simp
      thus ?case by blast
    qed
  }
  hence "\<forall> d \<le> x . rightgap run run' Run (x - d)" by blast
  hence "rightgap run run' Run 0" by force
  thus False using no_rightgap_at_start[OF assms(1,2)] by simp
qed

lemma acc_mismatch_implies_level_gap_upto:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined Run (upper_part_pure \<A>) word \<and> run_well_defined run \<A> word \<and> run_well_defined run' \<A> word \<and> (\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run Run word k) \<and> x < length run \<and> run' ! x \<in> accepting_states \<A> \<and> run ! x \<notin> accepting_states \<A> \<and> (\<forall> l < x . (run' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run ! l \<in> accepting_states \<A>)) \<Longrightarrow> \<exists> k \<le> x . leftgap run run' Run k"
proof (induction word arbitrary: run run' Run x rule: rev_induct)
  case Nil
  hence "run = [initial_state \<A>] \<and> run' = [initial_state \<A>]" using list_with_one_element unfolding run_well_defined_def pseudo_run_well_defined_def by force
  thus ?case using Nil unfolding leftgap_def by auto
next
  case (snoc a word)
  hence len: "length run = length (word @ [a]) + 1 \<and> length run = length run' \<and> length run = length Run"  unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  hence ne: "run \<noteq> [] \<and> run' \<noteq> [] \<and> Run \<noteq> []" by auto
  then obtain run1 run2 Run1 where var: "run = run1 @ [last run] \<and> run' = run2 @ [last run'] \<and> Run = Run1 @ [last Run]" using append_butlast_last_id by metis
  hence runs1: "run_well_defined run1 \<A> word \<and> run_well_defined run2 \<A> word \<and> run_well_defined Run1 (upper_part_pure \<A>) word" using snoc prun_well_defined_extension_snoc unfolding run_well_defined_def by metis
  hence len1: "length run1 = length word + 1 \<and> length run1 = length run2 \<and> length run1 = length Run1" unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  have "x < length (run1 @ [last run])" using snoc var by argo
  then consider (old) "x < length run1" | (last) "x = length run1" by fastforce
  thus ?case
  proof cases
    case old
    have no_steal1: "\<nexists> k . k < length run1 - 1 \<and> stolen_at \<A> run1 Run1 word k"
    proof(rule ccontr)
      assume "\<not> (\<nexists> k . k < length run1 - 1 \<and> stolen_at \<A> run1 Run1 word k)"
      then obtain k where k: "k < length run1 - 1 \<and> stolen_at \<A> run1 Run1 word k" by blast
      hence "stolen_at \<A> (run1 @ [last run]) (Run1 @ [last Run]) (word @ [a]) k" using stolen_at_lower_place_iff len1 by fast
      hence stolen: "stolen_at \<A> run Run (word @ [a]) k" using var by simp
      have "k < length run - 1" using k var length_append less_diff_conv trans_less_add1 by metis
      thus False using snoc stolen by blast
    qed
    have "run1 ! x = run ! x \<and> run2 ! x = run' ! x" using old len1 list_properties_length var by metis
    hence x_old': "x < length run1 \<and> run2 ! x \<in> accepting_states \<A> \<and> run1 ! x \<notin> accepting_states \<A> \<and> (\<forall> l < x . (run' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run ! l \<in> accepting_states \<A>))" using snoc old by metis
    {
      fix l assume assm: "l < x"
      hence "l < length run1 - 1" using old by auto
      hence "run1 ! l = run ! l \<and> run2 ! l = run' ! l" using old len1 list_properties_length var by metis
      hence "(run2 ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run1 ! l \<in> accepting_states \<A>)" using x_old' assm by presburger
    }
    hence x_old: "x < length run1 \<and> run2 ! x \<in> accepting_states \<A> \<and> run1 ! x \<notin> accepting_states \<A> \<and> (\<forall> l < x . (run2 ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run1 ! l \<in> accepting_states \<A>))" using x_old' by metis
    then obtain k where kmn: "k \<le> x \<and> leftgap run1 run2 Run1 k" using snoc assms runs1 no_steal1 by presburger
    hence "k < length run1" using x_old by linarith
    hence "Run1 ! k = Run ! k \<and> run1 ! k = run ! k \<and> run2 ! k = run' ! k" using var len1 list_properties_length by metis
    thus ?thesis using kmn unfolding leftgap_def by auto
  next    
    case last
    hence x_run: "x = length run - 1" using var butlast_snoc length_butlast by metis
    have "run1 \<noteq> []" using runs1 unfolding run_well_defined_def pseudo_run_well_defined_def by force
    hence x_gt_0: "x > 0" using last by blast
    {
      fix l assume assm: "l < length run1"
      hence eq_idx: "run2 ! l = run' ! l \<and> run1 ! l = run ! l" using  var len1 list_properties_length by metis
      have "l < x" using assm last by blast
      hence  "(run2 ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run1 ! l \<in> accepting_states \<A>)" using snoc eq_idx by presburger
    }
    hence prev_same_acc: "\<forall> l < length run1 . (run2 ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run1 ! l \<in> accepting_states \<A>)" by argo
    have not_empty: "Run1 \<noteq> [] \<and> run1 \<noteq> [] \<and> run2 \<noteq> []" using runs1 unfolding run_well_defined_def pseudo_run_well_defined_def by force
    hence "last Run1 = Run1 ! (length Run1 - 1) \<and> last run1 = run1 ! (length run1 - 1) \<and> last run2 = run2 ! (length run2 - 1)" using list_properties_not_empty by metis
    hence equi_last: "last Run1 = Run1 ! (length run1 - 1) \<and> last run1 = run1 ! (length run1 - 1) \<and> last run2 = run2 ! (length run1 - 1)" using len1 by argo
    have leq: "length run1 - 1 < length run1 \<and> length run1 - 1 < length run2" using len1 by simp
    then obtain i where i: "i < length (last Run1) \<and> last run1 \<in> last Run1 ! i" using run_state_in_upper_component assms runs1  equi_last by metis
    obtain j where j: "j < length (last Run1) \<and> last run2 \<in> last Run1 ! j" using run_state_in_upper_component assms runs1 len1 equi_last leq by metis
    consider (same) "i = j" | (leftgap) "i < j" | (rightgap) "j < i" using i j by linarith
    thus ?thesis
    proof cases
      case same
      have no_steal_last: "\<not> stolen_at \<A> run Run (word @ [a]) (length run - 2)"
      proof(rule ccontr)
        assume "\<not>\<not> stolen_at \<A> run Run (word @ [a]) (length run - 2)"
        hence h: "stolen_at \<A> run Run (word @ [a]) (length run - 2)" by blast
        have "length run - 2 < length run - 1" using x_gt_0 x_run by linarith
        thus False using snoc h by blast
      qed
      have idx_prev: "length run - 2 = length run1 - 1" using var last x_gt_0 len x_run by force
      have idx_Run_prev: "Run ! (length run - 2) = last Run1" using var idx_prev not_empty list_properties_not_empty len1 by metis
      have idx_run_prev: "run ! (length run - 2) = last run1" using var idx_prev not_empty list_properties_not_empty by metis
      have idx_run'_prev: "run' ! (length run - 2) = last run2" using var idx_prev not_empty list_properties_not_empty len1 by metis
      have i_le: "i < length (Run ! (length run - 2))" using i idx_Run_prev by auto
      have "run ! (length run - 2) \<in> (Run ! (length run - 2)) ! i \<and> run' ! (length run - 2) \<in> (Run ! (length run - 2)) ! i" using i j same idx_Run_prev idx_run_prev idx_run'_prev by argo
      hence same_prev: "samelevel run run' Run (length run - 2)" using i_le unfolding samelevel_def by blast
      have len_run_gt1: "length run > 1" using snoc unfolding run_well_defined_def pseudo_run_well_defined_def by simp
      have last_run_not_acc: "run ! (length run - 1) \<notin> accepting_states \<A>" using snoc x_run by blast
      have last_run'_acc: "run' ! (length run - 1) \<in> accepting_states \<A>" using snoc x_run by simp
      have Run_wd: "run_well_defined Run (upper_part_pure \<A>) (word @ [a])" using snoc by blast
      have run_wd: "run_well_defined run \<A> (word @ [a])" using snoc by blast
      have run'_wd: "run_well_defined run' \<A> (word @ [a])" using snoc by blast
      have suc_idx: "Suc (length run - 2) < length run" using len_run_gt1 by simp
      hence "leftgap run run' Run (Suc (length run - 2))" using samelevel_nonacc_acc_step_gives_leftgap_local[where \<A>=\<A> and Run=Run and word="word @ [a]" and alpha=run and beta=run' and k="length run - 2"] assms Run_wd run_wd run'_wd same_prev last_run_not_acc last_run'_acc no_steal_last Suc_1 Suc_diff_Suc len_run_gt1 by metis
      hence "leftgap run run' Run (length run - 1)" using len_run_gt1 Suc_1 Suc_diff_Suc by metis
      thus ?thesis using x_run by auto
    next
      case leftgap
      have x_prev: "x - 1 = length run1 - 1" using last x_gt_0 by simp
      hence ile: "i < length (Run ! (x - 1))" using i var equi_last len1 leq nth_append by metis
      have jle: "j < length (Run ! (x - 1))" using j var equi_last len1 leq nth_append x_prev by metis
      have runi: "run ! (x - 1) \<in> (Run ! (x - 1)) ! i" using i var equi_last len1 leq nth_append x_prev by metis
      have "run' ! (x - 1) \<in> (Run ! (x - 1)) ! j" using j var equi_last len1 leq nth_append x_prev by metis
      hence "leftgap run run' Run (x - 1)" using ile jle runi leftgap unfolding leftgap_def by blast
      thus ?thesis using last leq less_imp_le_nat by fast
    next
      case rightgap
      have idx_prev: "x - 1 = length run1 - 1" using last x_gt_0 by simp
      have idx_run1: "run ! (x - 1) = last run1" using var idx_prev not_empty list_properties_not_empty by metis
      have idx_run2: "run' ! (x - 1) = last run2" using var idx_prev not_empty list_properties_not_empty len1 by metis
      have idx_Run1: "Run ! (x - 1) = last Run1" using var idx_prev not_empty list_properties_not_empty len1 by metis
      have rightgap_prev: "rightgap run run' Run (x - 1)" using i j rightgap idx_run1 idx_run2 idx_Run1 unfolding rightgap_def by metis
      show ?thesis
      proof (rule ccontr)
        assume "\<not> (\<exists> k \<le> x . leftgap run run' Run k)"
        hence no_leftgap_upto: "\<nexists> j . j \<le> x - 1 \<and> leftgap run run' Run j" by force
        {
          fix l assume "l \<le> x - 1"
          hence llt: "l < length run1" using idx_prev leq by auto
          hence idx_eq: "run ! l = run1 ! l \<and> run' ! l = run2 ! l"  using var len1 list_properties_length by metis
          hence "(run ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run' ! l \<in> accepting_states \<A>)" using prev_same_acc llt by auto
        }     
        hence acc_eq_upto: "\<forall> l \<le> x - 1 . (run ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run' ! l \<in> accepting_states \<A>)" by blast
        have no_steal_global: "\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run Run (word @ [a]) k" using snoc by blast
        have xprev_lt: "x - 1 < length run" using x_gt_0 x_run by linarith
        have Run_wd: "run_well_defined Run (upper_part_pure \<A>) (word @ [a])" using snoc by blast
        have run_wd: "run_well_defined run \<A> (word @ [a])" using snoc by blast
        have run'_wd: "run_well_defined run' \<A> (word @ [a])" using snoc by blast
        thus False using rightgap_no_leftgap_impossible[OF assms Run_wd run_wd run'_wd xprev_lt rightgap_prev no_leftgap_upto acc_eq_upto no_steal_global] by blast
      qed
    qed
  qed
qed

lemma no_steal_run_has_max_acc_sum:
  assumes "auto_well_defined \<A>" "run_well_defined Run (upper_part_pure \<A>) word" "run_well_defined run \<A> word" "run_well_defined run' \<A> word" "\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run Run word k" "last run = last run'"
  shows "acc_sum \<A> run' \<le> acc_sum \<A> run"
proof (rule ccontr)
  assume "\<not> acc_sum \<A> run' \<le> acc_sum \<A> run"
  hence gt: "acc_sum \<A> run' > acc_sum \<A> run" by simp
  have len: "length run = length run' \<and> length run = length Run" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  then obtain z where z: "z < length run \<and> run' ! z \<in> accepting_states \<A> \<and> run ! z \<notin> accepting_states \<A> \<and> (\<forall> l < z . (run' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run ! l \<in> accepting_states \<A>))" using acc_sum_gt_ex_first_accept_diff gt by blast
  have levels_run: "\<forall> j < length run . \<exists> i < length (Run ! j) . run ! j \<in> (Run ! j) ! i" using run_state_in_upper_component assms by blast
  have levels_run': "\<forall> j < length run' . \<exists> i < length (Run ! j) . run' ! j \<in> (Run ! j) ! i" using run_state_in_upper_component assms by blast
  have first_right: "\<exists> k \<le> z . leftgap run run' Run k" using acc_mismatch_implies_level_gap_upto[OF assms(1)] assms z by presburger
  then obtain k where k: "k \<le> z \<and> leftgap run run' Run k" by blast
  {
    fix j
    have "k \<le> j \<and> j < length run \<Longrightarrow> leftgap run run' Run j"
    proof (induction j)
      case 0 thus ?case using first_right k by blast
    next
      case (Suc j) thus ?case
      proof (cases "k = Suc j")
        case True thus ?thesis using first_right k by blast
      next
        case False
        hence jcase: "k \<le> j \<and> j < length run" using Suc by force
        then obtain m n where mn: "m < n \<and> m < length (Run ! j) \<and> n < length (Run ! j) \<and> run ! j \<in> (Run ! j) ! m \<and> run' ! j \<in> (Run ! j) ! n" using Suc unfolding leftgap_def by blast
        obtain m' where m': "m' < length (Run ! Suc j) \<and> run ! Suc j \<in> (Run ! Suc j) ! m'" using levels_run Suc by blast
        obtain n' where n': "n' < length (Run ! Suc j) \<and> run' ! Suc j \<in> (Run ! Suc j) ! n'"  using levels_run' Suc len by auto
        have "Suc j < length word + 1" using Suc assms unfolding run_well_defined_def pseudo_run_well_defined_def by argo
        hence j_lt_word: "j < length word" by simp
        have "\<not> stolen_at \<A> run Run word j" using assms Suc by force
        hence "m' < n'" using no_steal_preserves_left_order assms j_lt_word mn m' n' by blast
        thus ?thesis using m' n' unfolding leftgap_def by blast
      qed
    qed
  }
  hence propagate: "\<forall> j . k \<le> j \<and> j < length run \<longrightarrow> leftgap run run' Run j" by blast
  have "k \<le> length run - 1 \<and> length run - 1 < length run" using k z by linarith
  hence exist: "\<exists> m n . m < n \<and> m < length (Run ! (length run - 1)) \<and> n < length (Run ! (length run - 1)) \<and> run ! (length run - 1) \<in> (Run ! (length run - 1)) ! m \<and> run' ! (length run - 1) \<in> (Run ! (length run - 1)) ! n" using propagate unfolding leftgap_def by blast
  have "run \<noteq> [] \<and> run' \<noteq> [] \<and> Run \<noteq> []" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "Run ! (length run - 1) = last Run \<and> run ! (length run - 1) = last run \<and> run' ! (length run - 1) = last run'" using list_properties_not_empty len by metis
  hence "\<exists> m n . m < n \<and> m < length (last Run) \<and> n < length (last Run) \<and> last run \<in> last Run ! m \<and> last run' \<in> last Run ! n" using exist by presburger
  then obtain m n where last_mn: "m < n \<and> m < length (last Run) \<and> n < length (last Run) \<and> last run \<in> last Run ! m \<and> last run' \<in> last Run ! n" by blast
  have not_empty: "last Run \<noteq> []" using assms last_not_empty_run by blast
  have "last Run \<in> states (upper_part_pure \<A>)" using assms well_def_upper_part_pure last_of_prun_is_state unfolding run_well_defined_def by fast 
  hence "last Run \<in> upper_states \<A>" using not_empty unfolding upper_part_pure_def by force
  hence "m = n" using assms last_mn unique_component_upper_state last_mn last_mn by metis
  thus False using last_mn by blast
qed

lemma no_steal_same_acc_no_level_gap:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined Run (upper_part_pure \<A>) word \<and> run_well_defined r1 \<A> word \<and> run_well_defined r2 \<A> word \<and> (\<nexists> k . k < length r1 - 1 \<and> stolen_at \<A> r1 Run word k) \<and> (\<nexists> k . k < length r2 - 1 \<and> stolen_at \<A> r2 Run word k) \<and> (\<forall> l < length r1 . (r1 ! l \<in> accepting_states \<A>) \<longleftrightarrow> (r2 ! l \<in> accepting_states \<A>)) \<and> k < length r1 \<Longrightarrow> \<not> leftgap r1 r2 Run k"
proof (induction word arbitrary: r1 r2 Run k rule: rev_induct)
  case Nil
  hence len: "length r1 = 1 \<and> length r2 = 1 \<and> length Run = 1" unfolding run_well_defined_def pseudo_run_well_defined_def by auto
  have Run0: "Run ! 0 = [{initial_state \<A>}] \<and> k = 0" using Nil unfolding run_well_defined_def pseudo_run_well_defined_def upper_part_pure_def by auto
  thus ?case unfolding leftgap_def by simp
next
  case (snoc a word)
  hence len: "length r1 = length (word @ [a]) + 1 \<and> length r1 = length r2 \<and> length r1 = length Run" unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  hence ne: "r1 \<noteq> [] \<and> r2 \<noteq> [] \<and> Run \<noteq> []" by auto
  then obtain r1' r2' Run' where var: "r1 = r1' @ [last r1] \<and> r2 = r2' @ [last r2] \<and> Run = Run' @ [last Run]" using append_butlast_last_id by metis
  hence pref: "run_well_defined r1' \<A> word \<and> run_well_defined r2' \<A> word \<and> run_well_defined Run' (upper_part_pure \<A>) word" using snoc prun_well_defined_extension_snoc unfolding run_well_defined_def by metis
  hence len1: "length r1' = length word + 1 \<and> length r1' = length r2' \<and> length r1' = length Run'" unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  show ?case
  proof (cases "k < length r1'")
    case True
    have no_steal1: "\<nexists> k . k < length r1' - 1 \<and> stolen_at \<A> r1' Run' word k"
    proof(rule ccontr)
      assume "\<not> (\<nexists> k . k < length r1' - 1 \<and> stolen_at \<A> r1' Run' word k)"
      then obtain k where k: "k < length r1' - 1 \<and> stolen_at \<A> r1' Run' word k" by blast
      hence "stolen_at \<A> (r1' @ [last r1]) (Run' @ [last Run]) (word @ [a]) k" using stolen_at_lower_place_iff len1 by fast
      hence stolen: "stolen_at \<A> r1 Run (word @ [a]) k" using var by simp
      have "k < length r1 - 1" using k var length_append less_diff_conv trans_less_add1 by metis
      thus False using snoc stolen by blast
    qed
    have no_steal2: "\<nexists> k . k < length r2' - 1 \<and> stolen_at \<A> r2' Run' word k"
    proof(rule ccontr)
      assume "\<not> (\<nexists> k . k < length r2' - 1 \<and> stolen_at \<A> r2' Run' word k)"
      then obtain k where k: "k < length r2' - 1 \<and> stolen_at \<A> r2' Run' word k" by blast
      hence "stolen_at \<A> (r2' @ [last r2]) (Run' @ [last Run]) (word @ [a]) k" using stolen_at_lower_place_iff len1 by metis
      hence stolen: "stolen_at \<A> r2 Run (word @ [a]) k" using var by simp
      have "k < length r2 - 1" using k var length_append less_diff_conv trans_less_add1 by metis
      thus False using snoc stolen by blast
    qed
    {
      fix l assume l: "l < length r1'"
      hence less: "l < length r1" using  var add_diff_cancel_right' len length_butlast snoc_eq_iff_butlast trans_less_add1 by metis
      have "r1' ! l = r1 ! l \<and> r2' ! l = r2 ! l" using l len1 var list_properties_length by metis
      hence "(r1' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (r2' ! l \<in> accepting_states \<A>)" using snoc less by presburger
    }
    hence "\<forall> l < length r1' . (r1' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (r2' ! l \<in> accepting_states \<A>)" by blast
    hence leftgap: "\<not> leftgap r1' r2' Run' k" using snoc pref no_steal1 no_steal2 True by presburger
    have "Run' ! k = Run ! k \<and> r1' ! k = r1 ! k \<and> r2' ! k = r2 ! k" using True len1 var list_properties_length by metis
    thus ?thesis using var True leftgap unfolding leftgap_def by presburger
  next
    case False
    have "length r1 = length r1' + length [last r1]" using var length_append by metis
    hence lenlen: "length r1 = length r1' + 1" by simp
    hence k_last: "k = length r1'" using snoc False by auto
    hence k_gt0: "k > 0" using len1 by simp
    hence idx_prev: "k - 1 = length r1' - 1" using k_last by simp
    hence k_prev_bound: "k - 1 < length r1'" using len1 by simp
    hence "k - 1 < length r1" using lenlen by auto
    hence step: "samelevel r1 r2 Run (k - 1) \<or> leftgap r1 r2 Run (k - 1) \<or> rightgap r1 r2 Run (k - 1)" using samelevel_or_leftgap_or_rightgap assms snoc by blast
    then consider (case1) "samelevel r1 r2 Run (k - 1)" | (case2) "leftgap r1 r2 Run (k - 1)" | (case3) "rightgap r1 r2 Run (k - 1)" by fast
    thus ?thesis
    proof cases
      case case1
      have k_word: "k - 1 < length (word @ [a])" using idx_prev len lenlen by simp
      have acc_eq: "(r1 ! k \<in> accepting_states \<A>) \<longleftrightarrow> (r2 ! k \<in> accepting_states \<A>)" using snoc k_last by blast
      have no_steal_r1: "\<not> stolen_at \<A> r1 Run (word @ [a]) (k - 1)" using snoc k_gt0 by force
      have no_steal_r2: "\<not> stolen_at \<A> r2 Run (word @ [a]) (k - 1)" using snoc k_gt0 add_diff_cancel_right' k_prev_bound len lenlen by metis
      have "\<not> rightgap r2 r1 Run (Suc (k - 1))" using samelevel_sameacc_step_not_rightgap_local[where \<A>=\<A> and Run=Run and word="word @ [a]" and alpha=r2 and beta=r1 and i="k - 1"] using assms snoc case1 k_word acc_eq no_steal_r2 Suc_diff_1 k_gt0 unfolding samelevel_def by metis
      hence "\<not> rightgap r2 r1 Run k" using k_gt0 by simp
      thus ?thesis unfolding leftgap_def rightgap_def by blast
    next
      case case2
      have no_steal1: "\<nexists> k . k < length r1' - 1 \<and> stolen_at \<A> r1' Run' word k"
      proof(rule ccontr)
        assume "\<not> (\<nexists> k . k < length r1' - 1 \<and> stolen_at \<A> r1' Run' word k)"
        then obtain k where k: "k < length r1' - 1 \<and> stolen_at \<A> r1' Run' word k" by blast
        hence "stolen_at \<A> (r1' @ [last r1]) (Run' @ [last Run]) (word @ [a]) k" using stolen_at_lower_place_iff len1 by fast
        hence stolen: "stolen_at \<A> r1 Run (word @ [a]) k" using var by simp
        have "k < length r1 - 1" using k var length_append less_diff_conv trans_less_add1 by metis
        thus False using snoc stolen by blast
      qed
      have no_steal2: "\<nexists> k . k < length r2' - 1 \<and> stolen_at \<A> r2' Run' word k"
      proof(rule ccontr)
        assume "\<not> (\<nexists> k . k < length r2' - 1 \<and> stolen_at \<A> r2' Run' word k)"
        then obtain k where k: "k < length r2' - 1 \<and> stolen_at \<A> r2' Run' word k" by blast
        hence "stolen_at \<A> (r2' @ [last r2]) (Run' @ [last Run]) (word @ [a]) k" using stolen_at_lower_place_iff len1 by metis
        hence stolen: "stolen_at \<A> r2 Run (word @ [a]) k" using var by simp
        have "k < length r2 - 1" using k var length_append less_diff_conv trans_less_add1 by metis
        thus False using snoc stolen by blast
      qed
      {
        fix l assume l: "l < length r1'"
        hence less: "l < length r1" using  var add_diff_cancel_right' len length_butlast snoc_eq_iff_butlast trans_less_add1 by metis
        have "r1' ! l = r1 ! l \<and> r2' ! l = r2 ! l" using l len1 var list_properties_length by metis
        hence "(r1' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (r2' ! l \<in> accepting_states \<A>)" using snoc less by presburger
      }
      hence "\<forall> l < length r1' . (r1' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (r2' ! l \<in> accepting_states \<A>)" by blast
      hence leftgap: "\<not> leftgap r1' r2' Run' (k - 1)" using snoc pref no_steal1 no_steal2 k_prev_bound by presburger
      have "Run' ! (k - 1) = Run ! (k - 1) \<and> r1' ! (k - 1) = r1 ! (k - 1) \<and> r2' ! (k - 1) = r2 ! (k - 1)" using var len1 k_prev_bound list_properties_length by metis 
      hence "\<not> leftgap r1 r2 Run (k - 1)" using leftgap unfolding leftgap_def by presburger
      thus ?thesis using case2 by blast
    next
      case case3
      have k_word: "k - 1 < length (word @ [a])" using idx_prev len lenlen by simp
      have no_steal_r2: "\<not> stolen_at \<A> r2 Run (word @ [a]) (k - 1)" using snoc k_gt0 add_diff_cancel_right' k_prev_bound len lenlen by metis
      have k_less: "k < length r1" using idx_prev len lenlen by simp
      then obtain i1 where i1: "i1 < length (Run ! k) \<and> r1 ! k \<in> (Run ! k) ! i1" using run_state_in_upper_component[OF assms] snoc by metis      
      obtain i2 where i2: "i2 < length (Run ! k) \<and> r2 ! k \<in> (Run ! k) ! i2" using run_state_in_upper_component[OF assms] snoc k_less len by metis   
      obtain j1 j2 where prev: "j2 < j1 \<and> j2 < length (Run ! (k - 1)) \<and> j1 < length (Run ! (k - 1)) \<and> r1 ! (k - 1) \<in> (Run ! (k - 1)) ! j1 \<and> r2 ! (k - 1) \<in> (Run ! (k - 1)) ! j2" using case3 unfolding rightgap_def by blast
      have "Suc (k - 1) = k" by (simp add: k_gt0)
      hence i2_lt_i1: "i2 < i1" using no_steal_preserves_left_order[where \<A>=\<A> and run=r2 and run'=r1 and Run=Run and word="word @ [a]" and i="k - 1" and m=j2 and n=j1 and m'=i2 and n'=i1] assms snoc k_word prev no_steal_r2 i1 i2 by argo
      have "length Run - 1 = k" using len k_last add_diff_cancel_right' lenlen by force
      hence Run_last: "Run ! k = last Run" using ne list_properties_not_empty by fast
      have last_not_empty: "last Run \<noteq> []" using last_not_empty_run[OF assms] snoc by blast
      have "last Run \<in> states (upper_part_pure \<A>)" using snoc well_def_upper_part_pure[OF assms] last_of_prun_is_state unfolding run_well_defined_def by fast
      hence last_upper: "last Run \<in> upper_states \<A>" using last_not_empty unfolding upper_part_pure_def by auto
      show ?thesis
      proof(rule ccontr)
        assume "\<not> \<not> leftgap r1 r2 Run k"
        hence "leftgap r1 r2 Run k" by argo
        then obtain m n where mn: "m < n \<and> m < length (Run ! k) \<and> n < length (Run ! k) \<and> r1 ! k \<in> (Run ! k) ! m \<and> r2 ! k \<in> (Run ! k) ! n" unfolding leftgap_def by blast
        have r1_i1: "r1 ! k \<in> last Run ! i1" using i1 Run_last by simp
        have r1_m: "r1 ! k \<in> last Run ! m" using mn Run_last by simp
        have i1_eq_m: "i1 = m" using unique_component_upper_state last_upper Run_last i1 mn r1_i1 r1_m by fastforce
        have r2_i2: "r2 ! k \<in> last Run ! i2" using i2 Run_last by simp
        have r2_n: "r2 ! k \<in> last Run ! n" using mn Run_last by simp
        have "i2 = n" using unique_component_upper_state last_upper Run_last i2 mn r2_i2 r2_n by metis
        hence "i1 < i2" using mn i1_eq_m by blast
        thus False using i2_lt_i1 by simp
      qed
    qed
  qed
qed

lemma acc_sum_append_strict_mono: "length alpha = length beta \<and> length alpha' = length beta' \<and> acc_sum \<A> alpha < acc_sum \<A> beta \<Longrightarrow> acc_sum \<A> (alpha @ alpha') < acc_sum \<A> (beta @ beta')"
proof (induction alpha' arbitrary: beta' alpha beta rule: rev_induct)
  case Nil thus ?case using Nil by simp
next
  case (snoc a alpha')
  hence not_empty: "beta' \<noteq> []" by force
  then obtain b beta'' where b: "beta' = beta'' @ [b]" using append_butlast_last_id by metis
  hence "length alpha = length beta \<and> length alpha' = length beta'' \<and> acc_sum \<A> alpha < acc_sum \<A> beta" using snoc by simp
  hence "length (alpha @ alpha') = length (beta @ beta'') \<and> acc_sum \<A> (alpha @ alpha') < acc_sum \<A> (beta @ beta'')" using snoc by simp
  hence "acc_sum \<A> ((alpha @ alpha') @ [a]) < acc_sum \<A> ((beta @ beta'') @ [b])" using acc_sum_append by fast
  thus ?case using b by simp
qed

lemma no_steal_run_has_max_acc_sum_unique:
  assumes "auto_well_defined \<A>" "run_well_defined Run (upper_part_pure \<A>) word" "run_well_defined run \<A> word" "run_well_defined run' \<A> word" "\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run Run word k" "last run = last run'" "\<exists> k < length run . rightgap run run' Run k" 
  shows "acc_sum \<A> run' < acc_sum \<A> run"
proof (rule ccontr)
  assume "\<not> acc_sum \<A> run' < acc_sum \<A> run"
  hence gt: "acc_sum \<A> run' > acc_sum \<A> run \<or> acc_sum \<A> run' = acc_sum \<A> run" by linarith
  then consider (case1) "acc_sum \<A> run' > acc_sum \<A> run" | (case2) "acc_sum \<A> run' = acc_sum \<A> run" by auto
  thus False
  proof cases
    case case1
    have "acc_sum \<A> run' \<le> acc_sum \<A> run" using assms no_steal_run_has_max_acc_sum by blast
    thus ?thesis using case1 by linarith
  next
    case case2
    have len: "length run = length run'" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by simp
    hence same_acc: "\<forall> l < length run . (run' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run ! l \<in> accepting_states \<A>)" using same_acc_states_equals_same_acc_sum_right case2 by blast
    obtain k where gap: "k < length run \<and> rightgap run run' Run k" using assms unfolding rightgap_def by blast
    have "length run = length word + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast
    hence k_leq: "k \<le> length word" using gap by simp
    have Suc_k: "Suc k = k + 1" by simp
    let ?pref_run = "take (Suc k) run"
    let ?pref_run'= "take (Suc k) run'"
    let ?pref_Run = "take (Suc k) Run"
    let ?pref_word = "take k word"
    have pref_wd: "run_well_defined ?pref_run \<A> ?pref_word \<and> run_well_defined ?pref_run' \<A> ?pref_word \<and> run_well_defined ?pref_Run (upper_part_pure \<A>) ?pref_word" using assms run_well_defined_take k_leq Suc_k by metis
    then obtain run_clean' where clean': "run_well_defined run_clean' \<A> ?pref_word \<and> last run_clean' = last ?pref_run' \<and> (\<nexists> j . j < length run_clean' - 1 \<and> stolen_at \<A> run_clean' ?pref_Run ?pref_word j)" using existence_of_run_without_stealing[OF assms(1)] gap by metis
    have no_steal_pref: "\<nexists> j . j < length ?pref_run - 1 \<and> stolen_at \<A> ?pref_run ?pref_Run ?pref_word j"
    proof (rule ccontr)
      assume "\<not> (\<nexists> j . j < length ?pref_run - 1 \<and> stolen_at \<A> ?pref_run ?pref_Run ?pref_word j)"
      then obtain j where j: "j < length ?pref_run - 1 \<and> stolen_at \<A> ?pref_run ?pref_Run ?pref_word j" by blast
      have "length ?pref_run = Suc k" using gap by force
      hence jlt: "j < length run - 1" using j gap by linarith
      have nth_run0: "?pref_run ! j = run ! j" using j by auto
      have nth_run1: "?pref_run ! Suc j = run ! Suc j" using j by auto
      have nth_Run: "?pref_Run ! j = Run ! j" using j by auto
      have nth_word: "?pref_word ! j = word ! j" using j by auto
      have "stolen_at \<A> ?pref_run ?pref_Run ?pref_word j" using j by blast
      hence "stolen_at \<A> run Run word j" using nth_run0 nth_run1 nth_Run nth_word unfolding stolen_at_def by simp
      thus False using assms jlt by blast
    qed
    have pref_eq_pref': "acc_sum \<A> ?pref_run = acc_sum \<A> ?pref_run'"
    proof -
      have decomp1: "run = ?pref_run @ drop (Suc k) run" by simp
      have decomp2: "run' = ?pref_run' @ drop (Suc k) run'" by simp
      have len_tail: "length (drop (Suc k) run) = length (drop (Suc k) run')" using len gap by simp
      have len_pref: "length ?pref_run = length ?pref_run'" using len gap by simp
      hence eq_tail: "acc_sum \<A> (drop (Suc k) run) = acc_sum \<A> (drop (Suc k) run') \<Longrightarrow> acc_sum \<A> ?pref_run = acc_sum \<A> ?pref_run'" using same_acc_sum_same_acc_sum[of ?pref_run ?pref_run' "drop (Suc k) run" "drop (Suc k) run'" \<A>] len_tail case2 decomp1 decomp2 by presburger
      have same_all: "acc_sum \<A> run = acc_sum \<A> run'" using case2 by simp
      thus ?thesis using decomp1 decomp2 eq_tail len_pref len_tail same_acc_sum_same_acc_sum_left by metis
    qed
    have "acc_sum \<A> ?pref_run' \<le> acc_sum \<A> run_clean'" using no_steal_run_has_max_acc_sum[OF assms(1), where Run="?pref_Run" and run=run_clean' and run'="?pref_run'" and word="?pref_word"] pref_wd clean' by blast
    then consider (eq) "acc_sum \<A> ?pref_run' = acc_sum \<A> run_clean'" | (lt) "acc_sum \<A> ?pref_run' < acc_sum \<A> run_clean'" by linarith
    hence False
    proof cases
      case eq
      have clean_same_acc: "\<forall> l < length ?pref_run . (?pref_run ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run_clean' ! l \<in> accepting_states \<A>)" using same_acc_states_equals_same_acc_sum_right[of ?pref_run run_clean' \<A>] eq pref_eq_pref' clean' pref_wd unfolding run_well_defined_def pseudo_run_well_defined_def by presburger
      have clean_gap: "rightgap ?pref_run run_clean' ?pref_Run k"
      proof -
        obtain m n where mn: "n < m \<and> m < length (Run ! k) \<and> n < length (Run ! k) \<and> run ! k \<in> (Run ! k) ! m \<and> run' ! k \<in> (Run ! k) ! n" using gap unfolding rightgap_def by blast
        have Runk: "?pref_Run ! k = Run ! k" using gap by simp
        have "last ?pref_run = run ! k" using gap last_and_take_list lessI less_nat_zero_code list.size(3) nth_take by metis
        hence last_pref: "?pref_run ! k = run ! k" by force
        have "k < length run'" using gap len by simp
        hence "last ?pref_run' = run' ! k" using last_and_take_list lessI less_nat_zero_code list.size(3) nth_take by metis
        hence last: "last run_clean' = run' ! k" using clean' by simp
        have suc_k: "length ?pref_run = Suc k" using gap by force
        have "length ?pref_run' = length ?pref_run" using pref_wd unfolding run_well_defined_def pseudo_run_well_defined_def by argo
        hence suc_k': "length ?pref_run' = Suc k" using suc_k by argo
        have "length ?pref_run' = length run_clean'" using pref_wd clean' unfolding run_well_defined_def pseudo_run_well_defined_def by argo
        hence "length run_clean' = Suc k" using suc_k' by argo
        hence suc_k'': "length run_clean' - 1 = k" by simp
        have "run_clean' \<noteq> []" using clean' unfolding run_well_defined_def pseudo_run_well_defined_def by force
        hence "last run_clean' = run_clean' ! k" using list_properties_not_empty suc_k'' by metis
        hence "run_clean' ! k = run' ! k" using last by auto
        thus ?thesis using mn Runk last_pref unfolding rightgap_def by auto
      qed
      have runs_well_def: "run_well_defined ?pref_Run (upper_part_pure \<A>) ?pref_word \<and> run_well_defined run_clean' \<A> ?pref_word \<and> run_well_defined ?pref_run \<A> ?pref_word" using pref_wd clean' by blast
      have no_stealing: "\<nexists> j . j < length run_clean' - 1 \<and> stolen_at \<A> run_clean' ?pref_Run ?pref_word j" using clean' by blast
      have "length ?pref_run' = length run_clean'" using pref_wd clean' unfolding run_well_defined_def pseudo_run_well_defined_def by argo
      hence same_length: "length ?pref_run = length run_clean'" using len by auto
      hence clean_same_acc_len: "\<forall> l < length run_clean' . (run_clean' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (?pref_run ! l \<in> accepting_states \<A>)" using clean_same_acc by presburger
      have "k < length run_clean'" using gap same_length by force
      hence "\<not> leftgap run_clean' ?pref_run ?pref_Run k" using no_steal_same_acc_no_level_gap[OF assms(1)] runs_well_def no_stealing no_steal_pref clean_same_acc_len same_length by blast 
      thus False using clean_gap unfolding leftgap_def rightgap_def by blast
    next
      case lt
      have pref_word_append: "?pref_word @ (drop k word) = word" by auto
      have lenlen: "length ?pref_run' = length run_clean'" using pref_wd clean' unfolding run_well_defined_def pseudo_run_well_defined_def by argo
      have "k < length run'" using gap len by simp
      hence "length (run_clean' @ (drop (Suc k) run')) = length run_clean' + length (drop (Suc k) run')" by force
      hence "length (run_clean' @ (drop (Suc k) run')) = length (?pref_run' @ (drop (Suc k) run'))" using lenlen by force
      hence "length (run_clean' @ (drop (Suc k) run')) = length run'" by simp
      hence pref_len: "length (run_clean' @ (drop (Suc k) run')) = length word + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by argo
      have big_wd: "run_well_defined (run_clean' @ (drop (Suc k) run')) \<A> word"
      proof -
        have "run_clean' \<noteq> []" using clean' unfolding run_well_defined_def pseudo_run_well_defined_def by force
        hence "(run_clean' @ (drop (Suc k) run')) ! 0 = run_clean' ! 0" using  Nil_is_append_conv hd_append2 hd_conv_nth by metis
        hence init: "(run_clean' @ (drop (Suc k) run')) ! 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using clean' unfolding run_well_defined_def pseudo_run_well_defined_def by argo
        {
          fix i assume assm: "i < length (run_clean' @ (drop (Suc k) run')) - 1"        
          then consider (case1) "i < length run_clean' - 1" | (case2) "i = length run_clean' - 1" | (case3) "i > length run_clean' - 1" by linarith
          hence tail_step: "((run_clean' @ (drop (Suc k) run')) ! i, word ! i, (run_clean' @ (drop (Suc k) run')) ! (i + 1)) \<in> transitions \<A>"
          proof cases
            case case1
            have i_pref: "i < length ?pref_word" using case1 clean' unfolding run_well_defined_def pseudo_run_well_defined_def by simp
            have step_clean: "(run_clean' ! i, ?pref_word ! i, run_clean' ! (i + 1)) \<in> transitions \<A>" using clean' case1 unfolding run_well_defined_def pseudo_run_well_defined_def by force
            have nth1: "(run_clean' @ drop (Suc k) run') ! i = run_clean' ! i" using case1 list_append_position4 by blast
            have nth2: "(run_clean' @ drop (Suc k) run') ! (i + 1) = run_clean' ! (i + 1)" using case1 list_append_position4 by blast
            have "word ! i = ?pref_word ! i" using i_pref by auto
            thus ?thesis using step_clean nth1 nth2 by argo
          next
            case case2
            have "run' \<noteq> []" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force 
            then consider (case4) "k < length run' - 1" | (case5) "k = length run' - 1" using gap len by linarith
            thus ?thesis
            proof cases
              case case4
              have rc_nonempty: "run_clean' \<noteq> []" using clean' unfolding run_well_defined_def pseudo_run_well_defined_def by force
              have suc_k: "length ?pref_run = Suc k" using gap by force
              have "length ?pref_run' = length ?pref_run" using pref_wd unfolding run_well_defined_def pseudo_run_well_defined_def by argo
              hence suc_k': "length ?pref_run' = Suc k" using suc_k by argo
              have "length ?pref_run' = length run_clean'" using pref_wd clean' unfolding run_well_defined_def pseudo_run_well_defined_def by argo
              hence suc_k: "length run_clean' = Suc k" using suc_k' by argo
              hence i_eq_k: "i = k" using case2 by force
              hence step_run': "(run' ! k, word ! k, run' ! (k + 1)) \<in> transitions \<A>" using assms case4 unfolding run_well_defined_def pseudo_run_well_defined_def by blast
              have "k < length run'" using gap len by simp
              hence "last ?pref_run' = run' ! k" using last_and_take_list lessI less_nat_zero_code list.size(3) nth_take by metis
              hence "last run_clean' = run' ! k" using clean' by simp
              hence nth_left: "(run_clean' @ drop (Suc k) run') ! i = run' ! k" using case2 i_eq_k rc_nonempty list_properties_not_empty suc_k lessI nth_append by metis
              have "(run_clean' @ drop (Suc k) run') ! (i + 1) = run' ! (k + 1)" using i_eq_k Nat.add_0_right Suc_eq_plus1 append_take_drop_id nth_append_length_plus suc_k suc_k' by metis
              thus ?thesis using step_run' nth_left i_eq_k by argo     
            next
              case case5
              hence "drop (Suc k) run' = []" by simp
              hence "(run_clean' @ drop (Suc k) run') = run_clean'" by blast
              thus ?thesis using assm case2 by auto
            qed
          next
            case case3
            have rc_nonempty: "run_clean' \<noteq> []" using clean' unfolding run_well_defined_def pseudo_run_well_defined_def by force
            have suc_k: "length ?pref_run = Suc k" using gap by force
            have "length ?pref_run' = length ?pref_run" using pref_wd unfolding run_well_defined_def pseudo_run_well_defined_def by argo
            hence suc_k': "length ?pref_run' = Suc k" using suc_k by argo
            have "length ?pref_run' = length run_clean'" using pref_wd clean' unfolding run_well_defined_def pseudo_run_well_defined_def by argo
            hence suc_k: "length run_clean' = Suc k" using suc_k' by argo
            then obtain t where t_def: "i = length run_clean' + t" using case3 less_natE by auto
            have i_bound: "i < length (run_clean' @ drop (Suc k) run') - 1" using assm by argo
            have len_run': "length (run_clean' @ drop (Suc k) run') = length run'" using suc_k gap len by force
            hence i_less: "i < length run' - 1" using i_bound by argo
            hence t_bound: "t < length run' - Suc k - 1" using t_def suc_k by auto
            have idx_cur: "(run_clean' @ drop (Suc k) run') ! i = run' ! i" using t_def append_take_drop_id lenlen nth_append_length_plus by metis
            have idx_nxt: "(run_clean' @ drop (Suc k) run') ! (i + 1) = run' ! (i + 1)" using case3 i_less len_run' append_take_drop_id lenlen nth_list_append1 by metis
            have "(run' ! i, word ! i, run' ! (i + 1)) \<in> transitions \<A>" using assms i_less unfolding run_well_defined_def pseudo_run_well_defined_def by blast
            thus ?thesis using idx_cur idx_nxt by argo
          qed
        }
        thus ?thesis using init pref_len unfolding pseudo_run_well_defined_def run_well_defined_def by blast
      qed
      then consider (case6) "k < length run' - 1" | (case7) "k = length run' - 1" using gap len by linarith
      hence last_big: "last (run_clean' @ drop (Suc k) run') = last run'"
      proof cases
        case case6 thus ?thesis by auto
      next
        case case7
        hence "drop (Suc k) run' = []" by simp
        hence equi1: "(run_clean' @ drop (Suc k) run') = run_clean'" by blast
        have equi2: "last run_clean' = last ?pref_run'" using clean' by blast
        have "?pref_run' = run'" using case7 by simp
        thus ?thesis using equi1 equi2 by argo
      qed
      have "run' = ?pref_run' @ (drop (Suc k) run')" by auto
      hence strict_big: "acc_sum \<A> run' < acc_sum \<A> (run_clean' @ drop (Suc k) run')" using lt acc_sum_append_strict_mono lenlen by metis
      have "acc_sum \<A> (run_clean' @ drop (Suc k) run') \<le> acc_sum \<A> run" using no_steal_run_has_max_acc_sum[OF assms(1), where Run=Run and run=run and run'="(run_clean' @ drop (Suc k) run')" and word=word] assms big_wd last_big by argo
      thus False using strict_big case2 by force
    qed
    thus False by blast
  qed
qed

lemma uniform_components_upper_step: "\<forall> S_m \<in> set (fst (upper_step \<A> a S)) . S_m \<subseteq> accepting_states \<A> \<or> S_m \<inter> accepting_states \<A> = {}"
  by (induction S) auto

lemma no_steal_runs_always_same_level:
  assumes "auto_well_defined \<A>" "run_well_defined Run (upper_part_pure \<A>) word" "run_well_defined run \<A> word" "run_well_defined run' \<A> word" "\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run Run word k" "\<nexists> k . k < length run' - 1 \<and> stolen_at \<A> run' Run word k" "last run = last run'"
  shows "\<forall> k < length run . samelevel run run' Run k"
proof - 
  have leq: "acc_sum \<A> run' \<le> acc_sum \<A> run" using assms no_steal_run_has_max_acc_sum by blast
  have "acc_sum \<A> run \<le> acc_sum \<A> run'" using assms no_steal_run_has_max_acc_sum by metis
  hence equi: "acc_sum \<A> run = acc_sum \<A> run'" using leq by auto
  have length: "length run = length run'" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  hence iff_l: "\<forall> l < length run . (run ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run' ! l \<in> accepting_states \<A>)" using equi same_acc_states_equals_same_acc_sum_right by metis
  have iff_r: "\<forall> l < length run' . (run' ! l \<in> accepting_states \<A>) \<longleftrightarrow> (run ! l \<in> accepting_states \<A>)" using equi length same_acc_states_equals_same_acc_sum_right by metis
  {
    fix k assume assm: "k < length run"
    then consider (case1) "samelevel run run' Run k" | (case2) "leftgap run run' Run k" | (case3) "rightgap run run' Run k" using assms samelevel_or_leftgap_or_rightgap by blast
    hence "samelevel run run' Run k"
    proof cases
      case case1 thus ?thesis by blast
    next
      case case2 thus ?thesis using assms assm no_steal_same_acc_no_level_gap iff_l by blast
    next
      case case3
      have "k < length run'" using length assm by simp
      hence "\<not> leftgap run' run Run k" using assms no_steal_same_acc_no_level_gap iff_r by blast
      hence "\<not> rightgap run run' Run k" unfolding leftgap_def rightgap_def by blast
      thus ?thesis using case3 by blast
    qed
  }
  thus ?thesis by blast
qed

lemma component_uniform_acc:
  assumes "run_well_defined Run (upper_part_pure \<A>) word" "k < length Run" "i < length (Run ! k)"
  shows "(Run ! k) ! i \<subseteq> accepting_states \<A> \<or> (Run ! k) ! i \<inter> accepting_states \<A> = {}"
proof (cases k)
  case 0
  have "Run ! 0 = [{initial_state \<A>}]" using assms unfolding run_well_defined_def pseudo_run_well_defined_def upper_part_pure_def by force
  hence "(Run ! k) ! i = {initial_state \<A>}" using 0 assms by auto
  thus ?thesis by auto
next
  case (Suc n)
  hence "(Run ! n, word ! n, Run ! Suc n) \<in> transitions (upper_part_pure \<A>)" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by force
  hence "Run ! Suc n = filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> (word ! n) (Run ! n)))" unfolding upper_part_pure_def upper_transitions_def by auto
  hence mem_fst: "(Run ! Suc n) ! i \<in> set (fst (upper_step \<A> (word ! n) (Run ! n)))" using assms Suc using nth_mem by fastforce
  have "\<forall> S_m \<in> set (fst (upper_step \<A> (word ! n) (Run ! n))) . S_m \<subseteq> accepting_states \<A> \<or> S_m \<inter> accepting_states \<A> = {}" using uniform_components_upper_step by fast
  thus ?thesis using Suc mem_fst by blast
qed

lemma same_acc_sum_for_equal_level_runs_left:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined Run (upper_part_pure \<A>) word \<and> run_well_defined alpha \<A> word \<and> run_well_defined beta \<A> word \<and> (\<forall> k < length alpha . samelevel alpha beta Run k) \<Longrightarrow> acc_sum \<A> alpha = acc_sum \<A> beta"
proof(induction word arbitrary: Run alpha beta rule: rev_induct)
  case Nil
  hence "alpha = [initial_state \<A>] \<and> beta = [initial_state \<A>]" using list_with_one_element unfolding run_well_defined_def pseudo_run_well_defined_def by force
  thus ?case by blast
next
  case (snoc a word)
  hence runs: "run_well_defined Run (upper_part_pure \<A>) (word @ [a]) \<and> run_well_defined alpha \<A> (word @ [a]) \<and> run_well_defined beta \<A> (word @ [a])" by blast
  hence not_empty: "Run \<noteq> [] \<and> beta \<noteq> [] \<and> alpha \<noteq> [] \<and> length beta = length alpha \<and> length Run = length alpha" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain Run' beta' alpha' where var: "Run = Run' @ [last Run] \<and> beta = beta' @ [last beta] \<and> alpha = alpha' @ [last alpha]" using append_butlast_last_id by metis
  hence runs': "run_well_defined Run' (upper_part_pure \<A>) word \<and> run_well_defined alpha' \<A> word \<and> run_well_defined beta' \<A> word \<and> (last alpha', a, last alpha) \<in> transitions \<A> \<and> (last beta', a, last beta) \<in> transitions \<A>" using runs prun_well_defined_extension_snoc unfolding run_well_defined_def by metis
  have len: "length beta' = length alpha' \<and> length Run' = length alpha'" using not_empty var butlast_snoc length_butlast by metis
  {
    fix k assume k: "k < length alpha'"
    have "length alpha' = length alpha - 1" using not_empty var butlast_snoc length_butlast by metis
    hence "k < length alpha" using k by linarith
    then obtain i where i: "i < length (Run ! k) \<and> alpha ! k \<in> (Run ! k) ! i \<and> beta ! k \<in> (Run ! k) ! i" using snoc unfolding samelevel_def by blast
    have "Run' ! k = Run ! k \<and> alpha' ! k = alpha ! k \<and> beta' ! k = beta ! k" using k len list_properties_length var by metis
    hence "i < length (Run' ! k) \<and> alpha' ! k \<in> (Run' ! k) ! i \<and> beta' ! k \<in> (Run' ! k) ! i" using i by auto
    hence "\<exists> i . i < length (Run' ! k) \<and> alpha' ! k \<in> (Run' ! k) ! i \<and> beta' ! k \<in> (Run' ! k) ! i" by blast
  }
  hence "\<forall> k < length alpha' . \<exists> i . i < length (Run' ! k) \<and> alpha' ! k \<in> (Run' ! k) ! i \<and> beta' ! k \<in> (Run' ! k) ! i" by blast
  hence equi: "acc_sum \<A> alpha' = acc_sum \<A> beta'" using snoc runs' unfolding samelevel_def by blast
  have acc_sum: "acc_sum \<A> alpha = 2 * acc_sum \<A> alpha' + acc_sum \<A> [last alpha] \<and> acc_sum \<A> beta = 2 * acc_sum \<A> beta' + acc_sum \<A> [last beta]" using var acc_sum_snoc by metis
  have "length alpha - 1 < length alpha" using not_empty by force
  hence lele: "length alpha - 1 < length alpha \<and> length alpha - 1 < length Run" using not_empty by argo
  then obtain i where i: "i < length (Run ! (length alpha - 1)) \<and> alpha ! (length alpha - 1) \<in> (Run ! (length alpha - 1)) ! i \<and> beta ! (length alpha - 1) \<in> (Run ! (length alpha - 1)) ! i" using snoc unfolding samelevel_def by presburger
  have "length alpha - 1 = length Run - 1 \<and> length beta - 1 = length alpha - 1" using len not_empty by argo
  hence "Run ! (length alpha - 1) = last Run \<and> alpha ! (length alpha - 1) = last alpha \<and> beta ! (length alpha - 1) = last beta" using not_empty list_properties_not_empty by metis
  hence in_set: "i < length (Run ! (length alpha - 1)) \<and> last alpha \<in> (Run ! (length alpha - 1)) ! i \<and> last beta \<in> (Run ! (length alpha - 1)) ! i" using i by argo
  hence "(Run ! (length alpha - 1)) ! i \<subseteq> accepting_states \<A> \<or> (Run ! (length alpha - 1)) ! i \<inter> accepting_states \<A> = {}" using component_uniform_acc lele runs by blast
  hence "last alpha \<in> accepting_states \<A> \<longleftrightarrow> last beta \<in> accepting_states \<A>" using in_set by blast
  thus ?case using equi acc_sum by force
qed

proposition no_stealing_runs_samelevel_iff_same_acc_sum:
  assumes "auto_well_defined \<A>" "run_well_defined Run (upper_part_pure \<A>) word" "run_well_defined run \<A> word" "run_well_defined run' \<A> word" "\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run Run word k" "\<nexists> k . k < length run' - 1 \<and> stolen_at \<A> run' Run word k" "last run = last run'"
  shows "(\<forall> k < length run . samelevel run run' Run k) \<longleftrightarrow> acc_sum \<A> run = acc_sum \<A> run'"
proof - 
  have "(\<forall> k < length run . samelevel run run' Run k) \<Longrightarrow> acc_sum \<A> run = acc_sum \<A> run'" using assms same_acc_sum_for_equal_level_runs_left by blast
  thus ?thesis using assms no_steal_runs_always_same_level by blast
qed

lemma no_steal_and_greedy_right:
  assumes "auto_well_defined \<A>" "run_well_defined Run (upper_part_pure \<A>) word" "run_well_defined run \<A> word" "\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run Run word k"
  shows "greedy_run run \<A> word"
proof(rule ccontr)
  assume "\<not> greedy_run run \<A> word"
  hence "\<exists> run' . run_well_defined run' \<A> word \<and> last run' = last run \<and> (acc_sum \<A> run') > (acc_sum \<A> run)" using assms unfolding greedy_run_def by blast
  then obtain run' where run': "run_well_defined run' \<A> word \<and> last run' = last run \<and> (acc_sum \<A> run') > (acc_sum \<A> run)" by blast
  hence "acc_sum \<A> run' \<le> acc_sum \<A> run" using no_steal_run_has_max_acc_sum assms by metis 
  thus False using run' by force
qed

lemma no_steal_and_greedy_left:
  assumes "auto_well_defined \<A>"
  shows "run_well_defined Run (upper_part_pure \<A>) word \<and> greedy_run run \<A> word \<Longrightarrow> \<nexists> k . k < length run - 1 \<and> stolen_at \<A> run Run word k"
proof(induction word arbitrary: run Run rule: rev_induct)
  case Nil
  hence "run_well_defined run \<A> []" unfolding greedy_run_def by blast
  hence "length run = 1" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  thus ?case by simp
next
  case (snoc a word)
  hence well_def: "run_well_defined run \<A> (word @ [a]) \<and> run_well_defined Run (upper_part_pure \<A>) (word @ [a])" unfolding greedy_run_def by blast
  hence not_empty: "run \<noteq> [] \<and> Run \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
  then obtain run' Run' where vars: "run = run' @ [last run] \<and> Run = Run' @ [last Run]" using append_butlast_last_id by metis
  hence props: "run_well_defined run' \<A> word \<and> (last run', a, last run) \<in> transitions \<A> \<and> run_well_defined Run' (upper_part_pure \<A>) word \<and> (last Run', a, last Run) \<in> transitions (upper_part_pure \<A>)" using well_def prun_well_defined_extension_snoc unfolding run_well_defined_def by metis
  hence equi_length: "length run' = length Run'" unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  have "greedy_run run' \<A> word" using snoc vars greedy_run_snoc by metis
  hence IH_no_steal: "\<nexists> k . k < length run' - 1 \<and> stolen_at \<A> run' Run' word k" using snoc props by blast
  show ?case
  proof (rule ccontr)
    assume "\<not> (\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run Run (word @ [a]) k)"
    then obtain k where k: "k < length run - 1 \<and> stolen_at \<A> run Run (word @ [a]) k" by blast
    have length: "length run = length run' + 1 \<and> length Run = length Run' + 1" using vars One_nat_def length_Cons length_append list.size(3) by metis
    have len_word: "length run = length (word @ [a]) + 1" using well_def unfolding run_well_defined_def pseudo_run_well_defined_def by blast
    hence len_word_pref: "length run' = length word + 1" using length by simp
    consider (old) "k < length run' - 1" | (last) "k = length run' - 1" using k length by linarith
    thus False
    proof cases
      case old thus ?thesis using k vars equi_length len_word_pref stolen_at_lower_place IH_no_steal by metis
    next
      case last
      hence k_2: "k = length run - 2" using length by simp
      hence stolen: "stolen_at \<A> run Run (word @ [a]) (length run - 2)" using k by blast
      then obtain m n where mn: "m < n \<and> m < length (Run ! (length run - 2)) \<and> n < length (Run ! (length run - 2)) \<and> run ! (length run - 2) \<in> (Run ! (length run - 2)) ! m \<and> run ! (Suc (length run - 2)) \<in> post_set \<A> ((Run ! (length run - 2)) ! n) ((word @ [a]) ! (length run - 2))" unfolding stolen_at_def by blast
      have suc_eq: "(Suc (length run - 2)) = length run - 1" by (simp add: len_word_pref length)
      obtain run_no_steal where run_no_steal: "run_well_defined run_no_steal \<A> (word @ [a]) \<and> last run = last run_no_steal \<and> (\<nexists> k . k < length run_no_steal - 1 \<and> stolen_at \<A> run_no_steal Run (word @ [a]) k)" using assms existence_of_run_without_stealing well_def by blast
      hence lenlen: "length run_no_steal = length run \<and> run_no_steal \<noteq> []" using well_def unfolding run_well_defined_def pseudo_run_well_defined_def by force
      hence last_equi: "run ! (length run - 1) = run_no_steal ! (length run - 1)" using list_properties_not_empty run_no_steal not_empty by metis
      have not_stolen: "\<not> stolen_at \<A> run_no_steal Run (word @ [a]) (length run - 2)" using run_no_steal k k_2 lenlen by metis
      have "length run - 2 < length run_no_steal" using k_2 add_diff_cancel_right' k length trans_less_add1 lenlen by metis
      then obtain h where h: "h < length (Run ! (length run - 2)) \<and> run_no_steal ! (length run - 2) \<in> (Run ! (length run - 2)) ! h" using assms well_def run_no_steal run_state_in_upper_component by blast
      have "m < h"
      proof (rule ccontr)
        assume "\<not> m < h"
        hence "h \<le> m" by simp
        hence h_lt_n: "h < n" using mn by linarith
        have comp_h: "run_no_steal ! (length run - 2) \<in> (Run ! (length run - 2)) ! h" using h by blast
        have "run_no_steal ! (Suc (length run - 2)) \<in> post_set \<A> ((Run ! (length run - 2)) ! n) ((word @ [a]) ! (length run - 2))" using mn last_equi suc_eq by argo
        hence "\<exists> h n . h < n \<and> h < length (Run ! (length run - 2)) \<and> n < length (Run ! (length run - 2)) \<and> run_no_steal ! (length run - 2) \<in> (Run ! (length run - 2)) ! h \<and> run_no_steal ! (Suc (length run - 2)) \<in> post_set \<A> ((Run ! (length run - 2)) ! n) ((word @ [a]) ! (length run - 2))" using h_lt_n comp_h mn h by blast
        hence "stolen_at \<A> run_no_steal Run (word @ [a]) (length run - 2)" unfolding stolen_at_def by blast
        thus False using not_stolen by blast
      qed
      hence "rightgap run_no_steal run Run (length run - 2)" using mn h h unfolding rightgap_def by blast
      hence "\<exists> k < length run_no_steal . rightgap run_no_steal run Run k" using lenlen k_2 last length Suc_eq_plus1 diff_less_Suc by metis
      hence "acc_sum \<A> run < acc_sum \<A> run_no_steal" using no_steal_run_has_max_acc_sum_unique assms run_no_steal well_def by metis
      thus ?thesis using snoc run_no_steal unfolding greedy_run_def by auto
    qed
  qed
qed

theorem no_steal_iff_greedy:
  assumes "auto_well_defined \<A>" "run_well_defined Run (upper_part_pure \<A>) word" "run_well_defined run \<A> word"
  shows "greedy_run run \<A> word \<longleftrightarrow> (\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run Run word k)"
  using assms no_steal_and_greedy_left no_steal_and_greedy_right by blast

lemma not_empty_omega_run:
  assumes "auto_well_defined \<A>" "omega_run_well_defined r \<A> x" "omega_run_well_defined Run (upper_part_pure \<A>) x"
  shows "\<forall> n . Run n \<noteq> []"
proof - 
  {
    fix n
    have "run_well_defined (pre_omega_run r n) \<A> (pre_omega_word x n) \<and> last (pre_omega_run r n) = r n" using assms omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
    then obtain Run' where Run': "run_well_defined Run' (upper_part_pure \<A>) (pre_omega_word x n) \<and> r n \<in> \<Union> (set (last Run'))" using assms run_on_upper_last by metis
    have well_def: "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
    have DFA: "DFA_property (upper_part_pure \<A>)" using assms DFA_property_upper_part_pure by blast
    have word: "word_well_defined (pre_omega_word x n) (alphabet (upper_part_pure \<A>))" using well_def well_def_implies_word_well_defined Run' unfolding run_well_defined_def by fast
    have "run_well_defined (pre_omega_run Run n) (upper_part_pure \<A>) (pre_omega_word x n) \<and> last (pre_omega_run Run n) = Run n"  using assms omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
    hence "pre_omega_run Run n = Run' \<and> last (pre_omega_run Run n) = Run n" using exists_only_one_run_for_DFA well_def DFA word Run' by fast
    hence "r n \<in> \<Union> (set (Run n))" using Run' by argo
    hence "Run n \<noteq> []" by auto
  }
  thus ?thesis by blast
qed

proposition omega_greedy_run_from_upper_run:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []"
  shows "\<exists> r . omega_greedy_run r \<A> x \<and> (\<forall> n . r n \<in> \<Union> (set (Run n)))"
proof -
  {
    fix n
    have Run_pref: "run_well_defined (pre_omega_run Run (Suc n)) (upper_part_pure \<A>) (pre_omega_word x (Suc n))" using assms omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
    have last_eq: "last (pre_omega_run Run (Suc n)) = Run (Suc n)" by (simp add: pre_omega_run_last)
    have not_empty: "Run (Suc n) \<noteq> []" using assms not_empty_omega_run by blast
    have "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
    hence "Run (Suc n) \<in> states (upper_part_pure \<A>)" using assms well_def_implies_omega_prun_states unfolding omega_prun_states_def omega_run_well_defined_def by fast
    hence "Run (Suc n) \<in> upper_states \<A> \<or> Run (Suc n) \<in> {[]}" unfolding upper_part_pure_def by auto
    hence "Run (Suc n) \<in> upper_states \<A>" using not_empty by blast     
    hence "\<forall> S_m \<in> set (Run (Suc n)) . S_m \<noteq> {}" unfolding upper_states_def by fast
    hence "\<Union> (set (last (pre_omega_run Run (Suc n)))) \<noteq> {}" using last_eq not_empty by auto
    then obtain s where s: "s \<in> \<Union> (set (last (pre_omega_run Run (Suc n))))" by fast
    then obtain run where run: "run_well_defined run \<A> (pre_omega_word x (Suc n)) \<and> last run = s" using upper_run_reaches_all[OF assms(1) Run_pref] by blast
    hence "\<exists> run . run_well_defined run \<A> (pre_omega_word x (Suc n)) \<and> last run \<in> \<Union> (set (Run (Suc n)))" using last_eq s by auto
    hence "\<exists> run . greedy_run run \<A> (pre_omega_word x (Suc n)) \<and> last run \<in> \<Union> (set (Run (Suc n)))" using assms greedy_run_exists by metis
  }
  hence prefix_runs: "\<forall> n . \<exists> run . greedy_run run \<A> (pre_omega_word x (Suc n)) \<and> last run \<in> \<Union> (set (Run (Suc n)))" by blast
  then obtain r where r_wd: "omega_greedy_run r \<A> x" using omega_run_exists_if_all_prefix_runs[OF assms(1)] unfolding greedy_run_def by blast
  {
    fix n
    have r_pref_wd: "run_well_defined (pre_omega_run r n) \<A> (pre_omega_word x n)" using r_wd omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def omega_greedy_run_def by metis
    then obtain Run' where Run': "run_well_defined Run' (upper_part_pure \<A>) (pre_omega_word x n) \<and> last (pre_omega_run r n) \<in> \<Union> (set (last Run'))" using run_on_upper_last[OF assms(1)] by blast
    have upper_wd: "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
    have upper_dfa: "DFA_property (upper_part_pure \<A>)" using assms DFA_property_upper_part_pure by blast
    have pref_Run_wd: "run_well_defined (pre_omega_run Run n) (upper_part_pure \<A>) (pre_omega_word x n)" using assms omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
    have pref_word_wd: "word_well_defined (pre_omega_word x n) (alphabet (upper_part_pure \<A>))" using pref_Run_wd upper_wd well_def_implies_word_well_defined unfolding run_well_defined_def by fast
    have uniq: "\<exists>! R . run_well_defined R (upper_part_pure \<A>) (pre_omega_word x n)" using exists_only_one_run_for_DFA[OF upper_wd upper_dfa pref_word_wd] by simp
    hence "Run' = pre_omega_run Run n" using Run' pref_Run_wd by blast
    hence "last (pre_omega_run r n) \<in> \<Union> (set (last (pre_omega_run Run n)))" using Run' by simp
    hence "last (pre_omega_run r n) \<in> \<Union> (set (Run n))" by (simp add: pre_omega_run_last)
  } 
  hence "\<forall> n . r n \<in> \<Union> (set (Run n))" by (simp add: pre_omega_run_last)
  thus ?thesis using r_wd by blast
qed

proposition accepting_run_on_upper_part_means_no_run:
  assumes "auto_well_defined \<A>" "omega_word \<in> omega_language_auto (upper_part_pure \<A>)"
  shows "omega_word_well_defined omega_word (alphabet \<A>) \<and> (\<nexists> omega_run . omega_run_well_defined omega_run \<A> omega_word)"
proof (rule ccontr)
  assume assm: "\<not> (omega_word_well_defined omega_word (alphabet \<A>) \<and> (\<nexists> omega_run . omega_run_well_defined omega_run \<A> omega_word))"
  have "omega_word_well_defined omega_word (alphabet (upper_part_pure \<A>))" using assms by (simp add: omega_word_in_omega_language_is_well_defined well_def_upper_part_pure)
  hence "omega_word_well_defined omega_word (alphabet \<A>)" unfolding upper_part_pure_def by simp
  then obtain omega_run where omega_run: "omega_run_well_defined omega_run \<A> omega_word" using assm by blast
  obtain omega_Run where omega_Run: "omega_run_accepting omega_Run (upper_part_pure \<A>) omega_word" using assms unfolding omega_language_auto_def by blast
  hence no_empty: "\<forall> n . omega_Run n \<noteq> []" using not_empty_omega_run assms omega_run unfolding omega_run_accepting_def by blast
  have "\<forall> n . \<exists> N > n . omega_Run N \<in> accepting_states (upper_part_pure \<A>)" using omega_Run unfolding omega_run_accepting_def by blast
  hence "\<exists> N > 0 . omega_Run N = []" unfolding upper_part_pure_def by auto
  thus False using no_empty by blast
qed

theorem accepting_run_on_upper_part_pure_iff_no_run:
  assumes "auto_well_defined \<A>"
  shows "omega_word \<in> omega_language_auto (upper_part_pure \<A>) \<longleftrightarrow> omega_word_well_defined omega_word (alphabet \<A>) \<and> (\<nexists> omega_run . omega_run_well_defined omega_run \<A> omega_word)"
  using assms accepting_run_on_upper_part_means_no_run no_run_means_accepting_run_on_upper_part_pure by blast

definition upper_child :: "('s states list) state \<Rightarrow> 'a symbol \<Rightarrow> ('s, 'a) automaton \<Rightarrow> ('s states list) state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "upper_child p a \<A> q j k = (j < length p \<and> k < length q \<and> q ! k \<subseteq> post_set \<A> (p ! j) a \<and> q ! k \<inter> snd (upper_step \<A> a (drop (Suc j) p)) = {})"

lemma lemma_3_4_12_left_to_right:
  assumes "auto_well_defined \<A>" "omega_greedy_run r \<A> x"
  shows "\<exists> Run js . omega_run_well_defined Run (upper_part_pure \<A>) x \<and> (\<forall> i . js i < length (Run i) \<and> r i \<in> (Run i) ! (js i) \<and> r (Suc i) \<in> (Run (Suc i)) ! (js (Suc i)) \<and> upper_child (Run i) (x i) \<A> (Run (Suc i)) (js i) (js (Suc i)))"
proof -
  have omega_r: "omega_pseudo_run_well_defined r \<A> (initial_state \<A>) x" using assms unfolding omega_greedy_run_def omega_run_well_defined_def by blast
  have well_def: "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
  have DFA: "DFA_property (upper_part_pure \<A>)" using assms DFA_property_upper_part_pure by blast
  have alpha: "alphabet \<A> = alphabet (upper_part_pure \<A>)" unfolding upper_part_pure_def by simp
  have "omega_word_well_defined x (alphabet \<A>)" using omega_r assms well_def_implies_omega_word_well_defined by fast
  then obtain Run where Run: "omega_run_well_defined Run (upper_part_pure \<A>) x" using exists_only_one_omega_run_for_DFA well_def assms DFA alpha by metis
  define js where "js = (\<lambda>i . (LEAST j . j < length (Run i) \<and> r i \<in> (Run i) ! j))"
  {
    fix i
    have "js i < length (Run i) \<and> r i \<in> (Run i) ! (js i) \<and> r (Suc i) \<in> (Run (Suc i)) ! (js (Suc i)) \<and> upper_child (Run i) (x i) \<A> (Run (Suc i)) (js i) (js (Suc i))"
    proof(induction i)
      case 0
      have r0: "r 0 = initial_state \<A>" using assms unfolding omega_greedy_run_def omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
      have "Run 0 = initial_state (upper_part_pure \<A>)" using Run unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by presburger
      hence Run0: "Run 0 = [{initial_state \<A>}]" unfolding upper_part_pure_def by auto
      hence props: "0 < length (Run 0) \<and> r 0 \<in> (Run 0) ! 0" using r0 by simp
      hence equi: "js 0 = 0" unfolding js_def by force
      hence js0: "(js 0 < length (Run 0)) \<and> (r 0 \<in> (Run 0) ! (js 0))" using props by presburger
      have "\<exists> j1 < length (Run 1) . r 1 \<in> (Run 1) ! j1"
      proof -
        have "pseudo_run_well_defined (pre_omega_run r 1) \<A> (initial_state \<A>) (pre_omega_word x 1) \<and> last (pre_omega_run r 1) = r 1" using omega_run_implies_pre_run_well_def omega_r by metis
        then obtain Run_pre where Run_pre: "run_well_defined Run_pre (upper_part_pure \<A>) (pre_omega_word x 1) \<and> r 1 \<in> \<Union> (set (last Run_pre))" using run_on_upper_last assms unfolding run_well_defined_def by metis
        hence "word_well_defined (pre_omega_word x 1) (alphabet (upper_part_pure \<A>))" using well_def_implies_word_well_defined well_def unfolding run_well_defined_def by fast
        hence uniq: "\<exists>! r'. run_well_defined r' (upper_part_pure \<A>) (pre_omega_word x 1)" using exists_only_one_run_for_DFA DFA well_def by blast
        have len: "length (pre_omega_run Run 1) = 2" by (simp add: pre_omega_run_length)
        have pre_run: "run_well_defined (pre_omega_run Run 1) (upper_part_pure \<A>) (pre_omega_word x 1)" using Run omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis 
        hence "(pre_omega_run Run 1) ! 0 = Run 0 \<and> (pre_omega_run Run 1) ! 1 = Run 1" using len pre_omega_run_nth unfolding run_well_defined_def by blast
        hence "(pre_omega_run Run 1) = [Run 0, Run 1]" using list_with_two_elements len by fast
        hence "Run_pre = [Run 0, Run 1]" using pre_run uniq Run_pre by blast
        hence "r 1 \<in> \<Union> (set (Run 1))" using Run_pre by auto
        thus ?thesis using Union_iff in_set_conv_nth by metis
      qed
      hence js1: "js 1 < length (Run 1) \<and> r 1 \<in> (Run 1) ! (js 1)" unfolding js_def by (rule LeastI_ex)
      hence Suc: "r (Suc 0) \<in> (Run (Suc 0)) ! (js (Suc 0))" by auto
      have not_empty: "Run 1 \<noteq> []" using js1 by auto
      have "(0::nat) + 1 = 1" by auto
      hence "(Run 0, x 0, Run 1) \<in> transitions (upper_part_pure \<A>)" using Run unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by metis
      hence "Run 1 = filter (\<lambda>S . S \<noteq> {}) (fst (upper_step \<A> (x 0) [{initial_state \<A>}]))" using Run0 not_empty unfolding upper_part_pure_def upper_transitions_def by force
      hence "(Run 1) ! (js 1) \<in> set (fst (upper_step \<A> (x 0) [{initial_state \<A>}]))" using js1 nth_mem set_filter mem_Collect_eq by (metis (no_types, lifting))
      hence "(Run 1) ! (js 1) \<subseteq> post_set \<A> {initial_state \<A>} (x 0)" by auto
      hence "(upper_child (Run 0) (x 0) \<A> (Run (Suc 0)) (js 0) (js (Suc 0)))" using Run0 equi js0 js1 unfolding upper_child_def by auto
      thus ?case using js0 Suc unfolding js_def by blast
    next
      case (Suc i)
      hence eq4: "(js (Suc i)) < length (Run (Suc i)) \<and> r (Suc i) \<in> Run (Suc i) ! (js (Suc i))" unfolding upper_child_def by blast
      have "run_well_defined (pre_omega_run r (Suc (Suc i))) \<A> (pre_omega_word x (Suc (Suc i))) \<and> last (pre_omega_run r (Suc (Suc i))) = r (Suc (Suc i))" using omega_r omega_run_implies_pre_run_well_def unfolding run_well_defined_def by metis
      then obtain Run' where Run': "run_well_defined Run' (upper_part_pure \<A>) (pre_omega_word x (Suc (Suc i))) \<and> r (Suc (Suc i)) \<in> \<Union> (set (last Run'))" using assms run_on_upper_last by metis
      hence word: "word_well_defined (pre_omega_word x (Suc (Suc i))) (alphabet (upper_part_pure \<A>))" using well_def well_def_implies_word_well_defined unfolding run_well_defined_def by fast
      have well_def_R: "run_well_defined (pre_omega_run Run (Suc (Suc i))) (upper_part_pure \<A>) (pre_omega_word x (Suc (Suc i))) \<and> last (pre_omega_run Run (Suc (Suc i))) = Run (Suc (Suc i))" using Run omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
      hence "pre_omega_run Run (Suc (Suc i)) = Run' \<and> last (pre_omega_run Run (Suc (Suc i))) = Run (Suc (Suc i))" using exists_only_one_run_for_DFA well_def DFA word Run' by fast
      hence "r (Suc (Suc i)) \<in> \<Union> (set (Run (Suc (Suc i))))" using Run' by argo
      hence "\<exists> j2 < length (Run (Suc (Suc i))) . r (Suc (Suc i)) \<in> (Run (Suc (Suc i))) ! j2" using in_set_conv_nth Union_iff by metis
      hence eq5: "js (Suc (Suc i)) < length (Run (Suc (Suc i))) \<and> r (Suc (Suc i)) \<in> (Run (Suc (Suc i))) ! (js (Suc (Suc i)))" unfolding js_def by (rule LeastI_ex)
      have not_stolen: "r (Suc (Suc i)) \<notin> (\<Union> k \<in> {k . js (Suc i) < k \<and> k < length (Run (Suc i))} . post_set \<A> ((Run (Suc i)) ! k) (x (Suc i)))"
      proof(rule ccontr)
        assume "\<not> r (Suc (Suc i)) \<notin> (\<Union> k \<in> {k . js (Suc i) < k \<and> k < length (Run (Suc i))} . post_set \<A> ((Run (Suc i)) ! k) (x (Suc i)))"
        hence "r (Suc (Suc i)) \<in> (\<Union> k \<in> {k . js (Suc i) < k \<and> k < length (Run (Suc i))} . post_set \<A> ((Run (Suc i)) ! k) (x (Suc i)))" by blast
        hence ex_k_le: "\<exists> j < length (Run (Suc i)) . js (Suc i) < j \<and> j < length (Run (Suc i)) \<and> r (Suc (Suc i)) \<in> post_set \<A> ((Run (Suc i)) ! j) (x (Suc i))" by blast
        hence "\<exists> j \<le> length (Run (Suc i)) - 1 . js (Suc i) < j \<and> j < length (Run (Suc i)) \<and> r (Suc (Suc i)) \<in> post_set \<A> ((Run (Suc i)) ! j) (x (Suc i))" using Nat.lessE diff_Suc_1 less_or_eq_imp_le by metis
        hence "\<exists> m \<le> length (Run (Suc i)) - 1 . js (Suc i) < m \<and> m < length (Run (Suc i)) \<and> r (Suc (Suc i)) \<in> post_set \<A> ((Run (Suc i)) ! m) (x (Suc i)) \<and> (\<forall> k . m < k \<and> k \<le> length (Run (Suc i)) - 1 \<longrightarrow> \<not> (js (Suc i) < k \<and> k < length (Run (Suc i)) \<and> r (Suc (Suc i)) \<in> post_set \<A> ((Run (Suc i)) ! k) (x (Suc i))))" using exists_max_index[where n="length (Run (Suc i)) - 1" and P="\<lambda>j. js (Suc i) < j \<and> j < length (Run (Suc i)) \<and> r (Suc (Suc i)) \<in> post_set \<A> ((Run (Suc i)) ! j) (x (Suc i))"] by blast
        then obtain k where k: "k \<le> length (Run (Suc i)) - 1 \<and> js (Suc i) < k \<and> k < length (Run (Suc i)) \<and> r (Suc (Suc i)) \<in> post_set \<A> ((Run (Suc i)) ! k) (x (Suc i)) \<and> (\<forall> j . k < j \<and> j \<le> length (Run (Suc i)) - 1 \<longrightarrow> \<not> (js (Suc i) < j \<and> j < length (Run (Suc i)) \<and> r (Suc (Suc i)) \<in> post_set \<A> ((Run (Suc i)) ! j) (x (Suc i))))" by blast
        hence k: "k < length (Run (Suc i)) \<and> js (Suc i) < k \<and> k < length (Run (Suc i)) \<and> r (Suc (Suc i)) \<in> post_set \<A> ((Run (Suc i)) ! k) (x (Suc i)) \<and> (\<forall> j . k < j \<and> j \<le> length (Run (Suc i)) - 1 \<longrightarrow> \<not> (js (Suc i) < j \<and> j < length (Run (Suc i)) \<and> r (Suc (Suc i)) \<in> post_set \<A> ((Run (Suc i)) ! j) (x (Suc i))))" by blast
        then obtain q where q: "q \<in> (Run (Suc i)) ! k \<and> (q, x (Suc i), r (Suc (Suc i))) \<in> transitions \<A>" unfolding post_set_def by blast
        have pre_Run: "run_well_defined (pre_omega_run Run (Suc i)) (upper_part_pure \<A>) (pre_omega_word x (Suc i))" using Run omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
        hence Run_suc_i: "last (pre_omega_run Run (Suc i)) = Run (Suc i)" using pre_omega_run_last by blast
        hence "q \<in> \<Union> (set (last (pre_omega_run Run (Suc i))))" using q k by fastforce
        then obtain r_pref where r_pref: "run_well_defined r_pref \<A> (pre_omega_word x (Suc i)) \<and> last r_pref = q" using upper_run_reaches_all assms pre_Run by blast
        then obtain r_pref' where r_pref': "run_well_defined r_pref' \<A> (pre_omega_word x (Suc i)) \<and> q = last r_pref' \<and> (\<nexists> k . k < length r_pref' - 1 \<and> stolen_at \<A> r_pref' (pre_omega_run Run (Suc i)) (pre_omega_word x (Suc i)) k)" using assms pre_Run existence_of_run_without_stealing_cor by blast
        let ?r' = "r_pref' @ [r (Suc (Suc i))]"
        have "(last r_pref', x (Suc i), r (Suc (Suc i))) \<in> transitions \<A>" using r_pref' q by blast
        hence r'_well_def: "run_well_defined ?r' \<A> (pre_omega_word x (Suc (Suc i)))" using r_pref' prun_well_defined_extension_snoc pre_omega_word_append unfolding run_well_defined_def by metis
        have rightgap: "rightgap ?r' (pre_omega_run r (Suc (Suc i))) (pre_omega_run Run (Suc (Suc i))) (Suc i)"
        proof -
          have len_pre: "length (pre_omega_run r (Suc (Suc i))) = Suc (Suc i) + 1" by (simp add: pre_omega_run_length)
          have len_Run: "length (pre_omega_run Run (Suc (Suc i))) = Suc (Suc i) + 1" by (simp add: pre_omega_run_length)
          have idx_pre_r: "(pre_omega_run r (Suc (Suc i))) ! (Suc i) = r (Suc i)" by (simp add: pre_omega_run_nth)
          have idx_pre_Run: "(pre_omega_run Run (Suc (Suc i))) ! (Suc i) = Run (Suc i)" by (simp add: pre_omega_run_nth)
          have "length r_pref' = length (pre_omega_word x (Suc i)) + 1" using r_pref' unfolding run_well_defined_def pseudo_run_well_defined_def by blast 
          hence "length r_pref' = Suc i + 1" by (simp add: pre_omega_word_length)
          hence len_suc_i: "length r_pref' - 1 = Suc i" by simp
          have not_empty: "r_pref' \<noteq> []" using r_pref' unfolding run_well_defined_def pseudo_run_well_defined_def by force 
          hence "last r_pref' = r_pref' ! (length r_pref' - 1)" using list_properties_not_empty by metis
          hence "r_pref' ! (Suc i) = q" using len_suc_i r_pref' by argo
          hence idx_r': "?r' ! (Suc i) = q" using not_empty len_suc_i list_properties_not_empty by metis
          have js_lt_k: "js (Suc i) < k" using k by blast
          have js_bound: "js (Suc i) < length ((pre_omega_run Run (Suc (Suc i))) ! (Suc i)) \<and> (pre_omega_run r (Suc (Suc i))) ! (Suc i) \<in> ((pre_omega_run Run (Suc (Suc i))) ! (Suc i)) ! (js (Suc i))" using eq4 idx_pre_r idx_pre_Run by simp
          have q_in: "q \<in> ((pre_omega_run Run (Suc (Suc i))) ! (Suc i)) ! k" using q idx_pre_Run by argo
          have "k < length ((pre_omega_run Run (Suc (Suc i))) ! (Suc i))" using k idx_pre_Run by auto
          hence "js (Suc i) < k \<and> js (Suc i) < length ((pre_omega_run Run (Suc (Suc i))) ! (Suc i)) \<and> k < length ((pre_omega_run Run (Suc (Suc i))) ! (Suc i)) \<and> ?r' ! (Suc i) \<in> ((pre_omega_run Run (Suc (Suc i))) ! (Suc i)) ! k \<and> (pre_omega_run r (Suc (Suc i))) ! (Suc i) \<in> ((pre_omega_run Run (Suc (Suc i))) ! (Suc i)) ! (js (Suc i))" using js_lt_k js_bound q_in idx_r' by blast
          thus ?thesis unfolding rightgap_def by blast
        qed
        have "length r_pref' = length (pre_omega_word x (Suc i)) + 1" using r_pref' unfolding run_well_defined_def pseudo_run_well_defined_def by blast 
        hence "length r_pref' = Suc i + 1" by (simp add: pre_omega_word_length)
        hence "Suc i < length ?r'" by auto
        hence rightgap_pref: "\<exists> k < length ?r' . rightgap ?r' (pre_omega_run r (Suc (Suc i))) (pre_omega_run Run (Suc (Suc i))) k" using rightgap by blast
        have greedy_pref: "greedy_run (pre_omega_run r (Suc (Suc i))) \<A> (pre_omega_word x (Suc (Suc i)))" using assms unfolding omega_greedy_run_def by blast
        have no_steal_r': "\<nexists> t . t < length ?r' - 1 \<and> stolen_at \<A> ?r' (pre_omega_run Run (Suc (Suc i))) (pre_omega_word x (Suc (Suc i))) t"
        proof (rule ccontr)
          assume "\<not> (\<nexists> t . t < length ?r' - 1 \<and> stolen_at \<A> ?r' (pre_omega_run Run (Suc (Suc i))) (pre_omega_word x (Suc (Suc i))) t)"
          then obtain t where t: "t < length ?r' - 1 \<and> stolen_at \<A> ?r' (pre_omega_run Run (Suc (Suc i))) (pre_omega_word x (Suc (Suc i))) t" by blast
          have len_rpref': "length r_pref' = Suc i + 1" using r_pref' unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
          hence len_r': "length ?r' = Suc (Suc i) + 1" by simp
          consider (old) "t < length ?r' - 2" | (last) "t = length ?r' - 2" using t by fastforce
          thus False
          proof cases
            case old
            hence t_lt: "t < length r_pref' - 1" using len_rpref' by simp
            have Run_decomp: "pre_omega_run Run (Suc (Suc i)) = pre_omega_run Run (Suc i) @ [Run (Suc (Suc i))]" by (simp add: pre_omega_run_Suc)
            have word_decomp: "pre_omega_word x (Suc (Suc i)) = pre_omega_word x (Suc i) @ [x (Suc i)]" by (simp add: pre_omega_word_Suc)
            have len_run_Run: "length r_pref' = length (pre_omega_run Run (Suc i))" using len_rpref' pre_omega_run_length Suc_eq_plus1 by metis 
            have "length r_pref' = length (pre_omega_word x (Suc i)) + 1" using r_pref' unfolding run_well_defined_def pseudo_run_well_defined_def by simp
            hence "stolen_at \<A> r_pref' (pre_omega_run Run (Suc i)) (pre_omega_word x (Suc i)) t" using stolen_at_lower_place_iff t_lt len_run_Run t Run_decomp word_decomp by metis
            thus False using r_pref' t_lt by blast
          next
            case last
            hence t_eq: "t = Suc i" using len_r' by simp
            then obtain m n where mn: "m < n \<and> m < length ((pre_omega_run Run (Suc (Suc i))) ! (Suc i)) \<and> n < length ((pre_omega_run Run (Suc (Suc i))) ! (Suc i)) \<and> ?r' ! (Suc i) \<in> ((pre_omega_run Run (Suc (Suc i))) ! (Suc i)) ! m \<and> ?r' ! (Suc (Suc i)) \<in> post_set \<A> (((pre_omega_run Run (Suc (Suc i))) ! (Suc i)) ! n) ((pre_omega_word x (Suc (Suc i))) ! (Suc i))" using t unfolding stolen_at_def by blast
            have idx_Run_suci: "(pre_omega_run Run (Suc (Suc i))) ! (Suc i) = Run (Suc i)" by (simp add: pre_omega_run_nth)
            have idx_word_suci: "(pre_omega_word x (Suc (Suc i))) ! (Suc i) = x (Suc i)" by (simp add: pre_omega_word_nth)
            have "length r_pref' = length (pre_omega_word x (Suc i)) + 1" using r_pref' unfolding run_well_defined_def pseudo_run_well_defined_def by blast 
            hence "length r_pref' = Suc i + 1" by (simp add: pre_omega_word_length)
            hence len_suc_i: "length r_pref' - 1 = Suc i" by simp
            have not_empty: "r_pref' \<noteq> []" using r_pref' unfolding run_well_defined_def pseudo_run_well_defined_def by force 
            hence "last r_pref' = r_pref' ! (length r_pref' - 1)" using list_properties_not_empty by metis
            hence "r_pref' ! (Suc i) = q" using len_suc_i r_pref' by argo
            hence idx_r'_suci: "?r' ! (Suc i) = q" using not_empty len_suc_i list_properties_not_empty by metis
            have idx_r'_sucsuci: "?r' ! (Suc (Suc i)) = r (Suc (Suc i))" using len_rpref' Suc_eq_plus1 nth_append_length by metis
            have n_gt_k: "k < n"
            proof -
              have Run_suci_ne: "Run (Suc i) \<noteq> []" using eq4 by auto
              have Run_suci_state: "Run (Suc i) \<in> states (upper_part_pure \<A>)" using Run_suc_i pre_Run Run well_def last_of_prun_is_state unfolding run_well_defined_def by metis
              have Run_suci_upper: "Run (Suc i) \<in> upper_states \<A>" using Run_suci_state Run_suci_ne unfolding upper_part_pure_def by auto
              have q_in_k: "q \<in> (Run (Suc i)) ! k" using q by blast
              have q_in_m: "q \<in> (Run (Suc i)) ! m" using mn idx_Run_suci idx_r'_suci by simp
              have "m < length (Run (Suc i))" using mn idx_Run_suci by simp
              hence "m = k" using unique_component_upper_state Run_suci_upper k q_in_m q_in_k by metis
              thus ?thesis using mn by simp
            qed
            have r_suc: "r (Suc (Suc i)) \<in> post_set \<A> ((Run (Suc i)) ! n) (x (Suc i))" using mn idx_Run_suci idx_word_suci idx_r'_sucsuci by simp
            have "n \<le> length (Run (Suc i)) - 1" using mn idx_Run_suci by force
            thus False using r_suc k n_gt_k by force
          qed
        qed
        have last_r': "last ?r' = r (Suc (Suc i))" by simp
        have "last (pre_omega_run r (Suc (Suc i))) = r (Suc (Suc i))" using pre_omega_run_last  by blast
        hence last_equi: "last ?r' = last (pre_omega_run r (Suc (Suc i)))" using last_r' by simp
        have "run_well_defined (pre_omega_run r (Suc (Suc i))) \<A> (pre_omega_word x (Suc (Suc i)))" using greedy_pref unfolding greedy_run_def by blast
        hence "acc_sum \<A> (pre_omega_run r (Suc (Suc i))) < acc_sum \<A> ?r'" using assms well_def_R r'_well_def no_steal_r' rightgap_pref last_equi no_steal_run_has_max_acc_sum_unique by blast
        thus False using greedy_pref r'_well_def last_equi unfolding greedy_run_def by blast
      qed
      have less: "(js (Suc i)) < length (Run (Suc i)) \<and> js (Suc (Suc i)) < length (Run (Suc (Suc i)))" using eq4 eq5 by blast
      define R where "R = snd (upper_step \<A> (x (Suc i)) (drop (Suc (js (Suc i))) (Run (Suc i))))"
      define L where "L = (post_set \<A> ((Run (Suc i)) ! (js (Suc i))) (x (Suc i)) - R) - accepting_states \<A>"
      define A where "A = (post_set \<A> ((Run (Suc i)) ! (js (Suc i))) (x (Suc i)) - R) \<inter> accepting_states \<A>"
      have r_not_R: "r (Suc (Suc i)) \<notin> R"
      proof
        assume "r (Suc (Suc i)) \<in> R"
        hence "r (Suc (Suc i)) \<in> post_set \<A> (\<Union> (set (drop (Suc (js (Suc i))) (Run (Suc i))))) (x (Suc i))" using snd_upper_step_eq_post_set_Union unfolding R_def by fast
        then obtain q where qU: "q \<in> \<Union> (set (drop (Suc (js (Suc i))) (Run (Suc i)))) \<and> (q, x (Suc i), r (Suc (Suc i))) \<in> transitions \<A>" unfolding post_set_def by blast
        then obtain n where "n < length (drop (Suc (js (Suc i))) (Run (Suc i))) \<and> q \<in> drop (Suc (js (Suc i))) (Run (Suc i)) ! n" using maximal_index_for_element by fast
        hence idx: "js (Suc i) < Suc (js (Suc i)) + n \<and> Suc (js (Suc i)) + n < length (Run (Suc i)) \<and> q \<in> (Run (Suc i)) ! (Suc (js (Suc i)) + n)" by force
        hence "r (Suc (Suc i)) \<in> post_set \<A> ((Run (Suc i)) ! (Suc (js (Suc i)) + n)) (x (Suc i))" using qU unfolding post_set_def by blast
        hence "r (Suc (Suc i)) \<in> (\<Union> k \<in> {k . js (Suc i) < k \<and> k < length (Run (Suc i))} . post_set \<A> ((Run (Suc i)) ! k) (x (Suc i)))" using idx by blast
        thus False using not_stolen by blast
      qed
      have trans_Run: "(Run (Suc i), x (Suc i), Run (Suc (Suc i))) \<in> transitions (upper_part_pure \<A>)" using Run unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
      have "Run (Suc (Suc i)) \<noteq> []" using eq5 by force
      hence RunSuc: "Run (Suc (Suc i)) = filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (x (Suc i)) (Run (Suc i))))" using trans_Run unfolding upper_part_pure_def upper_transitions_def by auto
      have lessless: "Suc i < Suc (Suc (Suc i))" by auto
      hence equi_Run: "(pre_omega_run Run (Suc (Suc i))) ! (Suc i) = Run (Suc i)" using pre_omega_run_nth by metis
      have equi_word: "(pre_omega_word x (Suc (Suc i))) ! (Suc i) = x (Suc i)" using lessless pre_omega_word_nth by blast
      have js_bound_pref: "js (Suc i) < length ((pre_omega_run Run (Suc (Suc i))) ! (Suc i))" using eq4 by (simp add: pre_omega_run_nth)
      obtain P where P: "filter (\<lambda>X . X \<noteq> {}) (fst (upper_step \<A> (x (Suc i)) (Run (Suc i)))) = P @ filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (x (Suc i)) (drop (Suc (js (Suc i))) (Run (Suc i)))))" using RunSuc_prefix_decomp[where m = "js (Suc i)" and Run = "(pre_omega_run Run (Suc (Suc i)))" and word = "(pre_omega_word x (Suc (Suc i)))" and i = "Suc i" and \<A> = \<A>] js_bound_pref well_def_R equi_Run equi_word unfolding R_def L_def A_def by fastforce
      have "(r (Suc i), x (Suc i), r (Suc (Suc i))) \<in> transitions \<A>" using omega_r unfolding omega_pseudo_run_well_defined_def by force
      hence "r (Suc (Suc i)) \<in> post_set \<A> ((Run (Suc i)) ! (js (Suc i))) (x (Suc i))" using eq4 unfolding post_set_def by blast
      hence r_in_head: "r (Suc (Suc i)) \<in> L \<union> A" using r_not_R unfolding L_def A_def by auto
      have Run_sucsuci_ne: "Run (Suc (Suc i)) \<noteq> []" using eq5 by auto
      have "Run (Suc (Suc i)) \<in> states (upper_part_pure \<A>)" using well_def_R well_def_upper_part_pure[OF assms(1)] last_of_prun_is_state unfolding run_well_defined_def by metis
      hence Run_sucsuci_upper: "Run (Suc (Suc i)) \<in> upper_states \<A>" using Run_sucsuci_ne unfolding upper_part_pure_def by auto
      have chosen_is_head: "(Run (Suc (Suc i))) ! (js (Suc (Suc i))) = L \<or> (Run (Suc (Suc i))) ! (js (Suc (Suc i))) = A"
      proof (cases "r (Suc (Suc i)) \<in> L")
        case True
        hence L_ne: "L \<noteq> {}" by auto
        have idxL_lt: "length P < length (Run (Suc (Suc i)))" using RunSuc P L_ne by auto
        have "r (Suc (Suc i)) \<in> (Run (Suc (Suc i))) ! (length P)" using RunSuc P True L_ne by auto
        hence "js (Suc (Suc i)) = length P" using unique_component_upper_state Run_sucsuci_upper less idxL_lt eq5 by metis
        thus ?thesis using RunSuc P True L_ne by auto
      next
        case False
        hence r_in_A: "r (Suc (Suc i)) \<in> A" using r_in_head by blast
        hence A_ne: "A \<noteq> {}" by auto
        show ?thesis
        proof (cases "L = {}")
          case True
          have idxA_lt: "length P < length (Run (Suc (Suc i)))" using RunSuc P True A_ne by auto
          have "r (Suc (Suc i)) \<in> (Run (Suc (Suc i))) ! (length P)" using RunSuc P True r_in_A by auto
          hence "js (Suc (Suc i)) = length P" using unique_component_upper_state Run_sucsuci_upper less idxA_lt eq5 by metis
          thus ?thesis using RunSuc P True r_in_A by auto
       next
          case False
          hence L_ne: "L \<noteq> {}" by simp
          hence idxA_lt: "length P + 1 < length (Run (Suc (Suc i)))" using RunSuc P A_ne by auto
          have A_at_1: "(filter (\<lambda>X . X \<noteq> {}) (L # A # fst (upper_step \<A> (x (Suc i)) (drop (Suc (js (Suc i))) (Run (Suc i)))))) ! 1 = A" using False L_ne A_ne by simp
          have "r (Suc (Suc i)) \<in> (Run (Suc (Suc i))) ! (length P + 1)" using RunSuc P False r_in_A A_at_1 nth_append_length_plus by metis
          hence "js (Suc (Suc i)) = length P + 1" using unique_component_upper_state Run_sucsuci_upper less idxA_lt eq5 by metis
          thus ?thesis using RunSuc P False r_in_A A_at_1 nth_append_length_plus by metis
        qed
      qed
      hence in_post_set: "(Run (Suc (Suc i))) ! (js (Suc (Suc i))) \<subseteq> post_set \<A> ((Run (Suc i)) ! (js (Suc i))) (x (Suc i))" unfolding L_def A_def by blast
      have chosen_disjoint_R: "(Run (Suc (Suc i))) ! (js (Suc (Suc i))) \<inter> R = {}" using chosen_is_head unfolding L_def A_def by blast    
      hence "upper_child (Run (Suc i)) (x (Suc i)) \<A> (Run (Suc (Suc i))) (js (Suc i)) (js (Suc (Suc i)))" using less in_post_set unfolding upper_child_def R_def by blast
      thus ?case using eq4 eq5 by blast
    qed
  }
  hence "\<forall> i . js i < length (Run i) \<and> r i \<in> (Run i) ! (js i) \<and> r (Suc i) \<in> (Run (Suc i)) ! (js (Suc i)) \<and> upper_child (Run i) (x i) \<A> (Run (Suc i)) (js i) (js (Suc i))" by blast
  thus ?thesis using Run by blast
qed

lemma prefixes_do_not_steal_from_upper_child:
  assumes "auto_well_defined \<A>" "omega_run_well_defined r \<A> x" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> i . js i < length (Run i) \<and> r i \<in> (Run i) ! (js i) \<and> r (Suc i) \<in> (Run (Suc i)) ! (js (Suc i)) \<and> upper_child (Run i) (x i) \<A> (Run (Suc i)) (js i) (js (Suc i))"
  shows "\<forall> n . \<nexists> k . k < length (pre_omega_run r n) - 1 \<and> stolen_at \<A> (pre_omega_run r n) (pre_omega_run Run n) (pre_omega_word x n) k"
proof -
  {
    fix n
    have "\<nexists> k . k < length (pre_omega_run r n) - 1 \<and> stolen_at \<A> (pre_omega_run r n) (pre_omega_run Run n) (pre_omega_word x n) k"
    proof (induction n)
      case 0
      hence "length (pre_omega_run r 0) = 1" using pre_omega_run_length by auto
      thus ?case by simp
    next
      case (Suc n)
      show ?case
      proof(rule ccontr)
        assume "\<not> (\<nexists> k . k < length (pre_omega_run r (Suc n)) - 1 \<and> stolen_at \<A> (pre_omega_run r (Suc n)) (pre_omega_run Run (Suc n)) (pre_omega_word x (Suc n)) k)"
        hence ex: "\<exists> k . k < length (pre_omega_run r (Suc n)) - 1 \<and> stolen_at \<A> (pre_omega_run r (Suc n)) (pre_omega_run Run (Suc n)) (pre_omega_word x (Suc n)) k" by auto
        then obtain k where k: "k < length (pre_omega_run r (Suc n)) - 1 \<and> stolen_at \<A> (pre_omega_run r (Suc n)) (pre_omega_run Run (Suc n)) (pre_omega_word x (Suc n)) k" by blast
        have "length (pre_omega_run r (Suc n)) - 1 = Suc (Suc n) - 1" using pre_omega_run_length by metis
        hence "length (pre_omega_run r (Suc n)) - 1 = n + 1" by simp
        hence "k \<le> n" using k by force
        then consider (old) "k < n" | (last) "k = n" by linarith
        thus False
        proof cases
          case old
          have "length (pre_omega_run r n) = Suc n" using pre_omega_run_length by auto
          hence "length (pre_omega_run r n) - 1 = n" by simp
          hence k_less: "k < length (pre_omega_run r n) - 1" using old by simp
          have len_eq: "length (pre_omega_run r n) = length (pre_omega_run Run n)" using pre_omega_run_length by metis
          have "run_well_defined (pre_omega_run r n) \<A> (pre_omega_word x n)" using assms omega_run_implies_pre_run_well_def unfolding run_well_defined_def omega_run_well_defined_def by metis
          hence len_word: "length (pre_omega_run r n) = length (pre_omega_word x n) + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by blast
          hence "stolen_at \<A> (pre_omega_run r n) (pre_omega_run Run n) (pre_omega_word x n) k" using k_less len_eq len_word pre_omega_run_Suc pre_omega_word_Suc stolen_at_lower_place_iff k by metis
          thus ?thesis using Suc k_less by blast
        next
          case last
          have rw: "run_well_defined (pre_omega_run r (Suc n)) \<A> (pre_omega_word x (Suc n))" using assms omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
          have Rw: "run_well_defined (pre_omega_run Run (Suc n)) (upper_part_pure \<A>) (pre_omega_word x (Suc n))" using assms omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
          have "length (pre_omega_word x (Suc n)) = Suc n" using pre_omega_word_length by auto
          hence idx: "n < length (pre_omega_word x (Suc n))" by simp
          then obtain js where jsn: "js n < length (Run n) \<and> r n \<in> (Run n) ! (js n) \<and> js (Suc n) < length (Run (Suc n)) \<and> r (Suc n) \<in> (Run (Suc n)) ! (js (Suc n)) \<and> upper_child (Run n) (x n) \<A> (Run (Suc n)) (js n) (js (Suc n))" using assms by blast 
          have last_not_stolen: "\<not> stolen_at \<A> (pre_omega_run r (Suc n)) (pre_omega_run Run (Suc n)) (pre_omega_word x (Suc n)) n"
          proof(rule ccontr)
            assume "\<not> \<not> stolen_at \<A> (pre_omega_run r (Suc n)) (pre_omega_run Run (Suc n)) (pre_omega_word x (Suc n)) n"
            hence st: "stolen_at \<A> (pre_omega_run r (Suc n)) (pre_omega_run Run (Suc n)) (pre_omega_word x (Suc n)) n" by blast
            then obtain m t where mt: "m < t \<and> m < length ((pre_omega_run Run (Suc n)) ! n) \<and> t < length ((pre_omega_run Run (Suc n)) ! n) \<and> (pre_omega_run r (Suc n)) ! n \<in> ((pre_omega_run Run (Suc n)) ! n) ! m \<and> (pre_omega_run r (Suc n)) ! Suc n \<in> post_set \<A> (((pre_omega_run Run (Suc n)) ! n) ! t) ((pre_omega_word x (Suc n)) ! n)" unfolding stolen_at_def by blast
            have n_less: "n < Suc (Suc n)" by simp
            have eq_run_n: "(pre_omega_run r (Suc n)) ! n = r n" using pre_omega_run_nth n_less by blast
            have "Suc n < Suc (Suc n)" by simp
            hence eq_run_Suc_n: "(pre_omega_run r (Suc n)) ! Suc n = r (Suc n)" using pre_omega_run_nth n_less by blast
            have eq_Run_n: "(pre_omega_run Run (Suc n)) ! n = Run n" using pre_omega_run_nth n_less by blast
            have eq_word_n: "(pre_omega_word x (Suc n)) ! n = x n" using pre_omega_word_nth n_less by blast
            have not_empty: "Run n \<noteq> []" using assms not_empty_omega_run by blast
            have "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
            hence "Run n \<in> states (upper_part_pure \<A>)" using assms well_def_implies_omega_prun_states unfolding omega_prun_states_def omega_run_well_defined_def by fast
            hence "Run n \<in> upper_states \<A> \<or> Run n \<in> {[]}" unfolding upper_part_pure_def by auto
            hence "Run n \<in> upper_states \<A>" using not_empty by blast
            hence "m = js n" using unique_component_upper_state mt jsn eq_run_n eq_Run_n by metis
            hence gt_js: "js n < t" using mt by simp
            have mem_right: "r (Suc n) \<in> post_set \<A> ((Run n) ! t) (x n)" using mt eq_run_Suc_n eq_Run_n eq_word_n by simp
            have child_disj: "(Run (Suc n)) ! (js (Suc n)) \<inter> snd (upper_step \<A> (x n) (drop (Suc (js n)) (Run n))) = {}" using jsn unfolding upper_child_def by blast
            have t_drop: "t - Suc (js n) < length (drop (Suc (js n)) (Run n))" using gt_js mt eq_Run_n by force
            have "drop (Suc (js n)) (Run n) ! (t - Suc (js n)) = (Run n) ! t" using mt gt_js eq_Run_n by auto
            hence "(Run n) ! t \<in> set (drop (Suc (js n)) (Run n))" using t_drop nth_mem by metis
            hence "r (Suc n) \<in> post_set \<A> (\<Union> (set (drop (Suc (js n)) (Run n)))) (x n)" using mem_right unfolding post_set_def by fast
            hence "r (Suc n) \<in> snd (upper_step \<A> (x n) (drop (Suc (js n)) (Run n)))" using snd_upper_step_eq_post_set_Union by fast
            hence "r (Suc n) \<in> (Run (Suc n)) ! (js (Suc n)) \<inter>  snd (upper_step \<A> (x n) (drop (Suc (js n)) (Run n)))" using jsn by fast
            thus False using child_disj by fast
          qed
          thus ?thesis using last k by blast
        qed
      qed
    qed
  }
  thus ?thesis by blast
qed

lemma lemma_3_4_12_right_to_left:
  assumes "auto_well_defined \<A>" "omega_run_well_defined r \<A> x" "\<exists> Run js . omega_run_well_defined Run (upper_part_pure \<A>) x \<and> (\<forall> i . js i < length (Run i) \<and> r i \<in> (Run i) ! (js i) \<and> r (Suc i) \<in> (Run (Suc i)) ! (js (Suc i)) \<and> upper_child (Run i) (x i) \<A> (Run (Suc i)) (js i) (js (Suc i)))"
  shows "omega_greedy_run r \<A> x"
proof -
  obtain Run js where Run: "omega_run_well_defined Run (upper_part_pure \<A>) x \<and> (\<forall> i . js i < length (Run i) \<and> r i \<in> (Run i) ! (js i) \<and> r (Suc i) \<in> (Run (Suc i)) ! (js (Suc i)) \<and> upper_child (Run i) (x i) \<A> (Run (Suc i)) (js i) (js (Suc i)))" using assms by blast
  hence pref_no_steal: "\<forall> n . \<nexists> k . k < length (pre_omega_run r n) - 1 \<and> stolen_at \<A> (pre_omega_run r n) (pre_omega_run Run n) (pre_omega_word x n) k" using prefixes_do_not_steal_from_upper_child assms by blast
  {
    fix n
    have rw: "run_well_defined (pre_omega_run r n) \<A> (pre_omega_word x n)" using assms omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
    have Rw: "run_well_defined (pre_omega_run Run n) (upper_part_pure \<A>) (pre_omega_word x n)" using Run omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
    have "greedy_run (pre_omega_run r n) \<A> (pre_omega_word x n)"
    proof(rule ccontr)
      assume "\<not> greedy_run (pre_omega_run r n) \<A> (pre_omega_word x n)"
      hence "\<exists> run' . run_well_defined run' \<A> (pre_omega_word x n) \<and> last run' = last (pre_omega_run r n) \<and> (acc_sum \<A> run') > (acc_sum \<A> (pre_omega_run r n))" using rw unfolding greedy_run_def by blast
      then obtain run' where run': "run_well_defined run' \<A> (pre_omega_word x n) \<and> last run' = last (pre_omega_run r n) \<and> (acc_sum \<A> run') > (acc_sum \<A> (pre_omega_run r n))" by blast
      have nosteal: "\<nexists> k . k < length (pre_omega_run r n) - 1 \<and> stolen_at \<A> (pre_omega_run r n) (pre_omega_run Run n) (pre_omega_word x n) k" using pref_no_steal by blast
      hence "acc_sum \<A> run' \<le> acc_sum \<A> (pre_omega_run r n)" using no_steal_run_has_max_acc_sum assms Rw rw run' by metis
      thus False using run' by auto
    qed
  }
  hence pref_greedy: "\<forall> n . greedy_run (pre_omega_run r n) \<A> (pre_omega_word x n)" by simp
  thus ?thesis using assms unfolding omega_greedy_run_def by auto
qed

theorem lemma_3_4_12:
  assumes "auto_well_defined \<A>" "omega_run_well_defined r \<A> x"
  shows "\<exists> Run js . omega_run_well_defined Run (upper_part_pure \<A>) x \<and> (\<forall> i . js i < length (Run i) \<and> r i \<in> (Run i) ! (js i) \<and> r (Suc i) \<in> (Run (Suc i)) ! (js (Suc i)) \<and> upper_child (Run i) (x i) \<A> (Run (Suc i)) (js i) (js (Suc i))) \<longleftrightarrow> omega_greedy_run r \<A> x"
  using assms lemma_3_4_12_left_to_right lemma_3_4_12_right_to_left by blast

definition upper_child_segment :: "('s states list) omega_run \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a omega_word \<Rightarrow> ('s,'a) automaton \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "upper_child_segment Run i N x \<A> j k = (\<exists> js . length js = N - i + 1 \<and> js ! 0 = j \<and> last js = k \<and> (\<forall> m < N - i . upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m)))"

definition upper_continued :: "('s states list) omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "upper_continued Run \<A> x i j = (\<forall> N > i . \<exists> k . upper_child_segment Run i N x \<A> j k)"

definition upper_continued_F :: "('s states list) omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "upper_continued_F omega_run \<A> omega_word i j = (upper_continued omega_run \<A> omega_word i j \<and> (omega_run i) ! j \<subseteq> accepting_states \<A>)"

definition upper_slice_continued_F :: "('s states list) omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> nat \<Rightarrow> bool" where "upper_slice_continued_F omega_run \<A> omega_word i = (\<exists> j < length (omega_run i) . upper_continued_F omega_run \<A> omega_word i j)"

lemma upper_continued_from_js:
  assumes "\<forall> m . js m < length (Run m) \<and> js (Suc m) < length (Run (Suc m)) \<and> upper_child (Run m) (x m) \<A> (Run (Suc m)) (js m) (js (Suc m))"
  shows "upper_continued Run \<A> x i (js i)"
proof -
  {
    fix N assume N: "N > i"
    let ?seg = "map js [i..<Suc N]"
    have len_seg: "length ?seg = N - i + 1" using N by simp
    hence "0 < Suc N - i" using N by auto
    hence "?seg ! 0 = js (i + 0)" using nth_map_upt by blast
    hence j0: "?seg ! 0 = js i" by auto
    have last_seg: "last ?seg = js N" using N by simp
    {
      fix m assume m: "m < N - i"
      hence "m < Suc N - i" using N by auto
      hence idx_m: "?seg ! m = js (i + m)" using nth_map_upt by blast
      have "Suc m < Suc N - i" using N m by fastforce
      hence idx_Suc_m: "?seg ! Suc m = js (i + Suc m)" using nth_map_upt by blast
      have "upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js (i + m)) (js (i + Suc m))" using assms by simp
      hence "upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (?seg ! m) (?seg ! Suc m)" using idx_m idx_Suc_m by simp
    }
    hence "\<forall> m < N - i . upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (?seg ! m) (?seg ! Suc m)" by blast
    hence "upper_child_segment Run i N x \<A> (js i) (js N)" using len_seg j0 last_seg unfolding upper_child_segment_def by blast
  }
  thus ?thesis unfolding upper_continued_def by blast
qed

lemma omega_run_uniform_components:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []"
  shows "\<forall> n j . j < length (Run n) \<longrightarrow> Run n ! j \<subseteq> accepting_states \<A> \<or> Run n ! j \<inter> accepting_states \<A> = {}"
proof -
  {
    fix n j assume j: "j < length (Run n)"
    have pref: "run_well_defined (pre_omega_run Run n) (upper_part_pure \<A>) (pre_omega_word x n)" using assms omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
    have len: "length (pre_omega_run Run n) = Suc n" using pre_omega_run_length by blast
    hence "pre_omega_run Run n \<noteq> []" by auto
    hence "last (pre_omega_run Run n) = (pre_omega_run Run n) ! (length (pre_omega_run Run n) - 1)" using list_properties_not_empty by metis
    hence equi: "Run n = (pre_omega_run Run n) ! (length (pre_omega_run Run n) - 1)" using pre_omega_run_last by metis
    hence nz: "(pre_omega_run Run n) ! (length (pre_omega_run Run n) - 1) \<noteq> []" using assms by auto
    have "length (pre_omega_run Run n) - 1 < length (pre_omega_run Run n)" using len by auto
    hence "\<forall> j < length (pre_omega_run Run n ! (length (pre_omega_run Run n) - 1)) . pre_omega_run Run n ! (length (pre_omega_run Run n) - 1) ! j \<subseteq> accepting_states \<A> \<or> pre_omega_run Run n ! (length (pre_omega_run Run n) - 1) ! j \<inter> accepting_states \<A> = {}" using component_uniform_acc pref nz by blast
    hence "Run n ! j \<subseteq> accepting_states \<A> \<or> Run n ! j \<inter> accepting_states \<A> = {}" using j equi by auto
  }
  thus ?thesis by blast
qed

lemma lemma_3_4_14:
  assumes "auto_well_defined \<A>" "x \<in> omega_language_auto \<A>"
  shows "\<exists> Run . omega_run_well_defined Run (upper_part_pure \<A>) x \<and> infinite {i . upper_slice_continued_F Run \<A> x i}"
proof -
  obtain omega_run where "omega_run_accepting omega_run \<A> x" using assms unfolding omega_language_auto_def by blast
  then obtain r where r: "omega_run_accepting r \<A> x \<and> omega_greedy_run r \<A> x" using cor_3_1_11[OF assms(1), of x] assms by blast
  then obtain Run js where R: "omega_run_well_defined Run (upper_part_pure \<A>) x \<and> (\<forall> i . js i < length (Run i) \<and> r i \<in> (Run i) ! (js i) \<and> r (Suc i) \<in> (Run (Suc i)) ! (js (Suc i)) \<and> upper_child (Run i) (x i) \<A> (Run (Suc i)) (js i) (js (Suc i)))" using lemma_3_4_12[OF assms(1)] unfolding omega_run_accepting_def by blast
  hence cont: "\<forall> i . upper_continued Run \<A> x i (js i)" using upper_continued_from_js[of js Run x \<A>] by blast
  have inf_acc_r: "\<forall> n . \<exists> N > n . r N \<in> accepting_states \<A>" using r unfolding omega_run_accepting_def by blast
  have "\<forall> n . Run n \<noteq> []" using assms R r not_empty_omega_run unfolding omega_run_accepting_def by blast
  hence uniform: "\<forall> n j . j < length (Run n) \<longrightarrow> Run n ! j \<subseteq> accepting_states \<A> \<or> Run n ! j \<inter> accepting_states \<A> = {}" using omega_run_uniform_components assms R by blast
  {
    fix n
    obtain N where N: "N > n \<and> r N \<in> accepting_states \<A>" using inf_acc_r by blast
    have mem: "r N \<in> (Run N) ! (js N)" using R by blast
    have jlt: "js N < length (Run N)" using R by blast
    have inter: "(Run N) ! (js N) \<subseteq> accepting_states \<A> \<or> (Run N) ! (js N) \<inter> accepting_states \<A> = {}" using uniform jlt by blast
    have "(Run N) ! (js N) \<inter> accepting_states \<A> \<noteq> {}" using mem N by blast
    hence "(Run N) ! (js N) \<subseteq> accepting_states \<A>" using inter by auto
    hence "upper_continued_F Run \<A> x N (js N)" using cont unfolding upper_continued_F_def by blast
    hence "upper_slice_continued_F Run \<A> x N" using jlt unfolding upper_slice_continued_F_def by blast
    hence "\<exists> N > n . upper_slice_continued_F Run \<A> x N" using N by blast
  }
  hence "\<forall> n . \<exists> N > n . upper_slice_continued_F Run \<A> x N" by blast
  hence  "infinite {i . upper_slice_continued_F Run \<A> x i}" using finite_nat_set_iff_bounded mem_Collect_eq not_less_iff_gr_or_eq by metis
  thus ?thesis using R by blast
qed

lemma no_steal_run_to_TF_component:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "j < length (Run i) \<and> upper_continued_F Run \<A> x i j"
  shows "\<forall> s \<in> (Run i) ! j . \<exists> run . run_well_defined run \<A> (pre_omega_word x i) \<and> run ! i = s \<and> (\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run (pre_omega_run Run i) (pre_omega_word x i) k)"
proof -
  {
    fix s assume "s \<in> (Run i) ! j"
    hence s_in: "s \<in> \<Union> (set (Run i))" using assms nth_mem by blast
    have well_def: "run_well_defined (pre_omega_run Run i) (upper_part_pure \<A>) (pre_omega_word x i) \<and> last (pre_omega_run Run i) = Run i" using omega_run_implies_pre_run_well_def assms unfolding omega_run_well_defined_def run_well_defined_def by metis
    then obtain run where "run_well_defined run \<A> (pre_omega_word x i) \<and> last run = s" using upper_run_reaches_all assms s_in by metis
    then obtain run' where run': "run_well_defined run' \<A> (pre_omega_word x i) \<and> last run' = s \<and> (\<nexists> k . k < length run' - 1 \<and> stolen_at \<A> run' (pre_omega_run Run i) (pre_omega_word x i) k)" using existence_of_run_without_stealing_cor assms well_def by metis
    hence not_empty: "run' \<noteq> []" unfolding run_well_defined_def pseudo_run_well_defined_def by force
    hence last: "last run' = run' ! (length run' - 1)" using list_properties_not_empty by metis
    have "length run' = length (pre_omega_word x i) + 1" using run' unfolding run_well_defined_def pseudo_run_well_defined_def by blast
    hence "length run' = i + 1" using pre_omega_word_length by auto
    hence "length run' - 1 = i" using not_empty by auto
    hence "s = run' ! i" using last run' by blast
    hence "\<exists> run . run_well_defined run \<A> (pre_omega_word x i) \<and> run ! i = s \<and> (\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run (pre_omega_run Run i) (pre_omega_word x i) k)" using run' by blast
  }
  thus ?thesis by auto
qed

lemma upper_child_has_state_predecessor:
  assumes "upper_child p a \<A> q j k" "t \<in> q ! k"
  shows "\<exists> s \<in> p ! j . (s, a, t) \<in> transitions \<A>"
proof -
  have "q ! k \<subseteq> post_set \<A> (p ! j) a" using assms unfolding upper_child_def by blast
  hence "t \<in> post_set \<A> (p ! j) a" using assms by blast
  thus ?thesis unfolding post_set_def by blast
qed

lemma upper_child_segment_has_state_path: "N \<ge> i \<and> t \<in> (Run N) ! k \<and> length js = N - i + 1 \<and> js ! 0 = j \<and> last js = k \<and> (\<forall> m < N - i . upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m)) \<Longrightarrow> \<exists> rs . length rs = N - i + 1 \<and> rs ! 0 \<in> (Run i) ! j \<and> last rs = t \<and> (\<forall> m < N - i . rs ! m \<in> (Run (i + m)) ! (js ! m) \<and> rs ! Suc m \<in> (Run (i + Suc m)) ! (js ! Suc m) \<and> upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m) \<and> (rs ! m, x (i + m), rs ! Suc m) \<in> transitions \<A>)"
proof(induction "N - i" arbitrary: N i t js k j)
  case 0
  hence Ni: "N = i" by auto
  hence "length js = 1 \<and> js ! 0 = j \<and> last js = k" using 0 by auto
  hence "j = k" using list_with_one_element by metis
  hence "length [t] = N - i + 1 \<and> [t] ! 0 \<in> (Run i) ! j \<and> last [t] = t" using 0 Ni by simp
  thus ?case by fastforce
next
  case (Suc n)
  have gt: "N > i" using Suc by linarith
  hence idx: "N - 1 - i < N - i" by simp
  have len: "length js = N - i + 1" using Suc by blast
  hence not_empty: "js \<noteq> []" using gt by force
  hence "js ! (length js - 1) = last js" using list_properties_not_empty by fast
  hence "js ! (N - i + 1 - 1) = last js" using len by argo
  hence lst: "js ! (N - i) = last js" by auto
  have Sucsuc: "Suc (N - 1 - i) = N - i" using idx by force
  hence "js ! Suc (N - 1 - i) = k" using lst Suc by argo
  hence step_last: "upper_child (Run (i + N - 1 - i)) (x (i + N - 1 - i)) \<A> (Run (i + Suc (N - 1 - i))) (js ! (N - 1 - i)) k" using Suc idx by auto
  have calc: "i + N - 1 - i = N - 1 \<and> i + Suc (N - 1 - i) = N" using Sucsuc by auto
  hence uc: "upper_child (Run (N - 1)) (x (N - 1)) \<A> (Run N) (js ! (N - 1 - i)) k \<and> t \<in> (Run N) ! k" using step_last Suc by argo
  then obtain u where u: "u \<in> (Run (N - 1)) ! (js ! (N - 1 - i)) \<and> (u, x (N - 1), t) \<in> transitions \<A>" using upper_child_has_state_predecessor by metis  
  obtain js' where var: "js = js' @ [last js]" using append_butlast_last_id not_empty by metis
  hence len_js': "length js' = (N - 1) - i + 1" using len Suc_eq_plus1 Sucsuc add.commute add_left_imp_eq length_append_singleton by metis
  hence len_js'_simp: "length js' = N - i" using Sucsuc by presburger
  hence js'_nth_simp: "\<forall> m < N - i - 1 . js' ! m = js ! m" using list_properties_length var idx by metis
  hence js'_nth: "\<forall> m < (N - 1) - i . js' ! m = js ! m" by simp
  have js'_Suc_nth_simp: "\<forall> m < N - i - 1 . js' ! (m + 1) = js ! (m + 1)" using list_properties_length var len_js'_simp by metis
  hence js'_Suc_nth: "\<forall> m < (N - 1) - i . js' ! Suc m = js ! Suc m" by simp
  have not_empty': "js' \<noteq> []" using gt len_js'_simp by auto
  hence "js' ! 0 = js ! 0" using list_properties_not_empty var by metis
  hence js'_0: "js' ! 0 = j" using Suc by blast
  have "last js' = js' ! (N - i - 1)" using not_empty' list_properties_not_empty len_js'_simp by metis
  hence "last js' = js' ! (N - 1 - i)" by simp
  hence js'_last: "last js' = js ! (N - 1 - i) \<and> js' ! (N - 1 - i) = js ! (N - 1 - i)" using list_properties_length idx len_js'_simp var by metis
  {
    fix m assume m: "m < (N - 1) - i"
    hence "m < N - i" by force
    hence "upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m)" using Suc by blast
    hence "upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js' ! m) (js' ! Suc m)" using m js'_nth js'_Suc_nth by presburger
  }
  hence steps_js': "\<forall> m < (N - 1) - i . upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js' ! m) (js' ! Suc m)" by blast
  have i_less: "(N - 1) \<ge> i" using gt by auto
  have "u \<in> (Run (N - 1)) ! (js' ! (N - 1 - i)) \<and> (u, x (N - 1), t) \<in> transitions \<A>" using u js'_last by argo
  hence IH_prems: "(N - 1) \<ge> i \<and> u \<in> (Run (N - 1)) ! (js' ! ((N - 1) - i)) \<and> length js' = (N - 1) - i + 1 \<and> js' ! 0 = j \<and> last js' = js' ! ((N - 1) - i) \<and> (\<forall> m < (N - 1) - i . upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js' ! m) (js' ! Suc m))" using i_less len_js' js'_0 js'_last steps_js' by metis
  have "n = (N - 1) - i" using Suc by linarith
  then obtain rs where rs: "length rs = (N - 1) - i + 1 \<and> rs ! 0 \<in> (Run i) ! j \<and> last rs = u \<and> (\<forall> m < (N - 1) - i . rs ! m \<in> (Run (i + m)) ! (js' ! m) \<and> rs ! Suc m \<in> (Run (i + Suc m)) ! (js' ! Suc m) \<and> upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js' ! m) (js' ! Suc m) \<and> (rs ! m, x (i + m), rs ! Suc m) \<in> transitions \<A>)" using Suc IH_prems by blast
  hence rs_not_empty: "rs \<noteq> []" by force
  let ?rs = "rs @ [t]"
  have length: "length ?rs = N - i + 1" using rs gt by simp
  have first: "?rs ! 0 \<in> (Run i) ! j" using rs rs_not_empty list_properties_not_empty by metis
  have last: "last ?rs = t" by simp
  have lila: "length rs = N - i" using rs Sucsuc by presburger
  hence equi: "\<forall> m < N - i . ?rs ! m = rs ! m" using list_properties_length by metis
  have "length rs - 1 = N - 1 - i" using lila by auto
  hence "\<forall> m < N - 1 - i . rs ! (m + 1) = ?rs ! (m + 1)" using list_properties_length by metis
  hence equi_suc: "\<forall> m < N - 1 - i . rs ! (Suc m) = ?rs ! (Suc m)" by auto
  {
    fix m assume m: "m < N - i"
    have "?rs ! m \<in> (Run (i + m)) ! (js ! m) \<and> ?rs ! Suc m \<in> (Run (i + Suc m)) ! (js ! Suc m) \<and> upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m) \<and> (?rs ! m, x (i + m), ?rs ! Suc m) \<in> transitions \<A>"
    proof (cases "m < N - 1 - i")
      case True
      hence "rs ! m \<in> (Run (i + m)) ! (js' ! m) \<and> rs ! Suc m \<in> (Run (i + Suc m)) ! (js' ! Suc m) \<and> upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js' ! m) (js' ! Suc m) \<and> (rs ! m, x (i + m), rs ! Suc m) \<in> transitions \<A>" using rs by presburger
      hence "?rs ! m \<in> (Run (i + m)) ! (js' ! m) \<and> ?rs ! Suc m \<in> (Run (i + Suc m)) ! (js' ! Suc m) \<and> upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js' ! m) (js' ! Suc m) \<and> (?rs ! m, x (i + m), ?rs ! Suc m) \<in> transitions \<A>" using equi equi_suc True m by metis
      thus ?thesis using True js'_nth_simp js'_Suc_nth_simp by force
    next
      case False
      hence meq: "m = N - 1 - i" using m gt by force
      hence equis: "N - 1 = i + m \<and> N - 1 - i = m \<and> N = i + Suc m \<and> N - i = Suc m" using calc by simp     
      have "?rs ! m = u" using meq rs by (simp add: list_append_position5)
      hence "?rs ! m \<in> (Run (N - 1)) ! (js ! (N - 1 - i)) \<and> (?rs ! m, x (N - 1), t) \<in> transitions \<A>" using u by blast
      hence step: "?rs ! m \<in> (Run (i + m)) ! (js ! m) \<and> (?rs ! m, x (N - 1), t) \<in> transitions \<A>" using equis by argo
      have "?rs ! Suc m = t" using equis Sucsuc lila nth_append_length by metis
      hence "?rs ! Suc m = t \<and> ?rs ! Suc m \<in> Run N ! (last js) \<and> upper_child (Run (N - 1)) (x (N - 1)) \<A> (Run N) (js ! (N - 1 - i)) (last js)" using uc Suc by argo
      hence "?rs ! Suc m = t \<and> ?rs ! Suc m \<in> (Run N) ! (js ! (N - i)) \<and> upper_child (Run (N - 1)) (x (N - 1)) \<A> (Run N) (js ! (N - 1 - i)) (js ! (N - i))" using lst by argo
      hence "?rs ! Suc m = t \<and> ?rs ! Suc m \<in> (Run (i + Suc m)) ! (js ! (Suc m)) \<and> upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! (Suc m))" using equis by argo
      thus ?thesis using step add_Suc_right calc diff_Suc_1 meq by metis
    qed
  }
  thus ?case using length first last by blast
qed

lemma run_extend_along_state_path:
  assumes "run_well_defined run \<A> (pre_omega_word x i)" "run ! i = rs ! 0" "length rs = N - i + 1" "\<forall> m < N - i . (rs ! m, x (i + m), rs ! Suc m) \<in> transitions \<A>" "i \<le> N"
  shows "run_well_defined (run @ tl rs) \<A> (pre_omega_word x N)"
proof -
  have len_run: "length run = i + 1" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
  hence run_ne: "run \<noteq> []" by auto
  have len: "length (tl rs) = N - i" using assms by (cases rs) auto
  hence len_total: "length (run @ tl rs) = N + 1" using len_run assms by fastforce
  hence lenlen: "length (run @ tl rs) = length (pre_omega_word x N) + 1" using pre_omega_word_length by metis
  have "run ! 0 = initial_state \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  hence init: "(run @ tl rs) ! 0 = initial_state \<A>" using run_ne list_properties_not_empty by metis
  have init_state: "initial_state \<A> \<in> states \<A>" using assms unfolding run_well_defined_def pseudo_run_well_defined_def by blast
  {
    fix n assume assm: "n < N"
    then consider (case1) "n < i" | (case2) "n = i" | (case3) "n > i" by linarith 
    hence "((run @ tl rs) ! n, (pre_omega_word x N) ! n, (run @ tl rs) ! (n + 1)) \<in> transitions \<A>"
    proof cases
      case case1
      hence step_run: "(run ! n, (pre_omega_word x i) ! n, run ! (n + 1)) \<in> transitions \<A>" using assms len_run unfolding run_well_defined_def pseudo_run_well_defined_def by simp
      have runn: "(run @ tl rs) ! n = run ! n" using case1 len_run nth_append trans_less_add1 by metis
      have runn1: "(run @ tl rs) ! (n + 1) = run ! (n + 1)" using case1 len_run by (simp add: nth_append)
      have "(pre_omega_word x N) ! n = (pre_omega_word x i) ! n" using case1  assm pre_omega_word_nth by metis
      thus ?thesis using runn runn1 step_run by simp
    next
      case case2
      have word_i: "(pre_omega_word x N) ! i = x i" using assm case2 by (simp add: pre_omega_word_nth)
      have run_i: "(run @ tl rs) ! i = run ! i" using len_run case2 by (simp add: nth_append)
      have run_Suc_i: "(run @ tl rs) ! (i + 1) = rs ! 1" using len assm case2 len_run add_diff_cancel_right' length_greater_0_conv list_append_position5 run_ne tl_more_elements2 zero_less_diff by metis
      have rs1: "rs ! 1 = rs ! Suc 0" by simp
      have "(rs ! 0, x (i + 0), rs ! Suc 0) \<in> transitions \<A>" using assms assm case2 zero_less_diff by blast
      thus ?thesis using case2 assms run_i run_Suc_i word_i rs1 by force
    next
      case case3
      then obtain m where m: "n = i + Suc m" using less_iff_Suc_add by auto
      have mlt: "Suc m < N - i" using assm case3 m assms by linarith
      have word_n: "(pre_omega_word x N) ! n = x (i + Suc m)" using assm m by (simp add: pre_omega_word_nth)
      have nm: "n = length run + m" using m len_run by simp
      have "Suc m < length rs" using assms mlt by simp
      hence run_n: "(run @ tl rs) ! n = rs ! (Suc m)" using nm by (cases rs) auto
      have n1m: "n + 1 = length run + Suc m" using m len_run by simp
      have "Suc (Suc m) < length rs" using assms mlt by simp
      have run_Suc_n: "(run @ tl rs) ! (n + 1) = rs ! (Suc (Suc m))" using n1m len mlt nth_append_length_plus nth_tl by metis
      have "(rs ! Suc m, x (i + Suc m), rs ! Suc (Suc m)) \<in> transitions \<A>" using assms mlt by blast        
      thus ?thesis using run_n run_Suc_n word_n by argo
    qed
  }
  hence "\<forall> n < N . ((run @ tl rs) ! n, (pre_omega_word x N) ! n, (run @ tl rs) ! (n + 1)) \<in> transitions \<A>" by blast
  hence "\<forall> n < length (run @ tl rs) - 1 . ((run @ tl rs) ! n, (pre_omega_word x N) ! n, (run @ tl rs) ! (n + 1)) \<in> transitions \<A>" using len_total by simp
  thus ?thesis using lenlen init init_state  unfolding run_well_defined_def pseudo_run_well_defined_def by blast
qed

lemma last_index_from_length:
  assumes "length list = Suc n"
  shows "last list = list ! n"
  using assms nth_equalityI pre_omega_run_last pre_omega_run_length pre_omega_run_nth by metis

lemma TF_component_has_extendable_no_steal_run:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []" "j < length (Run i) \<and> upper_continued_F Run \<A> x i j" "i \<le> N"
  shows "\<exists> run . run_well_defined run \<A> (pre_omega_word x N) \<and> run ! i \<in> (Run i) ! j \<and> (\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run (pre_omega_run Run N) (pre_omega_word x N) k)"
proof(cases "N = i")
  case True
  have j: "\<forall> s \<in> (Run i) ! j . \<exists> run . run_well_defined run \<A> (pre_omega_word x i) \<and> run ! i = s \<and> (\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run (pre_omega_run Run i) (pre_omega_word x i) k)" using assms no_steal_run_to_TF_component by blast
  have "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
  hence "Run i \<in> states (upper_part_pure \<A>)" using assms well_def_implies_omega_prun_states unfolding omega_prun_states_def omega_run_well_defined_def by fast
  hence "Run i \<in> upper_states \<A> \<or> Run i \<in> {[]}" unfolding upper_part_pure_def by auto
  hence "Run i \<in> upper_states \<A>" using assms by blast 
  then obtain s where "s \<in> (Run i) ! j" using assms j unfolding upper_states_def by fastforce
  hence "\<exists> run . run_well_defined run \<A> (pre_omega_word x i) \<and> run ! i \<in> (Run i) ! j \<and> (\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run (pre_omega_run Run i) (pre_omega_word x i) k)" using j by fast 
  thus ?thesis using True j by blast
next
  case False
  hence i_less: "i < N" using assms by linarith
  hence i_lt_N: "i \<le> N" by auto
  have j: "\<forall> s \<in> (Run i) ! j . \<exists> run . run_well_defined run \<A> (pre_omega_word x i) \<and> run ! i = s \<and> (\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run (pre_omega_run Run i) (pre_omega_word x i) k)" using no_steal_run_to_TF_component[OF assms(1,2,4)] by blast
  hence "\<forall> M > i . \<exists> k . upper_child_segment Run i M x \<A> j k" using assms unfolding upper_continued_def upper_continued_F_def by blast
  then obtain k where "upper_child_segment Run i N x \<A> j k" using i_less by blast
  then obtain js where js: "length js = N - i + 1 \<and> js ! 0 = j \<and> last js = k \<and> (\<forall> m < N - i . upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m))" unfolding upper_child_segment_def by blast
  have idx_last: "N - 1 - i < N - i" using i_less by simp
  hence equi: "i + (N - 1 - i) = N - 1 \<and> i + Suc (N - 1 - i) = N \<and> N - i = Suc (N - 1 - i)" by simp
  have js_last_idx: "js ! (N - i) = k" using js i_less last_index_from_length by fastforce
  have "upper_child (Run (i + (N - 1 - i))) (x (i + (N - 1 - i))) \<A> (Run (i + Suc (N - 1 - i))) (js ! (N - 1 - i)) (js ! Suc (N - 1 - i))" using js idx_last by blast
  hence "upper_child (Run (N - 1)) (x (N - 1)) \<A> (Run N) (js ! (N - 1 - i)) k" using equi js_last_idx by argo
  hence klt: "k < length (Run N)" unfolding upper_child_def by blast
  have upper_well_def: "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
  hence "Run N \<in> states (upper_part_pure \<A>)" using assms well_def_implies_omega_prun_states unfolding omega_prun_states_def omega_run_well_defined_def by fast
  hence "Run N \<in> upper_states \<A>" using assms unfolding upper_part_pure_def by auto
  hence "(Run N) ! k \<noteq> {}" using klt nth_mem unfolding upper_states_def by blast
  then obtain t where t: "t \<in> (Run N) ! k" by blast
  hence "N \<ge> i \<and> t \<in> (Run N) ! k \<and> length js = N - i + 1 \<and> js ! 0 = j \<and> last js = k \<and> (\<forall> m < N - i . upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m))" using i_lt_N js by blast
  hence "\<exists> rs . length rs = N - i + 1 \<and> rs ! 0 \<in> (Run i) ! j \<and> last rs = t \<and> (\<forall> m < N - i . rs ! m \<in> (Run (i + m)) ! (js ! m) \<and> rs ! Suc m \<in> (Run (i + Suc m)) ! (js ! Suc m) \<and> upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m) \<and> (rs ! m, x (i + m), rs ! Suc m) \<in> transitions \<A>)" using upper_child_segment_has_state_path[where N=N and i=i and Run=Run and j=j and t=t and js=js and x=x and \<A>=\<A>] by fast
  then obtain rs where rs: "length rs = N - i + 1 \<and> rs ! 0 \<in> (Run i) ! j \<and> last rs = t \<and> (\<forall> m < N - i . rs ! m \<in> (Run (i + m)) ! (js ! m) \<and> rs ! Suc m \<in> (Run (i + Suc m)) ! (js ! Suc m) \<and> upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m) \<and> (rs ! m, x (i + m), rs ! Suc m) \<in> transitions \<A>)" by presburger
  then obtain run0 where run0: "run_well_defined run0 \<A> (pre_omega_word x i) \<and> run0 ! i = rs ! 0 \<and> (\<nexists> k . k < length run0 - 1 \<and> stolen_at \<A> run0 (pre_omega_run Run i) (pre_omega_word x i) k)" using j by blast
  hence run_ext_wd: "run_well_defined (run0 @ tl rs) \<A> (pre_omega_word x N)" using run_extend_along_state_path rs i_lt_N by blast
  have "length run0 = i + 1" using run0 unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
  hence same_i: "(run0 @ tl rs) ! i = run0 ! i" by (simp add: nth_append)
  hence run_ext_i: "(run0 @ tl rs) ! i \<in> (Run i) ! j" using run0 rs by argo
  have no_steal_ext: "\<nexists> k . k < length (run0 @ tl rs) - 1 \<and> stolen_at \<A> (run0 @ tl rs) (pre_omega_run Run N) (pre_omega_word x N) k"
  proof (rule ccontr)
    assume "\<not> (\<nexists> k . k < length (run0 @ tl rs) - 1 \<and> stolen_at \<A> (run0 @ tl rs) (pre_omega_run Run N) (pre_omega_word x N) k)"
    then obtain k0 where k0: "k0 < length (run0 @ tl rs) - 1 \<and>stolen_at \<A> (run0 @ tl rs) (pre_omega_run Run N) (pre_omega_word x N) k0" by blast
    have len_run0: "length run0 = i + 1" using run0 unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
    hence len_ext: "length (run0 @ tl rs) = N + 1" using rs i_less by simp
    consider (old) "k0 < i" | (new) "i \<le> k0" by linarith
    thus False
    proof cases
      case old
      hence eq1: "(run0 @ tl rs) ! k0 = run0 ! k0" using len_run0 by (simp add: nth_append)
      have eq2: "(run0 @ tl rs) ! Suc k0 = run0 ! Suc k0" using old len_run0 by (simp add: nth_append)
      have eqR: "(pre_omega_run Run N) ! k0 = (pre_omega_run Run i) ! k0" using old i_less by (simp add: pre_omega_run_nth)
      have eqW: "(pre_omega_word x N) ! k0 = (pre_omega_word x i) ! k0" using old i_less by (simp add: pre_omega_word_nth)
      have bound: "k0 < length run0 - 1" using old len_run0 by simp
      have "stolen_at \<A> run0 (pre_omega_run Run i) (pre_omega_word x i) k0" using k0 eq1 eq2 eqR eqW unfolding stolen_at_def by auto
      thus False using run0 bound by blast
    next
      case new
      then obtain m where m: "k0 = i + m" using le_iff_add by metis
      hence mlt: "m < N - i" using k0 len_ext by linarith
      obtain u v where uv: "u < v \<and> u < length ((pre_omega_run Run N) ! k0) \<and> v < length ((pre_omega_run Run N) ! k0) \<and> (run0 @ tl rs) ! k0 \<in> ((pre_omega_run Run N) ! k0) ! u \<and> (run0 @ tl rs) ! Suc k0 \<in> post_set \<A> (((pre_omega_run Run N) ! k0) ! v) ((pre_omega_word x N) ! k0)" using k0 unfolding stolen_at_def by blast
      have idxRun: "(pre_omega_run Run N) ! k0 = Run (i + m)" using m mlt by (simp add: pre_omega_run_nth)
      have idxWord: "(pre_omega_word x N) ! k0 = x (i + m)" using m mlt by (simp add: pre_omega_word_nth)
      have idxCur: "(run0 @ tl rs) ! k0 = rs ! m"
      proof (cases m)
        case 0 thus ?thesis using m run0 same_i by force
      next
        case (Suc z) thus ?thesis using m len_run0 rs Suc_eq_plus1 Suc_lessD add_Suc_shift diff_add_inverse2 length_tl mlt nth_append_length_plus nth_tl by metis
      qed
      have idxNxt: "(run0 @ tl rs) ! Suc k0 = rs ! Suc m" using m mlt len_run0 rs Suc_eq_plus1 add_Suc diff_add_inverse2 length_tl nth_append_length_plus nth_tl by metis
      have pathm: "rs ! m \<in> (Run (i + m)) ! (js ! m) \<and> rs ! Suc m \<in> (Run (i + Suc m)) ! (js ! Suc m) \<and> upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m) \<and> (rs ! m, x (i + m), rs ! Suc m) \<in> transitions \<A>" using rs mlt by blast
      have in_R: "rs ! m \<in> (Run (i + m)) ! u \<and> u < length (Run (i + m))" using uv idxRun idxCur by simp
      have in_R2:  "rs ! m \<in> (Run (i + m)) ! (js ! m) \<and> js ! m < length (Run (i + m))" using pathm unfolding upper_child_def by blast
      have "Run (i + m) \<in> states (upper_part_pure \<A>)" using upper_well_def assms well_def_implies_omega_prun_states unfolding omega_prun_states_def omega_run_well_defined_def by fast
      hence "Run (i + m) \<in> upper_states \<A>" using assms unfolding upper_part_pure_def by auto
      hence "u = js ! m" using in_R2 in_R unique_component_upper_state by fast
      hence v_gt: "js ! m < v" using uv by simp
      have bad: "rs ! Suc m \<in> snd (upper_step \<A> (x (i + m)) (drop (Suc (js ! m)) (Run (i + m))))"
      proof -
        have post_v: "rs ! Suc m \<in> post_set \<A> ((Run (i + m)) ! v) (x (i + m))" using uv idxRun idxWord idxNxt by simp
        have v_bound: "v < length (Run (i + m))" using uv idxRun by simp
        have "Suc (js ! m) \<le> v" using v_gt by simp
        then obtain r where r: "v = Suc (js ! m) + r" using le_iff_add by metis
        have r_bound: "r < length (drop (Suc (js ! m)) (Run (i + m)))" using v_bound r in_R2 by simp
        have "drop (Suc (js ! m)) (Run (i + m)) ! r = (Run (i + m)) ! v" using r v_bound in_R2 by simp
        hence "(Run (i + m)) ! v \<in> set (drop (Suc (js ! m)) (Run (i + m)))"using r_bound nth_mem by metis
        hence "rs ! Suc m \<in> post_set \<A> (\<Union> (set (drop (Suc (js ! m)) (Run (i + m))))) (x (i + m))" using post_v unfolding post_set_def by blast
        thus ?thesis using snd_upper_step_eq_post_set_Union by fast
      qed
      have "(Run (i + Suc m)) ! (js ! Suc m) \<inter> snd (upper_step \<A> (x (i + m)) (drop (Suc (js ! m)) (Run (i + m)))) = {}" using pathm unfolding upper_child_def by blast
      thus False using bad pathm by blast
    qed
  qed
  show ?thesis using j run_ext_wd run_ext_i no_steal_ext by blast
qed

lemma TF_component_has_extendable_greedy_run:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []" "j < length (Run i) \<and> upper_continued_F Run \<A> x i j" "i \<le> N"
  shows "\<exists> run . greedy_run run \<A> (pre_omega_word x N) \<and> run ! i \<in> (Run i) ! j"
proof -
  obtain run where jrun: "run_well_defined run \<A> (pre_omega_word x N)" "run ! i \<in> (Run i) ! j" "\<nexists> k . k < length run - 1 \<and> stolen_at \<A> run (pre_omega_run Run N) (pre_omega_word x N) k" using TF_component_has_extendable_no_steal_run[OF assms] by blast
  have "run_well_defined (pre_omega_run Run N) (upper_part_pure \<A>) (pre_omega_word x N)" using assms omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
  hence "greedy_run run \<A> (pre_omega_word x N)" using no_steal_iff_greedy assms jrun by blast
  thus ?thesis using jrun by blast
qed

definition Rpref_hit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('s,'a) automaton \<Rightarrow> ('s states list) omega_run \<Rightarrow> 'a omega_word \<Rightarrow> 's run set" where "Rpref_hit i j n \<A> Run x = {run . greedy_run run \<A> (pre_omega_word x n) \<and> (if n < i then True else run ! i \<in> (Run i) ! j)}"

lemma Rpref_hit_finite:
  assumes "auto_well_defined \<A>"
  shows "finite (Rpref_hit i j N \<A> Run x)"
proof -
  {
    fix r assume "r \<in> Rpref_hit i j N \<A> Run x"
    hence "greedy_run r \<A> (pre_omega_word x N)" unfolding Rpref_hit_def by blast
    hence "run_well_defined r \<A> (pre_omega_word x N)" unfolding greedy_run_def by blast
    hence well_def: "pseudo_run_well_defined r \<A> (initial_state \<A>) (pre_omega_word x N)" unfolding run_well_defined_def by blast
    hence len: "length r = N + 1" unfolding pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
    have "prun_states r \<A>" using assms well_def well_def_implies_prun_states by fast
    hence "r \<in> {run . prun_states run \<A> \<and> length run = N + 1}" using len by blast
  }
  hence sub: "Rpref_hit i j N \<A> Run x \<subseteq> {run . prun_states run \<A> \<and> length run = N + 1}" by blast
  have "finite {run . prun_states run \<A> \<and> length run = N + 1}" using assms finite_lists_length_eq unfolding auto_well_defined_def prun_states_def by blast
  thus ?thesis using finite_subset sub by blast
qed

lemma greedy_run_take_hit:
  assumes "r \<in> Rpref_hit i j N \<A> Run x" "i \<le> M" "M \<le> N"
  shows "take (M + 1) r \<in> Rpref_hit i j M \<A> Run x"
proof -
  have gr: "greedy_run r \<A> (pre_omega_word x N)" using assms unfolding Rpref_hit_def by blast
  hence take_gr: "greedy_run (take (M + 1) r) \<A> (take M (pre_omega_word x N))" using greedy_run_take assms pre_omega_word_length by metis
  have take_word: "take M (pre_omega_word x N) = pre_omega_word x M" using assms pre_omega_word_take by blast
  have "run_well_defined r \<A> (pre_omega_word x N)" using gr unfolding greedy_run_def by blast
  hence "length r = N + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
  hence "(take (M + 1) r) ! i = r ! i" using assms by simp
  hence "(take (M + 1) r) ! i \<in> (Run i) ! j" using assms unfolding Rpref_hit_def by force
  thus ?thesis using take_gr take_word unfolding Rpref_hit_def by auto
qed

definition children_pref_hit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('s, 'a) automaton \<Rightarrow> ('s states list) omega_run \<Rightarrow> 'a omega_word \<Rightarrow> 's run \<Rightarrow> 's run set" where "children_pref_hit i j N \<A> Run x r = {r' \<in> Rpref_hit i j (Suc N) \<A> Run x . r \<prec> r'}"

definition descendants_pref_hit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('s, 'a) automaton \<Rightarrow> ('s states list) omega_run \<Rightarrow> 'a omega_word \<Rightarrow> 's run \<Rightarrow> 's run set" where "descendants_pref_hit i j N \<A> Run x r = {t . \<exists> M \<ge> N . t \<in> Rpref_hit i j M \<A> Run x \<and> r \<preceq> t}"

lemma infinite_Rpref_hit_union:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []" "j < length (Run i) \<and> upper_continued_F Run \<A> x i j"
  shows "infinite (\<Union> N \<in> {N . N \<ge> i} . Rpref_hit i j N \<A> Run x)"
proof -
  let ?pick = "\<lambda>n . SOME r . r \<in> Rpref_hit i j (i + n) \<A> Run x"
  {
    fix n
    have "\<exists> r . greedy_run r \<A> (pre_omega_word x (i + n)) \<and> r ! i \<in> (Run i) ! j" using TF_component_has_extendable_greedy_run assms by fastforce
    hence "Rpref_hit i j (i + n) \<A> Run x \<noteq> {}" unfolding Rpref_hit_def by auto
  }
  hence "\<forall> n . Rpref_hit i j (i + n) \<A> Run x \<noteq> {}" by simp
  hence pick_mem: "\<forall> n . ?pick n \<in> Rpref_hit i j (i + n) \<A> Run x" using someI_ex by fast
  have "inj ?pick"
  proof (rule injI)
    fix m n assume eq: "?pick m = ?pick n"
    have "greedy_run (?pick m) \<A> (pre_omega_word x (i + m))" using pick_mem unfolding Rpref_hit_def by blast
    hence "run_well_defined (?pick m) \<A> (pre_omega_word x (i + m))" unfolding greedy_run_def by blast
    hence lm: "length (?pick m) = i + m + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
    have "greedy_run (?pick n) \<A> (pre_omega_word x (i + n))" using pick_mem unfolding Rpref_hit_def by blast
    hence "run_well_defined (?pick n) \<A> (pre_omega_word x (i + n))" unfolding greedy_run_def by blast
    hence "length (?pick n) = i + n + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
    thus "m = n" using eq lm by presburger
  qed
  hence inf: "infinite (range ?pick)" using finite_imageD by blast
  {
    fix r assume "r \<in> range ?pick"
    then obtain n where r: "r = ?pick n" by blast
    have pick: "?pick n \<in> Rpref_hit i j (i + n) \<A> Run x" using pick_mem by blast
    have "i + n \<in> {N . N \<ge> i}" by simp
    hence "r \<in> (\<Union> N \<in> {N . N \<ge> i} . Rpref_hit i j N \<A> Run x)" using r pick by blast
  }
  hence "range ?pick \<subseteq> (\<Union> N \<in> {N . N \<ge> i} . Rpref_hit i j N \<A> Run x)" by fast
  thus ?thesis using inf infinite_super by blast
qed

lemma descendant_has_child_pref_hit:
  assumes "r \<in> Rpref_hit i j N \<A> Run x" "t \<in> descendants_pref_hit i j N \<A> Run x r" "t \<notin> Rpref_hit i j N \<A> Run x" "N \<ge> i"
  shows "\<exists> c \<in> children_pref_hit i j N \<A> Run x r . t \<in> descendants_pref_hit i j (Suc N) \<A> Run x c"
proof -
  obtain M where M: "M \<ge> N" "t \<in> Rpref_hit i j M \<A> Run x" "r \<preceq> t" using assms unfolding descendants_pref_hit_def by blast
  have "greedy_run t \<A> (pre_omega_word x M)" using M unfolding Rpref_hit_def by blast
  hence "run_well_defined t \<A> (pre_omega_word x M)" unfolding greedy_run_def by blast
  hence len_t: "length t = M + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
  have "greedy_run r \<A> (pre_omega_word x N)" using assms unfolding Rpref_hit_def by blast
  hence "run_well_defined r \<A> (pre_omega_word x N)" unfolding greedy_run_def by blast
  hence len_r: "length r = N + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
  have less: "M > N"
  proof (rule ccontr)
    assume "\<not> M > N"
    hence "M = N" using M by linarith
    thus False using M assms by simp
  qed
  define c where "c = take (Suc N + 1) t"
  hence c_len: "length c = Suc N + 1" using len_t less by force
  hence leq: "length r < length c" using len_r by simp
  have "take (length r) t = r" using M unfolding prefixeq_def by force
  hence "take (length r) c = r" using len_r less c_len len_t leq min.strict_order_iff take_take unfolding c_def by metis
  hence "r \<preceq> c" using append_take_drop_id unfolding prefixeq_def by metis
  then obtain d where d: "r @ d = c" unfolding prefixeq_def by blast
  hence "d \<noteq> []" using leq len_r by force
  hence r_proper_c: "r \<prec> c" using d unfolding proper_prefix_def by blast
  have "c \<in> Rpref_hit i j (Suc N) \<A> Run x" using greedy_run_take_hit M assms less unfolding c_def by fastforce
  hence c_child: "c \<in> children_pref_hit i j N \<A> Run x r" using r_proper_c unfolding children_pref_hit_def by blast
  have c_pre_t: "c \<preceq> t" using append_take_drop_id unfolding c_def prefixeq_def by metis
  have "M \<ge> Suc N" using less by simp
  hence "t \<in> descendants_pref_hit i j (Suc N) \<A> Run x c" using M c_pre_t unfolding descendants_pref_hit_def by blast
  thus ?thesis using c_child by blast
qed

lemma infinite_descendants_choose_child_pref_hit:
  assumes "auto_well_defined \<A>" "r \<in> Rpref_hit i j N \<A> Run x" "N \<ge> i" "infinite (descendants_pref_hit i j N \<A> Run x r)"
  shows "\<exists> c \<in> children_pref_hit i j N \<A> Run x r . infinite (descendants_pref_hit i j (Suc N) \<A> Run x c)"
proof -
  let ?Ch = "children_pref_hit i j N \<A> Run x r"
  have "finite (Rpref_hit i j (Suc N) \<A> Run x)" using Rpref_hit_finite assms by fastforce
  hence finCh: "finite ?Ch" unfolding children_pref_hit_def by auto
  let ?B = "{t . t \<in> Rpref_hit i j N \<A> Run x \<and> r \<preceq> t}"
  have "finite (Rpref_hit i j N \<A> Run x)" using Rpref_hit_finite assms by fastforce
  hence finB: "finite ?B" by simp
  {
    fix t assume assm: "t \<in> descendants_pref_hit i j N \<A> Run x r"
    hence "t \<in> ?B \<union> (\<Union> c \<in> ?Ch . descendants_pref_hit i j (Suc N) \<A> Run x c)"
    proof (cases "t \<in> Rpref_hit i j N \<A> Run x")
      case True thus ?thesis using assm unfolding descendants_pref_hit_def by blast
    next
      case False
      then obtain c where "c \<in> children_pref_hit i j N \<A> Run x r \<and> t \<in> descendants_pref_hit i j (Suc N) \<A> Run x c" using descendant_has_child_pref_hit[OF assms(2) assm False assms(3)] by blast
      thus ?thesis by blast
    qed
  }
  hence sub: "descendants_pref_hit i j N \<A> Run x r \<subseteq> ?B \<union> (\<Union> c \<in> ?Ch . descendants_pref_hit i j (Suc N) \<A> Run x c)" by blast
  have "infinite (\<Union> c \<in> ?Ch . descendants_pref_hit i j (Suc N) \<A> Run x c)"
  proof (rule ccontr)
    assume "\<not> infinite (\<Union> c \<in> ?Ch . descendants_pref_hit i j (Suc N) \<A> Run x c)"
    hence "finite (\<Union> c \<in> ?Ch . descendants_pref_hit i j (Suc N) \<A> Run x c)" by blast
    hence "finite (?B \<union> (\<Union> c \<in> ?Ch . descendants_pref_hit i j (Suc N) \<A> Run x c))" using finB by blast
    hence "finite (descendants_pref_hit i j N \<A> Run x r)" using sub finite_subset by blast
    thus False using assms by blast
  qed
  thus ?thesis using finCh by blast
qed

lemma infinite_descendants_at_level_i_hit:
  assumes "auto_well_defined \<A>" "infinite (\<Union> N \<in> {N . N \<ge> i} . Rpref_hit i j N \<A> Run x)"
  shows "\<exists> r0 \<in> Rpref_hit i j i \<A> Run x . infinite (descendants_pref_hit i j i \<A> Run x r0)"
proof -
  let ?U = "(\<Union> N \<in> {N . N \<ge> i} . Rpref_hit i j N \<A> Run x)"
  let ?R0 = "Rpref_hit i j i \<A> Run x"
  have finR0: "finite ?R0" using Rpref_hit_finite assms by blast
  {
    fix t assume "t \<in> ?U"
    then obtain N where N: "N \<ge> i" "t \<in> Rpref_hit i j N \<A> Run x" by blast
    define r0 where "r0 = take (i + 1) t"
    hence r0_in: "r0 \<in> ?R0" using greedy_run_take_hit[OF N(2)] N(1) by simp
    have "r0 \<preceq> t" unfolding r0_def prefixeq_def by (metis append_take_drop_id)
    hence "t \<in> descendants_pref_hit i j i \<A> Run x r0" using N r0_in unfolding descendants_pref_hit_def by blast
    hence "t \<in> (\<Union> r0 \<in> ?R0 . descendants_pref_hit i j i \<A> Run x r0)" using r0_in by blast
  }
  hence sub: "?U \<subseteq> (\<Union> r0 \<in> ?R0. descendants_pref_hit i j i \<A> Run x r0)" by fast
  have "\<exists> r0 \<in> ?R0 . infinite (descendants_pref_hit i j i \<A> Run x r0)"
  proof (rule ccontr)
    assume neg: "\<not> (\<exists> r0 \<in> ?R0 . infinite (descendants_pref_hit i j i \<A> Run x r0))"
    hence fin_each: "\<forall> r0 \<in> ?R0 . finite (descendants_pref_hit i j i \<A> Run x r0)" by blast
    have "finite (\<Union> r0 \<in> ?R0 . descendants_pref_hit i j i \<A> Run x r0)" using finR0 fin_each by blast
    hence "finite ?U" using sub finite_subset by blast
    thus False using assms by blast
  qed
  thus ?thesis by blast
qed

lemma chain_exists_Rpref_hit_from_i:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []" "j < length (Run i) \<and> upper_continued_F Run \<A> x i j"
  shows "\<exists> rseq . (\<forall> n . rseq n \<in> Rpref_hit i j (i + n) \<A> Run x \<and> rseq n \<prec> rseq (Suc n))"
proof -
  have infU: "infinite (\<Union> N \<in> {N . N \<ge> i} . Rpref_hit i j N \<A> Run x)" using infinite_Rpref_hit_union assms by blast
  obtain r0 where r0: "r0 \<in> Rpref_hit i j i \<A> Run x" "infinite (descendants_pref_hit i j i \<A> Run x r0)" using infinite_descendants_at_level_i_hit[OF assms(1) infU] by blast
  define rseq where "rseq = rec_nat r0 (\<lambda>n rn . SOME c . c \<in> children_pref_hit i j (i + n) \<A> Run x rn \<and> infinite (descendants_pref_hit i j (Suc (i + n)) \<A> Run x c))"
  {
    fix n
    have "rseq n \<in> Rpref_hit i j (i + n) \<A> Run x \<and> infinite (descendants_pref_hit i j (i + n) \<A> Run x (rseq n))"
    proof (induction n)
      case 0 thus ?case using r0 unfolding rseq_def by simp
    next
      case (Suc n)
      then obtain c where "c \<in> children_pref_hit i j (i + n) \<A> Run x (rseq n) \<and> infinite (descendants_pref_hit i j (Suc (i + n)) \<A> Run x c)" using infinite_descendants_choose_child_pref_hit[OF assms(1), of "rseq n" i j "i+n" Run x] by auto
      hence "(SOME c . c \<in> children_pref_hit i j (i + n) \<A> Run x (rseq n) \<and> infinite (descendants_pref_hit i j (Suc (i + n)) \<A> Run x c)) \<in> children_pref_hit i j (i + n) \<A> Run x (rseq n) \<and> infinite (descendants_pref_hit i j (Suc (i + n)) \<A> Run x (SOME c . c \<in> children_pref_hit i j (i + n) \<A> Run x (rseq n) \<and> infinite (descendants_pref_hit i j (Suc (i + n)) \<A> Run x c)))" by (rule someI2) auto
      thus ?case unfolding rseq_def children_pref_hit_def by simp
    qed
  }
  hence step_all: "\<forall> n . rseq n \<in> Rpref_hit i j (i + n) \<A> Run x \<and> infinite (descendants_pref_hit i j (i + n) \<A> Run x (rseq n))" by simp
  {
    fix n
    have IH: "rseq n \<in> Rpref_hit i j (i + n) \<A> Run x \<and> infinite (descendants_pref_hit i j (i + n) \<A> Run x (rseq n))" using step_all by simp
    then obtain c where "c \<in> children_pref_hit i j (i + n) \<A> Run x (rseq n) \<and> infinite (descendants_pref_hit i j (Suc (i + n)) \<A> Run x c)" using infinite_descendants_choose_child_pref_hit[OF assms(1), of "rseq n" i j "i+n" Run x] by auto
    hence "(SOME c . c \<in> children_pref_hit i j (i + n) \<A> Run x (rseq n) \<and> infinite (descendants_pref_hit i j (Suc (i + n)) \<A> Run x c)) \<in> children_pref_hit i j (i + n) \<A> Run x (rseq n)" by (rule someI2) auto
    hence "rseq (Suc n) \<in> children_pref_hit i j (i + n) \<A> Run x (rseq n)" unfolding rseq_def by simp
    hence "rseq n \<in> Rpref_hit i j (i + n) \<A> Run x \<and> rseq n \<prec> rseq (Suc n)" using IH unfolding children_pref_hit_def by auto
  }
  thus ?thesis by blast
qed

lemma chain_exists_Rpref_hit:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []" "j < length (Run i) \<and> upper_continued_F Run \<A> x i j"
  shows "\<exists> gseq . \<forall> n . gseq n \<in> Rpref_hit i j n \<A> Run x \<and> gseq n \<prec> gseq (Suc n)"
proof -
  obtain rseq where chain:  "\<forall> n . rseq n \<in> Rpref_hit i j (i + n) \<A> Run x \<and> rseq n \<prec> rseq (Suc n)" using chain_exists_Rpref_hit_from_i assms by blast
  define gseq where "gseq = (\<lambda>n. if n < i then take (n + 1) (rseq 0) else rseq (n - i))"
  have r0_in: "rseq 0 \<in> Rpref_hit i j i \<A> Run x" using chain Nat.add_0_right by metis
  hence "greedy_run (rseq 0) \<A> (pre_omega_word x i)" unfolding Rpref_hit_def by blast
  hence "run_well_defined (rseq 0) \<A> (pre_omega_word x i)" unfolding greedy_run_def by blast
  hence len_r0: "length (rseq 0) = i + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
  {
    fix n
    have "gseq n \<in> Rpref_hit i j n \<A> Run x \<and> gseq n \<prec> gseq (Suc n)"
    proof (cases "Suc n \<le> i")
      case True
      hence n_lt_i: "n < i" by simp
      have g_n: "gseq n = take (n + 1) (rseq 0)" using True unfolding gseq_def by simp
      have g_Suc: "gseq (Suc n) = take (Suc n + 1) (rseq 0)" using True diff_is_0_eq' le_eq_less_or_eq len_r0 take_all unfolding gseq_def by metis
      have gr0: "greedy_run (rseq 0) \<A> (pre_omega_word x i)" using r0_in unfolding Rpref_hit_def by blast
      hence "length (pre_omega_word x i) = i" by (simp add: pre_omega_word_length)
      hence n_leq: "n \<le> length (pre_omega_word x i)" using n_lt_i by simp
      hence take_gr: "greedy_run (take (n + 1) (rseq 0)) \<A> (take n (pre_omega_word x i))" using greedy_run_take gr0 by blast
      have "take n (pre_omega_word x i) = pre_omega_word x n" using pre_omega_word_take n_leq by (simp add: pre_omega_word_length)
      hence "greedy_run (take (n + 1) (rseq 0)) \<A> (pre_omega_word x n)" using take_gr by simp
      hence in_hit: "gseq n \<in> Rpref_hit i j n \<A> Run x"  using n_lt_i unfolding g_n Rpref_hit_def by simp
      have "n + 1 < length (rseq 0)" using len_r0 True by simp
      hence "take (Suc n + 1) (rseq 0) = take (n + 1) (rseq 0) @ [rseq 0 ! (n + 1)]" by (simp add: take_Suc_conv_app_nth)
      hence pref: "take (n + 1) (rseq 0) \<prec> take (Suc n + 1) (rseq 0)" unfolding proper_prefix_def prefixeq_def by simp
      thus ?thesis using in_hit unfolding g_n g_Suc by blast
    next
      case False
      hence n_ge_i: "i \<le> n" by simp
      define m where "m = n - i"
      hence n_eq: "n = i + m" using n_ge_i by simp
      have g_n: "gseq n = rseq m" using n_ge_i unfolding gseq_def m_def by simp
      have g_Suc: "gseq (Suc n) = rseq (Suc m)" using n_ge_i False Nat.add_diff_assoc less_or_eq_imp_le plus_1_eq_Suc unfolding gseq_def m_def by metis 
      have step: "rseq m \<in> Rpref_hit i j (i + m) \<A> Run x \<and> rseq m \<prec> rseq (Suc m)" using chain by blast
      hence in_hit: "gseq n \<in> Rpref_hit i j n \<A> Run x" using g_n n_eq by simp
      have pref: "gseq n \<prec> gseq (Suc n)" using step unfolding g_n g_Suc by simp
      thus ?thesis using in_hit by blast
    qed
  }
  thus ?thesis by auto
qed

lemma chain_nth_stable_Rpref_hit:
  assumes "\<forall> n . rseq n \<prec> rseq (Suc n) \<and> rseq n \<in> Rpref_hit i j n \<A> Run x" 
  shows "(rseq (Suc (Suc n))) ! n = (rseq (Suc n)) ! n"
proof -
  have "rseq (Suc n) \<prec> rseq (Suc (Suc n))" using assms by blast
  hence "rseq (Suc n) \<preceq> rseq (Suc (Suc n))" unfolding proper_prefix_def prefixeq_def by blast
  then obtain d where app: "rseq (Suc n) @ d = rseq (Suc (Suc n))" unfolding prefixeq_def by blast
  have "n < length (rseq (Suc n))" using assms chain_len_ge by blast
  thus ?thesis using app nth_append by metis
qed

lemma chain_nth_stable_iter_Rpref_hit: "m \<le> n \<and> (\<forall> n . rseq n \<in> Rpref_hit i j n \<A> Run x \<and> rseq n \<prec> rseq (Suc n)) \<Longrightarrow> (rseq (Suc n)) ! m = (rseq (Suc m)) ! m"
proof (induction "n - m" arbitrary: n)
  case 0 thus ?case by auto
next
  case (Suc k)
  hence "m < n" by simp
  then obtain n' where n: "n = Suc n'" by (cases n) auto
  hence m_le_n': "m \<le> n'" using Suc by simp
  hence IH: "(rseq (Suc n')) ! m = (rseq (Suc m)) ! m" using Suc Suc_diff_le Suc_inject n by metis
  have "rseq (Suc n') \<prec> rseq (Suc (Suc n'))" using Suc by blast
  hence "rseq (Suc n') \<preceq> rseq (Suc (Suc n'))" unfolding proper_prefix_def prefixeq_def by blast
  then obtain d where app: "rseq (Suc n') @ d = rseq (Suc (Suc n'))" unfolding prefixeq_def by blast
  have "rseq (Suc n') \<in> Rpref_hit i j (Suc n') \<A> Run x" using Suc by blast
  hence "greedy_run (rseq (Suc n')) \<A> (pre_omega_word x (Suc n'))" unfolding Rpref_hit_def by blast
  hence "run_well_defined (rseq (Suc n')) \<A> (pre_omega_word x (Suc n'))" unfolding greedy_run_def by blast
  hence "length (rseq (Suc n')) = Suc n' + 1" unfolding run_well_defined_def pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
  hence "m < length (rseq (Suc n'))" using m_le_n' by simp
  hence"(rseq (Suc (Suc n'))) ! m = (rseq (Suc n')) ! m" using app nth_append by metis
  thus ?case using IH unfolding n by simp
qed

lemma omega_greedy_hits_hit_component:
  assumes "\<forall> n . rseq n \<in> Rpref_hit i j n \<A> Run x \<and> rseq n \<prec> rseq (Suc n)"
  shows "(rho_from_chain rseq) i \<in> (Run i) ! j"
proof -
  have rho: "(rho_from_chain rseq) i = (rseq (Suc i)) ! i" unfolding rho_from_chain_def by simp
  have "rseq (Suc i) \<in> Rpref_hit i j (Suc i) \<A> Run x" using assms by blast
  hence "(rseq (Suc i)) ! i \<in> (Run i) ! j" unfolding Rpref_hit_def by auto
  thus ?thesis using rho by simp
qed

lemma Rpref_hit_length_const:
  assumes "r \<in> Rpref_hit i j n \<A> Run x"
  shows "length r = n + 1"
  using assms pre_omega_word_length unfolding Rpref_hit_def greedy_run_def run_well_defined_def pseudo_run_well_defined_def by auto

lemma pre_omega_run_rho_from_chain_hit:
  assumes "\<forall> n . rseq n \<in> Rpref_hit i j n \<A> Run x \<and> rseq n \<prec> rseq (Suc n)"
  shows "pre_omega_run (rho_from_chain rseq) n = rseq n"
proof (rule nth_equalityI)
  show "length (pre_omega_run (rho_from_chain rseq) n) = length (rseq n)" using assms Rpref_hit_length_const add.commute diff_zero length_map length_upt plus_1_eq_Suc unfolding pre_omega_run_def by metis
next
  fix k assume k: "k < length (pre_omega_run (rho_from_chain rseq) n)"
  hence k_lt: "k < n + 1" unfolding pre_omega_run_def by auto
  hence k_le: "k \<le> n" by simp
  have lhs: "(pre_omega_run (rho_from_chain rseq) n) ! k = (rho_from_chain rseq) k" using k pre_omega_run_length pre_omega_run_nth unfolding pre_omega_run_def by metis
  have rho_k: "(rho_from_chain rseq) k = (rseq (Suc k)) ! k" unfolding rho_from_chain_def by auto
  have stab: "(rseq (Suc n)) ! k = (rseq (Suc k)) ! k" using chain_nth_stable_iter_Rpref_hit assms k_le by blast
  have "rseq n \<prec> rseq (Suc n)" using assms by blast
  hence "rseq n \<preceq> rseq (Suc n)" unfolding proper_prefix_def prefixeq_def by blast
  then obtain d where app: "rseq n @ d = rseq (Suc n)" unfolding prefixeq_def by blast
  have "length (rseq n) = n + 1" using assms Rpref_hit_length_const by blast
  hence "k < length (rseq n)" using k_lt by simp
  hence "(rseq (Suc n)) ! k = (rseq n) ! k" using app nth_append by metis
  thus "(pre_omega_run (rho_from_chain rseq) n) ! k = (rseq n) ! k" using lhs rho_k stab by simp
qed

lemma rho_well_defined_Rpref_hit:
  assumes "auto_well_defined \<A>" "\<forall> n . rseq n \<in> Rpref_hit i j n \<A> Run x \<and> rseq n \<prec> rseq (Suc n)"
  shows "omega_run_well_defined (rho_from_chain rseq) \<A> x"
proof -
  let ?rho = "rho_from_chain rseq"
  have "rseq 1 \<in> Rpref_hit i j 1 \<A> Run x" using assms by auto
  hence r1: "run_well_defined (rseq 1) \<A> (pre_omega_word x 1)" unfolding Rpref_hit_def greedy_run_def by auto
  have "?rho 0 = (rseq 1) ! 0" unfolding rho_from_chain_def by auto
  hence init: "?rho 0 = initial_state \<A> \<and> initial_state \<A> \<in> states \<A>" using r1 unfolding run_well_defined_def pseudo_run_well_defined_def by argo
  {
    fix n
    have "rseq (Suc (Suc n)) \<in> Rpref_hit i j (Suc (Suc n)) \<A> Run x" using assms by blast
    hence pr: "pseudo_run_well_defined (rseq (Suc (Suc n))) \<A> (initial_state \<A>) (pre_omega_word x (Suc (Suc n)))" unfolding Rpref_hit_def greedy_run_def run_well_defined_def by simp
    hence "n < length (rseq (Suc (Suc n))) - 1" unfolding pseudo_run_well_defined_def by (simp add: pre_omega_word_length)
    hence trans: "((rseq (Suc (Suc n))) ! n, (pre_omega_word x (Suc (Suc n))) ! n, (rseq (Suc (Suc n))) ! (n + 1)) \<in> transitions \<A>" using pr unfolding pseudo_run_well_defined_def by blast
    have w_n: "(pre_omega_word x (Suc (Suc n))) ! n = x n" by (simp add: pre_omega_word_nth)
    have "(rseq (Suc (Suc n))) ! n = (rseq (Suc n)) ! n" using assms chain_nth_stable_Rpref_hit by blast
    hence rho_n: "?rho n = (rseq (Suc (Suc n))) ! n" unfolding rho_from_chain_def by auto
    have "?rho (n + 1) = (rseq (Suc (Suc n))) ! (n + 1)" unfolding rho_from_chain_def by auto
    hence "(?rho n, x n, ?rho (n + 1)) \<in> transitions \<A>" using trans w_n rho_n by argo
  }
  hence "\<forall> n . (?rho n, x n, ?rho (n + 1)) \<in> transitions \<A>" by blast
  thus ?thesis using init unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
qed

lemma rho_greedy_Rpref_hit:
  assumes "auto_well_defined \<A>" "\<forall> n . rseq n \<in> Rpref_hit i j n \<A> Run x \<and> rseq n \<prec> rseq (Suc n)"
  shows "omega_greedy_run (rho_from_chain rseq) \<A> x \<and> (rho_from_chain rseq) i \<in> (Run i) ! j"
proof -
  have wd: "omega_run_well_defined (rho_from_chain rseq) \<A> x" using rho_well_defined_Rpref_hit assms by blast
  {
    fix n
    have "rseq n \<in> Rpref_hit i j n \<A> Run x" using assms by blast
    hence greedy: "greedy_run (rseq n) \<A> (pre_omega_word x n)" unfolding Rpref_hit_def by blast
    have "pre_omega_run (rho_from_chain rseq) n = rseq n" using pre_omega_run_rho_from_chain_hit assms by blast
    hence "greedy_run (pre_omega_run (rho_from_chain rseq) n) \<A> (pre_omega_word x n)" using greedy by simp
  }
  hence "\<forall> n . greedy_run (pre_omega_run (rho_from_chain rseq) n) \<A> (pre_omega_word x n)" by auto
  thus ?thesis using wd assms omega_greedy_hits_hit_component unfolding omega_greedy_run_def by blast
qed

theorem omega_greedy_run_exists_through_TF_slice:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []" "upper_slice_continued_F Run \<A> x i"
  shows "\<exists> r j . j < length (Run i) \<and> upper_continued_F Run \<A> x i j \<and> omega_greedy_run r \<A> x \<and> r i \<in> (Run i) ! j"
proof -
  obtain j where j: "j < length (Run i)" "upper_continued_F Run \<A> x i j" using assms unfolding upper_slice_continued_F_def by blast
  then obtain rseq where chain:  "\<forall> n . rseq n \<in> Rpref_hit i j n \<A> Run x \<and> rseq n \<prec> rseq (Suc n)" using chain_exists_Rpref_hit[OF assms(1-3)] by blast
  have "omega_greedy_run (rho_from_chain rseq) \<A> x \<and> (rho_from_chain rseq) i \<in> (Run i) ! j" using rho_greedy_Rpref_hit[OF assms(1) chain] by blast
  thus ?thesis using j by blast
qed

lemma choose_greedy_runs_through_TF_slices:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n. Run n \<noteq> []" "infinite {i . upper_slice_continued_F Run \<A> x i}"
  shows "\<exists> f g . (\<forall> i \<in> {i . upper_slice_continued_F Run \<A> x i} . g i < length (Run i) \<and> upper_continued_F Run \<A> x i (g i) \<and> omega_greedy_run (f i) \<A> x \<and> (f i) i \<in> (Run i) ! (g i))"
proof -
  let ?I = "{i . upper_slice_continued_F Run \<A> x i}"
  have ex: "\<forall> i \<in> ?I . \<exists> p . case p of (r, j) => j < length (Run i) \<and> upper_continued_F Run \<A> x i j \<and> omega_greedy_run r \<A> x \<and> r i \<in> (Run i) ! j" using omega_greedy_run_exists_through_TF_slice[OF assms(1-3)] by force
  obtain h where h: "\<forall> i \<in> ?I . case h i of (r, j) => j < length (Run i) \<and> upper_continued_F Run \<A> x i j \<and> omega_greedy_run r \<A> x \<and> r i \<in> (Run i) ! j" using bchoice[OF ex] by blast
  define f where "f i = fst (h i)" for i
  define g where "g i = snd (h i)" for i
  {
    fix i assume "i \<in> ?I"
    hence hi: "case h i of (r, j) => j < length (Run i) \<and> upper_continued_F Run \<A> x i j \<and> omega_greedy_run r \<A> x \<and> r i \<in> (Run i) ! j" using h by simp
    hence "g i < length (Run i) \<and> upper_continued_F Run \<A> x i (g i) \<and> omega_greedy_run (f i) \<A> x \<and> (f i) i \<in> (Run i) ! (g i)" unfolding f_def g_def by (cases "h i") auto
  }
  hence "\<forall> i \<in> ?I . g i < length (Run i) \<and> upper_continued_F Run \<A> x i (g i) \<and> omega_greedy_run (f i) \<A> x \<and> (f i) i \<in> (Run i) ! (g i)" by blast
  thus ?thesis by blast
qed

lemma chosen_greedy_runs_accepting_at_index:
  assumes "\<forall> i \<in> {i . upper_slice_continued_F Run \<A> x i} . g i < length (Run i) \<and> upper_continued_F Run \<A> x i (g i) \<and> omega_greedy_run (f i) \<A> x \<and> (f i) i \<in> (Run i) ! (g i)"
  shows "\<forall> i \<in> {i . upper_slice_continued_F Run \<A> x i} . (f i) i \<in> accepting_states \<A>"
  using assms unfolding upper_continued_F_def by blast

definition samelevel_global :: "'s omega_run \<Rightarrow> 's omega_run \<Rightarrow> ('s states list) omega_run \<Rightarrow> bool" where "samelevel_global run run' Run = (\<forall> n . \<exists> i < length (Run n) . run n \<in> (Run n) ! i \<and> run' n \<in> (Run n) ! i)"

lemma samelevel_global_reflexiv:
  assumes "auto_well_defined \<A>" "omega_run_well_defined run \<A> word" "omega_run_well_defined Run (upper_part_pure \<A>) word"
  shows "samelevel_global run run Run"
proof -
  {
    fix n
    have run_pref: "run_well_defined (pre_omega_run run n) \<A> (pre_omega_word word n)" using assms omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
    have Run_pref: "run_well_defined (pre_omega_run Run n) (upper_part_pure \<A>) (pre_omega_word word n)" using assms omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
    have "n < length (pre_omega_run run n)" by (simp add: pre_omega_run_length)
    then obtain i where "i < length ((pre_omega_run Run n) ! n)" "(pre_omega_run run n) ! n \<in> ((pre_omega_run Run n) ! n) ! i" using run_state_in_upper_component[OF assms(1) run_pref Run_pref] by blast
    hence "\<exists> i < length (Run n) . run n \<in> (Run n) ! i" using pre_omega_run_nth lessI by metis
  }
  thus ?thesis unfolding samelevel_global_def by blast
qed

theorem samelevel_global_transitive:
  assumes "\<forall> n. Run n \<in> upper_states \<A>" "samelevel_global run run' Run" "samelevel_global run' run'' Run"
  shows "samelevel_global run run'' Run"
proof -
  {
    fix n
    have upper: "Run n \<in> upper_states \<A>"  using assms by blast
    have "\<exists> i . i < length (Run n) \<and> run n \<in> (Run n) ! i \<and> run' n \<in> (Run n) ! i" using assms unfolding samelevel_global_def by blast
    then obtain i where i: "i < length (Run n)" "run n \<in> (Run n) ! i" "run' n \<in> (Run n) ! i" by blast
    have "\<exists> j. j < length (Run n) \<and> run' n \<in> (Run n) ! j \<and> run'' n \<in> (Run n) ! j" using assms unfolding samelevel_global_def by blast
    then obtain j where j: "j < length (Run n)" "run' n \<in> (Run n) ! j" "run'' n \<in> (Run n) ! j" by blast
    have "i = j" using unique_component_upper_state upper i j by fast
    hence "\<exists> k . k < length (Run n) \<and> run n \<in> (Run n) ! k \<and> run'' n \<in> (Run n) ! k" using i j by blast
  }
  thus ?thesis unfolding samelevel_global_def by blast
qed

theorem samelevel_symmetry:
  assumes "samelevel_global run run' Run "
  shows "samelevel_global run' run Run "
  using assms unfolding samelevel_global_def by blast

lemma uniform_component_acceptance:
  assumes "S \<subseteq> accepting_states \<A> \<or> S \<inter> accepting_states \<A> = {}" "p \<in> S" "q \<in> S"
  shows "p \<in> accepting_states \<A> \<longleftrightarrow> q \<in> accepting_states \<A>"
  using assms by blast

lemma samelevel_global_preserves_acceptance_at_index:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n. Run n \<noteq> []" "samelevel_global r r' Run"
  shows "\<forall> i . r i \<in> accepting_states \<A> \<longleftrightarrow> r' i \<in> accepting_states \<A>"
proof -
  {
    fix i
    obtain j where j: "j < length (Run i)" "r i \<in> (Run i) ! j" "r' i \<in> (Run i) ! j" using assms unfolding samelevel_global_def by blast
    hence "(Run i) ! j \<subseteq> accepting_states \<A> \<or> (Run i) ! j \<inter> accepting_states \<A> = {}" using omega_run_uniform_components[OF assms(1,2,3)] by blast
    hence "r i \<in> accepting_states \<A> \<longleftrightarrow> r' i \<in> accepting_states \<A>" using uniform_component_acceptance[of "(Run i) ! j" \<A> "r i" "r' i"] j by blast
  }
  thus ?thesis by blast
qed

lemma omega_greedy_run_hits_some_component:
  assumes "auto_well_defined \<A>" "omega_greedy_run r \<A> x" "omega_run_well_defined Run (upper_part_pure \<A>) x"
  shows "\<forall> n . \<exists> j < length (Run n) . r n \<in> (Run n) ! j"
proof -
  {
    fix n
    have r_pref: "run_well_defined (pre_omega_run r n) \<A> (pre_omega_word x n)" using assms(2) omega_run_implies_pre_run_well_def unfolding omega_greedy_run_def omega_run_well_defined_def run_well_defined_def by metis
    hence n_less: "n < length (pre_omega_run r n)" by (simp add: pre_omega_run_length)
    have Run_pref: "run_well_defined (pre_omega_run Run n) (upper_part_pure \<A>) (pre_omega_word x n)" using assms(3) omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis
    hence "\<exists> j < length ((pre_omega_run Run n) ! n) . (pre_omega_run r n) ! n \<in> ((pre_omega_run Run n) ! n)! j" using run_state_in_upper_component r_pref n_less Run_pref assms by blast
    hence "\<exists> j < length (Run n) . r n \<in> (Run n) ! j" by (simp add: pre_omega_run_nth)
  }
  thus ?thesis by blast
qed

lemma omega_greedy_run_component_unique:
  assumes "auto_well_defined \<A>" "omega_greedy_run r \<A> x" "omega_run_well_defined Run (upper_part_pure \<A>) x" "j < length (Run n)" "k < length (Run n)" "r n \<in> (Run n) ! j" "r n \<in> (Run n) ! k"
  shows "j = k"
proof -
  have ne: "Run n \<noteq> []" using not_empty_omega_run assms unfolding omega_greedy_run_def by blast
  have "auto_well_defined (upper_part_pure \<A>)" using assms(1) well_def_upper_part_pure by blast
  hence "Run n \<in> states (upper_part_pure \<A>)" using assms well_def_implies_omega_prun_states unfolding omega_run_well_defined_def omega_prun_states_def by fast
  hence "Run n \<in> upper_states \<A>" using ne unfolding upper_part_pure_def by auto
  thus ?thesis using unique_component_upper_state assms by metis
qed

definition comp_idx :: "('s states list) omega_run \<Rightarrow> 's omega_run \<Rightarrow> nat \<Rightarrow> nat" where "comp_idx Run r n = (THE j . j < length (Run n) \<and> r n \<in> (Run n) ! j)"

lemma comp_idx_correct:
  assumes "auto_well_defined \<A>" "omega_greedy_run r \<A> x" "omega_run_well_defined Run (upper_part_pure \<A>) x"
  shows "comp_idx Run r n < length (Run n) \<and> r n \<in> (Run n) ! comp_idx Run r n"
proof -
  obtain j where j: "j < length (Run n)" "r n \<in> (Run n) ! j" using omega_greedy_run_hits_some_component[OF assms] by blast
  have uniq: "\<And>k . j < length (Run n) \<and> r n \<in> (Run n) ! j \<Longrightarrow> k < length (Run n) \<and> r n \<in> (Run n) ! k \<Longrightarrow> k = j" using omega_greedy_run_component_unique[OF assms, of j n] by blast
  show ?thesis unfolding comp_idx_def by (rule theI') (use j uniq in blast)
qed

lemma same_comp_step_back:
  assumes "auto_well_defined \<A>" "omega_greedy_run r \<A> x" "omega_greedy_run r' \<A> x" "omega_run_well_defined Run (upper_part_pure \<A>) x" "comp_idx Run r (Suc n) = comp_idx Run r' (Suc n)"
  shows "comp_idx Run r n = comp_idx Run r' n"
proof -
  let ?j = "comp_idx Run r (Suc n)"
  let ?m = "comp_idx Run r n"
  let ?m' = "comp_idx Run r' n"
  have r_pref: "run_well_defined (pre_omega_run r (Suc n)) \<A> (pre_omega_word x (Suc n))" using assms(2) omega_run_implies_pre_run_well_def unfolding omega_greedy_run_def omega_run_well_defined_def run_well_defined_def by metis
  have r'_pref: "run_well_defined (pre_omega_run r' (Suc n)) \<A> (pre_omega_word x (Suc n))" using assms(3) omega_run_implies_pre_run_well_def unfolding omega_greedy_run_def omega_run_well_defined_def run_well_defined_def by metis
  have Run_pref: "run_well_defined (pre_omega_run Run (Suc n)) (upper_part_pure \<A>) (pre_omega_word x (Suc n))" using assms(4) omega_run_implies_pre_run_well_def unfolding omega_run_well_defined_def run_well_defined_def by metis 
  hence no_steal_r: "\<not> stolen_at \<A> (pre_omega_run r (Suc n)) (pre_omega_run Run (Suc n)) (pre_omega_word x (Suc n)) n" using assms diff_Suc_1 lessI no_steal_and_greedy_left pre_omega_run_length unfolding omega_greedy_run_def by metis
  have no_steal_r': "\<not> stolen_at \<A> (pre_omega_run r' (Suc n)) (pre_omega_run Run (Suc n)) (pre_omega_word x (Suc n)) n" using assms Run_pref diff_Suc_1 lessI no_steal_and_greedy_left pre_omega_run_length unfolding omega_greedy_run_def by metis
  have m_props: "?m < length (Run n)" "r n \<in> (Run n) ! ?m" using comp_idx_correct[OF assms(1,2,4), of n] by simp_all
  have m'_props: "?m' < length (Run n)" "r' n \<in> (Run n) ! ?m'" using comp_idx_correct[OF assms(1,3,4), of n] by simp_all
  have j_props: "?j < length (Run (Suc n))" "r (Suc n) \<in> (Run (Suc n)) ! ?j" "r' (Suc n) \<in> (Run (Suc n)) ! ?j" using comp_idx_correct[OF assms(1,2,4), of "Suc n"] comp_idx_correct[OF assms(1,3,4), of "Suc n"] assms(5) by simp_all
  have idx: "n < length (pre_omega_word x (Suc n))" by (simp add: pre_omega_word_length)
  have m_pref: "?m < length ((pre_omega_run Run (Suc n)) ! n)" using m_props(1) by (simp add: pre_omega_run_nth)
  have m'_pref: "?m' < length ((pre_omega_run Run (Suc n)) ! n)" using m'_props(1) by (simp add: pre_omega_run_nth)
  have rn_pref: "(pre_omega_run r (Suc n)) ! n \<in> ((pre_omega_run Run (Suc n)) ! n) ! ?m" using m_props(2) by (simp add: pre_omega_run_nth)
  have rn'_pref: "(pre_omega_run r' (Suc n)) ! n \<in> ((pre_omega_run Run (Suc n)) ! n) ! ?m'" using m'_props(2) by (simp add: pre_omega_run_nth)
  have rSuc_pref: "(pre_omega_run r (Suc n)) ! Suc n \<in> ((pre_omega_run Run (Suc n)) ! Suc n) ! ?j" using j_props(2) by (simp add: pre_omega_run_nth)
  have r'Suc_pref: "(pre_omega_run r' (Suc n)) ! Suc n \<in> ((pre_omega_run Run (Suc n)) ! Suc n) ! ?j" using j_props(3) by (simp add: pre_omega_run_nth)
  have j_pref: "?j < length ((pre_omega_run Run (Suc n)) ! Suc n)" using j_props(1) by (simp add: pre_omega_run_nth)
  have not_less: "\<not> ?m < ?m'"
  proof(rule ccontr)
    assume "\<not> \<not> ?m < ?m'"
    hence "?m < ?m'" by simp
    hence "?j < ?j" using no_steal_preserves_left_order assms(1) r_pref r'_pref Run_pref idx m_pref m'_pref rn_pref rn'_pref no_steal_r rSuc_pref r'Suc_pref j_pref j_pref by blast
    thus False by simp
  qed
  have "\<not> ?m' < ?m"
   proof(rule ccontr)
    assume "\<not> \<not> ?m' < ?m"
    hence "?m' < ?m" by simp
    hence "?j < ?j" using no_steal_preserves_left_order assms(1) r'_pref r_pref Run_pref idx m'_pref m_pref rn'_pref rn_pref no_steal_r' r'Suc_pref rSuc_pref j_pref j_pref by blast
    thus False by simp
  qed
  thus ?thesis using not_less by auto
qed

lemma same_comp_at_n_implies_same_comp_before:
  assumes "auto_well_defined \<A>" "omega_greedy_run r \<A> x" "omega_greedy_run r' \<A> x" "omega_run_well_defined Run (upper_part_pure \<A>) x" "comp_idx Run r n = comp_idx Run r' n" "k \<le> n"
  shows "comp_idx Run r k = comp_idx Run r' k"
using assms proof (induction "n - k" arbitrary: n)
  case 0 thus ?case by simp
next
  case (Suc d)
  hence gt: "k < n" by simp
  then obtain n' where n': "n = Suc n'" by (cases n) auto
  hence eq_prev: "comp_idx Run r n' = comp_idx Run r' n'" using same_comp_step_back[OF assms(1-4)] Suc by blast
  have le_prev: "k \<le> n'" using gt n' by simp
  have  "n' - k = d" using Suc n' by simp
  thus ?case using Suc eq_prev le_prev by blast
qed

lemma not_same_comp_never_again:
  assumes "auto_well_defined \<A>" "omega_greedy_run r \<A> x" "omega_greedy_run r' \<A> x" "omega_run_well_defined Run (upper_part_pure \<A>) x" "comp_idx Run r n \<noteq> comp_idx Run r' n" "n \<le> N"
  shows "comp_idx Run r N \<noteq> comp_idx Run r' N"
proof(rule ccontr)
  assume "\<not> comp_idx Run r N \<noteq> comp_idx Run r' N"
  hence "comp_idx Run r N = comp_idx Run r' N" by simp
  hence "comp_idx Run r n = comp_idx Run r' n" using same_comp_at_n_implies_same_comp_before assms by blast
  thus False using assms by blast
qed

definition samelevel_local :: "'s omega_run \<Rightarrow> 's omega_run \<Rightarrow> ('s states list) omega_run \<Rightarrow> nat \<Rightarrow> bool" where "samelevel_local r r' Run n = (\<exists> j < length (Run n) . r n \<in> (Run n) ! j \<and> r' n \<in> (Run n) ! j)"

proposition samelevel_global_iff: "samelevel_global r r' Run \<longleftrightarrow> (\<forall> n . samelevel_local r r' Run n)"
  unfolding samelevel_global_def samelevel_local_def by simp

lemma samelevel_at_iff_comp_idx_eq:
  assumes "auto_well_defined \<A>" "omega_greedy_run r \<A> x" "omega_greedy_run r' \<A> x" "omega_run_well_defined Run (upper_part_pure \<A>) x"
  shows "samelevel_local r r' Run n \<longleftrightarrow> comp_idx Run r n = comp_idx Run r' n"
proof -
  {
    assume "samelevel_local r r' Run n"
    then obtain j where j: "j < length (Run n)" "r n \<in> (Run n) ! j" "r' n \<in> (Run n) ! j" unfolding samelevel_local_def by blast
    hence cj: "comp_idx Run r n = j" using comp_idx_correct[OF assms(1,2,4), of n] omega_greedy_run_component_unique[OF assms(1,2,4), of j n] by blast
    have "comp_idx Run r' n = j" using comp_idx_correct[OF assms(1,3,4), of n] omega_greedy_run_component_unique[OF assms(1,3,4), of j n] j by blast
    hence "comp_idx Run r n = comp_idx Run r' n" using cj by simp
  }
  hence left: "samelevel_local r r' Run n \<Longrightarrow> comp_idx Run r n = comp_idx Run r' n" by blast
  {
    assume eq: "comp_idx Run r n = comp_idx Run r' n"
    have cr: "comp_idx Run r n < length (Run n) \<and> r n \<in> (Run n) ! comp_idx Run r n" using comp_idx_correct[OF assms(1,2,4), of n] by simp
    have "comp_idx Run r' n < length (Run n) \<and> r' n \<in> (Run n) ! comp_idx Run r' n" using comp_idx_correct[OF assms(1,3,4), of n] by blast
    hence "samelevel_local r r' Run n" using cr eq unfolding samelevel_local_def by auto
  }
  thus ?thesis using left by blast
qed

lemma samelevel_global_iff_comp_idx:
  assumes "auto_well_defined \<A>" "omega_greedy_run r \<A> x" "omega_greedy_run r' \<A> x" "omega_run_well_defined Run (upper_part_pure \<A>) x"
  shows "samelevel_global r r' Run \<longleftrightarrow> (\<forall> n . comp_idx Run r n = comp_idx Run r' n)"
proof -
  {
    assume "samelevel_global r r' Run"
    hence "\<forall> n . comp_idx Run r n = comp_idx Run r' n" using samelevel_at_iff_comp_idx_eq[OF assms] unfolding samelevel_global_def samelevel_local_def by blast
  }
  hence left: "samelevel_global r r' Run \<Longrightarrow> (\<forall> n . comp_idx Run r n = comp_idx Run r' n)" by blast
  {
    assume "\<forall> n . comp_idx Run r n = comp_idx Run r' n"
    hence "samelevel_global r r' Run" using samelevel_at_iff_comp_idx_eq[OF assms] unfolding samelevel_global_def samelevel_local_def by blast
  }
  thus ?thesis using left by blast
qed

lemma not_samelevel_global_iff:
  assumes "auto_well_defined \<A>" "omega_greedy_run r \<A> x" "omega_greedy_run r' \<A> x" "omega_run_well_defined Run (upper_part_pure \<A>) x"
  shows "\<not> samelevel_global r r' Run \<longleftrightarrow> (\<exists> n . comp_idx Run r n \<noteq> comp_idx Run r' n)"
  using samelevel_global_iff_comp_idx[OF assms] by blast

lemma pairwise_not_samelevel_global_separated_forever:
  assumes "auto_well_defined \<A>" "omega_greedy_run r \<A> x" "omega_greedy_run r' \<A> x" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<not> samelevel_global r r' Run"
  shows "\<exists> n . \<forall> N \<ge> n . comp_idx Run r N \<noteq> comp_idx Run r' N"
proof -
  obtain n where neq: "comp_idx Run r n \<noteq> comp_idx Run r' n" using not_samelevel_global_iff assms by blast
  have "\<forall> N \<ge> n . comp_idx Run r N \<noteq> comp_idx Run r' N" using not_same_comp_never_again[OF assms(1-4) neq] by blast
  thus ?thesis by blast
qed

lemma at_most_card_states_many_pairwise_distinct_samelevel_global:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []" "finite Rs" "Rs \<subseteq> {r . omega_greedy_run r \<A> x}" "pairwise (\<lambda> r r' . \<not> samelevel_global r r' Run) Rs"
  shows "card Rs \<le> card (states \<A>)"
proof (cases "Rs = {}")
  case True thus ?thesis by simp
next
  case False
  let ?Pairs = "{(r, r') . r \<in> Rs \<and> r' \<in> Rs \<and> r \<noteq> r'}"
  have "?Pairs \<subseteq> Rs \<times> Rs" by auto
  hence finite_Pairs: "finite ?Pairs" using assms finite_SigmaI finite_subset by fast
  {
    fix p assume "p \<in> ?Pairs"
    then obtain r r' where p: "p = (r, r')" "r \<in> Rs" "r' \<in> Rs" "r \<noteq> r'" by blast
    hence gr: "omega_greedy_run r \<A> x" using assms by blast
    have gr': "omega_greedy_run r' \<A> x" using assms p by blast
    have ns: "\<not> samelevel_global r r' Run" using assms p by (auto dest: pairwiseD)
    have "\<exists> n . \<forall> N \<ge> n . comp_idx Run (fst p) N \<noteq> comp_idx Run (snd p) N" using pairwise_not_samelevel_global_separated_forever[OF assms(1) gr gr' assms(2) ns] unfolding p by simp
  }
  hence sep_ex: "\<forall> p \<in> ?Pairs . \<exists> n . \<forall> N \<ge> n . comp_idx Run (fst p) N \<noteq> comp_idx Run (snd p) N" by blast
  obtain sep where sep: "\<forall> p \<in> ?Pairs . \<forall> N \<ge> sep p . comp_idx Run (fst p) N \<noteq> comp_idx Run (snd p) N" using bchoice[OF sep_ex] by blast
  define N where "N = Max (insert 0 (sep ` ?Pairs))"
  hence N_ge_sep: "\<forall> p \<in> ?Pairs . sep p \<le> N" using finite_Pairs by fastforce
  have inj: "inj_on (\<lambda>r . comp_idx Run r N) Rs"
  proof (rule inj_onI)
    fix r r'
    assume r: "r \<in> Rs" and r': "r' \<in> Rs" and eq: "comp_idx Run r N = comp_idx Run r' N"
    show "r = r'"
    proof (rule ccontr)
      assume "r \<noteq> r'"
      hence pair: "(r, r') \<in> ?Pairs" using r r' by blast
      hence "sep (r, r') \<le> N" using N_ge_sep by blast
      hence "comp_idx Run r N \<noteq> comp_idx Run r' N" using sep pair by auto
      thus False using eq by blast
    qed
  qed
  {
    fix y assume "y \<in> (\<lambda>r . comp_idx Run r N) ` Rs"
    then obtain r where r: "r \<in> Rs" "y = comp_idx Run r N" by blast
    hence "omega_greedy_run r \<A> x" using assms by blast
    hence "comp_idx Run r N < length (Run N)" using comp_idx_correct[OF assms(1) _ assms(2), of r N] by simp
    hence "y \<in> {..< length (Run N)}" using r by simp
  }
  hence img_subset: "(\<lambda>r . comp_idx Run r N) ` Rs \<subseteq> {..< length (Run N)}" by blast
  have card_eq: "card Rs = card ((\<lambda>r . comp_idx Run r N) ` Rs)" using assms(4) inj by (simp add: card_image)
  have card_le: "card ((\<lambda>r . comp_idx Run r N) ` Rs) \<le> card {..< length (Run N)}" using img_subset assms card_mono by blast
  have "card {..< length (Run N)} = length (Run N)" by simp
  hence card_le_len: "card Rs \<le> length (Run N)" using card_eq card_le by presburger
  have "auto_well_defined (upper_part_pure \<A>)" using assms(1) well_def_upper_part_pure by blast
  hence "Run N \<in> states (upper_part_pure \<A>)" using assms well_def_implies_omega_prun_states unfolding omega_run_well_defined_def omega_prun_states_def by fast
  hence "Run N \<in> upper_states \<A>" using assms unfolding upper_part_pure_def by auto
  hence "length (Run N) \<le> card (states \<A>)" unfolding upper_states_def by blast
  thus ?thesis using card_le_len by linarith
qed

lemma infinite_many_TF_indices_yield_one_samelevel_global_class:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []" "infinite I" "\<forall> i \<in> I . omega_greedy_run (f i) \<A> x"
  shows "\<exists> r . omega_greedy_run r \<A> x \<and> infinite {i \<in> I . samelevel_global (f i) r Run}"
proof -
  let ?R = "{f i | i . i \<in> I}"
  have R_sub: "?R \<subseteq> {r . omega_greedy_run r \<A> x}" using assms by blast
  have "finite ?R \<or> infinite ?R" by blast
  then consider (finite) "finite ?R" |(infinite) "infinite ?R" by blast
  thus ?thesis
  proof cases
    case finite
    have I_decomp:"I = (\<Union> r \<in> ?R . {i \<in> I . f i = r})" by blast
    have "\<exists> r \<in> ?R . infinite {i \<in> I . f i = r}"
    proof (rule ccontr)
      assume "\<not> (\<exists> r \<in> ?R . infinite {i \<in> I . f i = r})"
      hence fin_fib: "\<forall> r \<in> ?R . finite {i \<in> I . f i = r}" by blast
      hence "finite (\<Union> r \<in> ?R . {i \<in> I . f i = r})"  using finite by blast
      hence "finite I" using I_decomp by simp
      thus False using assms(4) by blast
    qed
    then obtain r where r: "r \<in> ?R" "infinite {i \<in> I . f i = r}" by blast
    hence greedy: "omega_greedy_run r \<A> x" using R_sub by blast
    {
      fix i assume "i \<in> {i \<in> I . f i = r}"
      hence iI: "i \<in> I" and eq: "f i = r" by auto
      have wd_r: "omega_run_well_defined r \<A> x" using greedy unfolding omega_greedy_run_def by blast
      have "samelevel_global r r Run" using samelevel_global_reflexiv[OF assms(1) wd_r assms(2)] by blast
      hence "i \<in> {i \<in> I . samelevel_global (f i) r Run}" using iI eq by auto
    }
    hence "{i \<in> I . f i = r} \<subseteq> {i \<in> I . samelevel_global (f i) r Run}" by blast
    hence "infinite {i \<in> I. samelevel_global (f i) r Run}" using r infinite_super by blast
    thus ?thesis using greedy by blast
  next
    case infinite
    let ?Fam = "{Rs . finite Rs \<and> Rs \<subseteq> ?R \<and> pairwise (\<lambda>r r' . \<not> samelevel_global r r' Run) Rs}"
    let ?Cards = "image card ?Fam"
    have "{} \<in> ?Fam" by simp
    hence cards_nonempty: "?Cards \<noteq> {}" by blast
    {
      fix c assume "c \<in> ?Cards"
      then obtain Rs where Rs: "Rs \<in> ?Fam" "c = card Rs" by blast
      hence fin: "finite Rs" "Rs \<subseteq> ?R" "pairwise (\<lambda>r r' . \<not> samelevel_global r r' Run) Rs" by auto
      hence "Rs \<subseteq> {r . omega_greedy_run r \<A> x}" using R_sub by blast
      hence "card Rs \<le> card (states \<A>)" using fin at_most_card_states_many_pairwise_distinct_samelevel_global[OF assms(1,2,3)] by blast
      hence "c \<le> card (states \<A>)" using Rs by simp
    }
    hence cards_bdd: "\<forall>c \<in> ?Cards . c \<le> card (states \<A>)" by blast
    then obtain m where m: "m = Max ?Cards" by blast
    have "?Cards \<subseteq> {.. card (states \<A>)}" using cards_bdd by auto
    hence fin_cards: "finite ?Cards" by (rule finite_subset) simp
    hence "m \<in> ?Cards" using m cards_nonempty by simp
    then obtain Rs where Rs: "Rs \<in> ?Fam" "m = card Rs" by blast
    have Rs_fin: "finite Rs" and Rs_sub: "Rs \<subseteq> ?R" and Rs_pair: "pairwise (\<lambda>r r' . \<not> samelevel_global r r' Run) Rs" using Rs by auto
    have Rs_cover: "\<And>r . r \<in> ?R \<Longrightarrow> \<exists> r' \<in> Rs . samelevel_global r r' Run"
    proof -
      fix r assume rR: "r \<in> ?R"
      show "\<exists> r' \<in> Rs . samelevel_global r r' Run"
      proof (rule ccontr)
        assume neg: "\<not> (\<exists> r' \<in> Rs . samelevel_global r r' Run)"
        have r_notin: "r \<notin> Rs"
        proof
          assume assm: "r \<in> Rs"
          have "omega_greedy_run r \<A> x" using rR R_sub by blast
          hence wd_r: "omega_run_well_defined r \<A> x" unfolding omega_greedy_run_def by blast
          have "samelevel_global r r Run" using samelevel_global_reflexiv[OF assms(1) wd_r assms(2)] .
          hence "\<exists> r' \<in> Rs. samelevel_global r r' Run" using assm by blast
          thus False using neg by blast
        qed
        have "pairwise (\<lambda>r r' . \<not> samelevel_global r r' Run) (insert r Rs)"
        proof -
          have left: "\<forall> x \<in> Rs . \<not> samelevel_global r x Run" using neg by blast
          hence right: "\<forall> x \<in> Rs . \<not> samelevel_global x r Run" using samelevel_symmetry by blast
          have "pairwise (\<lambda>r r' . \<not> samelevel_global r r' Run) Rs" using Rs_pair .
          thus ?thesis using left right unfolding pairwise_def by fast
        qed
        hence "insert r Rs \<in> ?Fam" using Rs_fin Rs_sub rR by auto
        hence "card (insert r Rs) \<in> ?Cards" by blast
        hence less_Max: "card (insert r Rs) \<le> Max ?Cards" using fin_cards cards_nonempty by fastforce
        have "card Rs < card (insert r Rs)" using Rs_fin r_notin by simp
        hence "card Rs < Max ?Cards" using less_Max by linarith
        thus False using Rs m by simp
      qed
    qed
    have "\<exists> r \<in> Rs . infinite {i \<in> I . samelevel_global (f i) r Run}"
    proof (rule ccontr)
      assume neg: "\<not> (\<exists> r \<in> Rs . infinite {i \<in> I . samelevel_global (f i) r Run})"
      {
        fix i assume assm: "i \<in> I"
        hence "f i \<in> ?R" by blast
        then obtain r' where "r' \<in> Rs" "samelevel_global (f i) r' Run" using Rs_cover by blast
        hence "i \<in> (\<Union> r \<in> Rs . {i \<in> I . samelevel_global (f i) r Run})" using assm by blast
      }
      hence cover: "I \<subseteq> (\<Union> r \<in> Rs . {i \<in> I . samelevel_global (f i) r Run})" by fast
      have "\<forall> r \<in> Rs. finite {i \<in> I . samelevel_global (f i) r Run}" using neg by blast
      hence "finite (\<Union> r \<in> Rs . {i \<in> I . samelevel_global (f i) r Run})"  using Rs_fin by blast
      hence "finite I" using cover finite_subset by blast
      thus False using assms(4) by blast
    qed
    then obtain r where r: "r \<in> Rs" "infinite {i \<in> I . samelevel_global (f i) r Run}" by blast
    hence "r \<in> ?R" using Rs_sub by blast
    hence gr: "omega_greedy_run r \<A> x" using R_sub by blast
    thus ?thesis using r by blast
  qed
qed

lemma samelevel_class_representative_accepting_infinitely_often:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []" "infinite I" "\<forall> i \<in> I . omega_greedy_run (f i) \<A> x" "\<forall> i \<in> I . (f i) i \<in> accepting_states \<A>" "omega_greedy_run r \<A> x" "infinite {i \<in> I . samelevel_global (f i) r Run}"
  shows "infinite {i . r i \<in> accepting_states \<A>}"
proof -
  {
    fix i assume "i \<in> {i \<in> I . samelevel_global (f i) r Run}"
    hence iI: "i \<in> I" and sl: "samelevel_global (f i) r Run" by auto
    hence fi_acc: "(f i) i \<in> accepting_states \<A>" using assms by blast
    have same_acc: "\<forall> n . (f i) n \<in> accepting_states \<A> \<longleftrightarrow> r n \<in> accepting_states \<A>" using samelevel_global_preserves_acceptance_at_index assms sl iI by blast
    hence "i \<in> {i . r i \<in> accepting_states \<A>}" using fi_acc by auto
  }
  hence "{i \<in> I . samelevel_global (f i) r Run} \<subseteq> {i . r i \<in> accepting_states \<A>}" by blast
  thus ?thesis using assms(8) infinite_super by blast
qed

lemma omega_greedy_run_with_infinitely_many_accepting_positions_is_accepting:
  assumes "omega_greedy_run r \<A> x" "infinite {i . r i \<in> accepting_states \<A>}" "auto_well_defined \<A>"
  shows "omega_run_accepting r \<A> x"
proof -
  have wd: "omega_run_well_defined r \<A> x" using assms unfolding omega_greedy_run_def by blast
  {
    fix n
    have "\<exists> N > n . r N \<in> accepting_states \<A>"
    proof (rule ccontr)
      assume h: "\<not> (\<exists> N > n . r N \<in> accepting_states \<A>)"
      {
        fix N assume "N \<in> {i . r i \<in> accepting_states \<A>}"
        hence acc: "r N \<in> accepting_states \<A>" by simp
        have "N \<le> n"
        proof (rule ccontr)
          assume "\<not> N \<le> n" thus False using h acc by auto
        qed
      }
      hence "\<forall> N \<in> {i . r i \<in> accepting_states \<A>} . N \<le> n" by blast
      hence "finite {i . r i \<in> accepting_states \<A>}" using finite_nat_set_iff_bounded_le by blast
      thus False using assms(2) by blast
    qed
  }
  hence "\<forall> n . \<exists> N > n . r N \<in> accepting_states \<A>" by simp
  thus ?thesis using wd unfolding omega_run_accepting_def by blast
qed

theorem lemma_3_4_13:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []" "infinite {i . upper_slice_continued_F Run \<A> x i}"
  shows "x \<in> omega_language_auto \<A>"
proof -
  obtain f g where fg: "\<forall> i \<in> {i . upper_slice_continued_F Run \<A> x i} . g i < length (Run i) \<and> upper_continued_F Run \<A> x i (g i) \<and> omega_greedy_run (f i) \<A> x \<and> (f i) i \<in> (Run i) ! (g i)" using choose_greedy_runs_through_TF_slices[OF assms] by blast
  hence fg_greedy: "\<forall> i \<in> {i . upper_slice_continued_F Run \<A> x i} . omega_greedy_run (f i) \<A> x" by blast
  have fg_acc: "\<forall> i \<in> {i . upper_slice_continued_F Run \<A> x i} . (f i) i \<in> accepting_states \<A>" using chosen_greedy_runs_accepting_at_index[OF fg] .
  obtain r where r: "omega_greedy_run r \<A> x" "infinite {i \<in> {i . upper_slice_continued_F Run \<A> x i} . samelevel_global (f i) r Run}" using infinite_many_TF_indices_yield_one_samelevel_global_class[OF assms(1,2,3,4) fg_greedy] by blast
  have inf_acc: "infinite {i . r i \<in> accepting_states \<A>}" using samelevel_class_representative_accepting_infinitely_often[OF assms(1,2,3,4) fg_greedy fg_acc r] by blast
  have "omega_run_accepting r \<A> x" using omega_greedy_run_with_infinitely_many_accepting_positions_is_accepting[OF r(1) inf_acc assms(1)] by blast
  thus ?thesis unfolding omega_language_auto_def by blast
qed

corollary cor_3_4_15_pure:
  assumes "auto_well_defined \<A>"
  shows "x \<in> omega_language_auto \<A> \<longleftrightarrow> (\<exists> Run . omega_run_well_defined Run (upper_part_pure \<A>) x \<and> (\<forall> n . Run n \<noteq> []) \<and> infinite {i . upper_slice_continued_F Run \<A> x i})"
proof -
  {
    assume acc: "x \<in> omega_language_auto \<A>"
    then obtain r where r: "omega_run_accepting r \<A> x" unfolding omega_language_auto_def by blast
    then obtain Run where Run: "omega_run_well_defined Run (upper_part_pure \<A>) x" "infinite {i . upper_slice_continued_F Run \<A> x i}" using lemma_3_4_14[OF assms acc] by blast
    have "\<forall> n . Run n \<noteq> []" using not_empty_omega_run[OF assms] r Run(1) unfolding omega_run_accepting_def by blast
    hence "\<exists> Run . omega_run_well_defined Run (upper_part_pure \<A>) x \<and> (\<forall> n . Run n \<noteq> []) \<and> infinite {i . upper_slice_continued_F Run \<A> x i}" using Run by blast
  }
  hence left: "x \<in> omega_language_auto \<A> \<Longrightarrow> \<exists> Run . omega_run_well_defined Run (upper_part_pure \<A>) x \<and> (\<forall> n . Run n \<noteq> []) \<and> infinite {i . upper_slice_continued_F Run \<A> x i}" by blast
  {
    assume "\<exists> Run . omega_run_well_defined Run (upper_part_pure \<A>) x \<and> (\<forall> n . Run n \<noteq> []) \<and> infinite {i . upper_slice_continued_F Run \<A> x i}"
    then obtain Run where "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []" "infinite {i . upper_slice_continued_F Run \<A> x i}" by blast
    hence "x \<in> omega_language_auto \<A>" using lemma_3_4_13[OF assms] by blast
  }
  thus ?thesis using left by blast
qed

definition upper_part :: "('s, 'a) automaton \<Rightarrow> (('s states \<times> nat) list, 'a) automaton" where "upper_part \<A> = (type_encode_automaton (upper_part_pure \<A>) (map (cross_renaming_iso 3)) id)"

corollary alphabet_upper_part: "alphabet (upper_part \<A>) = alphabet \<A>" unfolding upper_part_def type_encode_preserves_alphabet upper_part_pure_def by simp

proposition bij_map_cross_renaming_iso: "bij_betw (map (cross_renaming_iso n)) (states \<A>) (image (map (cross_renaming_iso n)) (states \<A>))"
  using list.inj_map_strong unfolding bij_betw_def cross_renaming_iso_def inj_on_def by (metis (mono_tags, lifting) prod.inject)

proposition map_cross_renaming_iso_automaton_auto_well_defined:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (type_encode_automaton \<A> (map (cross_renaming_iso n)) id)"
  using assms id_bij_betw type_encode_preserves_well_def bij_map_cross_renaming_iso by blast

proposition map_cross_renaming_iso_automaton_auto_DFA:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "DFA_property (type_encode_automaton \<A> (map (cross_renaming_iso n)) id)"
  using assms id_bij_betw type_encode_preserves_dfa bij_map_cross_renaming_iso by blast

theorem well_def_upper_part:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (upper_part \<A>)"
  using assms well_def_upper_part_pure map_cross_renaming_iso_automaton_auto_well_defined unfolding upper_part_def by blast

theorem DFA_upper_part:
  assumes "auto_well_defined \<A>"
  shows "DFA_property (upper_part \<A>)"
  using assms well_def_upper_part_pure DFA_property_upper_part_pure map_cross_renaming_iso_automaton_auto_DFA unfolding upper_part_def by blast

corollary upper_part_pure_and_upper_part_same_omega_language:
  assumes "auto_well_defined \<A>"
  shows "omega_language_auto (upper_part_pure \<A>) = omega_language_auto (upper_part \<A>)"
proof -
  have "omega_language_auto (upper_part \<A>) = image (omega_map id) (omega_language_auto (upper_part_pure \<A>))" using assms well_def_upper_part_pure type_encode_preserves_omega_language bij_map_cross_renaming_iso[of 3 "upper_part_pure \<A>"] id_bij_betw unfolding upper_part_def by blast
  thus ?thesis unfolding omega_map_def by auto
qed

lemma upper_part_iso_data:
  assumes "auto_well_defined \<A>"
  shows "bij_betw (map (cross_renaming_iso 3)) (states (upper_part_pure \<A>)) (states (upper_part \<A>)) \<and> bij_betw id (alphabet (upper_part_pure \<A>)) (alphabet (upper_part \<A>)) \<and> map (cross_renaming_iso 3) (initial_state (upper_part_pure \<A>)) = initial_state (upper_part \<A>) \<and> image (map (cross_renaming_iso 3)) (accepting_states (upper_part_pure \<A>)) = accepting_states (upper_part \<A>) \<and> image (\<lambda> (s1,a,s2) . (map (cross_renaming_iso 3) s1, id a, map (cross_renaming_iso 3) s2)) (transitions (upper_part_pure \<A>)) = transitions (upper_part \<A>)"
  unfolding upper_part_def type_encode_automaton_def using bij_map_cross_renaming_iso[of 3 "upper_part_pure \<A>"] by auto

definition enc_upper_run where "enc_upper_run Run = (map (cross_renaming_iso 3)) \<circ> Run"

definition dec_upper_run where "dec_upper_run \<A> Run = (inv_into (states (upper_part_pure \<A>)) (map (cross_renaming_iso 3))) \<circ> Run"

lemma dec_enc_upper_run:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x"
  shows "dec_upper_run \<A> (enc_upper_run Run) = Run"
proof -
  {
    fix n
    have st: "Run n \<in> states (upper_part_pure \<A>)" using assms well_def_implies_omega_prun_states well_def_upper_part_pure unfolding omega_run_well_defined_def omega_prun_states_def by fast
    have "bij_betw (map (cross_renaming_iso 3)) (states (upper_part_pure \<A>)) (states (upper_part \<A>))" using upper_part_iso_data[OF assms(1)] by blast
    hence "dec_upper_run \<A> (enc_upper_run Run) n = Run n" unfolding dec_upper_run_def enc_upper_run_def using st by (simp add: bij_betw_inv_into_left)
  }
  thus ?thesis by blast
qed

lemma enc_dec_upper_run:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part \<A>) x"
  shows "enc_upper_run (dec_upper_run \<A> Run) = Run"
proof -
  {
    fix n
    have st: "Run n \<in> states (upper_part \<A>)" using assms well_def_implies_omega_prun_states well_def_upper_part unfolding omega_run_well_defined_def omega_prun_states_def by fast
    have "bij_betw (map (cross_renaming_iso 3)) (states (upper_part_pure \<A>)) (states (upper_part \<A>))" using upper_part_iso_data[OF assms(1)] by blast
    hence "enc_upper_run (dec_upper_run \<A> Run) n = Run n" unfolding dec_upper_run_def enc_upper_run_def using st by (simp add: bij_betw_inv_into_right)
  }
  thus ?thesis by blast
qed

lemma omega_run_well_defined_upper_part_transport:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part_pure \<A>) x"
  shows "omega_run_well_defined (enc_upper_run Run) (upper_part \<A>) x"
proof -
  have "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
  hence "omega_pseudo_run_well_defined Run (upper_part_pure \<A>) (initial_state (upper_part_pure \<A>)) x \<Longrightarrow> omega_pseudo_run_well_defined ((map (cross_renaming_iso 3)) \<circ> Run) (upper_part \<A>) (map (cross_renaming_iso 3) (initial_state (upper_part_pure \<A>))) x" using omega_soft_iso_prun_correct upper_part_iso_data assms by blast
  thus ?thesis using upper_part_iso_data assms unfolding omega_run_well_defined_def enc_upper_run_def by metis
qed

lemma omega_run_well_defined_upper_part_transport_back:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part \<A>) x"
  shows "omega_run_well_defined (dec_upper_run \<A> Run) (upper_part_pure \<A>) x"
proof -
  have init_back: "inv_into (states (upper_part_pure \<A>)) (map (cross_renaming_iso 3)) (initial_state (upper_part \<A>)) = initial_state (upper_part_pure \<A>)"
  proof -
    have bij: "bij_betw (map (cross_renaming_iso 3)) (states (upper_part_pure \<A>)) (states (upper_part \<A>))" using upper_part_iso_data assms by blast
    have init: "initial_state (upper_part_pure \<A>) \<in> states (upper_part_pure \<A>)" using assms(1) well_def_upper_part_pure unfolding auto_well_defined_def by blast
    have "map (cross_renaming_iso 3) (initial_state (upper_part_pure \<A>)) = initial_state (upper_part \<A>)" using upper_part_iso_data assms by blast
    thus ?thesis using bij init bij_betw_inv_into_left by metis
  qed
  have "auto_well_defined (upper_part_pure \<A>)" using assms well_def_upper_part_pure by blast
  hence "omega_pseudo_run_well_defined Run (upper_part \<A>) (initial_state (upper_part \<A>)) x \<Longrightarrow> omega_pseudo_run_well_defined ((inv_into (states (upper_part_pure \<A>)) (map (cross_renaming_iso 3))) \<circ> Run) (upper_part_pure \<A>) (inv_into (states (upper_part_pure \<A>)) (map (cross_renaming_iso 3)) (initial_state (upper_part \<A>))) x" using omega_soft_iso_prun_correct upper_part_iso_data assms by blast
  thus ?thesis using upper_part_iso_data assms init_back unfolding omega_run_well_defined_def dec_upper_run_def by argo
qed

lemma upper_part_transport_nonempty_all: "(\<forall> n . Run n \<noteq> []) \<longleftrightarrow> (\<forall> n . (enc_upper_run Run) n \<noteq> [])" unfolding enc_upper_run_def by auto

lemma upper_part_transport_nonempty_back:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part \<A>) x"
  shows "Run n \<noteq> [] \<longleftrightarrow> ((dec_upper_run \<A> Run) n) \<noteq> []"
proof -
  have "enc_upper_run (dec_upper_run \<A> Run) = Run" using enc_dec_upper_run[OF assms] .
  hence "map (cross_renaming_iso 3) ((dec_upper_run \<A> Run) n) = Run n" using Fun.comp_eq_dest_lhs unfolding enc_upper_run_def by fast
  thus ?thesis by auto
qed

lemma upper_part_transport_nonempty_all_back:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part \<A>) x"
  shows "(\<forall> n . Run n \<noteq> []) \<longleftrightarrow> (\<forall> n . (dec_upper_run \<A> Run) n \<noteq> [])"
  using upper_part_transport_nonempty_back[OF assms] by blast

definition upper_child_up :: "(('s states \<times> nat) list) state \<Rightarrow> 'a symbol \<Rightarrow> ('s,'a) automaton \<Rightarrow> (('s states \<times> nat) list) state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "upper_child_up p a \<A> q j k = (j < length p \<and> k < length q \<and> fst (q ! k) \<subseteq> post_set \<A> (fst (p ! j)) a \<and> fst (q ! k) \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst p))) = {})"

definition upper_child_segment_up :: "(('s states \<times> nat) list) omega_run \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a omega_word \<Rightarrow> ('s,'a) automaton \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "upper_child_segment_up Run i N x \<A> j k = (\<exists> js . length js = N - i + 1 \<and> js ! 0 = j \<and> last js = k \<and> (\<forall> m < N - i . upper_child_up (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m)))"

definition upper_continued_up :: "(('s states \<times> nat) list) omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "upper_continued_up Run \<A> x i j = (\<forall> N > i . \<exists> k . upper_child_segment_up Run i N x \<A> j k)"

definition upper_continued_F_up :: "(('s states \<times> nat) list) omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "upper_continued_F_up omega_run \<A> omega_word i j = (upper_continued_up omega_run \<A> omega_word i j \<and> fst (omega_run i ! j) \<subseteq> accepting_states \<A>)"

definition upper_slice_continued_F_up :: "(('s states \<times> nat) list) omega_run \<Rightarrow> ('s, 'a) automaton \<Rightarrow> 'a omega_word \<Rightarrow> nat \<Rightarrow> bool" where "upper_slice_continued_F_up omega_run \<A> omega_word i = (\<exists> j < length (omega_run i) . upper_continued_F_up omega_run \<A> omega_word i j)"

lemma map_fst_cross_renaming_iso: "map fst (map (cross_renaming_iso n) xs) = xs"
  unfolding cross_renaming_iso_def by(induction xs) auto

lemma map_fst_length: "j < length xs \<longleftrightarrow> j < length (map (cross_renaming_iso 3) xs)"
  unfolding cross_renaming_iso_def by(induction xs) auto

lemma map_k_th_q: "k < length q \<Longrightarrow> q ! k = fst ((map (cross_renaming_iso 3) q) ! k)"
  using map_fst_cross_renaming_iso map_fst_length nth_map by metis

lemma map_k_th_crossq: "k < length (map (cross_renaming_iso 3) q) \<Longrightarrow> q ! k = fst ((map (cross_renaming_iso 3) q) ! k)"
  using map_fst_cross_renaming_iso nth_map by metis

lemma upper_child_up_enc:
  assumes "upper_child p a \<A> q j k"
  shows "upper_child_up (map (cross_renaming_iso 3) p) a \<A> (map (cross_renaming_iso 3) q) j k"
proof -
  have "j < length p \<and> k < length q \<and> q ! k \<subseteq> post_set \<A> (p ! j) a \<and> q ! k \<inter> snd (upper_step \<A> a (drop (Suc j) p)) = {}" using assms unfolding upper_child_def by blast
  hence "j < length (map (cross_renaming_iso 3) p) \<and> k < length (map (cross_renaming_iso 3) q) \<and> fst ((map (cross_renaming_iso 3) q) ! k) \<subseteq> post_set \<A> (fst ((map (cross_renaming_iso 3) p) ! j)) a \<and> fst ((map (cross_renaming_iso 3) q) ! k) \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst (map (cross_renaming_iso 3) p)))) = {}" using map_fst_cross_renaming_iso map_fst_length map_k_th_q by metis
  thus ?thesis unfolding upper_child_up_def by blast
qed

lemma upper_child_up_dec:
  assumes "upper_child_up (map (cross_renaming_iso 3) p) a \<A> (map (cross_renaming_iso 3) q) j k"
  shows "upper_child p a \<A> q j k"
proof -
  have "j < length (map (cross_renaming_iso 3) p) \<and> k < length (map (cross_renaming_iso 3) q) \<and> fst ((map (cross_renaming_iso 3) q) ! k) \<subseteq> post_set \<A> (fst ((map (cross_renaming_iso 3) p) ! j)) a \<and> fst ((map (cross_renaming_iso 3) q) ! k) \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst (map (cross_renaming_iso 3) p)))) = {}" using assms unfolding upper_child_up_def by blast
  hence "j < length p \<and> k < length q \<and> q ! k \<subseteq> post_set \<A> (p ! j) a \<and> q ! k \<inter> snd (upper_step \<A> a (drop (Suc j) p)) = {}" using map_fst_cross_renaming_iso map_fst_length map_k_th_crossq by metis
  thus ?thesis unfolding upper_child_def by blast
qed

lemma upper_child_segment_up_enc:
  assumes "upper_child_segment Run i N x \<A> j k"
  shows "upper_child_segment_up (enc_upper_run Run) i N x \<A> j k"
proof -
  obtain js where js: "length js = N - i + 1" "js ! 0 = j" "last js = k" "\<forall> m < N - i . upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m)" using assms unfolding upper_child_segment_def by blast
  hence "\<forall> m < N - i . upper_child_up ((enc_upper_run Run) (i + m)) (x (i + m)) \<A> ((enc_upper_run Run) (i + Suc m)) (js ! m) (js ! Suc m)" using upper_child_up_enc unfolding enc_upper_run_def by fastforce
  thus ?thesis using js unfolding upper_child_segment_up_def by blast
qed

lemma upper_child_segment_up_dec:
  assumes "upper_child_segment_up (enc_upper_run Run) i N x \<A> j k"
  shows "upper_child_segment Run i N x \<A> j k"
proof -
  obtain js where js: "length js = N - i + 1" "js ! 0 = j" "last js = k" "\<forall> m < N - i . upper_child_up ((enc_upper_run Run) (i + m)) (x (i + m)) \<A> ((enc_upper_run Run) (i + Suc m)) (js ! m) (js ! Suc m)" using assms unfolding upper_child_segment_up_def by blast
  hence "\<forall> m < N - i . upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m)" using upper_child_up_dec unfolding enc_upper_run_def by fastforce
  thus ?thesis using js unfolding upper_child_segment_def by blast
qed

lemma upper_child_segment_up_enc_iff: "upper_child_segment_up (enc_upper_run Run) i N x \<A> j k \<longleftrightarrow> upper_child_segment Run i N x \<A> j k"
  using upper_child_segment_up_enc upper_child_segment_up_dec by blast

lemma upper_continued_up_enc_iff: "upper_continued_up (enc_upper_run Run) \<A> x i j \<longleftrightarrow> upper_continued Run \<A> x i j"
  using upper_child_segment_up_enc_iff unfolding upper_continued_up_def upper_continued_def by blast

lemma upper_continued_index:
  assumes "upper_continued Run \<A> x i j"
  shows "j < length (Run i)"
proof -
  obtain k where "upper_child_segment Run i (Suc i) x \<A> j k" using assms unfolding upper_continued_def by blast
  then obtain js where "length js = Suc i - i + 1" "js ! 0 = j" "last js = k" "\<forall> m < Suc i - i . upper_child (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m)" unfolding upper_child_segment_def by blast
  hence "upper_child (Run i) (x i) \<A> (Run (Suc i)) j (js ! 1)" by simp
  thus ?thesis unfolding upper_child_def by blast
qed

lemma upper_continued_up_index:
  assumes "upper_continued_up Run \<A> x i j"
  shows "j < length (Run i)"
proof -
  obtain k where "upper_child_segment_up Run i (Suc i) x \<A> j k" using assms unfolding upper_continued_up_def by blast
  then obtain js where "length js = Suc i - i + 1" "js ! 0 = j" "last js = k" "\<forall> m < Suc i - i . upper_child_up (Run (i + m)) (x (i + m)) \<A> (Run (i + Suc m)) (js ! m) (js ! Suc m)" unfolding upper_child_segment_up_def by blast
  hence "upper_child_up (Run i) (x i) \<A> (Run (Suc i)) j (js ! 1)" by simp
  thus ?thesis unfolding upper_child_up_def by blast
qed

lemma upper_continued_F_up_enc_iff: "upper_continued_F_up (enc_upper_run Run) \<A> x i j \<longleftrightarrow> upper_continued_F Run \<A> x i j"
proof -
  {
    assume "upper_continued_F_up (enc_upper_run Run) \<A> x i j"
    hence cont: "upper_continued_up (enc_upper_run Run) \<A> x i j \<and> fst ((enc_upper_run Run) i ! j) \<subseteq> accepting_states \<A>" unfolding upper_continued_F_up_def by blast
    hence cont': "upper_continued Run \<A> x i j" using upper_continued_up_enc_iff by blast
    hence "j < length (Run i)" using upper_continued_index by blast
    hence "fst ((enc_upper_run Run) i ! j) = Run i ! j" unfolding enc_upper_run_def cross_renaming_iso_def by simp
    hence "(Run i ! j) \<subseteq> accepting_states \<A>" using cont by simp
    hence "upper_continued_F Run \<A> x i j" using cont' unfolding upper_continued_F_def by blast
  }
  hence left: "upper_continued_F_up (enc_upper_run Run) \<A> x i j \<Longrightarrow> upper_continued_F Run \<A> x i j" by blast
  {
    assume "upper_continued_F Run \<A> x i j"
    hence cont: "upper_continued Run \<A> x i j \<and> Run i ! j \<subseteq> accepting_states \<A>" unfolding upper_continued_F_def by blast
    hence cont': "upper_continued_up (enc_upper_run Run) \<A> x i j" using upper_continued_up_enc_iff by blast
    have "j < length (Run i)" using cont upper_continued_index by blast
    hence "fst ((enc_upper_run Run) i ! j) = Run i ! j" unfolding enc_upper_run_def cross_renaming_iso_def by simp
    hence "fst ((enc_upper_run Run) i ! j) \<subseteq> accepting_states \<A>" using cont by simp
    hence "upper_continued_F_up (enc_upper_run Run) \<A> x i j" using cont' unfolding upper_continued_F_up_def by blast
  }
  thus ?thesis using left by blast
qed

lemma upper_slice_continued_F_up_enc_iff: "upper_slice_continued_F_up (enc_upper_run Run) \<A> x i \<longleftrightarrow> upper_slice_continued_F Run \<A> x i"
proof -
  {
    assume "upper_slice_continued_F_up (enc_upper_run Run) \<A> x i"
    then obtain j where j: "j < length ((enc_upper_run Run) i)" "upper_continued_F_up (enc_upper_run Run) \<A> x i j" unfolding upper_slice_continued_F_up_def by blast
    hence less: "j < length (Run i)" unfolding enc_upper_run_def by simp
    have "upper_continued_F Run \<A> x i j" using j upper_continued_F_up_enc_iff by blast
    hence "upper_slice_continued_F Run \<A> x i" using less unfolding upper_slice_continued_F_def by blast
  }
  hence left: "upper_slice_continued_F_up (enc_upper_run Run) \<A> x i \<Longrightarrow> upper_slice_continued_F Run \<A> x i" by blast
  {
    assume "upper_slice_continued_F Run \<A> x i"
    then obtain j where j: "j < length (Run i)" "upper_continued_F Run \<A> x i j" unfolding upper_slice_continued_F_def by blast
    hence less: "j < length ((enc_upper_run Run) i)" unfolding enc_upper_run_def by simp
    have "upper_continued_F_up (enc_upper_run Run) \<A> x i j" using j upper_continued_F_up_enc_iff by blast
    hence "upper_slice_continued_F_up (enc_upper_run Run) \<A> x i" using less
    unfolding upper_slice_continued_F_up_def by blast
  }
  thus ?thesis using left by blast
qed

corollary cor_3_4_15:
  assumes "auto_well_defined \<A>"
  shows "x \<in> omega_language_auto \<A> \<longleftrightarrow> (\<exists> Run . omega_run_well_defined Run (upper_part \<A>) x \<and> (\<forall> n . Run n \<noteq> []) \<and> infinite {i . upper_slice_continued_F_up Run \<A> x i})"
proof -
  {
    assume "x \<in> omega_language_auto \<A>"
    then obtain Run where Run: "omega_run_well_defined Run (upper_part_pure \<A>) x" "\<forall> n . Run n \<noteq> []" "infinite {i . upper_slice_continued_F Run \<A> x i}" using cor_3_4_15_pure[OF assms] by blast
    let ?Run = "enc_upper_run Run"
    have wd: "omega_run_well_defined ?Run (upper_part \<A>) x" using omega_run_well_defined_upper_part_transport assms Run by blast
    have ne: "\<forall> n . ?Run n \<noteq> []" using Run upper_part_transport_nonempty_all by metis
    have "{i . upper_slice_continued_F Run \<A> x i} = {i . upper_slice_continued_F_up ?Run \<A> x i}" using upper_slice_continued_F_up_enc_iff by blast
    hence "infinite {i . upper_slice_continued_F_up ?Run \<A> x i}" using Run by simp
    hence "\<exists> Run . omega_run_well_defined Run (upper_part \<A>) x \<and> (\<forall> n . Run n \<noteq> []) \<and> infinite {i . upper_slice_continued_F_up Run \<A> x i}" using wd ne by blast
  }
  hence left: "x \<in> omega_language_auto \<A> \<Longrightarrow> \<exists> Run . omega_run_well_defined Run (upper_part \<A>) x \<and> (\<forall> n . Run n \<noteq> []) \<and> infinite {i . upper_slice_continued_F_up Run \<A> x i}" by blast
  {
    assume "\<exists> Run . omega_run_well_defined Run (upper_part \<A>) x \<and> (\<forall> n . Run n \<noteq> []) \<and> infinite {i . upper_slice_continued_F_up Run \<A> x i}"
    then obtain Run where Run: "omega_run_well_defined Run (upper_part \<A>) x" "\<forall> n . Run n \<noteq> []" "infinite {i . upper_slice_continued_F_up Run \<A> x i}" by blast
    let ?Run = "dec_upper_run \<A> Run"
    have wd: "omega_run_well_defined ?Run (upper_part_pure \<A>) x" using omega_run_well_defined_upper_part_transport_back assms Run by blast
    have ne: "\<forall> n . ?Run n \<noteq> []" using upper_part_transport_nonempty_all_back assms Run unfolding dec_upper_run_def by blast
    have "{i . upper_slice_continued_F_up Run \<A> x i} = {i . upper_slice_continued_F_up (enc_upper_run ?Run) \<A> x i}" using enc_dec_upper_run assms Run by metis
    hence "{i . upper_slice_continued_F_up Run \<A> x i} = {i. upper_slice_continued_F ?Run \<A> x i}" using upper_slice_continued_F_up_enc_iff by blast
    hence "infinite {i. upper_slice_continued_F ?Run \<A> x i}" using Run by simp
    hence "x \<in> omega_language_auto \<A>" using cor_3_4_15_pure[OF assms] wd ne by blast
  }
  thus ?thesis using left by argo
qed

proposition accepting_run_on_upper_part_iff_no_run:
  assumes "auto_well_defined \<A>"
  shows "omega_word \<in> omega_language_auto (upper_part \<A>) \<longleftrightarrow> omega_word_well_defined omega_word (alphabet \<A>) \<and> (\<nexists> omega_run . omega_run_well_defined omega_run \<A> omega_word)"
  using assms accepting_run_on_upper_part_pure_iff_no_run upper_part_pure_and_upper_part_same_omega_language by blast

definition lower_states :: "('s, 'a) automaton \<Rightarrow> ('s states \<times> nat) list states" where "lower_states \<A> = {S . 1 \<le> length S \<and> length S \<le> card (states \<A>) \<and> distinct S \<and> pairwise (\<lambda> S_i S_j . (fst S_i) \<inter> (fst S_j) = {}) (set S) \<and> (\<forall> S_m \<in> set S . (fst S_m) \<subseteq> (states \<A>) \<and> (fst S_m) \<noteq> {} \<and> (snd S_m) \<in> {0, 1, 2})}"

definition lower_accepting :: "(('s states \<times> nat) list) \<Rightarrow> bool" where "lower_accepting S = (\<forall> (S_m, n) \<in> set S . n \<noteq> 2)"  

fun lower_step_acc :: "('s, 'a) automaton \<Rightarrow> 'a symbol \<Rightarrow> (('s states \<times> nat) list) \<Rightarrow> ((('s states \<times> nat) list) \<times> 's states)" where
  "lower_step_acc \<A> a [] = ([], {})" |
  "lower_step_acc \<A> a (S_m # S) = (((post_set \<A> (fst S_m) a - (snd (lower_step_acc \<A> a S))) - accepting_states \<A>, (min (2 * (snd S_m)) 2)) # ((post_set \<A> (fst S_m) a - (snd (lower_step_acc \<A> a S))) \<inter> accepting_states \<A>, 2) # fst (lower_step_acc \<A> a S), (snd (lower_step_acc \<A> a S)) \<union> post_set \<A> (fst S_m) a)"

fun lower_step_nacc :: "('s, 'a) automaton \<Rightarrow> 'a symbol \<Rightarrow> (('s states \<times> nat) list) \<Rightarrow> ((('s states \<times> nat) list) \<times> 's states)" where
  "lower_step_nacc \<A> a [] = ([], {})" |
  "lower_step_nacc \<A> a (S_m # S) = (((post_set \<A> (fst S_m) a - (snd (lower_step_nacc \<A> a S))) - accepting_states \<A>, (snd S_m)) # ((post_set \<A> (fst S_m) a - (snd (lower_step_nacc \<A> a S))) \<inter> accepting_states \<A>, (max (snd S_m) 1)) # fst (lower_step_nacc \<A> a S), (snd (lower_step_nacc \<A> a S)) \<union> post_set \<A> (fst S_m) a)"

definition lower_transitions :: "('s, 'a) automaton \<Rightarrow> ((('s states \<times> nat) list), 'a) transitions" where "lower_transitions \<A> = {(S, a, S') . S \<in> lower_states \<A> \<and> a \<in> alphabet \<A> \<and> S' = (if lower_accepting S then filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_acc \<A> a S)) else filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_nacc \<A> a S))) \<and> S' \<noteq> []}"

fun lower_step_from_upper :: "('s, 'a) automaton \<Rightarrow> 'a symbol \<Rightarrow> (('s states \<times> nat) list) \<Rightarrow> ((('s states \<times> nat) list) \<times> 's states)" where
  "lower_step_from_upper \<A> a [] = ([], {})" |
  "lower_step_from_upper \<A> a (S_m # S) = (((post_set \<A> (fst S_m) a - (snd (lower_step_from_upper \<A> a S))) - accepting_states \<A>, 0) # ((post_set \<A> (fst S_m) a - (snd (lower_step_from_upper \<A> a S))) \<inter> accepting_states \<A>, 2) # fst (lower_step_from_upper \<A> a S), (snd (lower_step_from_upper \<A> a S)) \<union> post_set \<A> (fst S_m) a)"

definition lower_transitions_from_upper :: "('s, 'a) automaton \<Rightarrow> ((('s states \<times> nat) list), 'a) transitions" where "lower_transitions_from_upper \<A> = {(S, a, S') . S \<in> states (upper_part \<A>) \<and> S \<noteq> [] \<and> a \<in> alphabet \<A> \<and> S' = filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_from_upper \<A> a S)) \<and> S' \<noteq> []}"

lemma lower_step_acc_fst_subset_states:
  assumes "auto_well_defined \<A>"
  shows "\<forall> S_m \<in> set (fst (lower_step_acc \<A> a S)) . fst S_m \<subseteq> states \<A> \<and> (snd S_m) \<in> {0, 1, 2}"
proof (induction S)
  case Nil thus ?case by auto
next
  case (Cons S_m S)
  have ps: "post_set \<A> (fst S_m) a \<subseteq> states \<A>" using assms unfolding auto_well_defined_def post_set_def by fast
  hence sub: "(post_set \<A> (fst S_m) a - snd (lower_step_acc \<A> a S)) - accepting_states \<A> \<subseteq> states \<A>" by blast
  have "(post_set \<A> (fst S_m) a - snd (lower_step_acc \<A> a S)) \<inter> accepting_states \<A> \<subseteq> states \<A>" using ps by blast
  thus ?case using Cons sub by auto
qed

lemma lower_step_acc_fst_subset_snd: "\<forall> S_m \<in> set (fst (lower_step_acc \<A> a S)) . fst S_m \<subseteq> snd (lower_step_acc \<A> a S)"
proof (induction S)
  case Nil thus ?case by simp
next
  case (Cons S_m S)
  let ?L = "post_set \<A> (fst S_m) a - snd (lower_step_acc \<A> a S) - accepting_states \<A>"
  let ?R = "(post_set \<A> (fst S_m) a - snd (lower_step_acc \<A> a S)) \<inter> accepting_states \<A>"
  have Lsub: "?L \<subseteq> (snd (lower_step_acc \<A> a (S_m # S)))" by force
  have Rsub: "?R \<subseteq> (snd (lower_step_acc \<A> a (S_m # S)))" by force
  have Usub: "snd (lower_step_acc \<A> a S) \<subseteq> snd (lower_step_acc \<A> a (S_m # S))" by simp
  {
    fix S_k assume "S_k \<in> set (fst (lower_step_acc \<A> a (S_m # S)))"
    hence "S_k = (?L, min (2 * snd S_m) 2) \<or> S_k = (?R, 2) \<or> S_k \<in> set (fst (lower_step_acc \<A> a S))" by simp
    then consider (case1) "S_k = (?L, min (2 * snd S_m) 2)" | (case2) "S_k = (?R, 2)" | (case3) "S_k \<in> set (fst (lower_step_acc \<A> a S))" by fast 
    hence "fst S_k \<subseteq> snd (lower_step_acc \<A> a (S_m # S))"
    proof cases
      case case1 thus ?thesis using Lsub by force
    next
      case case2 thus ?thesis using Rsub by force
    next
      case case3 thus ?thesis using Cons Usub by fast
    qed
  }  
  thus ?case by blast
qed

lemma lower_step_acc_fst_pairwise_list: "pairwise_list (\<lambda> S_i S_j . (fst S_i) \<inter> (fst S_j) = {}) (fst (lower_step_acc \<A> a S))"
proof (induction S)
  case Nil thus ?case unfolding pairwise_list_def by auto
next
  case (Cons S_m S)
  let ?L = "(post_set \<A> (fst S_m) a - (snd (lower_step_acc \<A> a S))) - accepting_states \<A>"
  let ?R = "(post_set \<A> (fst S_m) a - (snd (lower_step_acc \<A> a S))) \<inter> accepting_states \<A>"
  have LR: "?L \<inter> ?R = {}" by auto
  {
    fix j assume "j < length (fst (lower_step_acc \<A> a S))"
    hence "(fst (lower_step_acc \<A> a S)) ! j \<in> set (fst (lower_step_acc \<A> a S))" by auto
    hence "fst ((fst (lower_step_acc \<A> a S)) ! j) \<subseteq> (snd (lower_step_acc \<A> a S))" using lower_step_acc_fst_subset_snd by fast
    hence "?L \<inter> fst ((fst (lower_step_acc \<A> a S)) ! j) = {}" by blast
  }
  hence L_rest: "\<forall> j < length (fst (lower_step_acc \<A> a S)) . ?L \<inter> fst ((fst (lower_step_acc \<A> a S)) ! j) = {}" by blast
  {
    fix j assume "j < length (fst (lower_step_acc \<A> a S))"
    hence "(fst (lower_step_acc \<A> a S)) ! j \<in> set (fst (lower_step_acc \<A> a S))" by auto
    hence "fst ((fst (lower_step_acc \<A> a S)) ! j) \<subseteq> (snd (lower_step_acc \<A> a S))" using lower_step_acc_fst_subset_snd by fast
    hence "?R \<inter> fst ((fst (lower_step_acc \<A> a S)) ! j) = {}" by blast
  }
  hence R_rest: "\<forall>j < length (fst (lower_step_acc \<A> a S)) . ?R \<inter> fst ((fst (lower_step_acc \<A> a S)) ! j) = {}" by blast
  let ?Lpair = "(?L, min (2 * snd S_m) 2)"
  let ?Rpair = "(?R, 2)"
  {
    fix i j assume assm: "i < length (?Lpair # ?Rpair # (fst (lower_step_acc \<A> a S))) \<and> j < length (?Lpair # ?Rpair # (fst (lower_step_acc \<A> a S))) \<and> i < j"
    hence "fst ((?Lpair # ?Rpair # (fst (lower_step_acc \<A> a S))) ! i) \<inter> fst ((?Lpair # ?Rpair # (fst (lower_step_acc \<A> a S))) ! j) = {}"
    proof (cases i)
      case 0
      thus ?thesis
      proof (cases j)
        case 0 thus ?thesis using assm by blast
      next
        case (Suc j')
        hence j: "j = Suc j'" by blast
        thus ?thesis
        proof (cases j')
          case 0 thus ?thesis using assm Suc LR by force
        next
          case (Suc t) thus ?thesis using L_rest assm 0 j by auto
        qed
      qed
    next
      case (Suc i')
      hence i: "i = Suc i'" by blast
      thus ?thesis
      proof (cases i')
        case 0
        thus ?thesis
        proof (cases j)
          case 0 thus ?thesis using assm by blast
        next
          case (Suc j')
          hence j: "j = Suc j'" by blast
          thus ?thesis
          proof (cases j')
            case 0 thus ?thesis using assm Suc LR by auto
          next
            case (Suc t) thus ?thesis using R_rest assm 0 j i by auto
          qed
        qed
      next
        case (Suc i2)
        hence i2lt: "i2 < length (fst (lower_step_acc \<A> a S))" using i assm by simp
        have "\<exists> j2 . j = Suc (Suc j2)" using assm Suc i by presburger
        then obtain j2 where j2: "j = Suc (Suc j2)" by blast
        hence j2lt: "j2 < length (fst (lower_step_acc \<A> a S))" using assm by simp
        have "i2 < j2" using assm Suc j2 i by blast
        hence "fst ((fst (lower_step_acc \<A> a S)) ! i2) \<inter> fst ((fst (lower_step_acc \<A> a S)) ! j2) = {}" using Cons unfolding pairwise_list_def using i2lt j2lt by blast
        thus ?thesis using Suc assm j2 i by simp
      qed
    qed
  }
  hence "pairwise_list (\<lambda> S_i S_j . (fst S_i) \<inter> (fst S_j) = {}) (?Lpair # ?Rpair # (fst (lower_step_acc \<A> a S)))" unfolding pairwise_list_def by blast
  thus ?case by simp
qed

lemma lower_step_nacc_fst_subset_states:
  assumes "auto_well_defined \<A>"
  shows "\<forall> S_m \<in> set S . (snd S_m) \<in> {0, 1, 2} \<Longrightarrow> \<forall> S_m \<in> set (fst (lower_step_nacc \<A> a S)). fst S_m \<subseteq> states \<A> \<and> (snd S_m) \<in> {0, 1, 2}"
proof (induction S)
  case Nil thus ?case by auto
next
  case (Cons S_m S)
  have ps: "post_set \<A> (fst S_m) a \<subseteq> states \<A>" using assms unfolding auto_well_defined_def post_set_def by fast
  hence sub: "(post_set \<A> (fst S_m) a - snd (lower_step_nacc \<A> a S)) - accepting_states \<A> \<subseteq> states \<A>" by blast
  have "(post_set \<A> (fst S_m) a - snd (lower_step_nacc \<A> a S)) \<inter> accepting_states \<A> \<subseteq> states \<A>" using ps by blast
  thus ?case using Cons sub by auto
qed

lemma lower_step_nacc_fst_subset_snd: "\<forall> S_m \<in> set (fst (lower_step_nacc \<A> a S)) . fst S_m \<subseteq> snd (lower_step_nacc \<A> a S)"
proof (induction S)
  case Nil thus ?case by simp
next
  case (Cons S_m S)
  let ?L = "post_set \<A> (fst S_m) a - snd (lower_step_nacc \<A> a S) - accepting_states \<A>"
  let ?R = "(post_set \<A> (fst S_m) a - snd (lower_step_nacc \<A> a S)) \<inter> accepting_states \<A>"
  have Lsub: "?L \<subseteq> (snd (lower_step_nacc \<A> a (S_m # S)))" by force
  have Rsub: "?R \<subseteq> (snd (lower_step_nacc \<A> a (S_m # S)))" by force
  have Usub: "snd (lower_step_nacc \<A> a S) \<subseteq> snd (lower_step_nacc \<A> a (S_m # S))" by simp
  {
    fix S_k assume "S_k \<in> set (fst (lower_step_nacc \<A> a (S_m # S)))"
    hence "S_k = (?L, snd S_m) \<or> S_k = (?R, (max (snd S_m) 1)) \<or> S_k \<in> set (fst (lower_step_nacc \<A> a S))" by simp
    then consider (case1) "S_k = (?L, snd S_m)" | (case2) "S_k = (?R, (max (snd S_m) 1))" | (case3) "S_k \<in> set (fst (lower_step_nacc \<A> a S))" by fast 
    hence "fst S_k \<subseteq> snd (lower_step_nacc \<A> a (S_m # S))"
    proof cases
      case case1 thus ?thesis using Lsub by force
    next
      case case2 thus ?thesis using Rsub by force
    next
      case case3 thus ?thesis using Cons Usub by fast
    qed
  }  
  thus ?case by blast
qed

lemma lower_step_nacc_fst_pairwise_list: "pairwise_list (\<lambda> S_i S_j . (fst S_i) \<inter> (fst S_j) = {}) (fst (lower_step_nacc \<A> a S))"
proof (induction S)
  case Nil thus ?case unfolding pairwise_list_def by auto
next
  case (Cons S_m S)
  let ?L = "(post_set \<A> (fst S_m) a - (snd (lower_step_nacc \<A> a S))) - accepting_states \<A>"
  let ?R = "(post_set \<A> (fst S_m) a - (snd (lower_step_nacc \<A> a S))) \<inter> accepting_states \<A>"
  have LR: "?L \<inter> ?R = {}" by auto
  {
    fix j assume "j < length (fst (lower_step_nacc \<A> a S))"
    hence "(fst (lower_step_nacc \<A> a S)) ! j \<in> set (fst (lower_step_nacc \<A> a S))" by auto
    hence "fst ((fst (lower_step_nacc \<A> a S)) ! j) \<subseteq> (snd (lower_step_nacc \<A> a S))" using lower_step_nacc_fst_subset_snd by fast
    hence "?L \<inter> fst ((fst (lower_step_nacc \<A> a S)) ! j) = {}" by blast
  }
  hence L_rest: "\<forall> j < length (fst (lower_step_nacc \<A> a S)) . ?L \<inter> fst ((fst (lower_step_nacc \<A> a S)) ! j) = {}" by blast
  {
    fix j assume "j < length (fst (lower_step_nacc \<A> a S))"
    hence "(fst (lower_step_nacc \<A> a S)) ! j \<in> set (fst (lower_step_nacc \<A> a S))" by auto
    hence "fst ((fst (lower_step_nacc \<A> a S)) ! j) \<subseteq> (snd (lower_step_nacc \<A> a S))" using lower_step_nacc_fst_subset_snd by fast
    hence "?R \<inter> fst ((fst (lower_step_nacc \<A> a S)) ! j) = {}" by blast
  }
  hence R_rest: "\<forall>j < length (fst (lower_step_nacc \<A> a S)) . ?R \<inter> fst ((fst (lower_step_nacc \<A> a S)) ! j) = {}" by blast
  let ?Lpair = "(?L, snd S_m)"
  let ?Rpair = "(?R, (max (snd S_m) 1))"
  {
    fix i j assume assm: "i < length (?Lpair # ?Rpair # (fst (lower_step_nacc \<A> a S))) \<and> j < length (?Lpair # ?Rpair # (fst (lower_step_nacc \<A> a S))) \<and> i < j"
    hence "fst ((?Lpair # ?Rpair # (fst (lower_step_nacc \<A> a S))) ! i) \<inter> fst ((?Lpair # ?Rpair # (fst (lower_step_nacc \<A> a S))) ! j) = {}"
    proof (cases i)
      case 0
      thus ?thesis
      proof (cases j)
        case 0 thus ?thesis using assm by blast
      next
        case (Suc j')
        hence j: "j = Suc j'" by blast
        thus ?thesis
        proof (cases j')
          case 0 thus ?thesis using assm Suc LR by force
        next
          case (Suc t) thus ?thesis using L_rest assm 0 j by auto
        qed
      qed
    next
      case (Suc i')
      hence i: "i = Suc i'" by blast
      thus ?thesis
      proof (cases i')
        case 0
        thus ?thesis
        proof (cases j)
          case 0 thus ?thesis using assm by blast
        next
          case (Suc j')
          hence j: "j = Suc j'" by blast
          thus ?thesis
          proof (cases j')
            case 0 thus ?thesis using assm Suc LR by auto
          next
            case (Suc t) thus ?thesis using R_rest assm 0 j i by auto
          qed
        qed
      next
        case (Suc i2)
        hence i2lt: "i2 < length (fst (lower_step_nacc \<A> a S))" using i assm by simp
        have "\<exists> j2 . j = Suc (Suc j2)" using assm Suc i by presburger
        then obtain j2 where j2: "j = Suc (Suc j2)" by blast
        hence j2lt: "j2 < length (fst (lower_step_nacc \<A> a S))" using assm by simp
        have "i2 < j2" using assm Suc j2 i by blast
        hence "fst ((fst (lower_step_nacc \<A> a S)) ! i2) \<inter> fst ((fst (lower_step_nacc \<A> a S)) ! j2) = {}" using Cons unfolding pairwise_list_def using i2lt j2lt by blast
        thus ?thesis using Suc assm j2 i by simp
      qed
    qed
  }
  hence "pairwise_list (\<lambda> S_i S_j . (fst S_i) \<inter> (fst S_j) = {}) (?Lpair # ?Rpair # (fst (lower_step_nacc \<A> a S)))" unfolding pairwise_list_def by blast
  thus ?case by simp
qed

lemma lower_step_from_upper_fst_subset_states:
  assumes "auto_well_defined \<A>"
  shows "\<forall> S_m \<in> set (fst (lower_step_from_upper \<A> a S)) . fst S_m \<subseteq> states \<A> \<and> (snd S_m) \<in> {0, 1, 2}"
proof (induction S)
  case Nil thus ?case by auto
next
  case (Cons S_m S)
  have ps: "post_set \<A> (fst S_m) a \<subseteq> states \<A>" using assms unfolding auto_well_defined_def post_set_def by fast
  hence sub: "(post_set \<A> (fst S_m) a - snd (lower_step_from_upper \<A> a S)) - accepting_states \<A> \<subseteq> states \<A>" by blast
  have "(post_set \<A> (fst S_m) a - snd (lower_step_from_upper \<A> a S)) \<inter> accepting_states \<A> \<subseteq> states \<A>" using ps by blast
  thus ?case using Cons sub by auto
qed

lemma lower_step_from_upper_fst_subset_snd: "\<forall> S_m \<in> set (fst (lower_step_from_upper \<A> a S)) . fst S_m \<subseteq> snd (lower_step_from_upper \<A> a S)"
proof (induction S)
  case Nil thus ?case by simp
next
  case (Cons S_m S)
  let ?L = "post_set \<A> (fst S_m) a - snd (lower_step_from_upper \<A> a S) - accepting_states \<A>"
  let ?R = "(post_set \<A> (fst S_m) a - snd (lower_step_from_upper \<A> a S)) \<inter> accepting_states \<A>"
  have Lsub: "?L \<subseteq> (snd (lower_step_from_upper \<A> a (S_m # S)))" by force
  have Rsub: "?R \<subseteq> (snd (lower_step_from_upper \<A> a (S_m # S)))" by force
  have Usub: "snd (lower_step_from_upper \<A> a S) \<subseteq> snd (lower_step_from_upper \<A> a (S_m # S))" by simp
  {
    fix S_k assume "S_k \<in> set (fst (lower_step_from_upper \<A> a (S_m # S)))"
    hence "S_k = (?L, 0) \<or> S_k = (?R, 2) \<or> S_k \<in> set (fst (lower_step_from_upper \<A> a S))" by simp
    then consider (case1) "S_k = (?L, 0)" | (case2) "S_k = (?R, 2)" | (case3) "S_k \<in> set (fst (lower_step_from_upper \<A> a S))" by fast 
    hence "fst S_k \<subseteq> snd (lower_step_from_upper \<A> a (S_m # S))"
    proof cases
      case case1 thus ?thesis using Lsub by force
    next
      case case2 thus ?thesis using Rsub by force
    next
      case case3 thus ?thesis using Cons Usub by fast
    qed
  }  
  thus ?case by blast
qed

lemma lower_step_from_upper_fst_pairwise_list: "pairwise_list (\<lambda> S_i S_j . (fst S_i) \<inter> (fst S_j) = {}) (fst (lower_step_from_upper \<A> a S))"
proof (induction S)
  case Nil thus ?case unfolding pairwise_list_def by auto
next
  case (Cons S_m S)
  let ?L = "(post_set \<A> (fst S_m) a - (snd (lower_step_from_upper \<A> a S))) - accepting_states \<A>"
  let ?R = "(post_set \<A> (fst S_m) a - (snd (lower_step_from_upper \<A> a S))) \<inter> accepting_states \<A>"
  have LR: "?L \<inter> ?R = {}" by auto
  {
    fix j assume "j < length (fst (lower_step_from_upper \<A> a S))"
    hence "(fst (lower_step_from_upper \<A> a S)) ! j \<in> set (fst (lower_step_from_upper \<A> a S))" by auto
    hence "fst ((fst (lower_step_from_upper \<A> a S)) ! j) \<subseteq> (snd (lower_step_from_upper \<A> a S))" using lower_step_from_upper_fst_subset_snd by fast
    hence "?L \<inter> fst ((fst (lower_step_from_upper \<A> a S)) ! j) = {}" by blast
  }
  hence L_rest: "\<forall> j < length (fst (lower_step_from_upper \<A> a S)) . ?L \<inter> fst ((fst (lower_step_from_upper \<A> a S)) ! j) = {}" by blast
  {
    fix j assume "j < length (fst (lower_step_from_upper \<A> a S))"
    hence "(fst (lower_step_from_upper \<A> a S)) ! j \<in> set (fst (lower_step_from_upper \<A> a S))" by auto
    hence "fst ((fst (lower_step_from_upper \<A> a S)) ! j) \<subseteq> (snd (lower_step_from_upper \<A> a S))" using lower_step_from_upper_fst_subset_snd by fast
    hence "?R \<inter> fst ((fst (lower_step_from_upper \<A> a S)) ! j) = {}" by blast
  }
  hence R_rest: "\<forall>j < length (fst (lower_step_from_upper \<A> a S)) . ?R \<inter> fst ((fst (lower_step_from_upper \<A> a S)) ! j) = {}" by blast
  let ?Lpair = "(?L, 0)"
  let ?Rpair = "(?R, 2)"
  {
    fix i j assume assm: "i < length (?Lpair # ?Rpair # (fst (lower_step_from_upper \<A> a S))) \<and> j < length (?Lpair # ?Rpair # (fst (lower_step_from_upper \<A> a S))) \<and> i < j"
    hence "fst ((?Lpair # ?Rpair # (fst (lower_step_from_upper \<A> a S))) ! i) \<inter> fst ((?Lpair # ?Rpair # (fst (lower_step_from_upper \<A> a S))) ! j) = {}"
    proof (cases i)
      case 0
      thus ?thesis
      proof (cases j)
        case 0 thus ?thesis using assm by blast
      next
        case (Suc j')
        hence j: "j = Suc j'" by blast
        thus ?thesis
        proof (cases j')
          case 0 thus ?thesis using assm Suc LR by force
        next
          case (Suc t) thus ?thesis using L_rest assm 0 j by auto
        qed
      qed
    next
      case (Suc i')
      hence i: "i = Suc i'" by blast
      thus ?thesis
      proof (cases i')
        case 0
        thus ?thesis
        proof (cases j)
          case 0 thus ?thesis using assm by blast
        next
          case (Suc j')
          hence j: "j = Suc j'" by blast
          thus ?thesis
          proof (cases j')
            case 0 thus ?thesis using assm Suc LR by auto
          next
            case (Suc t) thus ?thesis using R_rest assm 0 j i by auto
          qed
        qed
      next
        case (Suc i2)
        hence i2lt: "i2 < length (fst (lower_step_from_upper \<A> a S))" using i assm by simp
        have "\<exists> j2 . j = Suc (Suc j2)" using assm Suc i by presburger
        then obtain j2 where j2: "j = Suc (Suc j2)" by blast
        hence j2lt: "j2 < length (fst (lower_step_from_upper \<A> a S))" using assm by simp
        have "i2 < j2" using assm Suc j2 i by blast
        hence "fst ((fst (lower_step_from_upper \<A> a S)) ! i2) \<inter> fst ((fst (lower_step_from_upper \<A> a S)) ! j2) = {}" using Cons unfolding pairwise_list_def using i2lt j2lt by blast
        thus ?thesis using Suc assm j2 i by simp
      qed
    qed
  }
  hence "pairwise_list (\<lambda> S_i S_j . (fst S_i) \<inter> (fst S_j) = {}) (?Lpair # ?Rpair # (fst (lower_step_from_upper \<A> a S)))" unfolding pairwise_list_def by blast
  thus ?case by simp
qed

lemma distinct_of_pairwise_list_disjoint_nonempty_lower_part:
  assumes "pairwise_list (\<lambda> S_i S_j . (fst S_i) \<inter> (fst S_j) = {}) S" "\<forall> S_m \<in> set S . fst S_m \<noteq> {}"
  shows "distinct S"
proof -
  {
    fix i j assume assm: "i < length S \<and> j < length S \<and> i \<noteq> j"
    hence "fst (S ! i) \<noteq> fst (S ! j)"
    proof(cases "i < j")
      case True
      hence disj: "fst (S ! i) \<inter> fst (S ! j) = {}" using assms assm unfolding pairwise_list_def by blast
      have "fst (S ! i) \<noteq> {}" using assms assm by auto
      thus ?thesis using disj by blast
    next
      case False
      hence "j < i" using assm by linarith
      hence disj: "fst (S ! i) \<inter> fst (S ! j) = {}" using assms assm unfolding pairwise_list_def by blast
      have "fst (S ! j) \<noteq> {}" using assms assm by auto
      thus ?thesis using disj by blast
    qed
  }
  thus ?thesis using distinct_conv_nth by metis
qed

lemma pairwise_list_disjoint_imp_pairwise_lower_part:
  assumes "pairwise_list (\<lambda> A B . fst A \<inter> fst B = {}) list"
  shows "pairwise (\<lambda> A B . fst A \<inter> fst B = {}) (set list)"
proof -
  {
    fix x y assume assm: "x \<in> set list \<and> y \<in> set list \<and> x \<noteq> y"
    then obtain i j  where var: "i < length list \<and> list ! i = x \<and> j < length list \<and> list ! j = y" using in_set_conv_nth by metis
    hence "i \<noteq> j" using assm by blast
    hence or: "i < j \<or> j < i" using linorder_neqE_nat by blast
    hence "fst x \<inter> fst y = {}"
    proof(cases "i < j")
      case True thus ?thesis using assms var unfolding pairwise_list_def by blast
    next
      case False
      hence "j < i" using or by blast
      thus ?thesis using assms var unfolding pairwise_list_def by blast
    qed
  }
  hence "\<forall> x \<in> set list . \<forall> y \<in> set list . x \<noteq> y \<longrightarrow> (fst x \<inter> fst y = {})" by blast
  thus ?thesis unfolding pairwise_def by blast
qed

lemma length_le_card_states_of_pairwise_disjoint_nonempty_lower_part:
  assumes "auto_well_defined \<A>" "\<forall> S_m \<in> set S . fst S_m \<subseteq> states \<A> \<and> fst S_m \<noteq> {}" "pairwise_list (\<lambda> S_i S_j . fst S_i \<inter> fst S_j = {}) S"
  shows "length S \<le> card (states \<A>)"
proof -
  have fin: "finite (states \<A>)" using assms unfolding auto_well_defined_def by blast
  have dist: "distinct S" using assms distinct_of_pairwise_list_disjoint_nonempty_lower_part by fast
  have pairwise: "pairwise (\<lambda> S_i S_j . fst S_i \<inter> fst S_j = {}) (set S)" using assms pairwise_list_disjoint_imp_pairwise_lower_part by auto
  let ?pick = "\<lambda> S_m . (SOME x . x \<in> fst S_m)"
  {
    fix S_m assume "S_m \<in> set S"
    hence "\<exists> x . x \<in> fst S_m" using assms by auto
    hence "?pick S_m \<in> fst S_m" by (rule someI_ex)
  }
  hence pick_in: "\<forall> S_m \<in> set S . ?pick S_m \<in> fst S_m" by blast
  hence pick_in_states: "\<forall> S_m \<in> set S . ?pick S_m \<in> states \<A>" using assms by blast
  {
    fix S_i S_j assume assm: "S_i \<in> set S \<and> S_j \<in> set S \<and> ?pick S_i = ?pick S_j"
    hence "S_i = S_j"
    proof (cases "S_i = S_j")
      case True thus ?thesis by blast
    next
      case False
      hence disj: "fst S_i \<inter> fst S_j = {}" using assm pairwise by (auto dest: pairwiseD)
      have pick: "?pick S_i \<in> fst S_i" using pick_in assm by blast
      have "?pick S_j \<in> fst S_j" using pick_in assm by blast
      hence "?pick S_i \<in> fst S_i \<inter> fst S_j" using pick assm by auto
      thus ?thesis using disj by auto
    qed
  }
  hence "inj_on ?pick (set S)" by (rule inj_onI) auto
  hence "card (set S) \<le> card (states \<A>)" using fin pick_in_states card_inj_on_le by blast
  thus ?thesis using dist distinct_card by metis
qed

lemma lower_transitions_target_in_lower_states:
  assumes "auto_well_defined \<A>" "(S, a, S') \<in> lower_transitions \<A>"
  shows "S \<in> lower_states \<A> \<and> a \<in> alphabet \<A> \<and> S' \<in> lower_states \<A>"
proof(cases "lower_accepting S")
  case True
  hence S'def: "S \<in> lower_states \<A> \<and> a \<in> alphabet \<A> \<and> S' = filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_acc \<A> a S)) \<and> S' \<noteq> []" using assms unfolding lower_transitions_def by auto
  have fin: "finite (states \<A>)" using assms unfolding auto_well_defined_def by auto
  have sub_fst: "\<forall> S_m \<in> set (fst (lower_step_acc \<A> a S)) . fst S_m \<subseteq> states \<A> \<and> (snd S_m) \<in> {0, 1, 2}" using lower_step_acc_fst_subset_states assms by metis
  {
    fix S_m assume assm: "S_m \<in> set S'"
    hence "S_m \<in> set (fst (lower_step_acc \<A> a S))" using S'def by auto
    hence S_m: "fst S_m \<subseteq> states \<A> \<and> (snd S_m) \<in> {0, 1, 2}" using sub_fst by blast
    have "fst S_m \<noteq> {}" using assm S'def by auto
    hence "fst S_m \<subseteq> states \<A> \<and> fst S_m \<noteq> {} \<and> (snd S_m) \<in> {0, 1, 2}" using S_m by blast
  }
  hence S_m: "\<forall> S_m \<in> set S' . fst S_m \<subseteq> states \<A> \<and> fst S_m \<noteq> {} \<and> (snd S_m) \<in> {0, 1, 2}" by blast
  have "pairwise_list (\<lambda> S_i S_j . fst S_i \<inter> fst S_j = {}) (fst (lower_step_acc \<A> a S))" using lower_step_acc_fst_pairwise_list by fast
  hence "pairwise_list (\<lambda> S_i S_j . fst S_i \<inter> fst S_j = {}) (filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_acc \<A> a S)))" using pairwise_list_filter by blast
  hence pwlS': "pairwise_list (\<lambda> S_i S_j . fst S_i \<inter> fst S_j = {}) S'" using S'def by simp
  hence distS': "distinct S'" using distinct_of_pairwise_list_disjoint_nonempty_lower_part S_m by blast
  have pwS': "pairwise (\<lambda>S_i S_j. fst S_i \<inter> fst S_j = {}) (set S')" using pairwise_list_disjoint_imp_pairwise_lower_part pwlS' by blast
  have "S' \<noteq> []" using S'def by blast
  hence "0 < length S'" by blast
  hence lenS': "1 \<le> length S'" by linarith
  have "length S' \<le> card (states \<A>)" using length_le_card_states_of_pairwise_disjoint_nonempty_lower_part assms S_m pwlS' by blast
  hence "S' \<in> lower_states \<A>" using lenS' distS' pwS' S_m unfolding lower_states_def by blast
  thus ?thesis using assms unfolding lower_transitions_def by fast
next
  case False
  hence S'def: "S \<in> lower_states \<A> \<and> a \<in> alphabet \<A> \<and> S' = filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_nacc \<A> a S)) \<and> S' \<noteq> []" using assms unfolding lower_transitions_def by auto
  hence in_nat: "\<forall> S_m \<in> set S . (snd S_m) \<in> {0, 1, 2}" unfolding lower_states_def by blast
  have fin: "finite (states \<A>)" using assms unfolding auto_well_defined_def by auto
  have sub_fst: "\<forall> S_m \<in> set (fst (lower_step_nacc \<A> a S)) . fst S_m \<subseteq> states \<A> \<and> (snd S_m) \<in> {0, 1, 2}" using in_nat lower_step_nacc_fst_subset_states assms by metis
  {
    fix S_m assume assm: "S_m \<in> set S'"
    hence "S_m \<in> set (fst (lower_step_nacc \<A> a S))" using S'def by auto
    hence S_m: "fst S_m \<subseteq> states \<A> \<and> (snd S_m) \<in> {0, 1, 2}" using sub_fst by blast
    have "fst S_m \<noteq> {}" using assm S'def by auto
    hence "fst S_m \<subseteq> states \<A> \<and> fst S_m \<noteq> {} \<and> (snd S_m) \<in> {0, 1, 2}" using S_m by blast
  }
  hence S_m: "\<forall> S_m \<in> set S' . fst S_m \<subseteq> states \<A> \<and> fst S_m \<noteq> {} \<and> (snd S_m) \<in> {0, 1, 2}" by blast
  have "pairwise_list (\<lambda> S_i S_j . fst S_i \<inter> fst S_j = {}) (fst (lower_step_nacc \<A> a S))" using lower_step_nacc_fst_pairwise_list by fast
  hence "pairwise_list (\<lambda> S_i S_j . fst S_i \<inter> fst S_j = {}) (filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_nacc \<A> a S)))" using pairwise_list_filter by blast
  hence pwlS': "pairwise_list (\<lambda> S_i S_j . fst S_i \<inter> fst S_j = {}) S'" using S'def by simp
  hence distS': "distinct S'" using distinct_of_pairwise_list_disjoint_nonempty_lower_part S_m by blast
  have pwS': "pairwise (\<lambda>S_i S_j. fst S_i \<inter> fst S_j = {}) (set S')" using pairwise_list_disjoint_imp_pairwise_lower_part pwlS' by blast
  have "S' \<noteq> []" using S'def by blast
  hence "0 < length S'" by blast
  hence lenS': "1 \<le> length S'" by linarith
  have "length S' \<le> card (states \<A>)" using length_le_card_states_of_pairwise_disjoint_nonempty_lower_part assms S_m pwlS' by blast
  hence "S' \<in> lower_states \<A>" using lenS' distS' pwS' S_m unfolding lower_states_def by blast
  thus ?thesis using assms unfolding lower_transitions_def by fast
qed

lemma lower_transitions_from_upper_target_in_lower_states:
  assumes "auto_well_defined \<A>" "(S, a, S') \<in> lower_transitions_from_upper \<A>"
  shows "S \<in> states (upper_part \<A>) \<and> S \<noteq> [] \<and> a \<in> alphabet \<A> \<and> S' \<in> lower_states \<A>"
proof -
  have S'def: "S \<in> states (upper_part \<A>) \<and> S \<noteq> [] \<and> a \<in> alphabet \<A> \<and> S' = filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_from_upper \<A> a S)) \<and> S' \<noteq> []" using assms unfolding lower_transitions_from_upper_def by auto
  have fin: "finite (states \<A>)" using assms unfolding auto_well_defined_def by auto
  have sub_fst: "\<forall> S_m \<in> set (fst (lower_step_from_upper \<A> a S)) . fst S_m \<subseteq> states \<A> \<and> (snd S_m) \<in> {0, 1, 2}" using lower_step_from_upper_fst_subset_states assms by metis
  {
    fix S_m assume assm: "S_m \<in> set S'"
    hence "S_m \<in> set (fst (lower_step_from_upper \<A> a S))" using S'def by auto
    hence S_m: "fst S_m \<subseteq> states \<A> \<and> (snd S_m) \<in> {0, 1, 2}" using sub_fst by blast
    have "fst S_m \<noteq> {}" using assm S'def by auto
    hence "fst S_m \<subseteq> states \<A> \<and> fst S_m \<noteq> {} \<and> (snd S_m) \<in> {0, 1, 2}" using S_m by blast
  }
  hence S_m: "\<forall> S_m \<in> set S' . fst S_m \<subseteq> states \<A> \<and> fst S_m \<noteq> {} \<and> (snd S_m) \<in> {0, 1, 2}" by blast
  have "pairwise_list (\<lambda> S_i S_j . fst S_i \<inter> fst S_j = {}) (fst (lower_step_from_upper \<A> a S))" using lower_step_from_upper_fst_pairwise_list by fast
  hence "pairwise_list (\<lambda> S_i S_j . fst S_i \<inter> fst S_j = {}) (filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_from_upper \<A> a S)))" using pairwise_list_filter by blast
  hence pwlS': "pairwise_list (\<lambda> S_i S_j . fst S_i \<inter> fst S_j = {}) S'" using S'def by simp
  hence distS': "distinct S'" using distinct_of_pairwise_list_disjoint_nonempty_lower_part S_m by blast
  have pwS': "pairwise (\<lambda>S_i S_j. fst S_i \<inter> fst S_j = {}) (set S')" using pairwise_list_disjoint_imp_pairwise_lower_part pwlS' by blast
  have "S' \<noteq> []" using S'def by blast
  hence "0 < length S'" by blast
  hence lenS': "1 \<le> length S'" by linarith
  have "length S' \<le> card (states \<A>)" using length_le_card_states_of_pairwise_disjoint_nonempty_lower_part assms S_m pwlS' by blast
  hence "S' \<in> lower_states \<A>" using lenS' distS' pwS' S_m unfolding lower_states_def by blast
  thus ?thesis using S'def by fast
qed

lemma finite_lower_states:
  assumes "auto_well_defined \<A>"
  shows "finite (lower_states \<A>)"
proof -
  have "finite (states \<A>)" using assms unfolding auto_well_defined_def by auto
  hence "finite (Pow (states \<A>))" by simp
  hence finPow: "finite (Pow (states \<A>) \<times> {0, 1 ,2})" by blast
  have sub: "lower_states \<A> \<subseteq> {S . set S \<subseteq> (Pow (states \<A>) \<times> {0, 1, 2}) \<and> length S \<le> card (states \<A>)}" unfolding lower_states_def by fastforce
  have "finite {S . set S \<subseteq> (Pow (states \<A>) \<times> {0, 1 ,2}) \<and> length S \<le> card (states \<A>)}" using finPow by (rule finite_lists_length_le)
  thus ?thesis using finite_subset sub by blast
qed

definition comp_omega_automaton :: "('s, 'a) automaton \<Rightarrow> ((('s states \<times> nat) list), 'a) automaton" where
  "comp_omega_automaton \<A> = Automaton
     (states (upper_part \<A>) \<union> lower_states \<A>)
     (alphabet \<A>)
     (transitions (upper_part \<A>) \<union> lower_transitions \<A> \<union> lower_transitions_from_upper \<A>)
     (initial_state (upper_part \<A>))
     ({S \<in> lower_states \<A> . lower_accepting S} \<union> accepting_states (upper_part \<A>))"

lemma comp_omega_automaton_alphabet: "alphabet \<A> = alphabet (comp_omega_automaton \<A>)"
  unfolding comp_omega_automaton_def by auto

theorem well_def_comp_omega_auto:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (comp_omega_automaton \<A>)"
proof - 
  let ?\<A> = "comp_omega_automaton \<A>"
  have fin: "finite (states (upper_part \<A>))" using assms well_def_upper_part unfolding auto_well_defined_def by auto
  have "finite (lower_states \<A>)" using assms finite_lower_states by blast
  hence fin_s: "finite (states ?\<A>)" using fin unfolding comp_omega_automaton_def by auto
  have "finite (alphabet \<A>)" using assms unfolding auto_well_defined_def by blast
  hence fin_a: "finite (alphabet ?\<A>)" unfolding comp_omega_automaton_def by auto  
  have "initial_state (upper_part \<A>) \<in> states (upper_part \<A>)" using assms well_def_upper_part unfolding auto_well_defined_def by blast
  hence init: "initial_state ?\<A> \<in> states ?\<A>" unfolding comp_omega_automaton_def by auto
  have acc: "accepting_states (comp_omega_automaton \<A>) \<subseteq> states (comp_omega_automaton \<A>)" using assms well_def_upper_part unfolding auto_well_defined_def comp_omega_automaton_def by auto 
  {
    fix s1 a s2 assume "(s1, a, s2) \<in> transitions ?\<A>"
    then consider (case1) "(s1, a, s2) \<in> transitions (upper_part \<A>)" | (case2) "(s1, a, s2) \<in> lower_transitions \<A>" | (case3) "(s1, a, s2) \<in> lower_transitions_from_upper \<A>" unfolding comp_omega_automaton_def by fastforce
    hence "s1 \<in> states ?\<A> \<and> a \<in> alphabet ?\<A> \<and> s2 \<in> states ?\<A>"
    proof cases
      case case1
      hence "s1 \<in> states (upper_part \<A>) \<and> a \<in> alphabet (upper_part \<A>) \<and> s2 \<in> states (upper_part \<A>)" using assms well_def_upper_part unfolding auto_well_defined_def by fast
      thus ?thesis using alphabet_upper_part unfolding comp_omega_automaton_def by force
    next
      case case2 thus ?thesis using assms lower_transitions_target_in_lower_states unfolding comp_omega_automaton_def by fastforce
    next
      case case3 thus ?thesis using assms lower_transitions_from_upper_target_in_lower_states unfolding comp_omega_automaton_def by fastforce
    qed
  }
  hence "\<forall> (s1, a, s2) \<in> transitions ?\<A> . s1 \<in> states ?\<A> \<and> a \<in> alphabet ?\<A> \<and> s2 \<in> states ?\<A>" by blast
  thus ?thesis using fin_s fin_a init acc unfolding auto_well_defined_def by blast
qed

lemma lower_step_from_upper_fst: "map fst (filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_from_upper \<A> a S))) = filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a (map fst S)))"
proof (induction S)
  case Nil thus ?case by simp
next
  case (Cons S_m S)
  let ?L = "(post_set \<A> (fst S_m) a - snd (lower_step_from_upper \<A> a S)) - accepting_states \<A>"
  let ?R = "(post_set \<A> (fst S_m) a - snd (lower_step_from_upper \<A> a S)) \<inter> accepting_states \<A>"
  let ?Lu = "(post_set \<A> (fst S_m) a - snd (upper_step \<A> a (map fst S))) - accepting_states \<A>"
  let ?Ru = "(post_set \<A> (fst S_m) a - snd (upper_step \<A> a (map fst S))) \<inter> accepting_states \<A>"
  have "snd (lower_step_from_upper \<A> a S) = snd (upper_step \<A> a (map fst S))" by (induction S) auto
  thus ?case using Cons by auto
qed

lemma lower_step_acc_fst: "map fst (filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_acc \<A> a S))) = filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a (map fst S)))"
proof (induction S)
  case Nil thus ?case by simp
next
  case (Cons S_m S)
  let ?L = "(post_set \<A> (fst S_m) a - snd (lower_step_acc \<A> a S)) - accepting_states \<A>"
  let ?R = "(post_set \<A> (fst S_m) a - snd (lower_step_acc \<A> a S)) \<inter> accepting_states \<A>"
  let ?Lu = "(post_set \<A> (fst S_m) a - snd (upper_step \<A> a (map fst S))) - accepting_states \<A>"
  let ?Ru = "(post_set \<A> (fst S_m) a - snd (upper_step \<A> a (map fst S))) \<inter> accepting_states \<A>"
  have "snd (lower_step_acc \<A> a S) = snd (upper_step \<A> a (map fst S))" by (induction S) auto
  thus ?case using Cons by auto
qed

lemma lower_step_nacc_fst: "map fst (filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_nacc \<A> a S))) = filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a (map fst S)))"
proof (induction S)
  case Nil thus ?case by simp
next
  case (Cons S_m S)
  let ?L = "(post_set \<A> (fst S_m) a - snd (lower_step_nacc \<A> a S)) - accepting_states \<A>"
  let ?R = "(post_set \<A> (fst S_m) a - snd (lower_step_nacc \<A> a S)) \<inter> accepting_states \<A>"
  let ?Lu = "(post_set \<A> (fst S_m) a - snd (upper_step \<A> a (map fst S))) - accepting_states \<A>"
  let ?Ru = "(post_set \<A> (fst S_m) a - snd (upper_step \<A> a (map fst S))) \<inter> accepting_states \<A>"
  have "snd (lower_step_nacc \<A> a S) = snd (upper_step \<A> a (map fst S))" by (induction S) auto
  thus ?case using Cons by auto
qed

lemma map_fst_state_upper_part:
  assumes "S \<in> states (upper_part \<A>)"
  shows "map fst S \<in> states (upper_part_pure \<A>)"
proof -
  have "S \<in> image (map (cross_renaming_iso 3)) (states (upper_part_pure \<A>))" using assms unfolding upper_part_def type_encode_automaton_def by simp
  then obtain T where T: "T \<in> states (upper_part_pure \<A>)" "S = map (cross_renaming_iso 3) T" by blast
  thus ?thesis using map_fst_cross_renaming_iso by metis
qed

lemma lower_transition_from_upper_projects_to_upper:
  assumes "(S, a, S') \<in> lower_transitions_from_upper \<A>"
  shows "(map fst S, a, map fst S') \<in> transitions (upper_part_pure \<A>)"
proof -
  have h: "S \<in> states (upper_part \<A>) \<and> S \<noteq> [] \<and> a \<in> alphabet \<A> \<and> S' = filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_from_upper \<A> a S)) \<and> S' \<noteq> []" using assms unfolding lower_transitions_from_upper_def by auto
  hence S_upper: "map fst S \<in> states (upper_part_pure \<A>)" using map_fst_state_upper_part by blast
  have a_alpha: "a \<in> alphabet (upper_part_pure \<A>)" using h unfolding upper_part_pure_def by auto
  have S'_eq: "map fst S' = filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a (map fst S)))" using h lower_step_from_upper_fst by simp
  have "map fst S' \<noteq> []" using h by auto
  hence "(map fst S, a, map fst S') \<in> upper_transitions \<A>" using S_upper a_alpha S'_eq unfolding upper_transitions_def upper_part_pure_def by force
  thus ?thesis unfolding upper_part_pure_def by auto
qed

lemma upper_transition_projects_to_upper_pure:
  assumes "(S, a, S') \<in> transitions (upper_part \<A>)"
  shows "(map fst S, a, map fst S') \<in> transitions (upper_part_pure \<A>)"
proof -
  have "(S, a, S') \<in> image (\<lambda>(s1, a, s2) . (map (cross_renaming_iso 3) s1, id a, map (cross_renaming_iso 3) s2)) (transitions (upper_part_pure \<A>))" using assms unfolding upper_part_def type_encode_automaton_def by simp
  then obtain s1 a' s2 where h: "(s1, a', s2) \<in> transitions (upper_part_pure \<A>)"  "(S, a, S') = (map (cross_renaming_iso 3) s1, id a', map (cross_renaming_iso 3) s2)" by fast
  hence "S = map (cross_renaming_iso 3) s1" "a = a'" "S' = map (cross_renaming_iso 3) s2" by auto
  hence "map fst S = s1 \<and> a = a' \<and> map fst S' = s2" using map_fst_cross_renaming_iso by auto
  thus ?thesis using h by auto
qed

lemma map_fst_lower_state_in_upper_states:
  assumes "S \<in> lower_states \<A>"
  shows "map fst S \<in> upper_states \<A>"
proof -
  have len1: "1 \<le> length S" using assms unfolding lower_states_def by blast
  have len2: "length S \<le> card (states \<A>)" using assms unfolding lower_states_def by blast
  have dist: "distinct S" using assms unfolding lower_states_def by blast
  have pw: "pairwise (\<lambda> S_i S_j . fst S_i \<inter> fst S_j = {}) (set S)" using assms unfolding lower_states_def by blast
  have sub: "\<forall> S_m \<in> set S . fst S_m \<subseteq> states \<A> \<and> fst S_m \<noteq> {}" using assms unfolding lower_states_def by blast
  have dist_map: "distinct (map fst S)"
  proof (rule ccontr)
    assume "\<not> distinct (map fst S)"
    then obtain i j where ij: "i < length S" "j < length S" "i \<noteq> j" "fst (S ! i) = fst (S ! j)" using dist distinct_conv_nth length_map nth_map by (metis (mono_tags, lifting))
    hence Si_ne: "fst (S ! i) \<noteq> {}"  using sub by auto
    have Si_in: "S ! i \<in> set S" using ij by auto
    have Sj_in: "S ! j \<in> set S" using ij by auto
    have "S ! i \<noteq> S ! j" using ij dist nth_eq_iff_index_eq by fast
    hence "fst (S ! i) \<inter> fst (S ! j) = {}" using pw Si_in Sj_in unfolding pairwise_def by blast
    thus False using ij Si_ne by auto
  qed
  have pw_map: "pairwise (\<lambda> A B . A \<inter> B = {}) (set (map fst S))" using pw unfolding pairwise_def by fastforce
  have "\<forall> S_m \<in> set (map fst S) . S_m \<subseteq> states \<A> \<and> S_m \<noteq> {}" using sub by auto
  thus ?thesis using len1 len2 dist_map pw_map unfolding upper_states_def by auto
qed

lemma lower_transition_projects_to_upper:
  assumes "(S, a, S') \<in> lower_transitions \<A>"
  shows "(map fst S, a, map fst S') \<in> transitions (upper_part_pure \<A>)"
proof (cases "lower_accepting S")
  case True
  hence h: "S \<in> lower_states \<A> \<and> a \<in> alphabet \<A> \<and> S' = filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_acc \<A> a S)) \<and> S' \<noteq> []" using assms unfolding lower_transitions_def by auto
  hence S_upper: "map fst S \<in> states (upper_part_pure \<A>)" using map_fst_lower_state_in_upper_states unfolding upper_part_pure_def by auto
  have a_alpha: "a \<in> alphabet (upper_part_pure \<A>)" using h unfolding upper_part_pure_def by auto
  have S'_eq: "map fst S' = filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a (map fst S)))" using h lower_step_acc_fst by simp
  have "map fst S' \<noteq> []" using h by auto
  hence "(map fst S, a, map fst S') \<in> upper_transitions \<A>" using S_upper a_alpha S'_eq unfolding upper_transitions_def upper_part_pure_def by force
  thus ?thesis unfolding upper_part_pure_def by auto
next
  case False
  hence h: "S \<in> lower_states \<A> \<and> a \<in> alphabet \<A> \<and> S' = filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_nacc \<A> a S)) \<and> S' \<noteq> []" using assms unfolding lower_transitions_def by auto
  hence S_upper: "map fst S \<in> states (upper_part_pure \<A>)" using map_fst_lower_state_in_upper_states unfolding upper_part_pure_def by auto
  have a_alpha: "a \<in> alphabet (upper_part_pure \<A>)" using h unfolding upper_part_pure_def by auto
  have S'_eq: "map fst S' = filter (\<lambda>S_m. S_m \<noteq> {}) (fst (upper_step \<A> a (map fst S)))" using h lower_step_nacc_fst by simp
  have "map fst S' \<noteq> []" using h by auto
  hence "(map fst S, a, map fst S') \<in> upper_transitions \<A>" using S_upper a_alpha S'_eq unfolding upper_transitions_def upper_part_pure_def by force
  thus ?thesis unfolding upper_part_pure_def by auto
qed

lemma comp_transition_projects_to_upper:
  assumes "(S, a, S') \<in> transitions (comp_omega_automaton \<A>)"
  shows "(map fst S, a, map fst S') \<in> transitions (upper_part_pure \<A>)"
proof -
  have "(S, a, S') \<in> transitions (upper_part \<A>) \<or> (S, a, S') \<in> lower_transitions \<A> \<or> (S, a, S') \<in> lower_transitions_from_upper \<A>" using assms unfolding comp_omega_automaton_def by auto
  then consider (case1) "(S, a, S') \<in> transitions (upper_part \<A>)" | (case2) "(S, a, S') \<in> lower_transitions \<A>" | (case3) "(S, a, S') \<in> lower_transitions_from_upper \<A>" by fast
  thus ?thesis
  proof cases
    case case1 thus ?thesis using upper_transition_projects_to_upper_pure by fast
  next
    case case2 thus ?thesis using lower_transition_projects_to_upper by fast
  next
    case case3 thus ?thesis using lower_transition_from_upper_projects_to_upper by fast
  qed
qed

definition upper_proj_run :: "(('s states \<times> nat) list) omega_run \<Rightarrow> 's states list omega_run" where "upper_proj_run rc = (map fst) \<circ> rc"

proposition comp_run_projects_to_upper_pure:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x"
  shows "omega_run_well_defined (upper_proj_run rc) (upper_part_pure \<A>) x"
proof -
  have "rc 0 = initial_state (comp_omega_automaton \<A>)" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
  hence "upper_proj_run rc 0 = map fst (initial_state (comp_omega_automaton \<A>))" unfolding upper_proj_run_def by simp
  hence rc_0: "upper_proj_run rc 0 = map fst (initial_state (upper_part \<A>))" unfolding comp_omega_automaton_def by simp
  have map_init: "map fst (initial_state (upper_part \<A>)) = initial_state (upper_part_pure \<A>)" unfolding upper_part_def type_encode_automaton_def upper_part_pure_def cross_renaming_iso_def by simp
  hence init: "upper_proj_run rc 0 = initial_state (upper_part_pure \<A>)" using rc_0 by auto
  have st0: "initial_state (upper_part_pure \<A>) \<in> states (upper_part_pure \<A>)" using assms well_def_upper_part_pure unfolding auto_well_defined_def by blast
  {
    fix n
    have "(rc n, x n, rc (Suc n)) \<in> transitions (comp_omega_automaton \<A>)" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
    hence "(upper_proj_run rc n, x n, upper_proj_run rc (Suc n)) \<in> transitions (upper_part_pure \<A>)" using comp_transition_projects_to_upper unfolding upper_proj_run_def by simp
  }
  thus ?thesis using init st0  unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by simp
qed

lemma upper_child_up_proj_iff: "upper_child_up p a \<A> q j k \<longleftrightarrow> upper_child (map fst p) a \<A> (map fst q) j k" unfolding upper_child_up_def upper_child_def by auto

lemma upper_child_segment_up_proj_iff: "upper_child_segment_up rc i N x \<A> j k \<longleftrightarrow> upper_child_segment (upper_proj_run rc) i N x \<A> j k"
proof -
  {
    assume  "upper_child_segment_up rc i N x \<A> j k"
    then obtain js where js: "length js = N - i + 1" "js ! 0 = j""last js = k" "\<forall> m < N - i . upper_child_up (rc (i + m)) (x (i + m)) \<A> (rc (i + Suc m)) (js ! m) (js ! Suc m)" unfolding upper_child_segment_up_def by blast
    hence "\<forall> m < N - i . upper_child ((upper_proj_run rc) (i + m)) (x (i + m)) \<A> ((upper_proj_run rc) (i + Suc m)) (js ! m) (js ! Suc m)" using upper_child_up_proj_iff unfolding upper_proj_run_def by fastforce
    hence "upper_child_segment (upper_proj_run rc) i N x \<A> j k" using js unfolding upper_child_segment_def by blast
  }
  hence left: "upper_child_segment_up rc i N x \<A> j k \<Longrightarrow> upper_child_segment (upper_proj_run rc) i N x \<A> j k" by blast
  {
    assume "upper_child_segment (upper_proj_run rc) i N x \<A> j k"
    then obtain js where js: "length js = N - i + 1" "js ! 0 = j" "last js = k" "\<forall> m < N - i . upper_child ((upper_proj_run rc) (i + m)) (x (i + m)) \<A> ((upper_proj_run rc) (i + Suc m)) (js ! m) (js ! Suc m)" unfolding upper_child_segment_def by blast
    hence "\<forall> m < N - i . upper_child_up (rc (i + m)) (x (i + m)) \<A> (rc (i + Suc m)) (js ! m) (js ! Suc m)" using upper_child_up_proj_iff unfolding upper_proj_run_def by fastforce
    hence "upper_child_segment_up rc i N x \<A> j k" using js unfolding upper_child_segment_up_def by blast
  }
  thus ?thesis using left by blast
qed

lemma upper_continued_up_proj_iff: "upper_continued_up rc \<A> x i j \<longleftrightarrow> upper_continued (upper_proj_run rc) \<A> x i j" using upper_child_segment_up_proj_iff unfolding upper_continued_up_def upper_continued_def by blast

lemma upper_continued_F_up_proj_iff: "upper_continued_F_up rc \<A> x i j \<longleftrightarrow> upper_continued_F (upper_proj_run rc) \<A> x i j"
proof -
  {
    assume "upper_continued_F_up rc \<A> x i j"
    hence cont: "upper_continued_up rc \<A> x i j \<and> fst (rc i ! j) \<subseteq> accepting_states \<A>" unfolding upper_continued_F_up_def by blast
    hence cont': "upper_continued (upper_proj_run rc) \<A> x i j" using upper_continued_up_proj_iff by blast
    hence "j < length ((upper_proj_run rc) i)" using upper_continued_index by blast
    hence "fst (rc i ! j) = (upper_proj_run rc) i ! j" unfolding upper_proj_run_def by simp
    hence "(upper_proj_run rc i ! j) \<subseteq> accepting_states \<A>" using cont by simp
    hence "upper_continued_F (upper_proj_run rc) \<A> x i j" using cont' unfolding upper_continued_F_def by blast
  }
  hence left: "upper_continued_F_up rc \<A> x i j \<Longrightarrow> upper_continued_F (upper_proj_run rc) \<A> x i j" by blast
  {
    assume "upper_continued_F (upper_proj_run rc) \<A> x i j"
    hence cont: "upper_continued (upper_proj_run rc) \<A> x i j \<and> (upper_proj_run rc) i ! j \<subseteq> accepting_states \<A>" unfolding upper_continued_F_def by blast
    hence cont': "upper_continued_up rc \<A> x i j" using upper_continued_up_proj_iff by blast
    have "j < length ((upper_proj_run rc) i)" using cont upper_continued_index by blast
    hence "fst (rc i ! j) = (upper_proj_run rc) i ! j" unfolding upper_proj_run_def by simp
    hence "fst (rc i ! j) \<subseteq> accepting_states \<A>" using cont by simp
    hence "upper_continued_F_up rc \<A> x i j" using cont' unfolding upper_continued_F_up_def by blast
  }
  thus ?thesis using left by blast
qed

lemma upper_slice_continued_F_up_proj_iff: "upper_slice_continued_F_up rc \<A> x i \<longleftrightarrow> upper_slice_continued_F (upper_proj_run rc) \<A> x i"
proof -
  {
    assume "upper_slice_continued_F_up rc \<A> x i"
    then obtain j where j: "j < length (rc i)" "upper_continued_F_up rc \<A> x i j" unfolding upper_slice_continued_F_up_def by blast
    hence less: "j < length ((upper_proj_run rc) i)" unfolding upper_proj_run_def by simp
    have "upper_continued_F (upper_proj_run rc) \<A> x i j" using j upper_continued_F_up_proj_iff by blast
    hence "upper_slice_continued_F (upper_proj_run rc) \<A> x i" using less unfolding upper_slice_continued_F_def by blast
  }
  hence left: "upper_slice_continued_F_up rc \<A> x i \<Longrightarrow> upper_slice_continued_F (upper_proj_run rc) \<A> x i" by blast
  {
    assume "upper_slice_continued_F (upper_proj_run rc) \<A> x i"
    then obtain j where j: "j < length ((upper_proj_run rc) i)" "upper_continued_F (upper_proj_run rc) \<A> x i j" unfolding upper_slice_continued_F_def by blast
    hence less: "j < length (rc i)" unfolding upper_proj_run_def by simp
    have "upper_continued_F_up rc \<A> x i j" using j upper_continued_F_up_proj_iff by blast
    hence "upper_slice_continued_F_up rc \<A> x i" using less unfolding upper_slice_continued_F_up_def by blast
  }
  thus ?thesis using left by blast
qed

lemma state_in_upper_part_has_color_3:
  assumes "S \<in> states (upper_part \<A>)"
  shows "\<forall> x \<in> set S . snd x = 3"
  using assms unfolding upper_part_def type_encode_automaton_def cross_renaming_iso_def by force

lemma upper_and_lower_states_disjoint: "states (upper_part \<A>) \<inter> lower_states \<A> = {}"
proof(rule ccontr)
  assume "states (upper_part \<A>) \<inter> lower_states \<A> \<noteq> {}"
  then obtain S where S: "S \<in> states (upper_part \<A>)" "S \<in> lower_states \<A>" by blast
  have up: "\<forall> x \<in> set S . snd x = 3" using state_in_upper_part_has_color_3[OF S(1)] by blast
  have low: "\<forall> x \<in> set S . snd x \<in> {0,1,2}" using S(2) unfolding lower_states_def by blast
  have "S \<noteq> []" using S(2) unfolding lower_states_def by auto
  then obtain x where "x \<in> set S" using empty_iff in_listsI insert_iff lists_empty by metis
  hence "snd x = 3 \<and> snd x \<in> {0,1,2}" using up low by blast
  thus False by auto
qed

lemma comp_run_lower_step_stays_lower:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "rc i \<in> lower_states \<A>"
  shows "rc (Suc i) \<in> lower_states \<A>"
proof(rule ccontr)
  assume assm: "rc (Suc i) \<notin> lower_states \<A>"
  have "(rc i, x i, rc (Suc i)) \<in> transitions (comp_omega_automaton \<A>)" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
  hence "(rc i, x i, rc (Suc i)) \<in> transitions (upper_part \<A>) \<or> (rc i, x i, rc (Suc i)) \<in> lower_transitions \<A> \<or> (rc i, x i, rc (Suc i)) \<in> lower_transitions_from_upper \<A>" unfolding comp_omega_automaton_def by auto
  then consider (case1) "(rc i, x i, rc (Suc i)) \<in> transitions (upper_part \<A>)" | (case2) "(rc i, x i, rc (Suc i)) \<in> lower_transitions \<A>" | (case3) "(rc i, x i, rc (Suc i)) \<in> lower_transitions_from_upper \<A>" by fast
  thus False
  proof cases
    case case1
    hence "rc i \<in> states (upper_part \<A>) \<inter> lower_states \<A>" using assms well_def_upper_part well_def_trans_components by fast
    thus ?thesis using upper_and_lower_states_disjoint by blast
  next
    case case2 thus ?thesis using lower_transitions_target_in_lower_states[of \<A> "rc i" "x i" "rc (Suc i)"] assms assm by blast
  next
    case case3 thus ?thesis using assms upper_and_lower_states_disjoint unfolding lower_transitions_from_upper_def by fast
  qed
qed

lemma comp_run_stays_in_lower_after_entry:
  assumes "auto_well_defined \<A>"
  shows "omega_run_well_defined rc (comp_omega_automaton \<A>) x \<and> rc i \<in> lower_states \<A> \<and> i \<le> j \<Longrightarrow> rc j \<in> lower_states \<A>"
proof (induction "j - i" arbitrary: j)
  case 0 thus ?case by auto
next
  case (Suc d)
  then obtain j' where j': "j = Suc j'" by (cases j) auto
  hence "rc j' \<in> lower_states \<A>" using Suc by simp
  hence "rc (Suc j') \<in> lower_states \<A>" using assms comp_run_lower_step_stays_lower Suc by blast
  thus ?case using j' by simp
qed

lemma upper_slice_continued_F_up_proj_infinite_iff: "infinite {i . upper_slice_continued_F_up rc \<A> x i} \<longleftrightarrow> infinite {i . upper_slice_continued_F (upper_proj_run rc) \<A> x i}"
proof - 
  have "{i . upper_slice_continued_F_up rc \<A> x i} = {i . upper_slice_continued_F (upper_proj_run rc) \<A> x i}" using upper_slice_continued_F_up_proj_iff by blast
  thus ?thesis by argo
qed

lemma comp_run_acceptance_criterion_via_projection:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "\<forall> n . rc n \<noteq> []"
  shows "x \<in> omega_language_auto \<A> \<longleftrightarrow> infinite {i . upper_slice_continued_F_up rc \<A> x i}"
proof -
  let ?Runp = "upper_proj_run rc"
  let ?Run = "enc_upper_run ?Runp"
  have proj_wd: "omega_run_well_defined ?Runp (upper_part_pure \<A>) x" using comp_run_projects_to_upper_pure[OF assms(1,2)] by blast
  have upper_wd: "auto_well_defined (upper_part \<A>)"  using well_def_upper_part[OF assms(1)] by blast
  have run_wd: "omega_run_well_defined ?Run (upper_part \<A>) x" using omega_run_well_defined_upper_part_transport[OF assms(1) proj_wd] by blast
  hence word_wd: "omega_word_well_defined x (alphabet (upper_part \<A>))" using upper_wd well_def_implies_omega_word_well_defined unfolding omega_run_well_defined_def by fast
  have upper_dfa: "DFA_property (upper_part \<A>)" using DFA_upper_part[OF assms(1)] by blast
  have uniq: "\<exists>! Run . omega_run_well_defined Run (upper_part \<A>) x" using exists_only_one_omega_run_for_DFA[OF upper_wd upper_dfa word_wd] by blast
  have "\<forall> n . ?Runp n \<noteq> []" using assms(3) unfolding upper_proj_run_def by auto
  hence run_ne: "\<forall> n . ?Run n \<noteq> []" using upper_part_transport_nonempty_all[of ?Runp] unfolding enc_upper_run_def by blast
  have "infinite {i . upper_slice_continued_F_up ?Run \<A> x i} \<longleftrightarrow> infinite {i . upper_slice_continued_F ?Runp \<A> x i}" using upper_slice_continued_F_up_enc_iff Collect_cong by metis
  hence "infinite {i . upper_slice_continued_F_up ?Run \<A> x i} \<longleftrightarrow> infinite {i . upper_slice_continued_F_up rc \<A> x i}" using upper_slice_continued_F_up_proj_infinite_iff by blast
  hence run_tf_iff: "infinite {i . upper_slice_continued_F_up ?Run \<A> x i} \<longleftrightarrow> infinite {i . upper_slice_continued_F_up rc \<A> x i}" by blast
  {
    assume "x \<in> omega_language_auto \<A>"
    then obtain Run' where Run': "omega_run_well_defined Run' (upper_part \<A>) x" "\<forall> n . Run' n \<noteq> []" "infinite {i . upper_slice_continued_F_up Run' \<A> x i}" using cor_3_4_15[OF assms(1)] by blast
    have "Run' = ?Run" using uniq Run'(1) run_wd by blast
    hence "infinite {i . upper_slice_continued_F_up rc \<A> x i}" using Run'(3) run_tf_iff by simp
  }
  hence left: "x \<in> omega_language_auto \<A> \<Longrightarrow> infinite {i . upper_slice_continued_F_up rc \<A> x i}" by blast
  {
    assume "infinite {i . upper_slice_continued_F_up rc \<A> x i}"
    hence "infinite {i . upper_slice_continued_F_up ?Run \<A> x i}" using run_tf_iff by blast
    hence "omega_run_well_defined ?Run (upper_part \<A>) x \<and> (\<forall> n . ?Run n \<noteq> []) \<and> infinite {i . upper_slice_continued_F_up ?Run \<A> x i}" using run_wd run_ne by blast
    hence "x \<in> omega_language_auto \<A>" using cor_3_4_15[OF assms(1)] by blast
  }
  thus ?thesis using left by blast
qed

lemma comp_run_staying_upper_is_upper_run:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "\<forall> n . rc n \<in> states (upper_part \<A>)"
  shows "omega_run_well_defined rc (upper_part \<A>) x"
proof -
  have init: "rc 0 = initial_state (upper_part \<A>)" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def comp_omega_automaton_def by simp
  hence init_in: "initial_state (upper_part \<A>) \<in> states (upper_part \<A>)" using assms by metis
  {
    fix n
    have step: "(rc n, x n, rc (Suc n)) \<in> transitions (comp_omega_automaton \<A>)" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
    have up_n: "rc n \<in> states (upper_part \<A>)" using assms by blast
    have up_suc: "rc (Suc n) \<in> states (upper_part \<A>)" using assms by blast
    have not_low_n: "rc n \<notin> lower_states \<A>" using up_n upper_and_lower_states_disjoint by blast
    have not_low_suc: "rc (Suc n) \<notin> lower_states \<A>" using up_suc upper_and_lower_states_disjoint by blast
    have "(rc n, x n, rc (Suc n)) \<in> transitions (upper_part \<A>) \<or> (rc n, x n, rc (Suc n)) \<in> lower_transitions \<A> \<or> (rc n, x n, rc (Suc n)) \<in> lower_transitions_from_upper \<A>" using step unfolding comp_omega_automaton_def by auto
    then consider (case1) "(rc n, x n, rc (Suc n)) \<in> transitions (upper_part \<A>)" | (case2) "(rc n, x n, rc (Suc n)) \<in> lower_transitions \<A>" | (case3) "(rc n, x n, rc (Suc n)) \<in> lower_transitions_from_upper \<A>" by fast
    hence "(rc n, x n, rc (Suc n)) \<in> transitions (upper_part \<A>)"
    proof cases
      case case1 thus ?thesis by blast
    next
      case case2
      hence "rc n \<in> lower_states \<A>"  unfolding lower_transitions_def by fast
      thus ?thesis using not_low_n by blast
    next
      case case3
      hence "rc (Suc n) \<in> lower_states \<A>" using assms lower_transitions_from_upper_target_in_lower_states by fast
      thus ?thesis using not_low_suc by blast
    qed
  }
  hence "\<forall> n . (rc n, x n, rc (Suc n)) \<in> transitions (upper_part \<A>)" by blast
  thus ?thesis unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def using init init_in by auto
qed

lemma comp_run_upper_case_not_accepting:
  assumes "auto_well_defined \<A>" "x \<in> omega_language_auto \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "\<forall> n . rc n \<in> states (upper_part \<A>)"
  shows "\<not> omega_run_accepting rc (comp_omega_automaton \<A>) x"
proof(rule ccontr)
  assume"\<not> \<not> omega_run_accepting rc (comp_omega_automaton \<A>) x"
  hence acc: "omega_run_accepting rc (comp_omega_automaton \<A>) x" by blast
  have upper_wd: "omega_run_well_defined rc (upper_part \<A>) x" using comp_run_staying_upper_is_upper_run assms by blast
  have dec_wd: "omega_run_well_defined (dec_upper_run \<A> rc) (upper_part_pure \<A>) x" using omega_run_well_defined_upper_part_transport_back[OF assms(1) upper_wd] by blast
  obtain r where r: "omega_run_well_defined r \<A> x" using assms unfolding omega_language_auto_def omega_run_accepting_def by blast
  hence "\<forall> n . (dec_upper_run \<A> rc) n \<noteq> []" using not_empty_omega_run[OF assms(1) r dec_wd] by blast
  hence nonempty_rc: "\<forall> n . rc n \<noteq> []" using upper_part_transport_nonempty_all_back[OF assms(1) upper_wd] by blast
  {
    fix n
    have in_states: "rc n \<in> states (upper_part \<A>)" using assms by blast
    have "rc n \<noteq> []" using nonempty_rc by blast
    hence "rc n \<notin> accepting_states (comp_omega_automaton \<A>)" using upper_and_lower_states_disjoint in_states unfolding comp_omega_automaton_def upper_part_def type_encode_automaton_def upper_part_pure_def by force
  }
  hence never_acc: "\<forall> n . rc n \<notin> accepting_states (comp_omega_automaton \<A>)" by blast
  thus False using acc unfolding omega_run_accepting_def by blast
qed

lemma lower_step_from_upper_raw_accepting_component_has_color2:
  assumes "X \<in> set (fst (lower_step_from_upper \<A> a S))" "fst X \<subseteq> accepting_states \<A>" "fst X \<noteq> {}"
  shows "snd X = 2"
using assms proof (induction S arbitrary: X)
  case Nil thus ?case by simp
next
  case (Cons Sm S)
  let ?L = "(post_set \<A> (fst Sm) a - snd (lower_step_from_upper \<A> a S)) - accepting_states \<A>"
  let ?R = "(post_set \<A> (fst Sm) a - snd (lower_step_from_upper \<A> a S)) \<inter> accepting_states \<A>"
  have "X = (?L, 0) \<or> X = (?R, 2) \<or> X \<in> set (fst (lower_step_from_upper \<A> a S))" using Cons by simp
  then consider (case1) "X = (?L, 0)" | (case2) "X = (?R, 2)" | (case3) "X \<in> set (fst (lower_step_from_upper \<A> a S))" by fast
  thus ?case
  proof cases
    case case1 thus ?thesis using Cons by auto
  next
    case case2 thus ?thesis by simp
  next
    case case3 thus ?thesis using Cons by blast
  qed
qed

lemma lower_from_upper_target_accepting_component_has_color2:
  assumes "(S, a, S') \<in> lower_transitions_from_upper \<A>" "j < length S'" "fst (S' ! j) \<subseteq> accepting_states \<A>"
  shows "snd (S' ! j) = 2"
proof -
  have S_def: "S' = filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_from_upper \<A> a S))" using assms unfolding lower_transitions_from_upper_def by blast
  have in_filt: "S' ! j \<in> set S'" using assms(2) by auto
  hence in_raw: "S' ! j \<in> set (fst (lower_step_from_upper \<A> a S))" using S_def by auto
  have nz: "fst (S' ! j) \<noteq> {}" using in_filt S_def by auto
  show ?thesis using lower_step_from_upper_raw_accepting_component_has_color2[OF in_raw assms(3) nz] by blast
qed

lemma lower_step_acc_raw_accepting_component_has_color2:
  assumes "X \<in> set (fst (lower_step_acc \<A> a S))" "fst X \<subseteq> accepting_states \<A>" "fst X \<noteq> {}"
  shows "snd X = 2"
using assms proof (induction S arbitrary: X)
  case Nil thus ?case by simp
next
  case (Cons Sm S)
  let ?L = "((post_set \<A> (fst Sm) a - snd (lower_step_acc \<A> a S)) - accepting_states \<A>, min (2 * snd Sm) 2)"
  let ?R = "((post_set \<A> (fst Sm) a - snd (lower_step_acc \<A> a S)) \<inter> accepting_states \<A>, 2)"
  have "X = ?L \<or> X = ?R \<or> X \<in> set (fst (lower_step_acc \<A> a S))" using Cons by simp
  then consider (case1) "X = ?L" | (case2) "X = ?R" | (case3) "X \<in> set (fst (lower_step_acc \<A> a S))" by fast
  thus ?case
  proof cases
    case case1 thus ?thesis using Cons by auto
  next
    case case2 thus ?thesis by simp
  next
    case case3 thus ?thesis using Cons by blast
  qed
qed

lemma lower_step_nacc_raw_accepting_component_has_color12:
  assumes "X \<in> set (fst (lower_step_nacc \<A> a S))" "fst X \<subseteq> accepting_states \<A>" "fst X \<noteq> {}" "\<forall> S_m \<in> set S . snd S_m \<in> {0,1,2}"
  shows "snd X = 1 \<or> snd X = 2"
using assms proof (induction S arbitrary: X)
  case Nil thus ?case by simp
next
  case (Cons Sm S)
  let ?L = "((post_set \<A> (fst Sm) a - snd (lower_step_nacc \<A> a S)) - accepting_states \<A>, snd Sm)"
  let ?R = "((post_set \<A> (fst Sm) a - snd (lower_step_nacc \<A> a S)) \<inter> accepting_states \<A>, max (snd Sm) 1)"
  have "X = ?L \<or> X = ?R \<or> X \<in> set (fst (lower_step_nacc \<A> a S))" using Cons by simp
  then consider (case1) "X = ?L" | (case2) "X = ?R" | (case3) "X \<in> set (fst (lower_step_nacc \<A> a S))" by fast
  thus ?case
  proof cases
    case case1 thus ?thesis using Cons by auto
  next
    case case2
    have "snd Sm \<in> {0,1,2}" using Cons by auto
    hence "max (snd Sm) 1 = 1 \<or> max (snd Sm) 1 = 2" by auto
    thus ?thesis using case2 by simp
  next
    case case3 thus ?thesis using case3 Cons by simp
  qed
qed

lemma lower_target_accepting_component_has_color12:
  assumes "(S, a, S') \<in> lower_transitions \<A>" "j < length S'" "fst (S' ! j) \<subseteq> accepting_states \<A>"
  shows "snd (S' ! j) = 1 \<or> snd (S' ! j) = 2"
proof(cases "lower_accepting S")
  case True
  hence S_def: "S' = filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_acc \<A> a S))" using assms unfolding lower_transitions_def by auto
  have in_filt: "S' ! j \<in> set S'" using assms by auto
  hence in_raw: "S' ! j \<in> set (fst (lower_step_acc \<A> a S))" using S_def by auto
  have nz: "fst (S' ! j) \<noteq> {}" using in_filt S_def by auto
  thus ?thesis using lower_step_acc_raw_accepting_component_has_color2[OF in_raw assms(3) nz] by blast
next
  case False
  hence S_def: "S' = filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_nacc \<A> a S))" using assms unfolding lower_transitions_def by auto
  have in_filt: "S' ! j \<in> set S'" using assms by auto
  hence in_raw: "S' ! j \<in> set (fst (lower_step_nacc \<A> a S))" using S_def by auto
  have nz: "fst (S' ! j) \<noteq> {}" using in_filt S_def by auto
  have colors: "\<forall> S_m \<in> set S . snd S_m \<in> {0,1,2}" using assms False unfolding lower_transitions_def lower_states_def by auto
  thus ?thesis using lower_step_nacc_raw_accepting_component_has_color12[OF in_raw assms(3) nz colors] by blast
qed

lemma upper_continued_F_up_in_lower_implies_color12:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "rc i \<in> lower_states \<A>" "upper_continued_F_up rc \<A> x i j"
  shows "snd (rc i ! j) = 1 \<or> snd (rc i ! j) = 2"
proof -
  have jlt: "j < length (rc i)" using assms(4) upper_continued_up_index unfolding upper_continued_F_up_def by blast
  have acc_fst: "fst (rc i ! j) \<subseteq> accepting_states \<A>" using assms(4) unfolding upper_continued_F_up_def by blast
  have i_pos: "i > 0"
  proof (rule ccontr)
    assume "\<not> i > 0"
    hence i0: "i = 0" by simp
    have "rc 0 = initial_state (comp_omega_automaton \<A>)" using assms(2) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by blast
    hence "rc i \<in> states (upper_part \<A>)" using i0 assms(1) well_def_upper_part unfolding comp_omega_automaton_def auto_well_defined_def by auto
    thus False using assms upper_and_lower_states_disjoint by blast
  qed
  obtain p where p: "i = Suc p" using i_pos by (cases i) auto
  hence "(rc p, x p, rc i) \<in> transitions (comp_omega_automaton \<A>)" using assms(2) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
  hence "(rc p, x p, rc i) \<in> transitions (upper_part \<A>) \<or> (rc p, x p, rc i) \<in> lower_transitions \<A> \<or> (rc p, x p, rc i) \<in> lower_transitions_from_upper \<A>" unfolding comp_omega_automaton_def by auto
  then consider (up) "(rc p, x p, rc i) \<in> transitions (upper_part \<A>)" | (low) "(rc p, x p, rc i) \<in> lower_transitions \<A>" | (jump) "(rc p, x p, rc i) \<in> lower_transitions_from_upper \<A>" by fast
  thus ?thesis
  proof cases
    case up
    hence "rc i \<in> states (upper_part \<A>)" using assms(1) well_def_upper_part unfolding auto_well_defined_def by blast
    thus ?thesis using assms upper_and_lower_states_disjoint by blast
  next
    case low thus ?thesis using lower_target_accepting_component_has_color12[OF low jlt acc_fst] by blast
  next
    case jump thus ?thesis using lower_from_upper_target_accepting_component_has_color2[OF jump jlt acc_fst] by blast
  qed
qed

lemma lower_step_acc_snd_eq_upper_step: "snd (lower_step_acc \<A> a S) = snd (upper_step \<A> a (map fst S))" by (induction S) auto

lemma lower_step_nacc_snd_eq_upper_step: "snd (lower_step_nacc \<A> a S) = snd (upper_step \<A> a (map fst S))" by (induction S) auto

lemma lower_step_acc_child_color2_preserved_head:
  assumes "X \<in> set (fst (lower_step_acc \<A> a (Sm # S)))" "fst X \<subseteq> post_set \<A> (fst Sm) a" "fst X \<inter> snd (upper_step \<A> a (map fst S)) = {}" "snd Sm = 2" "fst X \<noteq> {}"
  shows "snd X = 2"
proof -
  let ?L = "((post_set \<A> (fst Sm) a - snd (lower_step_acc \<A> a S)) - accepting_states \<A>, min (2 * snd Sm) 2)"
  let ?R = "((post_set \<A> (fst Sm) a - snd (lower_step_acc \<A> a S)) \<inter> accepting_states \<A>, 2)"
  have "X = ?L \<or> X = ?R \<or> X \<in> set (fst (lower_step_acc \<A> a S))" using assms(1) by simp
  then consider "X = ?L" | "X = ?R" | "X \<in> set (fst (lower_step_acc \<A> a S))" by fast
  thus ?thesis
  proof cases
    case 1 thus ?thesis using assms(4) by simp
  next
    case 2 thus ?thesis by simp
  next
    case 3
    hence "fst X \<subseteq> snd (lower_step_acc \<A> a S)" using lower_step_acc_fst_subset_snd by fast
    hence "fst X \<subseteq> snd (upper_step \<A> a (map fst S))" using lower_step_acc_snd_eq_upper_step by fast
    hence "fst X = {}" using assms(3) by blast
    thus ?thesis using assms(5) by blast
  qed
qed

lemma lower_step_nacc_child_color2_preserved_head:
  assumes "X \<in> set (fst (lower_step_nacc \<A> a (Sm # S)))" "fst X \<subseteq> post_set \<A> (fst Sm) a" "fst X \<inter> snd (upper_step \<A> a (map fst S)) = {}" "snd Sm = 2" "fst X \<noteq> {}"
  shows "snd X = 2"
proof -
  let ?L = "((post_set \<A> (fst Sm) a - snd (lower_step_nacc \<A> a S)) - accepting_states \<A>, snd Sm)"
  let ?R = "((post_set \<A> (fst Sm) a - snd (lower_step_nacc \<A> a S)) \<inter> accepting_states \<A>, max (snd Sm) 1)"
  have "X = ?L \<or> X = ?R \<or> X \<in> set (fst (lower_step_nacc \<A> a S))" using assms(1) by simp
  then consider "X = ?L" | "X = ?R" | "X \<in> set (fst (lower_step_nacc \<A> a S))" by fast
  thus ?thesis
  proof cases
    case 1 thus ?thesis using assms(4) by simp
  next
    case 2 thus ?thesis using assms(4) by simp
  next
    case 3
    hence "fst X \<subseteq> snd (lower_step_nacc \<A> a S)" using lower_step_nacc_fst_subset_snd by fast
    hence "fst X \<subseteq> snd (upper_step \<A> a (map fst S))" using lower_step_nacc_snd_eq_upper_step by fast
    hence "fst X = {}" using assms(3) by blast
    thus ?thesis using assms(5) by blast
  qed
qed

lemma lower_step_acc_drop_child_color2_preserved:
  assumes "X \<in> set (fst (lower_step_acc \<A> a (drop j S)))" "j < length S" "fst X \<subseteq> post_set \<A> (fst (S ! j)) a" "fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}" "snd (S ! j) = 2" "fst X \<noteq> {}"
  shows "snd X = 2"
proof -
  have drop_decomp: "drop j S = S ! j # drop (Suc j) S" using assms(2) by (simp add: Cons_nth_drop_Suc)
  have "map fst (drop (Suc j) S) = drop (Suc j) (map fst S)" by (simp add: drop_map)
  thus ?thesis using lower_step_acc_child_color2_preserved_head[of X \<A> a "S ! j" "drop (Suc j) S"] assms drop_decomp by argo
qed

lemma lower_step_nacc_drop_child_color2_preserved:
  assumes "X \<in> set (fst (lower_step_nacc \<A> a (drop j S)))" "j < length S" "fst X \<subseteq> post_set \<A> (fst (S ! j)) a" "fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}" "snd (S ! j) = 2" "fst X \<noteq> {}"
  shows "snd X = 2"
proof -
  have drop_decomp: "drop j S = S ! j # drop (Suc j) S" using assms(2) by (simp add: Cons_nth_drop_Suc)
  have "map fst (drop (Suc j) S) = drop (Suc j) (map fst S)" by (simp add: drop_map)
  thus ?thesis using lower_step_nacc_child_color2_preserved_head[ of X \<A> a "S ! j" "drop (Suc j) S"] assms drop_decomp by argo
qed

lemma lower_step_acc_snd_append: "snd (lower_step_acc \<A> a (X @ Y)) = snd (lower_step_acc \<A> a X) \<union> snd (lower_step_acc \<A> a Y)"
  by (induction X) auto

lemma lower_step_nacc_snd_append: "snd (lower_step_nacc \<A> a (X @ Y)) = snd (lower_step_nacc \<A> a X) \<union> snd (lower_step_nacc \<A> a Y)"
  by (induction X) auto

lemma lower_step_acc_fst_append: "fst (lower_step_acc \<A> a (X @ Y)) = map (\<lambda>P . (fst P - snd (lower_step_acc \<A> a Y), snd P)) (fst (lower_step_acc \<A> a X)) @ fst (lower_step_acc \<A> a Y)"
proof (induction X)
  case Nil thus ?case by simp
next
  case (Cons Sm X) thus ?case using lower_step_acc_snd_append[of \<A> a X Y] by auto
qed

lemma lower_step_nacc_fst_append: "fst (lower_step_nacc \<A> a (X @ Y)) = map (\<lambda>P . (fst P - snd (lower_step_nacc \<A> a Y), snd P)) (fst (lower_step_nacc \<A> a X)) @ fst (lower_step_nacc \<A> a Y)"
proof (induction X)
  case Nil thus ?case by simp
next
  case (Cons Sm X) thus ?case using lower_step_nacc_snd_append[of \<A> a X Y] by auto
qed

lemma lower_step_acc_child_raw_in_drop:
  assumes "X \<in> set (fst (lower_step_acc \<A> a S))" "j < length S" "fst X \<subseteq> post_set \<A> (fst (S ! j)) a" "fst X \<noteq> {}"
  shows "X \<in> set (fst (lower_step_acc \<A> a (drop j S)))"
proof -
  have decomp: "S = take j S @ drop j S" by simp
  have raw_decomp: "fst (lower_step_acc \<A> a S) = map (\<lambda>P . (fst P - snd (lower_step_acc \<A> a (drop j S)), snd P)) (fst (lower_step_acc \<A> a (take j S))) @ fst (lower_step_acc \<A> a (drop j S))" using lower_step_acc_fst_append[of \<A> a "take j S" "drop j S"] by simp
  have "drop j S = S ! j # drop (Suc j) S" using assms(2) by (simp add: Cons_nth_drop_Suc)
  hence post_sub: "post_set \<A> (fst (S ! j)) a \<subseteq> snd (lower_step_acc \<A> a (drop j S))" by auto
  show ?thesis
  proof (rule ccontr)
    assume notin: "X \<notin> set (fst (lower_step_acc \<A> a (drop j S)))"
    hence "X \<in> set (map (\<lambda>P . (fst P - snd (lower_step_acc \<A> a (drop j S)), snd P)) (fst (lower_step_acc \<A> a (take j S))))" using assms(1) raw_decomp by auto
    then obtain P where "P \<in> set (fst (lower_step_acc \<A> a (take j S)))" "X = (fst P - snd (lower_step_acc \<A> a (drop j S)), snd P)" by auto
    hence fst: "fst X \<inter> snd (lower_step_acc \<A> a (drop j S)) = {}" by auto
    have "fst X \<subseteq> snd (lower_step_acc \<A> a (drop j S))" using assms(3) post_sub by blast
    hence "fst X = {}" using fst by blast
    thus False using assms(4) by blast
  qed
qed

lemma lower_step_nacc_child_raw_in_drop:
  assumes "X \<in> set (fst (lower_step_nacc \<A> a S))" "j < length S" "fst X \<subseteq> post_set \<A> (fst (S ! j)) a" "fst X \<noteq> {}"
  shows "X \<in> set (fst (lower_step_nacc \<A> a (drop j S)))"
proof -
  have decomp: "S = take j S @ drop j S" by simp
  have raw_decomp: "fst (lower_step_nacc \<A> a S) = map (\<lambda>P . (fst P - snd (lower_step_nacc \<A> a (drop j S)), snd P)) (fst (lower_step_nacc \<A> a (take j S))) @ fst (lower_step_nacc \<A> a (drop j S))" using lower_step_nacc_fst_append[of \<A> a "take j S" "drop j S"] by simp
  have "drop j S = S ! j # drop (Suc j) S" using assms(2) by (simp add: Cons_nth_drop_Suc)
  hence post_sub: "post_set \<A> (fst (S ! j)) a \<subseteq> snd (lower_step_nacc \<A> a (drop j S))" by auto
  show ?thesis
  proof (rule ccontr)
    assume notin: "X \<notin> set (fst (lower_step_nacc \<A> a (drop j S)))"
    hence "X \<in> set (map (\<lambda>P . (fst P - snd (lower_step_nacc \<A> a (drop j S)), snd P)) (fst (lower_step_nacc \<A> a (take j S))))" using assms(1) raw_decomp by auto
    then obtain P where "P \<in> set (fst (lower_step_nacc \<A> a (take j S)))" "X = (fst P - snd (lower_step_nacc \<A> a (drop j S)), snd P)" by auto
    hence fst: "fst X \<inter> snd (lower_step_nacc \<A> a (drop j S)) = {}" by auto
    have "fst X \<subseteq> snd (lower_step_nacc \<A> a (drop j S))" using assms(3) post_sub by blast
    hence "fst X = {}" using fst by blast
    thus False using assms(4) by blast
  qed
qed

lemma lower_child_color2_preserved:
  assumes "(S, a, S') \<in> lower_transitions \<A>" "upper_child_up S a \<A> S' j k" "snd (S ! j) = 2"
  shows "snd (S' ! k) = 2"
proof -
  have child: "j < length S" "k < length S'" "fst (S' ! k) \<subseteq> post_set \<A> (fst (S ! j)) a" "fst (S' ! k) \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}" using assms(2) unfolding upper_child_up_def by blast+
  hence in_set: "S' ! k \<in> set S'" by auto
  hence nz: "fst (S' ! k) \<noteq> {}" using assms(1) unfolding lower_transitions_def by (cases "lower_accepting S") auto
  show ?thesis
  proof (cases "lower_accepting S")
    case True
    hence "S' = filter (\<lambda>X . fst X \<noteq> {}) (fst (lower_step_acc \<A> a S))" using assms(1) unfolding lower_transitions_def by auto
    hence raw: "S' ! k \<in> set (fst (lower_step_acc \<A> a S))" using child(2) in_set filter_is_subset subsetD by fast
    have raw_drop: "S' ! k \<in> set (fst (lower_step_acc \<A> a (drop j S)))" using lower_step_acc_child_raw_in_drop[OF raw child(1) child(3) nz] by blast
    thus ?thesis using lower_step_acc_drop_child_color2_preserved[OF raw_drop child(1) child(3) child(4) assms(3) nz] by blast
  next
    case False
    hence "S' = filter (\<lambda>X . fst X \<noteq> {}) (fst (lower_step_nacc \<A> a S))" using assms(1) unfolding lower_transitions_def by auto
    hence raw: "S' ! k \<in> set (fst (lower_step_nacc \<A> a S))" using child(2) in_set filter_is_subset subsetD by fast
    have raw_drop: "S' ! k \<in> set (fst (lower_step_nacc \<A> a (drop j S)))" using lower_step_nacc_child_raw_in_drop[OF raw child(1) child(3) nz] by blast
    thus ?thesis using lower_step_nacc_drop_child_color2_preserved[OF raw_drop child(1) child(3) child(4) assms(3) nz] by blast
  qed
qed

lemma lower_child_segment_color2_preserved:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "\<forall> n \<ge> i . rc n \<in> lower_states \<A>" "i \<le> N" "upper_child_segment_up rc i N x \<A> j k" "snd (rc i ! j) = 2"
  shows "snd (rc N ! k) = 2"
proof -
  obtain js where js: "length js = N - i + 1" "js ! 0 = j" "last js = k" "\<forall> m < N - i . upper_child_up (rc (i + m)) (x (i + m)) \<A> (rc (i + Suc m)) (js ! m) (js ! Suc m)" using assms(5) unfolding upper_child_segment_up_def by blast
  {
    fix m assume "m \<le> N - i"
    hence "snd (rc (i + m) ! (js ! m)) = 2"
    proof (induction m rule: less_induct)
      case (less m) show ?case
      proof (cases m)
        case 0 thus ?thesis using assms(6) js(2) by simp
      next
        case (Suc m')
        hence "m' < N - i" using less by simp 
        hence child: "upper_child_up (rc (i + m')) (x (i + m')) \<A> (rc (i + Suc m')) (js ! m') (js ! Suc m')" using js(4) by blast
        have prev: "snd (rc (i + m') ! (js ! m')) = 2" using less.IH[of m'] Suc less by auto
        have step: "(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> lower_transitions \<A>"
        proof -
          have low_src: "rc (i + m') \<in> lower_states \<A>" using assms(3) by simp
          have "(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> transitions (comp_omega_automaton \<A>)" using assms(2) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by simp
          hence "(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> transitions (upper_part \<A>) \<or> (rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> lower_transitions \<A> \<or>(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> lower_transitions_from_upper \<A>" unfolding comp_omega_automaton_def by auto
          then consider (up) "(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> transitions (upper_part \<A>)" | (low) "(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> lower_transitions \<A>" | (jump) "(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> lower_transitions_from_upper \<A>" by fast
          thus ?thesis
          proof cases
            case up
            hence "rc (i + m') \<in> states (upper_part \<A>)" using assms(1) well_def_upper_part well_def_trans_components by fast
            hence "rc (i + m') \<in> states (upper_part \<A>) \<inter> lower_states \<A>" using low_src by blast
            thus ?thesis using upper_and_lower_states_disjoint by blast
          next
            case low thus ?thesis by blast
          next
            case jump
            hence "rc (i + m') \<in> states (upper_part \<A>)" unfolding lower_transitions_from_upper_def by auto
            hence "rc (i + m') \<in> states (upper_part \<A>) \<inter> lower_states \<A>" using low_src by blast
            thus ?thesis using upper_and_lower_states_disjoint by blast
          qed
        qed
        have "snd (rc (i + Suc m') ! (js ! Suc m')) = 2" using lower_child_color2_preserved[OF step child prev] by blast
        thus ?thesis using Suc by simp
      qed
    qed
  }
  hence "\<forall> m \<le> N - i . snd (rc (i + m) ! (js ! m)) = 2" by blast
  hence "snd (rc (i + (N - i)) ! (js ! (N - i))) = 2" by simp
  hence snd: "snd (rc N ! (js ! (N - i))) = 2" using assms(4) by simp
  have "N - i < length js" using js(1) by simp
  hence "js ! (N - i) = last js" using js(1) last_index_from_length by fastforce
  hence "js ! (N - i) = k" using js(3) by simp
  thus ?thesis using snd by simp
qed

lemma upper_continued_up_color2_forever:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "\<forall> n \<ge> i . rc n \<in> lower_states \<A>" "upper_continued_up rc \<A> x i j" "snd (rc i ! j) = 2"
  shows "\<forall> N \<ge> i . \<exists> k < length (rc N) . snd (rc N ! k) = 2"
proof -
  {
    fix N assume assm: "i \<le> N"
    hence "\<exists> k < length (rc N) . snd (rc N ! k) = 2"
    proof (cases "N = i")
      case True
      have "j < length (rc i)" using assms(4) upper_continued_up_index unfolding upper_continued_F_up_def by blast
      thus ?thesis using assms(5) True by blast
    next
      case False
      hence gt: "N > i" using assm by linarith
      then obtain k where seg: "upper_child_segment_up rc i N x \<A> j k" using assms(4) unfolding upper_continued_F_up_def upper_continued_up_def by blast
      have color: "snd (rc N ! k) = 2" using lower_child_segment_color2_preserved[OF assms(1,2,3) assm seg assms(5)] by blast
      have "k < length (rc N)"
      proof -
        obtain js where js: "length js = N - i + 1" "last js = k" "\<forall> m < N - i . upper_child_up (rc (i + m)) (x (i + m)) \<A> (rc (i + Suc m)) (js ! m) (js ! Suc m)" using seg unfolding upper_child_segment_up_def by blast
        have "N - i > 0" using gt by simp
        hence "N - i - 1 < N - i" by linarith
        hence last_step: "upper_child_up (rc (i + (N - i - 1))) (x (i + (N - i - 1))) \<A> (rc (i + Suc (N - i - 1))) (js ! (N - i - 1)) (js ! Suc (N - i - 1))" using js(3) by blast
        have i_N: "i + Suc (N - i - 1) = N" using gt by simp
        have Suc_i_N: "Suc (N - i - 1) = N - i" using gt by simp
        have "js ! (N - i) = last js" using js(1) Suc_eq_plus1 last_index_from_length by metis
        hence "js ! Suc (N - i - 1) = k" using js(2) Suc_i_N by simp
        thus ?thesis using last_step i_N unfolding upper_child_up_def by argo
      qed
      thus ?thesis using color by blast
    qed
  }
  thus ?thesis by blast
qed

lemma lower_color2_forever_not_accepting:
  assumes "auto_well_defined \<A>" "\<forall> N \<ge> i . rc N \<in> lower_states \<A>" "\<forall> N \<ge> i . \<exists> k < length (rc N) . snd (rc N ! k) = 2"
  shows "\<not> omega_run_accepting rc (comp_omega_automaton \<A>) x"
proof(rule ccontr)
  assume "\<not> \<not> omega_run_accepting rc (comp_omega_automaton \<A>) x"
  then obtain N where N: "N > i" "rc N \<in> accepting_states (comp_omega_automaton \<A>)" unfolding omega_run_accepting_def by blast
  hence "N \<ge> i" by simp
  then obtain k where k: "k < length (rc N)" "snd (rc N ! k) = 2" using assms N(1) by blast
  have lower: "rc N \<in> lower_states \<A>" using assms N by auto
  have lower_acc: "lower_accepting (rc N)"
  proof -
    have in_acc: "rc N \<in> {S \<in> lower_states \<A> . lower_accepting S} \<union> accepting_states (upper_part \<A>)" using N unfolding comp_omega_automaton_def  by auto
    have "auto_well_defined (upper_part \<A>)" using assms well_def_upper_part by blast
    hence "rc N \<notin> accepting_states (upper_part \<A>)" using lower upper_and_lower_states_disjoint unfolding auto_well_defined_def by blast
    thus ?thesis using lower in_acc by auto
  qed
  have "(fst (rc N ! k), snd (rc N ! k)) \<in> set (rc N)" using k(1) by auto
  hence  "snd (rc N ! k) \<noteq> 2" using lower_acc unfolding lower_accepting_def by blast
  thus False using k(2) by blast
qed

lemma lower_step_acc_child_color1_to_color2_preserved_head:
  assumes "X \<in> set (fst (lower_step_acc \<A> a (Sm # S)))" "fst X \<subseteq> post_set \<A> (fst Sm) a" "fst X \<inter> snd (upper_step \<A> a (map fst S)) = {}" "snd Sm = 1" "fst X \<noteq> {}"
  shows "snd X = 2"
proof -
  let ?L = "((post_set \<A> (fst Sm) a - snd (lower_step_acc \<A> a S)) - accepting_states \<A>, min (2 * snd Sm) 2)"
  let ?R = "((post_set \<A> (fst Sm) a - snd (lower_step_acc \<A> a S)) \<inter> accepting_states \<A>, 2)"
  have snd_eq: "snd (lower_step_acc \<A> a S) = snd (upper_step \<A> a (map fst S))" by (induction S) auto
  have "X = ?L \<or> X = ?R \<or> X \<in> set (fst (lower_step_acc \<A> a S))" using assms(1) by simp
  then consider (case1) "X = ?L" | (case2) "X = ?R" | (case3) "X \<in> set (fst (lower_step_acc \<A> a S))" by fast
  thus ?thesis
  proof cases
    case case1 thus ?thesis using assms by auto
  next
    case case2 thus ?thesis by simp
  next
    case case3 
    hence "fst X \<subseteq> snd (lower_step_acc \<A> a S)" using lower_step_acc_fst_subset_snd by fast
    hence "fst X \<subseteq> snd (upper_step \<A> a (map fst S))" using snd_eq by simp
    hence "fst X = {}"using assms(3) by blast
    thus ?thesis using assms(5) by blast
  qed
qed  

lemma lower_step_acc_drop_child_color1_to_color2:
  assumes "X \<in> set (fst (lower_step_acc \<A> a (drop j S)))" "j < length S" "fst X \<subseteq> post_set \<A> (fst (S ! j)) a" "fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}" "snd (S ! j) = 1" "fst X \<noteq> {}"
  shows "snd X = 2"
proof -
  have drop_decomp: "drop j S = S ! j # drop (Suc j) S" using assms(2) by (simp add: Cons_nth_drop_Suc)
  have "map fst (drop (Suc j) S) = drop (Suc j) (map fst S)" by (simp add: drop_map)
  thus ?thesis using lower_step_acc_child_color1_to_color2_preserved_head[of X \<A> a "S ! j" "drop (Suc j) S"] assms drop_decomp  by argo
qed

lemma lower_accepting_child_color1_to_color2:
  assumes "(S, a, S') \<in> lower_transitions \<A>" "lower_accepting S" "upper_child_up S a \<A> S' j k" "snd (S ! j) = 1"
  shows "snd (S' ! k) = 2"
proof -
  have child: "j < length S" "k < length S'" "fst (S' ! k) \<subseteq> post_set \<A> (fst (S ! j)) a" "fst (S' ! k) \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}" using assms(3) unfolding upper_child_up_def by blast+
  have S'_def: "S' = filter (\<lambda>X. fst X \<noteq> {}) (fst (lower_step_acc \<A> a S))" using assms(1,2) unfolding lower_transitions_def by auto
  hence raw: "S' ! k \<in> set (fst (lower_step_acc \<A> a S))" using child(2) filter_is_subset nth_mem subsetD by metis
  have nz: "fst (S' ! k) \<noteq> {}" using child(2) S'_def nth_mem by fastforce
  have raw_drop: "S' ! k \<in> set (fst (lower_step_acc \<A> a (drop j S)))" using lower_step_acc_child_raw_in_drop[OF raw child(1) child(3) nz] by blast
  thus ?thesis using lower_step_acc_drop_child_color1_to_color2[OF raw_drop child(1) child(3) child(4) assms(4) nz] by blast
qed

lemma lower_step_nacc_child_color12_preserved_head:
  assumes "X \<in> set (fst (lower_step_nacc \<A> a (Sm # S)))" "fst X \<subseteq> post_set \<A> (fst Sm) a" "fst X \<inter> snd (upper_step \<A> a (map fst S)) = {}" "snd Sm = 1" "fst X \<noteq> {}"
  shows "snd X = 1 \<or> snd X = 2"
proof -
  let ?L = "((post_set \<A> (fst Sm) a - snd (lower_step_nacc \<A> a S)) - accepting_states \<A>, snd Sm)"
  let ?R = "((post_set \<A> (fst Sm) a - snd (lower_step_nacc \<A> a S)) \<inter> accepting_states \<A>, max (snd Sm) 1)"
  have snd_eq: "snd (lower_step_nacc \<A> a S) = snd (upper_step \<A> a (map fst S))" by (induction S) auto  
  have "X = ?L \<or> X = ?R \<or> X \<in> set (fst (lower_step_nacc \<A> a S))" using assms(1) by simp
  then consider "X = ?L" | "X = ?R" | "X \<in> set (fst (lower_step_nacc \<A> a S))" by fast
  thus ?thesis
  proof cases
    case 1 thus ?thesis using assms(4) by simp
  next
    case 2 thus ?thesis using assms(4) by simp
  next
    case 3
    hence "fst X \<subseteq> snd (lower_step_nacc \<A> a S)" using lower_step_nacc_fst_subset_snd by fast
    hence "fst X \<subseteq> snd (upper_step \<A> a (map fst S))" using snd_eq by simp
    hence "fst X = {}" using assms(3) by blast
    thus ?thesis using assms(5) by blast
  qed
qed
  
lemma lower_step_nacc_drop_child_color12_preserved:
  assumes "X \<in> set (fst (lower_step_nacc \<A> a (drop j S)))" "j < length S" "fst X \<subseteq> post_set \<A> (fst (S ! j)) a" "fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}" "snd (S ! j) = 1" "fst X \<noteq> {}"
  shows "snd X = 1 \<or> snd X = 2"
proof -
  have drop_decomp: "drop j S = S ! j # drop (Suc j) S" using assms(2) by (simp add: Cons_nth_drop_Suc)
  have "map fst (drop (Suc j) S) = drop (Suc j) (map fst S)" by (simp add: drop_map)
  thus ?thesis using lower_step_nacc_child_color12_preserved_head[of X \<A> a "S ! j" "drop (Suc j) S"] assms drop_decomp by simp
qed

lemma lower_child_color12_preserved:
  assumes "(S, a, S') \<in> lower_transitions \<A>" "upper_child_up S a \<A> S' j k" "snd (S ! j) = 1 \<or> snd (S ! j) = 2"
  shows "snd (S' ! k) = 1 \<or> snd (S' ! k) = 2"
proof (cases "snd (S ! j) = 2")
  case True
  hence "snd (S' ! k) = 2" using lower_child_color2_preserved[OF assms(1,2)] by blast
  thus ?thesis by blast
next
  case False
  hence color1: "snd (S ! j) = 1" using assms(3) by blast
  show ?thesis
  proof (cases "lower_accepting S")
    case True
    hence "snd (S' ! k) = 2" using lower_accepting_child_color1_to_color2[OF assms(1) True assms(2) color1] by blast
    thus ?thesis by blast
  next
    case False
    have child: "j < length S" "k < length S'" "fst (S' ! k) \<subseteq> post_set \<A> (fst (S ! j)) a" "fst (S' ! k) \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}" using assms(2) unfolding upper_child_up_def by blast+
    have S'_def: "S' = filter (\<lambda>X. fst X \<noteq> {}) (fst (lower_step_nacc \<A> a S))" using assms(1) False unfolding lower_transitions_def by auto
    hence raw: "S' ! k \<in> set (fst (lower_step_nacc \<A> a S))" using child(2) filter_is_subset nth_mem subsetD by metis
    have nz: "fst (S' ! k) \<noteq> {}" using child(2) S'_def nth_mem by fastforce
    have raw_drop: "S' ! k \<in> set (fst (lower_step_nacc \<A> a (drop j S)))" using lower_step_nacc_child_raw_in_drop[OF raw child(1) child(3) nz] by blast
    thus ?thesis using lower_step_nacc_drop_child_color12_preserved[OF raw_drop child(1) child(3) child(4) color1 nz] by blast
  qed
qed

lemma segment_endpoint_color12:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "\<forall> n \<ge> i . rc n \<in> lower_states \<A>" "upper_continued_F_up rc \<A> x i j" "i \<le> N" "upper_child_segment_up rc i N x \<A> j k"
  shows "snd (rc N ! k) = 1 \<or> snd (rc N ! k) = 2"
proof -
  obtain js where js: "length js = N - i + 1" "js ! 0 = j" "last js = k" "\<forall> m < N - i . upper_child_up (rc (i + m)) (x (i + m)) \<A> (rc (i + Suc m)) (js ! m) (js ! Suc m)" using assms(6) unfolding upper_child_segment_up_def by blast
  have init_color: "snd (rc i ! j) = 1 \<or> snd (rc i ! j) = 2" using upper_continued_F_up_in_lower_implies_color12[OF assms(1,2) _ assms(4)] assms(3) by blast
  {
    fix m
    have "m \<le> N - i \<longrightarrow> snd (rc (i + m) ! (js ! m)) = 1 \<or> snd (rc (i + m) ! (js ! m)) = 2"
    proof (induction m rule: less_induct)
      case (less m)
      show ?case
      proof
        assume m_le: "m \<le> N - i"
        show "snd (rc (i + m) ! (js ! m)) = 1 \<or> snd (rc (i + m) ! (js ! m)) = 2"
        proof (cases m)
          case 0 thus ?thesis using init_color js(2) by simp
        next
          case (Suc m')
          hence m'_lt: "m' < N - i" using m_le by simp
          have prev: "snd (rc (i + m') ! (js ! m')) = 1 \<or> snd (rc (i + m') ! (js ! m')) = 2" using less.IH[of m'] Suc m_le by simp
          have child: "upper_child_up (rc (i + m')) (x (i + m')) \<A> (rc (i + Suc m')) (js ! m') (js ! Suc m')" using js(4) m'_lt by blast
          have step:  "(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> lower_transitions \<A>"
          proof -
            have low_src: "rc (i + m') \<in> lower_states \<A>" using assms(3) by simp
            have "(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> transitions (comp_omega_automaton \<A>)" using assms(2) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
            hence "(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> transitions (upper_part \<A>) \<or> (rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> lower_transitions \<A> \<or> (rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> lower_transitions_from_upper \<A>" unfolding comp_omega_automaton_def by auto
            then consider (up) "(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> transitions (upper_part \<A>)" | (low) "(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> lower_transitions \<A>" | (jump) "(rc (i + m'), x (i + m'), rc (i + Suc m')) \<in> lower_transitions_from_upper \<A>" by fast
            thus ?thesis
            proof cases
              case up
              hence "rc (i + m') \<in> states (upper_part \<A>)" using assms(1) well_def_upper_part well_def_trans_components by fast
              hence "rc (i + m') \<in> states (upper_part \<A>) \<inter> lower_states \<A>" using low_src by blast
              thus ?thesis using upper_and_lower_states_disjoint by blast
            next
              case low thus ?thesis by blast
            next
              case jump
              hence "rc (i + m') \<in> states (upper_part \<A>)" unfolding lower_transitions_from_upper_def by auto
              hence "rc (i + m') \<in> states (upper_part \<A>) \<inter> lower_states \<A>" using low_src by blast
              thus ?thesis using upper_and_lower_states_disjoint by blast
            qed
          qed
          have succ_color: "snd (rc (i + Suc m') ! (js ! Suc m')) = 1 \<or> snd (rc (i + Suc m') ! (js ! Suc m')) = 2" using lower_child_color12_preserved[OF step child prev] by blast
          thus ?thesis using Suc by simp
        qed
      qed
    qed
  }
  hence color: "\<forall> m \<le> N - i . snd (rc (i + m) ! (js ! m)) = 1 \<or> snd (rc (i + m) ! (js ! m)) = 2" by blast
  have "N - i < length js" using js(1) by simp
  hence "js ! (N - i) = last js" using js(1) Suc_eq_plus1 last_index_from_length by metis
  hence idx_last: "js ! (N - i) = k" using js(3) by simp
  have "snd (rc (i + (N - i)) ! (js ! (N - i))) = 1 \<or> snd (rc (i + (N - i)) ! (js ! (N - i))) = 2" using color by simp
  hence "snd (rc N ! (js ! (N - i))) = 1 \<or> snd (rc N ! (js ! (N - i))) = 2" using assms(5) by simp
  thus ?thesis using idx_last by simp
qed

lemma continued_color1_either_eventually_color2_or_all_color1:
  assumes "\<forall> N \<ge> i . rc N \<in> lower_states \<A>" "\<forall> N \<ge> i . \<forall> k . upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k \<longrightarrow> (snd (rc N ! k) = 1 \<or> snd (rc N ! k) = 2)" "snd (rc i ! j) = 1" "j < length (rc i)"
  shows "(\<exists> N \<ge> i . \<exists> k . upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k \<and> snd (rc N ! k) = 2) \<or> (\<forall> N \<ge> i . \<forall> k . upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k \<longrightarrow> snd (rc N ! k) = 1)"
proof (cases "\<exists> N \<ge> i . \<exists> k . upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k \<and> snd (rc N ! k) = 2")
  case True thus ?thesis by blast
next
  case False
  hence no2: "\<forall> N \<ge> i . \<forall> k . upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k \<longrightarrow> snd (rc N ! k) \<noteq> 2" by blast
  {
    fix N k assume assm: "i \<le> N \<and> upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k"
    hence color12: "snd (rc N ! k) = 1 \<or> snd (rc N ! k) = 2" using assms(2) by blast
    have "snd (rc N ! k) \<noteq> 2" using no2 assm by blast
    hence "snd (rc N ! k) = 1" using color12 by blast
  }
  hence all1: "\<forall> N \<ge> i . \<forall> k . upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k \<longrightarrow> snd (rc N ! k) = 1" by blast
  thus ?thesis by blast
qed

lemma upper_child_segment_up_refl:
  assumes "j < length (rc i)"
  shows "upper_child_segment_up rc i i x \<A> j j"
  using assms unfolding upper_child_segment_up_def by (intro exI[of _ "[j]"]) auto

lemma upper_child_segment_up_extend_one:
  assumes "upper_child_segment_up rc i N x \<A> j k" "upper_child_up (rc N) (x N) \<A> (rc (Suc N)) k k'" "i \<le> N"
  shows "upper_child_segment_up rc i (Suc N) x \<A> j k'"
proof -
  obtain js where js: "length js = N - i + 1" "js ! 0 = j" "last js = k" "\<forall> m < N - i . upper_child_up (rc (i + m)) (x (i + m)) \<A> (rc (i + Suc m)) (js ! m) (js ! Suc m)" using assms(1) unfolding upper_child_segment_up_def by blast
  define js' where "js' = js @ [k']"
  hence len: "length js' = Suc N - i + 1" using js(1) assms(3) by simp
  have hd: "js' ! 0 = j" using js(1,2) One_nat_def add_gr_0 list_properties_length zero_less_Suc unfolding js'_def by metis
  have last: "last js' = k'" unfolding js'_def by simp
  {
    fix m assume mlt: "m < Suc N - i"
    have "upper_child_up (rc (i + m)) (x (i + m)) \<A> (rc (i + Suc m)) (js' ! m) (js' ! Suc m)"
    proof (cases "m < N - i")
      case True
      hence jsm: "js' ! m = js ! m" using js(1) add_diff_cancel_right' list_properties_length unfolding js'_def by metis
      have "js' ! Suc m = js ! Suc m" using True js(1) list_properties_length add.commute add_diff_cancel_right' plus_1_eq_Suc unfolding js'_def by metis
      thus ?thesis using js(4) True jsm by simp
    next
      case False
      hence m_eq: "m = N - i" using mlt assms(3) by linarith
      hence jsm: "js' ! m = k" using js(1,3) One_nat_def Suc_eq_plus1 diff_Suc_Suc list_append_position5 minus_nat.diff_0 not_Cons_self2 zero_less_Suc unfolding js'_def by metis
      have jssuc: "js' ! Suc m = k'" using js(1) m_eq Suc_diff_1 add_diff_cancel_right' add_gr_0 less_numeral_extra(1) nth_append_length unfolding js'_def by metis
      have "i + m = N" using assms(3) m_eq by simp
      thus ?thesis using assms(2) jsm jssuc by simp
    qed
  }
  thus ?thesis using len hd last unfolding upper_child_segment_up_def by blast
qed

lemma finite_arbitrarily_large_choice:
  assumes "finite K" "\<forall> M > (N :: nat) . \<exists> k \<in> K . P k M"
  shows "\<exists> k \<in> K . \<forall> M > N . \<exists> M' \<ge> M . P k M'"
proof (rule ccontr)
  assume "\<not> (\<exists> k \<in> K . \<forall> M > N . \<exists> M' \<ge> M . P k M')"
  hence bad: "\<forall> k \<in> K . \<exists> B > N . \<forall> M' \<ge> B . \<not> P k M'" by simp
  obtain B where B: "\<forall> k \<in> K . B k > N \<and> (\<forall> M' \<ge> B k . \<not> P k M')" using bchoice[OF bad] by presburger
  define Bmax where "Bmax = Max (insert (Suc N) (B ` K))"
  hence "Bmax > N" using assms(1) by (simp add: Suc_le_lessD)
  then obtain k where k: "k \<in> K" "P k Bmax" using assms(2) by blast
  hence "B k \<le> Bmax" using assms(1) unfolding Bmax_def by simp
  hence "\<not> P k Bmax" using B k(1) by blast
  thus False using k(2) by blast
qed

lemma upper_child_segment_up_prefix:
  assumes "upper_child_segment_up rc i M x \<A> j l" "i \<le> N" "N \<le> M"
  shows "\<exists> k . upper_child_segment_up rc i N x \<A> j k"
proof -
  obtain js where js: "length js = M - i + 1" "js ! 0 = j" "last js = l" "\<forall> m < M - i . upper_child_up (rc (i + m)) (x (i + m)) \<A> (rc (i + Suc m)) (js ! m) (js ! Suc m)" using assms(1) unfolding upper_child_segment_up_def by blast
  let ?k = "js ! (N - i)"
  let ?js = "take (N - i + 1) js"
  have len: "length ?js = N - i + 1" using js(1) assms(2,3) by simp
  hence first: "?js ! 0 = j" using js(2) by simp
  have len_pos: "N - i + 1 > 0" by simp
  have "N - i + 1 \<le> length js" using js(1) assms(2,3) by simp
  hence len_le: "length ?js = N - i + 1" by simp
  hence "?js \<noteq> []" by fastforce
  hence "last ?js = ?js ! ((N - i + 1) - 1)" using len_pos len_le list_properties_not_empty by metis
  hence last: "last ?js = ?k" by simp
  {
    fix m assume mlt: "m < N - i"
    hence mltM: "m < M - i" using assms(2,3) by simp
    have jsm: "?js ! m = js ! m" using mlt by simp
    have "?js ! Suc m = js ! Suc m" using mlt by simp
    hence "upper_child_up (rc (i + m)) (x (i + m)) \<A> (rc (i + Suc m)) (?js ! m) (?js ! Suc m)" using js(4) mltM jsm by simp
  }
  thus ?thesis unfolding upper_child_segment_up_def using len first last by blast
qed

lemma continued_has_continued_successor:
  assumes "upper_continued_up rc \<A> x i j"
  shows "\<exists> k . upper_child_up (rc i) (x i) \<A> (rc (Suc i)) j k \<and> upper_continued_up rc \<A> x (Suc i) k"
proof -
  {
    fix M assume "M > Suc i"
    hence less: "M > i" by simp
    then obtain l where "upper_child_segment_up rc i M x \<A> j l" using assms unfolding upper_continued_up_def by blast
    then obtain js where js: "length js = M - i + 1" "js ! 0 = j" "last js = l" "\<forall> m < M - i . upper_child_up (rc (i + m)) (x (i + m)) \<A> (rc (i + Suc m)) (js ! m) (js ! Suc m)" unfolding upper_child_segment_up_def by blast
    hence k_def: "upper_child_up (rc i) (x i) \<A> (rc (Suc i)) j (js ! 1)" using less Suc_eq_plus1 add.left_neutral add.right_neutral zero_less_diff by metis
    have len: "length (tl js) = M - Suc i + 1" using js(1) less by (simp add: Suc_diff_Suc)
    hence last': "last (tl js) = l" using js(1,3) Suc_diff_Suc Suc_eq_plus1 last_tl length_greater_0_conv less zero_less_diff by metis
    have hd: "(tl js) ! 0 = js ! 1" using js(1) less  by (simp add: tl_list_run_spezial)
    {
      fix m assume mlt: "m < M - Suc i"
      hence idx: "Suc m < M - i" by simp
      hence step: "upper_child_up (rc (i + Suc m)) (x (i + Suc m)) \<A> (rc (i + Suc (Suc m))) (js ! Suc m) (js ! Suc (Suc m))" using js(4) by blast
      have a1: "Suc i + m = i + Suc m" by simp
      have a2: "Suc i + Suc m = i + Suc (Suc m)" by simp
      have t1: "(tl js) ! m = js ! Suc m" using idx js(1) by (simp add: nth_tl)
      have t2: "(tl js) ! Suc m = js ! Suc (Suc m)" using idx js(1) by (simp add: nth_tl)
      have "upper_child_up (rc (Suc i + m)) (x (Suc i + m)) \<A> (rc (Suc i + Suc m)) ((tl js) ! m) ((tl js) ! Suc m)" using step a1 a2 t1 t2 by simp
    }
    hence "upper_child_segment_up rc (Suc i) M x \<A> (js ! 1) l" using len hd last' unfolding upper_child_segment_up_def by blast
    hence "\<exists> k l . upper_child_up (rc i) (x i) \<A> (rc (Suc i)) j k \<and> upper_child_segment_up rc (Suc i) M x \<A> k l" using k_def  by blast
  }
  hence seg_all: "\<forall> M > Suc i . \<exists> k l . upper_child_up (rc i) (x i) \<A> (rc (Suc i)) j k \<and> upper_child_segment_up rc (Suc i) M x \<A> k l" by blast
  let ?K = "{k . k < length (rc (Suc i)) \<and> upper_child_up (rc i) (x i) \<A> (rc (Suc i)) j k}"
  have finK: "finite ?K" by simp
  {
    fix M assume "M > Suc i"
    then obtain k l where kl: "upper_child_up (rc i) (x i) \<A> (rc (Suc i)) j k" "upper_child_segment_up rc (Suc i) M x \<A> k l" using seg_all by blast
    hence "k < length (rc (Suc i))" unfolding upper_child_up_def by blast
    hence "k \<in> ?K" using kl(1) by blast
    hence "\<exists> k \<in> ?K . \<exists> l . upper_child_segment_up rc (Suc i) M x \<A> k l" using kl(2) by blast
  }
  hence exK: "\<forall> M > Suc i . \<exists> k \<in> ?K . \<exists> l . upper_child_segment_up rc (Suc i) M x \<A> k l" by blast
  obtain k where k_prop: "k \<in> ?K" "\<forall> M > Suc i . \<exists> M' \<ge> M . \<exists> l . upper_child_segment_up rc (Suc i) M' x \<A> k l" using finite_arbitrarily_large_choice[OF finK exK] by blast
  hence k_lt: "k < length (rc (Suc i))" by blast
  have step: "upper_child_up (rc i) (x i) \<A> (rc (Suc i)) j k" using k_prop(1) by blast
  {
    fix M assume M_gt: "M > Suc i"
    then obtain M' l where Ml: "M' \<ge> M" "upper_child_segment_up rc (Suc i) M' x \<A> k l" using k_prop(2) by blast
    then obtain l' where "upper_child_segment_up rc (Suc i) M x \<A> k l'" using upper_child_segment_up_prefix[OF Ml(2)] M_gt by fastforce
    hence "\<exists> l . upper_child_segment_up rc (Suc i) M x \<A> k l" by blast
  }
  hence "\<forall> M > Suc i . \<exists> l . upper_child_segment_up rc (Suc i) M x \<A> k l" by blast
  hence "upper_continued_up rc \<A> x (Suc i) k" unfolding upper_continued_up_def by blast
  thus ?thesis using step by blast
qed

lemma continued_reaches_continued_component:
  assumes "upper_continued_up rc \<A> x i j" "i \<le> N" "j < length (rc i)"
  shows "\<exists> k . upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k"
using assms proof (induction "N - i" arbitrary: N j)
  case 0
  hence Ni: "N = i" by simp
  hence seg: "upper_child_segment_up rc i N x \<A> j j" using upper_child_segment_up_refl 0 by simp
  thus ?case using 0 Ni by blast
next
  case (Suc d)
  hence i_lt_N: "i < N" by simp
  then obtain N' where N': "N = Suc N'" by (cases N) auto
  hence i_le_N': "i \<le> N'" using i_lt_N by simp
  hence "N' - i = d" using Suc N' by linarith
  then obtain k where k: "upper_child_segment_up rc i N' x \<A> j k" "upper_continued_up rc \<A> x N' k" using Suc i_le_N' by blast
  obtain k' where k': "upper_child_up (rc N') (x N') \<A> (rc (Suc N')) k k'" "upper_continued_up rc \<A> x (Suc N') k'" using continued_has_continued_successor[OF k(2)] by blast
  have "upper_child_segment_up rc i (Suc N') x \<A> j k'" using upper_child_segment_up_extend_one[OF k(1) k'(1) i_le_N'] by blast
  thus ?case using k'(2) N' by blast
qed

lemma lemma_3_4_16:
  assumes "auto_well_defined \<A>" "x \<in> omega_language_auto \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x"
  shows "\<not> omega_run_accepting rc (comp_omega_automaton \<A>) x"
proof (cases "\<forall> n . rc n \<in> states (upper_part \<A>)")
  case True thus ?thesis using comp_run_upper_case_not_accepting[OF assms(1,2,3)] by blast
next
  case False
  then obtain l where l_not_upper: "rc l \<notin> states (upper_part \<A>)" by blast
  have "auto_well_defined (comp_omega_automaton \<A>)" using assms well_def_comp_omega_auto by auto
  hence rc_states: "\<forall> n . rc n \<in> states (comp_omega_automaton \<A>)" using assms(3) well_def_implies_omega_prun_states unfolding omega_run_well_defined_def omega_prun_states_def by metis
  hence "rc l \<in> states (upper_part \<A>) \<union> lower_states \<A>" unfolding comp_omega_automaton_def by simp
  hence "rc l \<in> lower_states \<A>" using l_not_upper by blast
  hence lower_forever: "\<forall> n \<ge> l . rc n \<in> lower_states \<A>" using comp_run_stays_in_lower_after_entry assms by blast
  obtain r where r_wd: "omega_run_well_defined r \<A> x" using assms(2) unfolding omega_language_auto_def omega_run_accepting_def by blast
  have proj_wd: "omega_run_well_defined (upper_proj_run rc) (upper_part_pure \<A>) x" using comp_run_projects_to_upper_pure[OF assms(1,3)] by blast
  have "\<forall> n . upper_proj_run rc n \<noteq> []" using not_empty_omega_run[OF assms(1) r_wd proj_wd] by argo
  hence rc_ne: "\<forall> n . rc n \<noteq> []" unfolding upper_proj_run_def  by auto
  have inf_TF: "infinite {i . upper_slice_continued_F_up rc \<A> x i}" using comp_run_acceptance_criterion_via_projection[OF assms(1,3) rc_ne] assms(2) by blast
  then obtain i where i: "i \<ge> l" "upper_slice_continued_F_up rc \<A> x i" using finite_nat_set_iff_bounded_le le_cases mem_Collect_eq by metis
  then obtain j where j: "j < length (rc i)" "upper_continued_F_up rc \<A> x i j" unfolding upper_slice_continued_F_up_def by blast
  have lower_i: "rc i \<in> lower_states \<A>" using lower_forever i(1) by blast
  have color12: "snd (rc i ! j) = 1 \<or> snd (rc i ! j) = 2" using upper_continued_F_up_in_lower_implies_color12[OF assms(1,3) lower_i j(2)] by blast
  show ?thesis
  proof (cases "snd (rc i ! j) = 2")
    case True
    have lower_from_i: "\<forall> n \<ge> i . rc n \<in> lower_states \<A>" using lower_forever i(1) by auto
    have cont_up: "upper_continued_up rc \<A> x i j" using j(2) unfolding upper_continued_F_up_def by blast
    have color2_forever: "\<forall> N \<ge> i . \<exists> k < length (rc N). snd (rc N ! k) = 2" using upper_continued_up_color2_forever[OF assms(1) assms(3) lower_from_i cont_up True] by blast
    thus ?thesis using lower_color2_forever_not_accepting[OF assms(1) lower_from_i color2_forever] by blast
  next
    case False
    hence color1: "snd (rc i ! j) = 1" using color12 by blast
    have lower_from_i: "\<forall> n \<ge> i . rc n \<in> lower_states \<A>" using lower_forever i(1) by auto
    {
      fix N k assume assm: "i \<le> N" "upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k"
      hence "snd (rc N ! k) = 1 \<or> snd (rc N ! k) = 2" using segment_endpoint_color12[OF assms(1) assms(3) lower_from_i j(2) assm(1)] by blast
    }
    hence color12_cont_segments: "\<forall> N \<ge> i . \<forall> k . upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k \<longrightarrow> (snd (rc N ! k) = 1 \<or> snd (rc N ! k) = 2)" by blast
    have either: "(\<exists> N \<ge> i . \<exists> k . upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k \<and> snd (rc N ! k) = 2) \<or> (\<forall> N \<ge> i . \<forall> k . upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k \<longrightarrow> snd (rc N ! k) = 1)" using continued_color1_either_eventually_color2_or_all_color1[OF lower_from_i color12_cont_segments color1 j(1)] by blast
    have cont_up_i: "upper_continued_up rc \<A> x i j" using j(2) unfolding upper_continued_F_up_def by blast
    show ?thesis using either
    proof
      assume "\<exists> N \<ge> i . \<exists> k . upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k \<and> snd (rc N ! k) = 2"
      then obtain N k where Nk: "N \<ge> i" "upper_child_segment_up rc i N x \<A> j k" "upper_continued_up rc \<A> x N k" "snd (rc N ! k) = 2" by blast
      hence lower_from_N: "\<forall> M \<ge> N . rc M \<in> lower_states \<A>" using lower_from_i by auto
      have color2_forever: "\<forall> M \<ge> N . \<exists> q < length (rc M) . snd (rc M ! q) = 2" using upper_continued_up_color2_forever[OF assms(1) assms(3) lower_from_N Nk(3) Nk(4)] by blast
      show ?thesis using lower_color2_forever_not_accepting[OF assms(1) lower_from_N color2_forever] by blast
    next
      assume all1: "\<forall> N \<ge> i . \<forall> k . upper_child_segment_up rc i N x \<A> j k \<and> upper_continued_up rc \<A> x N k \<longrightarrow> snd (rc N ! k) = 1"
      show ?thesis
      proof (rule ccontr)
        assume "\<not> \<not> omega_run_accepting rc (comp_omega_automaton \<A>) x"
        hence "omega_run_accepting rc (comp_omega_automaton \<A>) x" by blast
        then obtain N where N: "N > i" "rc N \<in> accepting_states (comp_omega_automaton \<A>)" unfolding omega_run_accepting_def by blast
        hence lowerN: "rc N \<in> lower_states \<A>" using lower_from_i by auto
        have lower_acc_N: "lower_accepting (rc N)"
        proof -
          have in_acc: "rc N \<in> {S \<in> lower_states \<A> . lower_accepting S} \<union> accepting_states (upper_part \<A>)" using N(2) unfolding comp_omega_automaton_def by auto
          have upper_wd: "auto_well_defined (upper_part \<A>)" using well_def_upper_part[OF assms(1)] by blast
          have "rc N \<notin> accepting_states (upper_part \<A>)"
          proof
            assume "rc N \<in> accepting_states (upper_part \<A>)"
            hence "rc N \<in> states (upper_part \<A>)" using upper_wd unfolding auto_well_defined_def by blast
            hence "rc N \<in> states (upper_part \<A>) \<inter> lower_states \<A>" using lowerN by blast
            thus False using upper_and_lower_states_disjoint by blast
          qed
          thus ?thesis using in_acc lowerN by auto
        qed
        obtain kN where kN: "upper_child_segment_up rc i N x \<A> j kN" "upper_continued_up rc \<A> x N kN" using continued_reaches_continued_component[OF cont_up_i _ j(1), of N] using N(1) by auto
        hence color1_N: "snd (rc N ! kN) = 1" using all1 N(1) by auto
        obtain kS where kS: "upper_child_up (rc N) (x N) \<A> (rc (Suc N)) kN kS" "upper_continued_up rc \<A> x (Suc N) kS" using continued_has_continued_successor[OF kN(2)] by blast
        have stepN: "(rc N, x N, rc (Suc N)) \<in> lower_transitions \<A>"
        proof -
          have "(rc N, x N, rc (Suc N)) \<in> transitions (comp_omega_automaton \<A>)" using assms(3) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
          hence "(rc N, x N, rc (Suc N)) \<in> transitions (upper_part \<A>) \<or> (rc N, x N, rc (Suc N)) \<in> lower_transitions \<A> \<or> (rc N, x N, rc (Suc N)) \<in> lower_transitions_from_upper \<A>" unfolding comp_omega_automaton_def by auto
          then consider (up) "(rc N, x N, rc (Suc N)) \<in> transitions (upper_part \<A>)" | (low) "(rc N, x N, rc (Suc N)) \<in> lower_transitions \<A>" | (jump) "(rc N, x N, rc (Suc N)) \<in> lower_transitions_from_upper \<A>" by fast
          thus ?thesis
          proof cases
            case up
            hence "rc N \<in> states (upper_part \<A>)" using assms(1) well_def_upper_part well_def_trans_components by fast
            hence "rc N \<in> states (upper_part \<A>) \<inter> lower_states \<A>" using lowerN by blast
            thus ?thesis using upper_and_lower_states_disjoint by blast
          next
            case low thus ?thesis by blast
          next
            case jump
            hence "rc N \<in> states (upper_part \<A>)" unfolding lower_transitions_from_upper_def by auto
            hence "rc N \<in> states (upper_part \<A>) \<inter> lower_states \<A>" using lowerN by blast
            thus ?thesis using upper_and_lower_states_disjoint by blast
          qed
        qed
        have color2_suc: "snd (rc (Suc N) ! kS) = 2" using lower_accepting_child_color1_to_color2[OF stepN lower_acc_N kS(1) color1_N] by blast
        have seg_suc: "upper_child_segment_up rc i (Suc N) x \<A> j kS" using upper_child_segment_up_extend_one[OF kN(1) kS(1)] using N(1) by auto
        have color1_suc: "snd (rc (Suc N) ! kS) = 1" using all1 seg_suc kS(2) N(1) by auto
        thus False using color2_suc by auto
      qed
    qed
  qed
qed

lemma not_in_language_eventually_no_TF:
  assumes "auto_well_defined \<A>" "omega_word_well_defined x (alphabet \<A>)" "x \<notin> omega_language_auto \<A>" "omega_run_well_defined Run (upper_part \<A>) x" "\<forall> n . Run n \<noteq> []"
  shows "\<exists> k . \<forall> i \<ge> k . \<not> upper_slice_continued_F_up Run \<A> x i"
proof -
  have "\<not> (\<exists> Run . omega_run_well_defined Run (upper_part \<A>) x \<and> (\<forall> n . Run n \<noteq> []) \<and> infinite {i . upper_slice_continued_F_up Run \<A> x i})" using assms(1,3) cor_3_4_15 by blast
  hence "finite {i . upper_slice_continued_F_up Run \<A> x i}" using assms(4,5) by blast
  then obtain k where "\<forall> i \<ge> k . i \<notin> {i . upper_slice_continued_F_up Run \<A> x i}" using finite_nat_set_iff_bounded_le not_less_eq_eq by metis
  thus ?thesis by blast
qed

lemma exists_upper_part_run:
  assumes "auto_well_defined \<A>" "omega_word_well_defined x (alphabet \<A>)"
  shows "\<exists> Run . omega_run_well_defined Run (upper_part \<A>) x"
proof -
  have wd_up: "auto_well_defined (upper_part \<A>)" using well_def_upper_part[OF assms(1)] by blast
  have alph: "alphabet (upper_part \<A>) = alphabet \<A>" using alphabet_upper_part by fast
  have word_up: "omega_word_well_defined x (alphabet (upper_part \<A>))" using assms(2) alph by simp
  thus ?thesis using exists_only_one_omega_run_for_DFA[OF wd_up DFA_upper_part[OF assms(1)] word_up] by blast
qed

lemma upper_part_empty_transition_sink:
  assumes "([], a, q) \<in> transitions (upper_part \<A>)"
  shows "q = []"
proof -
  have "([], a, q) \<in> image (\<lambda>(s1, a, s2). (map (cross_renaming_iso 3) s1, id a, map (cross_renaming_iso 3) s2)) (transitions (upper_part_pure \<A>))" using assms unfolding upper_part_def type_encode_automaton_def by simp
  then obtain s1 s2 where h: "map (cross_renaming_iso 3) s1 = []" "q = map (cross_renaming_iso 3) s2" "(s1, a, s2) \<in> transitions (upper_part_pure \<A>)" by auto
  hence "s1 = []" by simp
  hence "s2 = []" using h(3) unfolding upper_part_pure_def upper_transitions_def by auto
  thus ?thesis using h(2) by simp
qed

lemma upper_part_empty_state_accepting:
  assumes "omega_run_well_defined Run (upper_part \<A>) x" "Run n = []"
  shows "omega_run_accepting Run (upper_part \<A>) x"
proof -
  have acc_empty: "[] \<in> accepting_states (upper_part \<A>)" unfolding upper_part_def type_encode_automaton_def upper_part_pure_def cross_renaming_iso_def by auto
  {
    fix m assume "m \<ge> n"
    hence "Run m = []"
    proof (induction "m - n" arbitrary: m)
      case 0 thus ?case using assms(2) by auto
    next
      case (Suc d)
      then obtain m' where m': "m = Suc m'" by (cases m) auto
      hence "m' \<ge> n" using Suc by linarith
      hence prev: "Run m' = []" using Suc m' by simp
      have "(Run m', x m', Run (Suc m')) \<in> transitions (upper_part \<A>)" using assms(1) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
      hence "Run (Suc m') = []" using prev upper_part_empty_transition_sink[of "x m'" "Run (Suc m')" \<A>] by simp
      thus ?case using m' by simp
    qed
  }
  hence sink: "\<forall> m \<ge> n . Run m = []" by blast
  {
    fix q
    let ?N = "max n q + 1"
    have N: "?N > q" by simp
    have "Run ?N = []" using sink by simp
    hence "\<exists> N > q . Run N \<in> accepting_states (upper_part \<A>)" using acc_empty N by auto
  }
  thus ?thesis using assms(1) unfolding omega_run_accepting_def by blast
qed

lemma upper_run_is_comp_run:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part \<A>) x"
  shows "omega_run_well_defined Run (comp_omega_automaton \<A>) x"
proof -
  have init: "Run 0 = initial_state (comp_omega_automaton \<A>)" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def comp_omega_automaton_def by auto
  have in_states: "initial_state (comp_omega_automaton \<A>) \<in> states (comp_omega_automaton \<A>)" using assms well_def_comp_omega_auto unfolding auto_well_defined_def by blast
  have "\<forall> n . (Run n, x n, Run (Suc n)) \<in> transitions (comp_omega_automaton \<A>)" using assms unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def comp_omega_automaton_def by auto
  thus ?thesis unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def using init in_states by auto
qed

lemma upper_accepting_run_is_comp_accepting_run:
  assumes "auto_well_defined \<A>" "omega_run_accepting Run (upper_part \<A>) x"
  shows "omega_run_accepting Run (comp_omega_automaton \<A>) x"
proof -
  have upper_wd:  "omega_run_well_defined Run (upper_part \<A>) x" using assms(2) unfolding omega_run_accepting_def by blast
  have comp_wd: "omega_run_well_defined Run (comp_omega_automaton \<A>) x"  using upper_run_is_comp_run[OF assms(1) upper_wd] by blast
  {
    fix n obtain N where N: "N > n" "Run N \<in> accepting_states (upper_part \<A>)" using assms(2) unfolding omega_run_accepting_def by blast
    hence "Run N \<in> accepting_states (comp_omega_automaton \<A>)" unfolding comp_omega_automaton_def by auto
    hence "\<exists> N > n . Run N \<in> accepting_states (comp_omega_automaton \<A>)" using N(1) by blast
  }
  thus ?thesis using comp_wd unfolding omega_run_accepting_def by blast
qed

lemma upper_part_empty_yields_comp_accepting_run:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part \<A>) x" "\<exists> n . Run n = []"
  shows "\<exists> rc . omega_run_accepting rc (comp_omega_automaton \<A>) x"
proof -
  obtain n where n: "Run n = []" using assms(3) by blast
  have upper_acc: "omega_run_accepting Run (upper_part \<A>) x" using upper_part_empty_state_accepting[OF assms(2) n] by blast
  have comp_acc: "omega_run_accepting Run (comp_omega_automaton \<A>) x" using upper_accepting_run_is_comp_accepting_run[OF assms(1) upper_acc] by blast
  thus ?thesis by blast
qed

lemma upper_transition_nonempty_has_lower_successor:
  assumes "auto_well_defined \<A>" "(S, a, S') \<in> transitions (upper_part \<A>)" "S \<noteq> []" "S' \<noteq> []"
  shows "\<exists> L . (S, a, L) \<in> lower_transitions_from_upper \<A> \<and> L \<in> lower_states \<A>"
proof -
  define L where "L = filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_from_upper \<A> a S))"
  have S_in: "S \<in> states (upper_part \<A>)" using assms(1,2) well_def_upper_part well_def_trans_components by fast
  have "a \<in> alphabet (upper_part \<A>)" using assms(1,2) well_def_upper_part well_def_trans_components by fast
  hence a_in: "a \<in> alphabet \<A>" using alphabet_upper_part by fast

  have "(map fst S, a, map fst S') \<in> transitions (upper_part_pure \<A>)" using upper_transition_projects_to_upper_pure[OF assms(2)] by blast
  hence "(map fst S, a, map fst S') \<in> upper_transitions \<A>" using assms(3,4) unfolding upper_part_pure_def by auto
  hence S'_eq: "map fst S' = filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a (map fst S)))" unfolding upper_transitions_def by auto
  have "map fst L = map fst S'" using lower_step_from_upper_fst[of \<A> a S] S'_eq unfolding L_def by simp
  hence "L \<noteq> []" using assms(4) by auto
  hence trans_lower: "(S, a, L) \<in> lower_transitions_from_upper \<A>" using S_in assms(3) a_in unfolding lower_transitions_from_upper_def L_def by blast
  have "L \<in> lower_states \<A>" using lower_transitions_from_upper_target_in_lower_states[OF assms(1) trans_lower] by blast
  thus ?thesis using trans_lower by blast
qed

lemma upper_transition_nonempty_has_lower_successor_project:
  assumes "auto_well_defined \<A>" "(S, a, S') \<in> transitions (upper_part \<A>)" "S \<noteq> []" "S' \<noteq> []"
  shows "\<exists> L . (S, a, L) \<in> lower_transitions_from_upper \<A> \<and> L \<in> lower_states \<A> \<and> map fst L = map fst S'"
proof -
  obtain L where L: "(S, a, L) \<in> lower_transitions_from_upper \<A>" "L \<in> lower_states \<A>" using upper_transition_nonempty_has_lower_successor[OF assms] by blast
  hence L_def: "L = filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_from_upper \<A> a S))" unfolding lower_transitions_from_upper_def by auto
  have "(map fst S, a, map fst S') \<in> transitions (upper_part_pure \<A>)" using upper_transition_projects_to_upper_pure[OF assms(2)] by blast
  hence "(map fst S, a, map fst S') \<in> upper_transitions \<A>" using assms(3,4) unfolding upper_part_pure_def by auto
  hence "map fst S' = filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a (map fst S)))" unfolding upper_transitions_def by auto
  hence "map fst L = map fst S'" using lower_step_from_upper_fst[of \<A> a S] unfolding L_def  by simp
  thus ?thesis using L by blast
qed

lemma lower_transition_target_unique:
  assumes "(S, a, S1) \<in> lower_transitions \<A>" "(S, a, S2) \<in> lower_transitions \<A>"
  shows "S1 = S2"
  using assms unfolding lower_transitions_def by auto

lemma comp_lower_transition_unique:
  assumes "auto_well_defined \<A>" "S \<in> lower_states \<A>" "(S, a, S1) \<in> transitions (comp_omega_automaton \<A>)" "(S, a, S2) \<in> transitions (comp_omega_automaton \<A>)"
  shows "S1 = S2 \<and> S1 \<in> lower_states \<A>"
proof -
  have not_upper: "S \<notin> states (upper_part \<A>)" using assms(2) upper_and_lower_states_disjoint by blast
  hence not_up_trans1: "(S, a, S1) \<notin> transitions (upper_part \<A>)" using assms(1) well_def_upper_part well_def_trans_components by fast
  have "(S, a, S1) \<notin> lower_transitions_from_upper \<A>" using not_upper unfolding lower_transitions_from_upper_def by auto
  hence t1: "(S, a, S1) \<in> lower_transitions \<A>" using assms(3) not_up_trans1 unfolding comp_omega_automaton_def by auto
  have not_up_trans2: "(S, a, S2) \<notin> transitions (upper_part \<A>)" using assms(1) well_def_upper_part well_def_trans_components not_upper by fast
  have "(S, a, S2) \<notin> lower_transitions_from_upper \<A>" using not_upper unfolding lower_transitions_from_upper_def by auto
  hence t2: "(S, a, S2) \<in> lower_transitions \<A>" using assms(4) not_up_trans2 unfolding comp_omega_automaton_def by auto
  show ?thesis using lower_transition_target_unique[OF t1 t2] lower_transitions_target_in_lower_states[OF assms(1) t1] by blast
qed

lemma comp_lower_transition_ex1:
  assumes "auto_well_defined \<A>" "S \<in> lower_states \<A>" "a \<in> alphabet \<A>" "\<exists> S'. (S, a, S') \<in> transitions (comp_omega_automaton \<A>)"
  shows "\<exists>! S'. S' \<in> states (comp_omega_automaton \<A>) \<and> (S, a, S') \<in> transitions (comp_omega_automaton \<A>)"
proof -
  obtain S' where tr: "(S, a, S') \<in> transitions (comp_omega_automaton \<A>)" using assms(4) by blast
  hence S'_state: "S' \<in> states (comp_omega_automaton \<A>)" using assms(1) well_def_comp_omega_auto well_def_trans_components by fast
  have "\<forall> T . T \<in> states (comp_omega_automaton \<A>) \<and> (S, a, T) \<in> transitions (comp_omega_automaton \<A>) \<longrightarrow> T = S'" using comp_lower_transition_unique[OF assms(1,2)] tr by blast
  thus ?thesis using tr S'_state by blast
qed

lemma omega_prun_from_lower_are_lower_states:
  assumes "auto_well_defined \<A>" "s \<in> lower_states \<A>" "omega_word_well_defined w (alphabet \<A>)" "\<forall> n . \<exists> s2 . (omega_prun_from s (comp_omega_automaton \<A>) w n, w n, s2) \<in> transitions (comp_omega_automaton \<A>)"
  shows "omega_prun_from s (comp_omega_automaton \<A>) w n \<in> lower_states \<A>"
proof (induction n)
  case 0 thus ?case using assms(2) by simp
next
  case (Suc n)
  hence curr: "omega_prun_from s (comp_omega_automaton \<A>) w n \<in> lower_states \<A>" by blast
  obtain s2 where s2: "(omega_prun_from s (comp_omega_automaton \<A>) w n, w n, s2) \<in> transitions (comp_omega_automaton \<A>)" using assms by blast
  have a_in: "w n \<in> alphabet \<A>" using assms(3) unfolding omega_word_well_defined_def by blast
  have ex1: "\<exists>! t . t \<in> states (comp_omega_automaton \<A>) \<and> (omega_prun_from s (comp_omega_automaton \<A>) w n, w n, t) \<in> transitions (comp_omega_automaton \<A>)" using comp_lower_transition_ex1[OF assms(1) curr a_in] s2 by blast
  have "s2 \<in> states (comp_omega_automaton \<A>)" using assms(1) s2 well_def_comp_omega_auto well_def_trans_components by fast
  hence next_eq: "omega_prun_from s (comp_omega_automaton \<A>) w (Suc n) = s2" using the1_equality[OF ex1, of s2] s2 by simp
  have "s2 \<in> lower_states \<A>" using comp_lower_transition_unique[OF assms(1) curr s2] s2 by blast
  thus ?case using next_eq by simp
qed

lemma omega_prun_from_lower_transitions:
  assumes "auto_well_defined \<A>" "s \<in> lower_states \<A>" "omega_word_well_defined w (alphabet \<A>)" "\<forall> n . \<exists> s2 . (omega_prun_from s (comp_omega_automaton \<A>) w n, w n, s2) \<in> transitions (comp_omega_automaton \<A>)"
  shows "(omega_prun_from s (comp_omega_automaton \<A>) w n, w n, omega_prun_from s (comp_omega_automaton \<A>) w (n + 1)) \<in> transitions (comp_omega_automaton \<A>)"
proof -
  have curr: "omega_prun_from s (comp_omega_automaton \<A>) w n \<in> lower_states \<A>" using omega_prun_from_lower_are_lower_states[OF assms] .
  obtain s2 where s2: "(omega_prun_from s (comp_omega_automaton \<A>) w n, w n, s2) \<in> transitions (comp_omega_automaton \<A>)" using assms by blast
  have a_in: "w n \<in> alphabet \<A>" using assms(3) unfolding omega_word_well_defined_def by blast
  have ex1: "\<exists>! t . t \<in> states (comp_omega_automaton \<A>) \<and> (omega_prun_from s (comp_omega_automaton \<A>) w n, w n, t) \<in> transitions (comp_omega_automaton \<A>)" using comp_lower_transition_ex1[OF assms(1) curr a_in] s2 by blast
  have "s2 \<in> states (comp_omega_automaton \<A>)" using assms(1) s2 well_def_comp_omega_auto well_def_trans_components by fast
  hence next_eq: "omega_prun_from s (comp_omega_automaton \<A>) w (Suc n) = s2" using the1_equality[OF ex1, of s2] s2 by simp
  thus ?thesis using s2 by auto
qed

lemma omega_prun_from_lower_pseudo_run:
  assumes "auto_well_defined \<A>" "s \<in> lower_states \<A>" "omega_word_well_defined w (alphabet \<A>)" "\<forall> n . \<exists> s2 . (omega_prun_from s (comp_omega_automaton \<A>) w n, w n, s2) \<in> transitions (comp_omega_automaton \<A>)"
  shows "omega_pseudo_run_well_defined (omega_prun_from s (comp_omega_automaton \<A>) w) (comp_omega_automaton \<A>) s w"
proof -
  have s_state: "s \<in> states (comp_omega_automaton \<A>)" using assms(2) unfolding comp_omega_automaton_def by auto
  have "\<forall> n . (omega_prun_from s (comp_omega_automaton \<A>) w n, w n, omega_prun_from s (comp_omega_automaton \<A>) w (n + 1)) \<in> transitions (comp_omega_automaton \<A>)" using omega_prun_from_lower_transitions[OF assms] by blast
  thus ?thesis using s_state  unfolding omega_pseudo_run_well_defined_def by auto
qed

lemma lower_step_simulates_upper:
  assumes "auto_well_defined \<A>" "S \<in> lower_states \<A>" "(map fst S, a, U') \<in> transitions (upper_part_pure \<A>)" "U' \<noteq> []"
  shows "\<exists> S' . (S, a, S') \<in> lower_transitions \<A> \<and> S' \<in> lower_states \<A> \<and> map fst S' = U'"
proof -
  define S' where "S' = (if lower_accepting S then filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_acc \<A> a S)) else filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_nacc \<A> a S)))"
  have src_upper: "map fst S \<in> upper_states \<A>" using map_fst_lower_state_in_upper_states[OF assms(2)] by blast
  have src_ne: "map fst S \<noteq> []" using assms(2) unfolding lower_states_def by auto
  have "(map fst S, a, U') \<in> upper_transitions \<A> \<union> {(s1, a, s2) . s1 \<in> upper_states \<A> \<and> s2 = [] \<and> a \<in> alphabet \<A> \<and> (\<nexists>s . (s1, a, s) \<in> upper_transitions \<A>)} \<union> {(s1, a, s2) . s1 = [] \<and> s2 = [] \<and> a \<in> alphabet \<A>}" using assms(3) unfolding upper_part_pure_def by auto
  hence up_trans: "(map fst S, a, U') \<in> upper_transitions \<A>" using assms(4) src_ne by auto
  hence up_def: "U' = filter (\<lambda>S_m . S_m \<noteq> {}) (fst (upper_step \<A> a (map fst S)))" unfolding upper_transitions_def by auto
  have acc_proj: "map fst (filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_acc \<A> a S))) = U'" using lower_step_acc_fst[of \<A> a S] up_def by simp
  have nacc_proj: "map fst (filter (\<lambda>S_m . fst S_m \<noteq> {}) (fst (lower_step_nacc \<A> a S))) = U'" using lower_step_nacc_fst[of \<A> a S] up_def by simp
  have proj: "map fst S' = U'" using acc_proj nacc_proj unfolding S'_def by auto
  hence not_empty: "S' \<noteq> []" using assms(4) by auto
  have "a \<in> alphabet \<A>" using up_trans unfolding upper_transitions_def by auto
  hence lower: "(S, a, S') \<in> lower_transitions \<A>" using assms(2) not_empty  unfolding lower_transitions_def S'_def by auto
  have "S' \<in> lower_states \<A>" using lower_transitions_target_in_lower_states[OF assms(1) lower] by blast
  thus ?thesis using proj lower by blast
qed

lemma omega_prun_from_lower_follows_upper:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part \<A>) x" "\<forall> n . Run n \<noteq> []" "s \<in> lower_states \<A>" "map fst s = map fst (Run l)"
  shows "omega_prun_from s (comp_omega_automaton \<A>) (\<lambda>n . x (l + n)) n \<in> lower_states \<A> \<and> map fst (omega_prun_from s (comp_omega_automaton \<A>) (\<lambda>n . x (l + n)) n) = map fst (Run (l + n))"
proof (induction n)
  case 0 thus ?case using assms(4,5) by force
next
  case (Suc n)
  let ?C = "comp_omega_automaton \<A>"
  let ?w = "\<lambda>n . x (l + n)"
  let ?r = "omega_prun_from s ?C ?w"
  have curr_lower: "?r n \<in> lower_states \<A>" using Suc by blast
  have curr_proj: "map fst (?r n) = map fst (Run (l + n))"  using Suc by blast
  have upper_tr: "(Run (l + n), x (l + n), Run (Suc (l + n))) \<in> transitions (upper_part \<A>)" using assms(2) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
  have "(map fst (Run (l + n)), x (l + n), map fst (Run (Suc (l + n)))) \<in> transitions (upper_part_pure \<A>)" using upper_transition_projects_to_upper_pure[OF upper_tr] by blast
  hence upper_pure_tr_curr: "(map fst (?r n), ?w n, map fst (Run (Suc (l + n)))) \<in> transitions (upper_part_pure \<A>)" using curr_proj by simp
  have next_ne: "map fst (Run (Suc (l + n))) \<noteq> []" using assms(3) by auto
  obtain Snext where Snext: "(?r n, ?w n, Snext) \<in> lower_transitions \<A>" "Snext \<in> lower_states \<A>" "map fst Snext = map fst (Run (Suc (l + n)))" using lower_step_simulates_upper[OF assms(1) curr_lower upper_pure_tr_curr next_ne] by blast
  hence trans_comp: "(?r n, ?w n, Snext) \<in> transitions ?C" unfolding comp_omega_automaton_def by auto
  have Snext_state: "Snext \<in> states ?C" using Snext(2) unfolding comp_omega_automaton_def by auto
  have "\<And>t . t \<in> states ?C \<Longrightarrow> (?r n, ?w n, t) \<in> transitions ?C \<Longrightarrow> t = Snext" using comp_lower_transition_unique[OF assms(1) curr_lower _ trans_comp]  by blast
  hence ex1: "\<exists>! t . t \<in> states ?C \<and> (?r n, ?w n, t) \<in> transitions ?C" using Snext_state trans_comp  by blast
  have next_eq: "?r (Suc n) = Snext" using the1_equality[OF ex1, of Snext] Snext_state trans_comp by simp
  have "Suc (l + n) = l + Suc n" by simp
  thus ?case using next_eq Snext by simp
qed

lemma omega_prun_from_lower_has_successor_from_upper:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part \<A>) x" "\<forall> n . Run n \<noteq> []" "s \<in> lower_states \<A>" "map fst s = map fst (Run l)"
  shows "\<forall> n . \<exists> s2 . (omega_prun_from s (comp_omega_automaton \<A>) (\<lambda>n . x (l + n)) n, x (l + n), s2) \<in> transitions (comp_omega_automaton \<A>)"
proof
  fix n
  let ?r = "omega_prun_from s (comp_omega_automaton \<A>) (\<lambda>n . x (l + n))"
  have rn: "?r n \<in> lower_states \<A>" "map fst (?r n) = map fst (Run (l + n))" using omega_prun_from_lower_follows_upper[OF assms, of n] by blast+
  have upper_tr: "(Run (l + n), x (l + n), Run (Suc (l + n))) \<in> transitions (upper_part \<A>)" using assms(2) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
  have upper_pure_tr: "(map fst (Run (l + n)), x (l + n), map fst (Run (Suc (l + n)))) \<in> transitions (upper_part_pure \<A>)" using upper_transition_projects_to_upper_pure[OF upper_tr] by blast
  have "map fst (Run (Suc (l + n))) \<noteq> []" using assms(3) by auto
  then obtain s2 where "(?r n, x (l + n), s2) \<in> lower_transitions \<A>" "s2 \<in> lower_states \<A>" "map fst s2 = map fst (Run (Suc (l + n)))" using lower_step_simulates_upper[OF assms(1) rn(1), of "x (l + n)" "map fst (Run (Suc (l + n)))"] upper_pure_tr rn(2) by auto
  thus "\<exists> s2 . (?r n, x (l + n), s2) \<in> transitions (comp_omega_automaton \<A>)" unfolding comp_omega_automaton_def by auto
qed

lemma omega_prun_from_lower_pseudo_run_from_upper:
  assumes "auto_well_defined \<A>" "omega_run_well_defined Run (upper_part \<A>) x" "\<forall> n . Run n \<noteq> []" "s \<in> lower_states \<A>" "map fst s = map fst (Run l)" "omega_word_well_defined (\<lambda>n . x (l + n)) (alphabet \<A>)"
  shows "omega_pseudo_run_well_defined (omega_prun_from s (comp_omega_automaton \<A>) (\<lambda>n . x (l + n))) (comp_omega_automaton \<A>) s (\<lambda>n . x (l + n))"
  using omega_prun_from_lower_pseudo_run[OF assms(1) assms(4) assms(6) omega_prun_from_lower_has_successor_from_upper[OF assms(1,2,3,4,5)]] by simp

definition jump_lower_run :: "(('s states \<times> nat) list) omega_run \<Rightarrow> (('s states \<times> nat) list) \<Rightarrow> nat \<Rightarrow> 'a omega_word \<Rightarrow> ('s, 'a) automaton \<Rightarrow> (('s states \<times> nat) list) omega_run" where "jump_lower_run Run L l x \<A> n = (if n < l then Run n else omega_prun_from L (comp_omega_automaton \<A>) (\<lambda>m . x (l + m)) (n - l))"

lemma upper_run_nonempty_can_jump_to_lower_at:
  assumes "auto_well_defined \<A>" "omega_word_well_defined x (alphabet \<A>)" "omega_run_well_defined Run (upper_part \<A>) x" "\<forall> n . Run n \<noteq> []" "l > 0"
  shows "\<exists> rc . omega_run_well_defined rc (comp_omega_automaton \<A>) x \<and> (\<forall> n < l . rc n = Run n) \<and> rc l \<in> lower_states \<A> \<and> (\<exists> S a . (S, a, rc l) \<in> lower_transitions_from_upper \<A>) \<and> (\<forall> n \<ge> l . map fst (rc n) = map fst (Run n))"
proof -
  define p where "p = l - 1"
  hence l_eq: "l = Suc p" using assms(5) by simp
  hence upper_step: "(Run p, x p, Run l) \<in> transitions (upper_part \<A>)" using assms(3) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
  obtain L where L: "(Run p, x p, L) \<in> lower_transitions_from_upper \<A>" "L \<in> lower_states \<A>" "map fst L = map fst (Run l)" using upper_transition_nonempty_has_lower_successor_project[OF assms(1) upper_step assms(4)[rule_format] assms(4)[rule_format]] by blast
  define rc where "rc = jump_lower_run Run L l x \<A>"
  have shift_word: "omega_word_well_defined (\<lambda>m . x (l + m)) (alphabet \<A>)" using assms(2) unfolding omega_word_well_defined_def by auto
  have lower_prun: "omega_pseudo_run_well_defined (omega_prun_from L (comp_omega_automaton \<A>) (\<lambda>m . x (l + m))) (comp_omega_automaton \<A>) L (\<lambda>m . x (l + m))" using omega_prun_from_lower_pseudo_run_from_upper[OF assms(1,3,4) L(2,3) shift_word] by blast
  have "rc 0 = Run 0" using assms(5)  unfolding rc_def jump_lower_run_def by simp
  hence "rc 0 = initial_state (upper_part \<A>)" using assms(3) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by simp
  hence init: "rc 0 = initial_state (comp_omega_automaton \<A>)" unfolding comp_omega_automaton_def by simp
  have init_in: "initial_state (comp_omega_automaton \<A>) \<in> states (comp_omega_automaton \<A>)" using well_def_comp_omega_auto[OF assms(1)] unfolding auto_well_defined_def by blast
  {
    fix n
    consider (case1) "Suc n < l" | (case2) "Suc n = l" | (case3) "Suc n > l" by linarith
    hence "(rc n, x n, rc (Suc n)) \<in> transitions (comp_omega_automaton \<A>)"
    proof cases
      case case1
      hence n: "rc n = Run n" unfolding rc_def jump_lower_run_def by simp
      have sucn: "rc (Suc n) = Run (Suc n)" using case1 unfolding rc_def jump_lower_run_def by simp
      have "(Run n, x n, Run (Suc n)) \<in> transitions (upper_part \<A>)" using assms(3) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
      thus ?thesis using n sucn unfolding comp_omega_automaton_def by auto
    next
      case case2
        hence n_eq: "n = p" using l_eq by simp
        hence n: "rc n = Run p" using assms(5) l_eq unfolding rc_def jump_lower_run_def by simp
        have "rc (Suc n) = L" using case2 unfolding rc_def jump_lower_run_def by simp
        thus ?thesis using L(1) n_eq n unfolding comp_omega_automaton_def by auto
    next
      case case3
      hence rc_n: "rc n = omega_prun_from L (comp_omega_automaton \<A>) (\<lambda>m . x (l + m)) (n - l)" unfolding rc_def jump_lower_run_def by simp
      have rc_suc: "rc (Suc n) = omega_prun_from L (comp_omega_automaton \<A>) (\<lambda>m . x (l + m)) (Suc n - l)" using case3 unfolding rc_def jump_lower_run_def by simp
      have opf: "(omega_prun_from L (comp_omega_automaton \<A>) (\<lambda>m . x (l + m)) (n - l), (\<lambda>m . x (l + m)) (n - l), omega_prun_from L (comp_omega_automaton \<A>) (\<lambda>m . x (l + m)) ((n - l) + 1)) \<in> transitions (comp_omega_automaton \<A>)" using lower_prun unfolding omega_pseudo_run_well_defined_def by blast
      have xn: "(\<lambda>m . x (l + m)) (n - l) = x n" using case3 by simp
      have "(n - l) + 1 = Suc n - l" using case3 by simp
      hence "(omega_prun_from L (comp_omega_automaton \<A>) (\<lambda>m . x (l + m)) (n - l), x n, omega_prun_from L (comp_omega_automaton \<A>) (\<lambda>m . x (l + m)) (Suc n - l)) \<in> transitions (comp_omega_automaton \<A>)" using opf xn by argo
      thus ?thesis  using rc_n rc_suc by simp
    qed
  }
  hence "\<forall> n . (rc n, x n, rc (Suc n)) \<in> transitions (comp_omega_automaton \<A>)" by blast
  hence rc_wd: "omega_run_well_defined rc (comp_omega_automaton \<A>) x" using init init_in unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by simp
  {
    fix n assume nl: "n \<ge> l"
    hence rc_n: "rc n = omega_prun_from L (comp_omega_automaton \<A>) (\<lambda>m . x (l + m)) (n - l)" unfolding rc_def jump_lower_run_def by simp
    have "map fst (omega_prun_from L (comp_omega_automaton \<A>) (\<lambda>m . x (l + m)) (n - l)) = map fst (Run (l + (n - l)))" using omega_prun_from_lower_follows_upper[OF assms(1,3,4) L(2,3), of "n - l"] by blast
    hence "map fst (rc n) = map fst (Run n)" using rc_n nl by simp
  }
  hence same_fst_from_l: "\<forall> n \<ge> l . map fst (rc n) = map fst (Run n)" by blast
  have prefix: "\<forall> n < l . rc n = Run n" unfolding rc_def jump_lower_run_def by simp
  have rc_l: "rc l \<in> lower_states \<A>" using L(2) unfolding rc_def jump_lower_run_def by simp
  have "rc l = L" unfolding rc_def jump_lower_run_def by simp
  hence "\<exists> S a . (S, a, rc l) \<in> lower_transitions_from_upper \<A>" using L(1) by blast
  thus ?thesis using rc_wd prefix rc_l same_fst_from_l by blast
qed

lemma lower_nonaccepting_contains_color2:
  assumes "S \<in> lower_states \<A>" "S \<notin> accepting_states (comp_omega_automaton \<A>)"
  shows "\<exists> j < length S . snd (S ! j) = 2"
proof -
  have "\<not> lower_accepting S" using assms unfolding comp_omega_automaton_def by force
  then obtain X where X:  "X \<in> set S" "snd X = 2" unfolding lower_accepting_def by force
  then obtain j where j: "j < length S" "S ! j = X" using in_set_conv_nth by metis
  thus ?thesis using X by auto
qed

lemma lower_step_nacc_raw_color2_has_pred:
  assumes "\<forall> Sm \<in> set S . snd Sm \<in> {0, 1, 2}" "X \<in> set (fst (lower_step_nacc \<A> a S))" "fst X \<noteq> {}" "snd X = 2"
  shows "\<exists> j < length S . snd (S ! j) = 2 \<and> fst X \<subseteq> post_set \<A> (fst (S ! j)) a \<and> fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}"
using assms proof (induction S arbitrary: X)
  case Nil thus ?case by simp
next
  case (Cons Sm S)
  let ?L = "((post_set \<A> (fst Sm) a - snd (lower_step_nacc \<A> a S)) - accepting_states \<A>, snd Sm)"
  let ?R = "((post_set \<A> (fst Sm) a - snd (lower_step_nacc \<A> a S)) \<inter> accepting_states \<A>, max (snd Sm) 1)"
  have snd_eq: "snd (lower_step_nacc \<A> a S) = snd (upper_step \<A> a (map fst S))" using lower_step_nacc_snd_eq_upper_step by fast
  have "X = ?L \<or> X = ?R \<or> X \<in> set (fst (lower_step_nacc \<A> a S))" using Cons by simp
  then consider (case1) "X = ?L" | (case2) "X = ?R" | (case3) "X \<in> set (fst (lower_step_nacc \<A> a S))" by fast
  thus ?case
  proof cases
    case case1
    hence "snd Sm = 2" using Cons by simp
    thus ?thesis using case1 snd_eq by auto
  next
    case case2
    hence "snd Sm = 2" using Cons by auto
    thus ?thesis using case2 snd_eq by auto
  next
    case case3
    have cols_tail: "\<forall> Sm \<in> set S . snd Sm \<in> {0, 1, 2}" using Cons by auto
    obtain j where "j < length S" "snd (S ! j) = 2" "fst X \<subseteq> post_set \<A> (fst (S ! j)) a" "fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}" using Cons.IH[OF cols_tail case3 Cons.prems(3,4)] by blast
    thus ?thesis by fastforce
  qed
qed
    
lemma lower_nonaccepting_color2_has_color2_predecessor:
  assumes "(S, a, S') \<in> lower_transitions \<A>" "\<not> lower_accepting S" "k < length S'" "snd (S' ! k) = 2"
  shows "\<exists> j < length S . snd (S ! j) = 2 \<and> upper_child_up S a \<A> S' j k"
proof -
  have S_def: "S \<in> lower_states \<A>" "S' = filter (\<lambda>X . fst X \<noteq> {}) (fst (lower_step_nacc \<A> a S))" using assms(1,2) unfolding lower_transitions_def by auto
  hence cols: "\<forall> Sm \<in> set S . snd Sm \<in> {0, 1, 2}" unfolding lower_states_def by blast
  have raw: "S' ! k \<in> set (fst (lower_step_nacc \<A> a S))" using assms S_def filter_is_subset nth_mem subsetD by metis
  have nz: "fst (S' ! k) \<noteq> {}" using assms(3) S_def(2) nth_mem by fastforce
  obtain j where j: "j < length S" "snd (S ! j) = 2" "fst (S' ! k) \<subseteq> post_set \<A> (fst (S ! j)) a" "fst (S' ! k) \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}" using lower_step_nacc_raw_color2_has_pred[OF cols raw nz assms(4)] by blast
  hence "upper_child_up S a \<A> S' j k" using assms(3) unfolding upper_child_up_def by blast
  thus ?thesis using j by blast
qed

lemma lower_run_nonaccepting_color2_segment_backwards:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "\<forall> n \<ge> B . rc n \<in> lower_states \<A>" "\<forall> n \<ge> B . \<not> lower_accepting (rc n)" "M \<ge> B" "k < length (rc M)" "snd (rc M ! k) = 2"
  shows "\<exists> j . j < length (rc B) \<and> snd (rc B ! j) = 2 \<and> upper_child_segment_up rc B M x \<A> j k"
using assms proof (induction "M - B" arbitrary: M k)
  case 0
  hence MB: "M = B" by simp
  hence "upper_child_segment_up rc B M x \<A> k k" unfolding upper_child_segment_up_def by (intro exI[of _ "[k]"]) auto
  thus ?case using 0 MB by blast
next
  case (Suc d)
  then obtain M' where M': "M = Suc M'" "B \<le> M'" by (cases M) auto
  hence diff: "d = M' - B" using Suc by simp
  have lower_M': "rc M' \<in> lower_states \<A>" using assms(3) M'(2) by blast
  have not_lower_acc_M': "\<not> lower_accepting (rc M')" using assms(4) M'(2) by blast
  have trans: "(rc M', x M', rc (Suc M')) \<in> transitions (comp_omega_automaton \<A>)" using assms(2) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
  have not_upper: "rc M' \<notin> states (upper_part \<A>)" using lower_M' upper_and_lower_states_disjoint by blast
  have not_up: "(rc M', x M', rc (Suc M')) \<notin> transitions (upper_part \<A>)"
  proof
    assume "(rc M', x M', rc (Suc M')) \<in> transitions (upper_part \<A>)"
    hence "rc M' \<in> states (upper_part \<A>)" using assms(1) well_def_upper_part well_def_trans_components by fast
    thus False using not_upper by blast
  qed
  have "(rc M', x M', rc (Suc M')) \<notin> lower_transitions_from_upper \<A>" using not_upper unfolding lower_transitions_from_upper_def by auto
  hence trans_lower: "(rc M', x M', rc (Suc M')) \<in> lower_transitions \<A>" using trans not_up  unfolding comp_omega_automaton_def by auto
  have k_len_M: "k < length (rc (Suc M'))" using Suc.prems M' by auto
  have k_col_M: "snd (rc (Suc M') ! k) = 2" using Suc.prems M' by auto
  obtain k' where pred: "k' < length (rc M')" "snd (rc M' ! k') = 2" "upper_child_up (rc M') (x M') \<A> (rc (Suc M')) k' k" using lower_nonaccepting_color2_has_color2_predecessor[OF trans_lower not_lower_acc_M' k_len_M k_col_M] by blast
  then obtain j where IH: "j < length (rc B)" "snd (rc B ! j) = 2" "upper_child_segment_up rc B M' x \<A> j k'" using Suc M' diff by blast
  have "upper_child_segment_up rc B M x \<A> j k" using upper_child_segment_up_extend_one[OF IH(3) pred(3) M'(2)] M' by simp
  thus ?case using IH(1,2) by blast
qed

lemma eventually_color2_has_continued_color2_at_B:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "\<forall> n \<ge> B . rc n \<in> lower_states \<A>" "\<forall> n \<ge> B . \<not> lower_accepting (rc n)" "\<forall> n \<ge> B . \<exists> k < length (rc n) . snd (rc n ! k) = 2"
  shows "\<exists> j < length (rc B) . snd (rc B ! j) = 2 \<and> upper_continued_up rc \<A> x B j"
proof -
  let ?K = "{j . j < length (rc B) \<and> snd (rc B ! j) = 2}"
  have finK: "finite ?K" by simp
  {
    fix M assume MB: "M > B"
    then obtain kM where "kM < length (rc M)" "snd (rc M ! kM) = 2" using assms(5) less_or_eq_imp_le by metis
    then obtain j where j: "j < length (rc B)" "snd (rc B ! j) = 2" "upper_child_segment_up rc B M x \<A> j kM" using lower_run_nonaccepting_color2_segment_backwards[OF assms(1,2,3,4), of M kM] MB by auto
    hence "j \<in> ?K" by simp
    hence "\<exists> j \<in> ?K . \<exists> k . upper_child_segment_up rc B M x \<A> j k" using j(3) by blast
  }
  hence exK: "\<forall> M > B . \<exists> j \<in> ?K . \<exists> k . upper_child_segment_up rc B M x \<A> j k" by blast
  obtain j where j: "j \<in> ?K" "\<forall> M > B . \<exists> M' \<ge> M . \<exists> k . upper_child_segment_up rc B M' x \<A> j k" using finite_arbitrarily_large_choice[OF finK exK] by blast
  hence j_len: "j < length (rc B)" by simp
  have j_col: "snd (rc B ! j) = 2" using j(1) by simp
  {
    fix M assume MB: "M > B"
    then obtain M' k where Mk: "M' \<ge> M" "upper_child_segment_up rc B M' x \<A> j k" using j(2) by blast
    then obtain k' where "upper_child_segment_up rc B M x \<A> j k'" using upper_child_segment_up_prefix[OF Mk(2)] MB  by force
    hence "\<exists> k . upper_child_segment_up rc B M x \<A> j k" by blast
  }
  hence "\<forall> M > B . \<exists> k .upper_child_segment_up rc B M x \<A> j k" by blast
  hence "upper_continued_up rc \<A> x B j" unfolding upper_continued_up_def by blast
  thus ?thesis using j_len j_col by blast
qed

lemma lower_nacc_color2_target_has_color2_pred_or_is_F:
  assumes "(S, a, S') \<in> lower_transitions \<A>" "\<not> lower_accepting S" "k < length S'" "snd (S' ! k) = 2"
  shows "(\<exists> j < length S . snd (S ! j) = 2 \<and> upper_child_up S a \<A> S' j k) \<or> fst (S' ! k) \<subseteq> accepting_states \<A>"
proof -
  have S'_def: "S' = filter (\<lambda>X . fst X \<noteq> {}) (fst (lower_step_nacc \<A> a S))" using assms(1,2) unfolding lower_transitions_def by auto
  hence raw: "S' ! k \<in> set (fst (lower_step_nacc \<A> a S))" using assms filter_is_subset nth_mem subsetD by metis
  have "S' ! k \<in> set S'" using assms(3) by simp
  hence nz: "fst (S' ! k) \<noteq> {}" using S'_def by force
  show ?thesis
  proof (cases "fst (S' ! k) \<subseteq> accepting_states \<A>")
    case True thus ?thesis by blast
  next
    case False
    have "S \<in> lower_states \<A>" using assms(1) unfolding lower_transitions_def by auto
    hence cols: "\<forall> Sm \<in> set S . snd Sm \<in> {0,1,2}" unfolding lower_states_def by blast
    obtain j where j: "j < length S" "snd (S ! j) = 2" "fst (S' ! k) \<subseteq> post_set \<A> (fst (S ! j)) a" "fst (S' ! k) \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}" using lower_step_nacc_raw_color2_has_pred[OF cols raw nz assms(4)] by blast
    hence "upper_child_up S a \<A> S' j k" using assms(3) unfolding upper_child_up_def by blast
    thus ?thesis using j(1,2) by blast
  qed
qed

lemma lower_run_color2_target_has_color2_pred_or_TF:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "rc n \<in> lower_states \<A>" "\<not> lower_accepting (rc n)" "k < length (rc (Suc n))" "snd (rc (Suc n) ! k) = 2"
  shows "(\<exists> j < length (rc n) . snd (rc n ! j) = 2 \<and> upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k) \<or> fst (rc (Suc n) ! k) \<subseteq> accepting_states \<A>"
proof -
  have trans: "(rc n, x n, rc (Suc n)) \<in> transitions (comp_omega_automaton \<A>)" using assms(2) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
  have not_upper: "rc n \<notin> states (upper_part \<A>)" using assms(3) upper_and_lower_states_disjoint by blast
  hence not_up_trans: "(rc n, x n, rc (Suc n)) \<notin> transitions (upper_part \<A>)" using assms(1) well_def_upper_part well_def_trans_components by fast
  have "(rc n, x n, rc (Suc n)) \<notin> lower_transitions_from_upper \<A>" using not_upper unfolding lower_transitions_from_upper_def by auto
  hence lower_trans: "(rc n, x n, rc (Suc n)) \<in> lower_transitions \<A>" using trans not_up_trans unfolding comp_omega_automaton_def by auto
  thus ?thesis using lower_nacc_color2_target_has_color2_pred_or_is_F[OF lower_trans assms(4,5,6)] by blast
qed

lemma upper_continued_up_prepend_one:
  assumes "upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k" "upper_continued_up rc \<A> x (Suc n) k"
  shows "upper_continued_up rc \<A> x n j"
proof -
  {
    fix M assume M_gt: "M > n"
    have "\<exists> q . upper_child_segment_up rc n M x \<A> j q"
    proof (cases "M = Suc n")
      case True
      have "upper_child_segment_up rc n M x \<A> j k" using assms(1) True unfolding upper_child_segment_up_def by (intro exI[of _ "[j,k]"]) auto
      thus ?thesis by blast
    next
      case False
      hence M_gt_suc: "M > Suc n" using M_gt by simp
      then obtain q where q: "upper_child_segment_up rc (Suc n) M x \<A> k q" using assms(2) unfolding upper_continued_up_def by blast
      have "upper_child_segment_up rc n M x \<A> j q"
      proof -
        obtain js where js: "length js = M - Suc n + 1" "js ! 0 = k" "last js = q" "\<forall> m < M - Suc n . upper_child_up (rc (Suc n + m)) (x (Suc n + m)) \<A> (rc (Suc n + Suc m)) (js ! m) (js ! Suc m)" using q unfolding upper_child_segment_up_def by blast
        define js' where "js' = j # js"
        hence len: "length js' = M - n + 1" using js(1) M_gt_suc by simp
        have first: "js' ! 0 = j" unfolding js'_def by simp
        have last: "last js' = q" using js(1,3) unfolding js'_def by fastforce
        {
          fix m assume mlt: "m < M - n"
          have "upper_child_up (rc (n + m)) (x (n + m)) \<A> (rc (n + Suc m)) (js' ! m) (js' ! Suc m)"
          proof (cases m)
            case 0 thus ?thesis using assms(1) js(2) unfolding js'_def by simp
          next
            case (Suc m')
            hence "m' < M - Suc n" using mlt by simp
            hence step: "upper_child_up (rc (Suc n + m')) (x (Suc n + m')) \<A> (rc (Suc n + Suc m')) (js ! m') (js ! Suc m')" using js(4) by blast
            thus ?thesis using Suc unfolding js'_def by simp
          qed
        }
        hence steps: "\<forall> m < M - n . upper_child_up (rc (n + m)) (x (n + m)) \<A> (rc (n + Suc m)) (js' ! m) (js' ! Suc m)" by blast
        thus ?thesis unfolding upper_child_segment_up_def using len first last by blast
      qed
      thus ?thesis by blast
    qed
  }
  hence "\<forall> M > n . \<exists> q . upper_child_segment_up rc n M x \<A> j q" by blast
  thus ?thesis unfolding upper_continued_up_def by blast
qed

lemma lower_from_upper_color2_continued_implies_TF:
  assumes "(S, a, rc n) \<in> lower_transitions_from_upper \<A>" "k < length (rc n)" "snd (rc n ! k) = 2" "upper_continued_up rc \<A> x n k"
  shows "upper_slice_continued_F_up rc \<A> x n"
proof -
  have S'_def: "rc n = filter (\<lambda>X . fst X \<noteq> {}) (fst (lower_step_from_upper \<A> a S))" using assms(1) unfolding lower_transitions_from_upper_def by auto
  have raw: "(rc n ! k) \<in> set (fst (lower_step_from_upper \<A> a S))" using assms S'_def filter_is_subset nth_mem subsetD by metis
  have "rc n ! k \<in> set (rc n)" using assms(2) by simp
  hence nz: "fst (rc n ! k) \<noteq> {}" using S'_def by simp
  have "fst (rc n ! k) \<subseteq> accepting_states \<A>"
  proof -
    have "\<forall> X \<in> set (fst (lower_step_from_upper \<A> a S)) . snd X = 2 \<longrightarrow> fst X \<subseteq> accepting_states \<A>"
    proof (induction S)
      case Nil thus ?case by simp
    next
      case (Cons Sm S)
      let ?L = "((post_set \<A> (fst Sm) a - snd (lower_step_from_upper \<A> a S)) - accepting_states \<A>, 0)"
      let ?R = "((post_set \<A> (fst Sm) a - snd (lower_step_from_upper \<A> a S)) \<inter> accepting_states \<A>, 2)"
      {
        fix X assume X: "X \<in> set (fst (lower_step_from_upper \<A> a (Sm # S))) \<and> snd X = 2"
        hence "X = ?L \<or> X = ?R \<or> X \<in> set (fst (lower_step_from_upper \<A> a S))" by simp
        then consider (case1) "X = ?L" | (case2) "X = ?R" | (case3) "X \<in> set (fst (lower_step_from_upper \<A> a S))" by fast
        hence "fst X \<subseteq> accepting_states \<A>"
        proof cases
          case case1 thus ?thesis using X by simp
        next
          case case2 thus ?thesis by auto
        next
          case case3 thus ?thesis using Cons.IH X by blast
        qed
      }
      thus ?case by blast
    qed
    thus ?thesis using raw assms(3) by blast
  qed
  hence "fst (rc n ! k) \<subseteq> accepting_states \<A>" using raw assms(3) by blast
  hence "upper_continued_F_up rc \<A> x n k" using assms(4) unfolding upper_continued_F_up_def by blast
  thus ?thesis using assms(2) unfolding upper_slice_continued_F_up_def by blast
qed

lemma lower_step_acc_raw_color2_is_F_or_color1_pred:
  assumes "\<forall> Sm \<in> set S . snd Sm \<in> {0, 1, 2}" "lower_accepting S" "X \<in> set (fst (lower_step_acc \<A> a S))" "snd X = 2"
  shows "fst X \<subseteq> accepting_states \<A> \<or> (\<exists> j < length S . snd (S ! j) = 1 \<and> fst X \<subseteq> post_set \<A> (fst (S ! j)) a \<and> fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {})"
using assms proof (induction S arbitrary: X)
  case Nil thus ?case by simp
next
  case (Cons Sm S)
  let ?L = "((post_set \<A> (fst Sm) a - snd (lower_step_acc \<A> a S)) - accepting_states \<A>, min (2 * snd Sm) 2)"
  let ?R = "((post_set \<A> (fst Sm) a - snd (lower_step_acc \<A> a S)) \<inter> accepting_states \<A>, 2)"
  have "X = ?L \<or> X = ?R \<or> X \<in> set (fst (lower_step_acc \<A> a S))" using Cons.prems(3) by simp
  then consider (L) "X = ?L" | (R) "X = ?R" | (Tail) "X \<in> set (fst (lower_step_acc \<A> a S))" by blast
  thus ?case
  proof cases
    case L
    have sm_not2: "snd Sm \<noteq> 2" using Cons.prems(2) unfolding lower_accepting_def by auto
    have sm_color: "snd Sm \<in> {0, 1, 2}" using Cons.prems(1) by auto
    have "snd Sm \<noteq> 0" using L Cons.prems(4) by auto
    hence sm_one: "snd Sm = 1" using sm_not2 sm_color by auto
    have sub: "fst X \<subseteq> post_set \<A> (fst Sm) a" using L by auto
    have "snd (lower_step_acc \<A> a S) = snd (upper_step \<A> a (map fst S))" using lower_step_acc_snd_eq_upper_step by fast
    hence "fst X \<inter> snd (upper_step \<A> a (drop (Suc 0) (map fst (Sm # S)))) = {}" using L by auto
    thus ?thesis using sm_one sub by (intro disjI2 exI[of _ 0]) auto
  next
    case R thus ?thesis by auto
  next
    case Tail
    have colors_tail: "\<forall> Sm \<in> set S . snd Sm \<in> {0, 1, 2}" using Cons.prems(1) by auto
    have acc_tail: "lower_accepting S" using Cons.prems(2) unfolding lower_accepting_def by auto
    have IH: "fst X \<subseteq> accepting_states \<A> \<or> (\<exists> j < length S . snd (S ! j) = 1 \<and> fst X \<subseteq> post_set \<A> (fst (S ! j)) a \<and> fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {})" using Cons.IH[OF colors_tail acc_tail Tail Cons.prems(4)] .
    thus ?thesis
    proof
      assume "fst X \<subseteq> accepting_states \<A>" thus ?thesis by blast
    next
      assume "\<exists> j < length S . snd (S ! j) = 1 \<and> fst X \<subseteq> post_set \<A> (fst (S ! j)) a \<and> fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}"
      then obtain j where j: "j < length S" "snd (S ! j) = 1" "fst X \<subseteq> post_set \<A> (fst (S ! j)) a" "fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}" by blast
      thus ?thesis by (intro disjI2 exI[of _ "Suc j"]) auto
    qed
  qed
qed

lemma lower_acc_color2_target_continued_implies_TF_or_color1_pred:
  assumes "(rc n, x n, rc (Suc n)) \<in> lower_transitions \<A>" "lower_accepting (rc n)" "k < length (rc (Suc n))" "snd (rc (Suc n) ! k) = 2" "upper_continued_up rc \<A> x (Suc n) k"
  shows "upper_slice_continued_F_up rc \<A> x (Suc n) \<or> (\<exists> j < length (rc n) . snd (rc n ! j) = 1 \<and> upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k \<and> upper_continued_up rc \<A> x n j)"
proof -
  have "rc (Suc n) = filter (\<lambda>X . fst X \<noteq> {}) (fst (lower_step_acc \<A> (x n) (rc n)))" using assms(1,2) unfolding lower_transitions_def by auto
  hence raw:"rc (Suc n) ! k \<in> set (fst (lower_step_acc \<A> (x n) (rc n)))" using assms(3) filter_is_subset nth_mem subsetD by metis
  hence "(rc n) \<in> lower_states \<A>" using assms(1) unfolding lower_transitions_def by auto
  hence colors: "\<forall> Sm \<in> set (rc n) . snd Sm \<in> {0, 1, 2}" unfolding lower_states_def by blast
  have raw_cases: "fst (rc (Suc n) ! k) \<subseteq> accepting_states \<A> \<or> (\<exists> j < length (rc n) . snd (rc n ! j) = 1 \<and> fst (rc (Suc n) ! k) \<subseteq> post_set \<A> (fst (rc n ! j)) (x n) \<and> fst (rc (Suc n) ! k) \<inter> snd (upper_step \<A> (x n) (drop (Suc j) (map fst (rc n)))) = {})" using lower_step_acc_raw_color2_is_F_or_color1_pred[OF colors assms(2) raw assms(4)] by blast
  thus ?thesis
  proof
    assume "fst (rc (Suc n) ! k) \<subseteq> accepting_states \<A>"
    hence "upper_continued_F_up rc \<A> x (Suc n) k" using assms(5) unfolding upper_continued_F_up_def by blast
    thus ?thesis using assms(3) unfolding upper_slice_continued_F_up_def by blast
  next
    assume "\<exists> j < length (rc n) . snd ((rc n) ! j) = 1 \<and> fst (rc (Suc n) ! k) \<subseteq> post_set \<A> (fst ((rc n) ! j)) (x n) \<and> fst (rc (Suc n) ! k) \<inter> snd (upper_step \<A> (x n) (drop (Suc j) (map fst (rc n)))) = {}"
    then obtain j where j: "j < length (rc n)" "snd ((rc n) ! j) = 1" "fst (rc (Suc n) ! k) \<subseteq> post_set \<A> (fst ((rc n) ! j)) (x n)" "fst (rc (Suc n) ! k) \<inter> snd (upper_step \<A> (x n) (drop (Suc j) (map fst (rc n)))) = {}" by blast
    hence child: "upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k" using assms(3) unfolding upper_child_up_def by blast
    hence "upper_continued_up rc \<A> x n j" using upper_continued_up_prepend_one assms(5) by blast
    thus ?thesis using j(1,2) child by blast
  qed
qed

lemma lower_run_acc_color2_target_continued_implies_TF_or_color1_pred:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "rc n \<in> lower_states \<A>" "lower_accepting (rc n)" "k < length (rc (Suc n))" "snd (rc (Suc n) ! k) = 2" "upper_continued_up rc \<A> x (Suc n) k"
  shows "upper_slice_continued_F_up rc \<A> x (Suc n) \<or> (\<exists> j < length (rc n) . snd (rc n ! j) = 1 \<and> upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k \<and> upper_continued_up rc \<A> x n j)"
proof -
  have trans: "(rc n, x n, rc (Suc n)) \<in> transitions (comp_omega_automaton \<A>)" using assms(2) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
  have not_upper: "rc n \<notin> states (upper_part \<A>)" using assms(3) upper_and_lower_states_disjoint by blast
  have not_up_trans: "(rc n, x n, rc (Suc n)) \<notin> transitions (upper_part \<A>)"
  proof
    assume "(rc n, x n, rc (Suc n)) \<in> transitions (upper_part \<A>)"
    hence "rc n \<in> states (upper_part \<A>)" using assms(1) well_def_upper_part well_def_trans_components by fast
    thus False using not_upper by blast
  qed
  have "(rc n, x n, rc (Suc n)) \<notin> lower_transitions_from_upper \<A>" using not_upper unfolding lower_transitions_from_upper_def by auto
  hence lower_trans: "(rc n, x n, rc (Suc n)) \<in> lower_transitions \<A>" using trans not_up_trans unfolding comp_omega_automaton_def by auto
  show ?thesis using lower_acc_color2_target_continued_implies_TF_or_color1_pred[OF lower_trans assms(4,5,6,7)] by blast
qed

lemma lower_jump_positive_continued_implies_TF:
  assumes "(S, a, rc l) \<in> lower_transitions_from_upper \<A>" "k < length (rc l)" "snd (rc l ! k) \<noteq> 0" "upper_continued_up rc \<A> x l k"
  shows "upper_slice_continued_F_up rc \<A> x l"
proof -
  have "rc l = filter (\<lambda>X . fst X \<noteq> {}) (fst (lower_step_from_upper \<A> a S))" using assms(1) unfolding lower_transitions_from_upper_def by auto
  hence raw: "rc l ! k \<in> set (fst (lower_step_from_upper \<A> a S))" using assms(2) filter_is_subset nth_mem subsetD by metis
  have pos_is_2: "snd (rc l ! k) = 2"
  proof -
    have "snd (rc l ! k) = 0 \<or> snd (rc l ! k) = 2" using raw
    proof (induction S)
      case Nil thus ?case by simp
    next
      case (Cons Sm S)
      let ?L = "((post_set \<A> (fst Sm) a - snd (lower_step_from_upper \<A> a S)) - accepting_states \<A>, 0)"
      let ?R = "((post_set \<A> (fst Sm) a - snd (lower_step_from_upper \<A> a S)) \<inter> accepting_states \<A>, 2)"
      have "rc l ! k = ?L \<or> rc l ! k = ?R \<or> rc l ! k \<in> set (fst (lower_step_from_upper \<A> a S))" using Cons.prems by simp
      thus ?case using Cons.IH by auto
    qed
    thus ?thesis using assms(3) by blast
  qed
  show ?thesis using lower_from_upper_color2_continued_implies_TF[OF assms(1,2) pos_is_2 assms(4)] by blast
qed

lemma lower_step_nacc_raw_color1_is_F_or_color1_pred:
  assumes "X \<in> set (fst (lower_step_nacc \<A> a S))" "snd X = 1"
  shows "fst X \<subseteq> accepting_states \<A> \<or> (\<exists> j < length S . snd (S ! j) = 1 \<and> fst X \<subseteq> post_set \<A> (fst (S ! j)) a \<and> fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {})"
using assms proof (induction S arbitrary: X)
  case Nil thus ?case by simp
next
  case (Cons Sm S)
  let ?L = "((post_set \<A> (fst Sm) a - snd (lower_step_nacc \<A> a S)) - accepting_states \<A>, snd Sm)"
  let ?R = "((post_set \<A> (fst Sm) a - snd (lower_step_nacc \<A> a S)) \<inter> accepting_states \<A>, max (snd Sm) 1)"
  have "X = ?L \<or> X = ?R \<or> X \<in> set (fst (lower_step_nacc \<A> a S))" using Cons.prems(1) by simp
  then consider (L) "X = ?L" | (R) "X = ?R" | (Tail) "X \<in> set (fst (lower_step_nacc \<A> a S))" by blast
  thus ?case
  proof cases
    case L
    hence sm1: "snd Sm = 1" using Cons.prems(2) by simp
    have sub: "fst X \<subseteq> post_set \<A> (fst Sm) a" using L by auto
    have "snd (lower_step_nacc \<A> a S) = snd (upper_step \<A> a (map fst S))" using lower_step_nacc_snd_eq_upper_step by fast
    hence "fst X \<inter> snd (upper_step \<A> a (drop (Suc 0) (map fst (Sm # S)))) = {}" using L by auto
    thus ?thesis using sm1 sub by (intro disjI2 exI[of _ 0]) auto
  next
    case R thus ?thesis using Cons.prems(1) by simp
  next
    case Tail
    have "fst X \<subseteq> accepting_states \<A> \<or> (\<exists> j < length S . snd (S ! j) = 1 \<and> fst X \<subseteq> post_set \<A> (fst (S ! j)) a \<and> fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {})" using Cons.IH[OF Tail Cons.prems(2)] by blast
    thus ?thesis
    proof
      assume "fst X \<subseteq> accepting_states \<A>" thus ?thesis by blast
    next
      assume "\<exists> j < length S . snd (S ! j) = 1 \<and> fst X \<subseteq> post_set \<A> (fst (S ! j)) a \<and> fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}"
      then obtain j where "j < length S" "snd (S ! j) = 1" "fst X \<subseteq> post_set \<A> (fst (S ! j)) a" "fst X \<inter> snd (upper_step \<A> a (drop (Suc j) (map fst S))) = {}" by blast
      thus ?thesis by (intro disjI2 exI[of _ "Suc j"]) auto
    qed
  qed
qed

lemma lower_step_acc_raw_no_color1:
  assumes "X \<in> set (fst (lower_step_acc \<A> a S))" "lower_accepting S" "\<forall> Sm \<in> set S . snd Sm \<in> {0, 1, 2}"
  shows "snd X \<noteq> 1"
using assms
proof (induction S arbitrary: X)
  case Nil thus ?case by simp
next
  case (Cons Sm S)
  let ?L = "((post_set \<A> (fst Sm) a - snd (lower_step_acc \<A> a S)) - accepting_states \<A>, min (2 * snd Sm) 2)"
  let ?R = "((post_set \<A> (fst Sm) a - snd (lower_step_acc \<A> a S)) \<inter> accepting_states \<A>, 2)"
  have "X = ?L \<or> X = ?R \<or> X \<in> set (fst (lower_step_acc \<A> a S))" using Cons.prems(1) by simp
  then consider (L) "X = ?L" | (R) "X = ?R" | (Tail) "X \<in> set (fst (lower_step_acc \<A> a S))" by blast
  thus ?case
  proof cases
    case L
    have sm_not2: "snd Sm \<noteq> 2" using Cons.prems(2) unfolding lower_accepting_def by auto
    have "snd Sm \<in> {0, 1, 2}" using Cons.prems(3) by auto
    hence "snd Sm = 0 \<or> snd Sm = 1" using sm_not2 by auto
    thus ?thesis using L by auto
  next
    case R thus ?thesis by simp
  next
    case Tail
    have acc_tail: "lower_accepting S"  using Cons.prems(2) unfolding lower_accepting_def by auto
    have colors_tail: "\<forall> Sm \<in> set S . snd Sm \<in> {0, 1, 2}" using Cons.prems(3) by auto
    show ?thesis using Cons.IH[OF Tail acc_tail colors_tail] by blast
  qed
qed

lemma lower_run_color1_target_continued_implies_TF_or_color1_pred:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "rc n \<in> lower_states \<A>" "k < length (rc (Suc n))" "snd (rc (Suc n) ! k) = 1" "upper_continued_up rc \<A> x (Suc n) k"
  shows "upper_slice_continued_F_up rc \<A> x (Suc n) \<or> (\<exists> j < length (rc n) . snd (rc n ! j) = 1 \<and> upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k \<and> upper_continued_up rc \<A> x n j)"
proof -
  have trans: "(rc n, x n, rc (Suc n)) \<in> transitions (comp_omega_automaton \<A>)" using assms(2) unfolding omega_run_well_defined_def omega_pseudo_run_well_defined_def by auto
  have not_upper: "rc n \<notin> states (upper_part \<A>)" using assms(3) upper_and_lower_states_disjoint by blast
  have not_up_trans: "(rc n, x n, rc (Suc n)) \<notin> transitions (upper_part \<A>)"
  proof
    assume "(rc n, x n, rc (Suc n)) \<in> transitions (upper_part \<A>)"
    hence "rc n \<in> states (upper_part \<A>)" using assms(1) well_def_upper_part well_def_trans_components by fast
    thus False using not_upper by blast
  qed
  have "(rc n, x n, rc (Suc n)) \<notin> lower_transitions_from_upper \<A>" using not_upper unfolding lower_transitions_from_upper_def by auto
  hence lower_trans: "(rc n, x n, rc (Suc n)) \<in> lower_transitions \<A>" using trans not_up_trans unfolding comp_omega_automaton_def by auto
  have "\<not> lower_accepting (rc n) \<or> lower_accepting (rc n)" by blast
  thus ?thesis
  proof
    assume "\<not> lower_accepting (rc n)"
    hence "rc (Suc n) = filter (\<lambda>X . fst X \<noteq> {}) (fst (lower_step_nacc \<A> (x n) (rc n)))" using lower_trans unfolding lower_transitions_def by auto
    hence raw: "rc (Suc n) ! k \<in> set (fst (lower_step_nacc \<A> (x n) (rc n)))" using assms(4) filter_is_subset nth_mem subsetD by metis
    have "fst (rc (Suc n) ! k) \<subseteq> accepting_states \<A> \<or> (\<exists> j < length (rc n) . snd (rc n ! j) = 1 \<and> fst (rc (Suc n) ! k) \<subseteq> post_set \<A> (fst (rc n ! j)) (x n) \<and> fst (rc (Suc n) ! k) \<inter> snd (upper_step \<A> (x n) (drop (Suc j) (map fst (rc n)))) = {})" using lower_step_nacc_raw_color1_is_F_or_color1_pred[OF raw assms(5)] by blast
    thus ?thesis
    proof
      assume "fst (rc (Suc n) ! k) \<subseteq> accepting_states \<A>"
      hence "upper_continued_F_up rc \<A> x (Suc n) k" using assms(6) unfolding upper_continued_F_up_def by blast
      hence "upper_slice_continued_F_up rc \<A> x (Suc n)" using assms(4) unfolding upper_slice_continued_F_up_def by blast
      thus ?thesis by blast
    next
      assume "\<exists> j < length (rc n) . snd (rc n ! j) = 1 \<and> fst (rc (Suc n) ! k) \<subseteq> post_set \<A> (fst (rc n ! j)) (x n) \<and> fst (rc (Suc n) ! k) \<inter> snd (upper_step \<A> (x n) (drop (Suc j) (map fst (rc n)))) = {}"
      then obtain j where j: "j < length (rc n)" "snd (rc n ! j) = 1" "fst (rc (Suc n) ! k) \<subseteq> post_set \<A> (fst (rc n ! j)) (x n)" "fst (rc (Suc n) ! k) \<inter> snd (upper_step \<A> (x n) (drop (Suc j) (map fst (rc n)))) = {}" by blast
      hence child: "upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k" using assms(4) unfolding upper_child_up_def by blast
      have "upper_continued_up rc \<A> x n j" using upper_continued_up_prepend_one[OF child assms(6)] by blast
      thus ?thesis using j(1,2) child by blast
    qed
  next
    assume acc: "lower_accepting (rc n)"
    have "rc (Suc n) = filter (\<lambda>X . fst X \<noteq> {}) (fst (lower_step_acc \<A> (x n) (rc n)))" using lower_trans acc unfolding lower_transitions_def by auto
    hence raw: "rc (Suc n) ! k \<in> set (fst (lower_step_acc \<A> (x n) (rc n)))" using assms(4) filter_is_subset nth_mem subsetD by metis
    have colors: "\<forall> Sm \<in> set (rc n) . snd Sm \<in> {0, 1, 2}" using assms(3) unfolding lower_states_def by blast
    have "snd (rc (Suc n) ! k) \<noteq> 1" using lower_step_acc_raw_no_color1[OF raw acc colors] by blast
    thus ?thesis using assms(5)  by blast
  qed
qed

lemma lower_run_pos_color_backwards_origin_step:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "rc n \<in> lower_states \<A>" "k < length (rc (Suc n))" "snd (rc (Suc n) ! k) \<noteq> 0" "upper_continued_up rc \<A> x (Suc n) k"
  shows "upper_slice_continued_F_up rc \<A> x (Suc n) \<or> (\<exists> j < length (rc n) . snd (rc n ! j) \<noteq> 0 \<and> upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k \<and> upper_continued_up rc \<A> x n j)"
proof -
  have "rc (Suc n) \<in> lower_states \<A>" using comp_run_lower_step_stays_lower[OF assms(1,2,3)] by blast
  hence "snd (rc (Suc n) ! k) \<in> {0, 1, 2}" using assms(4) unfolding lower_states_def by auto
  hence color: "snd (rc (Suc n) ! k) = 1 \<or> snd (rc (Suc n) ! k) = 2" using assms(5) by auto
  thus ?thesis
  proof
    assume color1: "snd (rc (Suc n) ! k) = 1"
    have "upper_slice_continued_F_up rc \<A> x (Suc n) \<or> (\<exists> j < length (rc n) . snd (rc n ! j) = 1 \<and> upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k \<and> upper_continued_up rc \<A> x n j)" using lower_run_color1_target_continued_implies_TF_or_color1_pred[OF assms(1,2,3,4) color1 assms(6)] by blast
    thus ?thesis by force
  next
    assume color2: "snd (rc (Suc n) ! k) = 2"
    have "upper_slice_continued_F_up rc \<A> x (Suc n) \<or> (\<exists> j < length (rc n) . snd (rc n ! j) \<noteq> 0 \<and> upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k \<and> upper_continued_up rc \<A> x n j)"
    proof (cases "lower_accepting (rc n)")
      case True
      have "upper_slice_continued_F_up rc \<A> x (Suc n) \<or> (\<exists> j < length (rc n) . snd (rc n ! j) = 1 \<and> upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k \<and> upper_continued_up rc \<A> x n j)" using lower_run_acc_color2_target_continued_implies_TF_or_color1_pred[OF assms(1,2,3) True assms(4) color2 assms(6)] by blast
      thus ?thesis by force
    next
      case False
      have "(\<exists> j < length (rc n) . snd (rc n ! j) = 2 \<and> upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k) \<or> fst (rc (Suc n) ! k) \<subseteq> accepting_states \<A>" using lower_run_color2_target_has_color2_pred_or_TF[OF assms(1,2,3) False assms(4) color2] by blast
      thus ?thesis
      proof
        assume pred: "\<exists> j < length (rc n) . snd (rc n ! j) = 2 \<and> upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k"
        then obtain j where j: "j < length (rc n)" "snd (rc n ! j) = 2" "upper_child_up (rc n) (x n) \<A> (rc (Suc n)) j k" by blast
        have "upper_continued_up rc \<A> x n j" using upper_continued_up_prepend_one[OF j(3) assms(6)] by blast
        thus ?thesis using j by auto
      next
        assume "fst (rc (Suc n) ! k) \<subseteq> accepting_states \<A>"
        hence "upper_continued_F_up rc \<A> x (Suc n) k" using assms(6) unfolding upper_continued_F_up_def by blast
        hence "upper_slice_continued_F_up rc \<A> x (Suc n)" using assms(4) unfolding upper_slice_continued_F_up_def by blast
        thus ?thesis by blast
      qed
    qed
    thus ?thesis by blast
  qed
qed

lemma continued_positive_color_has_TF_origin_between_jump_and_tail:
  assumes "auto_well_defined \<A>" "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "\<forall> n \<ge> l . rc n \<in> lower_states \<A>" "l \<le> B" "j < length (rc B)" "snd (rc B ! j) \<noteq> 0" "upper_continued_up rc \<A> x B j" "\<exists> S a . (S, a, rc l) \<in> lower_transitions_from_upper \<A>"
  shows "\<exists> i \<ge> l . i \<le> B \<and> upper_slice_continued_F_up rc \<A> x i"
using assms(1-7)
proof (induction "B - l" arbitrary: B j)
  case 0
  hence B_eq: "B = l" by simp
  obtain S a where "(S, a, rc l) \<in> lower_transitions_from_upper \<A>" using assms(8) by blast
  hence "upper_slice_continued_F_up rc \<A> x l" using lower_jump_positive_continued_implies_TF 0 B_eq by fast
  thus ?case using B_eq by blast
next
  case (Suc d)
  then obtain B' where B': "B = Suc B'" "l \<le> B'" using add_Suc le_add2 le_add_diff_inverse2 by metis
  hence diff: "d = B' - l" using Suc.hyps(2) by simp
  have lower_B': "rc B' \<in> lower_states \<A>" using Suc.prems(3) B'(2) by blast
  have "upper_slice_continued_F_up rc \<A> x B \<or> (\<exists> j' < length (rc B') . snd (rc B' ! j') \<noteq> 0 \<and> upper_child_up (rc B') (x B') \<A> (rc B) j' j \<and> upper_continued_up rc \<A> x B' j')" using lower_run_pos_color_backwards_origin_step[OF Suc.prems(1,2) lower_B'] Suc B' by blast
  thus ?case
  proof
    assume "upper_slice_continued_F_up rc \<A> x B" thus ?thesis using Suc.prems(4) by blast
  next
    assume "\<exists> j' < length (rc B') . snd (rc B' ! j') \<noteq> 0 \<and> upper_child_up (rc B') (x B') \<A> (rc B) j' j \<and> upper_continued_up rc \<A> x B' j'"
    then obtain j' where "j' < length (rc B')" "snd (rc B' ! j') \<noteq> 0" "upper_child_up (rc B') (x B') \<A> (rc B) j' j" "upper_continued_up rc \<A> x B' j'" by blast
    hence "\<exists> i \<ge> l . i \<le> B' \<and> upper_slice_continued_F_up rc \<A> x i" using Suc diff B'(2) by blast
    thus ?thesis using B' by auto
  qed
qed

lemma upper_child_up_same_fst:
  assumes "map fst p = map fst p'" "map fst q = map fst q'" "upper_child_up p a \<A> q j k"
  shows "upper_child_up p' a \<A> q' j k"
proof -
  have len_p: "length p = length p'" using assms(1) by (metis length_map)
  have len_q: "length q = length q'" using assms(2) by (metis length_map)
  have jlt: "j < length p" using assms(3) unfolding upper_child_up_def by blast
  have klt: "k < length q" using assms(3) unfolding upper_child_up_def by blast
  have fst_p: "fst (p' ! j) = fst (p ! j)" using assms(1) jlt len_p by (metis nth_map)
  have fst_q: "fst (q' ! k) = fst (q ! k)" using assms(2) klt len_q by (metis nth_map)
  have "drop (Suc j) (map fst p') = drop (Suc j) (map fst p)" using assms(1) by simp
  thus ?thesis using assms(3) len_p len_q fst_p fst_q unfolding upper_child_up_def by auto
qed

lemma upper_child_segment_up_same_fst_from:
  assumes "\<forall> n \<ge> i . map fst (r n) = map fst (s n)" "upper_child_segment_up r i N x \<A> j k"
  shows "upper_child_segment_up s i N x \<A> j k"
proof -
  obtain js where js: "length js = N - i + 1" "js ! 0 = j" "last js = k" "\<forall> m < N - i . upper_child_up (r (i + m)) (x (i + m)) \<A> (r (i + Suc m)) (js ! m) (js ! Suc m)" using assms unfolding upper_child_segment_up_def by blast
  {
    fix m assume mlt: "m < N - i"
    have eq1: "map fst (r (i + m)) = map fst (s (i + m))" using assms by simp
    have eq2: "map fst (r (i + Suc m)) = map fst (s (i + Suc m))" using assms by simp
    hence "upper_child_up (s (i + m)) (x (i + m)) \<A> (s (i + Suc m)) (js ! m) (js ! Suc m)" using js(4) mlt eq1 upper_child_up_same_fst by fast
  }
  hence "\<forall> m < N - i . upper_child_up (s (i + m)) (x (i + m)) \<A> (s (i + Suc m)) (js ! m) (js ! Suc m)" by blast
  thus ?thesis unfolding upper_child_segment_up_def using js by blast
qed

lemma upper_continued_up_same_fst_from:
  assumes "\<forall> n \<ge> i . map fst (r n) = map fst (s n)" "upper_continued_up r \<A> x i j"
  shows "upper_continued_up s \<A> x i j"
proof -
  {
    fix N assume "N > i"
    then obtain k where "upper_child_segment_up r i N x \<A> j k" using assms unfolding upper_continued_up_def by blast
    hence "upper_child_segment_up s i N x \<A> j k" using upper_child_segment_up_same_fst_from assms by blast
    hence "\<exists> k . upper_child_segment_up s i N x \<A> j k" by blast
  }
  hence "\<forall> N > i . \<exists> k . upper_child_segment_up s i N x \<A> j k" by blast
  thus ?thesis unfolding upper_continued_up_def by blast
qed

lemma upper_continued_F_up_same_fst_from:
  assumes "\<forall> n \<ge> i . map fst (r n) = map fst (s n)" "upper_continued_F_up r \<A> x i j"
  shows "upper_continued_F_up s \<A> x i j"
proof -
  have cont: "upper_continued_up r \<A> x i j" using assms unfolding upper_continued_F_up_def by blast
  have F: "fst (r i ! j) \<subseteq> accepting_states \<A>" using assms unfolding upper_continued_F_up_def by blast
  obtain N k where N: "N > i" "upper_child_segment_up r i N x \<A> j k" using cont unfolding upper_continued_up_def by (metis lessI)
  hence jlt_r: "j < length (r i)" unfolding upper_child_segment_up_def upper_child_up_def by (cases "N - i") auto
  have "length (r i) = length (s i)" using assms by (metis le_refl length_map)
  hence "fst (s i ! j) = fst (r i ! j)" using assms jlt_r by (metis le_refl nth_map)
  hence in_acc: "fst (s i ! j) \<subseteq> accepting_states \<A>" using F by simp
  have "upper_continued_up s \<A> x i j" using upper_continued_up_same_fst_from assms cont by blast
  thus ?thesis using in_acc unfolding upper_continued_F_up_def by blast
qed

lemma upper_slice_continued_F_up_same_fst_from:
  assumes "\<forall> n \<ge> i . map fst (r n) = map fst (s n)" "upper_slice_continued_F_up r \<A> x i"
  shows "upper_slice_continued_F_up s \<A> x i"
proof -
  obtain j where j: "j < length (r i)" "upper_continued_F_up r \<A> x i j" using assms unfolding upper_slice_continued_F_up_def by blast
  have "length (r i) = length (s i)" using assms by (metis le_refl length_map)
  hence len: "j < length (s i)" using j(1) by simp
  have "upper_continued_F_up s \<A> x i j" using upper_continued_F_up_same_fst_from[OF assms(1) j(2)] .
  thus ?thesis using len unfolding upper_slice_continued_F_up_def by blast
qed

lemma lemma_3_4_17:
  assumes "auto_well_defined \<A>" "omega_word_well_defined x (alphabet \<A>)" "x \<notin> omega_language_auto \<A>"
  shows "\<exists> rc . omega_run_accepting rc (comp_omega_automaton \<A>) x"
proof -
  obtain Run where Run: "omega_run_well_defined Run (upper_part \<A>) x" using exists_upper_part_run[OF assms(1,2)] by blast
  show ?thesis
  proof (cases "\<exists> n . Run n = []")
    case True thus ?thesis using upper_part_empty_yields_comp_accepting_run[OF assms(1) Run] by blast
  next
    case False
    hence Run_ne: "\<forall> n . Run n \<noteq> []" by blast
    obtain k where no_TF: "\<forall> i \<ge> k . \<not> upper_slice_continued_F_up Run \<A> x i" using not_in_language_eventually_no_TF[OF assms(1,2,3) Run Run_ne] by blast
    define l where "l = Suc k"
    hence "\<exists> rc . omega_run_well_defined rc (comp_omega_automaton \<A>) x \<and> (\<forall> n < l . rc n = Run n) \<and> rc l \<in> lower_states \<A> \<and> (\<exists> S a . (S, a, rc l) \<in> lower_transitions_from_upper \<A>) \<and> (\<forall> n \<ge> l . map fst (rc n) = map fst (Run n))" using upper_run_nonempty_can_jump_to_lower_at[OF assms(1,2) Run Run_ne] by simp
    then obtain rc where rc: "omega_run_well_defined rc (comp_omega_automaton \<A>) x" "\<forall> n < l . rc n = Run n" "rc l \<in> lower_states \<A>" "\<exists> S a . (S, a, rc l) \<in> lower_transitions_from_upper \<A>" "\<forall> n \<ge> l . map fst (rc n) = map fst (Run n)" by blast
    hence lower_forever: "\<forall> n \<ge> l . rc n \<in> lower_states \<A>" using comp_run_stays_in_lower_after_entry[OF assms(1)] by blast
    show ?thesis
    proof (rule ccontr)
      assume "\<not> (\<exists> rc . omega_run_accepting rc (comp_omega_automaton \<A>) x)"
      hence "\<not> omega_run_accepting rc (comp_omega_automaton \<A>) x" by blast
      hence "\<not> (\<forall> n . \<exists> N > n . rc N \<in> accepting_states (comp_omega_automaton \<A>))" using rc(1) unfolding omega_run_accepting_def by blast
      hence ex: "\<exists> b . \<forall> N > b . rc N \<notin> accepting_states (comp_omega_automaton \<A>)" by blast
      define l' where "l' = (LEAST b . \<forall> N > b . rc N \<notin> accepting_states (comp_omega_automaton \<A>))"
      have l'_tail: "\<forall> N > l' . rc N \<notin> accepting_states (comp_omega_automaton \<A>)" using ex unfolding l'_def by (rule LeastI2_ex) auto
      have l'_least: "\<And> b . (\<forall> N > b . rc N \<notin> accepting_states (comp_omega_automaton \<A>)) \<Longrightarrow> l' \<le> b" unfolding l'_def by (rule Least_le)
      have eventually_lower_nonacc: "\<forall> N \<ge> max l (Suc l') . rc N \<in> lower_states \<A> \<and> rc N \<notin> accepting_states (comp_omega_automaton \<A>)" using lower_forever l'_tail by auto
      hence eventually_color2: "\<forall> N \<ge> max l (Suc l') . \<exists> j < length (rc N) . snd (rc N ! j) = 2" using lower_nonaccepting_contains_color2 by blast
      define B where "B = max l (Suc l')"
      have lower_from_B: "\<forall> n \<ge> B . rc n \<in> lower_states \<A>" using eventually_lower_nonacc unfolding B_def by blast
      {
        fix n assume "n \<ge> B"
        hence "rc n \<in> lower_states \<A>" "rc n \<notin> accepting_states (comp_omega_automaton \<A>)" using eventually_lower_nonacc unfolding B_def by blast+
        hence "\<not> lower_accepting (rc n)" unfolding comp_omega_automaton_def by auto
      }
      hence nacc_from_B: "\<forall> n \<ge> B . \<not> lower_accepting (rc n)" by blast
      obtain jB where jB: "jB < length (rc B)" "snd (rc B ! jB) = 2" "upper_continued_up rc \<A> x B jB" using eventually_color2_has_continued_color2_at_B[OF assms(1) rc(1) lower_from_B nacc_from_B] using eventually_color2 unfolding B_def by blast
      have l_le_B: "l \<le> B" unfolding B_def by simp
      have "snd (rc B ! jB) \<noteq> 0" using jB(2) by simp
      then obtain iTF where iTF: "iTF \<ge> l" "iTF \<le> B" "upper_slice_continued_F_up rc \<A> x iTF" using continued_positive_color_has_TF_origin_between_jump_and_tail[of \<A> rc x l B jB] using assms(1) rc(1) lower_forever l_le_B jB(1) jB(3) rc(4) by blast
      hence same_from_iTF: "\<forall> n \<ge> iTF . map fst (rc n) = map fst (Run n)" using rc(5) by auto
      have TF_Run: "upper_slice_continued_F_up Run \<A> x iTF" using upper_slice_continued_F_up_same_fst_from[OF same_from_iTF iTF(3)] .
      have "iTF \<ge> k" using iTF(1) unfolding l_def by simp
      thus False using no_TF TF_Run by blast
    qed
  qed
qed

theorem comp_omega_automaton_language_correctness:
  assumes "auto_well_defined \<A>"
  shows "omega_language_auto (comp_omega_automaton \<A>) = comp_omega_language (alphabet \<A>) (omega_language_auto \<A>)"
proof -
  {
    fix x assume "x \<in> omega_language_auto (comp_omega_automaton \<A>)"
    then obtain rc where rc: "omega_run_accepting rc (comp_omega_automaton \<A>) x" unfolding omega_language_auto_def by blast
    have rc_wd:  "omega_run_well_defined rc (comp_omega_automaton \<A>) x" using rc unfolding omega_run_accepting_def by blast
    have comp_wd: "auto_well_defined (comp_omega_automaton \<A>)" using well_def_comp_omega_auto[OF assms] .
    have "omega_word_well_defined x (alphabet (comp_omega_automaton \<A>))" using well_def_implies_omega_word_well_defined[OF comp_wd] rc_wd unfolding omega_run_well_defined_def by blast
    hence x_wd: "omega_word_well_defined x (alphabet \<A>)" unfolding comp_omega_automaton_def by simp
    have "x \<notin> omega_language_auto \<A>"
    proof
      assume x_A: "x \<in> omega_language_auto \<A>"
      have "\<not> omega_run_accepting rc (comp_omega_automaton \<A>) x" using lemma_3_4_16[OF assms x_A rc_wd] .
      thus False using rc by blast
    qed
    hence "x \<in> comp_omega_language (alphabet \<A>) (omega_language_auto \<A>)" using x_wd unfolding comp_omega_language_def omega_sigma_star_def by blast
  }
  hence sub: "omega_language_auto (comp_omega_automaton \<A>) \<subseteq> comp_omega_language (alphabet \<A>) (omega_language_auto \<A>)" by blast
  {
    fix x assume x_comp_lang: "x \<in> comp_omega_language (alphabet \<A>) (omega_language_auto \<A>)"
    hence x_wd: "omega_word_well_defined x (alphabet \<A>)" unfolding comp_omega_language_def omega_sigma_star_def by blast
    have x_not_A: "x \<notin> omega_language_auto \<A>" using x_comp_lang unfolding comp_omega_language_def by blast
    obtain rc where "omega_run_accepting rc (comp_omega_automaton \<A>) x" using lemma_3_4_17[OF assms x_wd x_not_A] by blast
    hence "x \<in> omega_language_auto (comp_omega_automaton \<A>)" unfolding omega_language_auto_def by blast
  }
  hence "comp_omega_language (alphabet \<A>) (omega_language_auto \<A>) \<subseteq> omega_language_auto (comp_omega_automaton \<A>)" by blast
  thus ?thesis using sub by blast
qed

corollary comp_comp_omega_language_auto:
  assumes "auto_well_defined \<A>"
  shows "omega_language_auto \<A> = comp_omega_language (alphabet (comp_omega_automaton \<A>)) (omega_language_auto (comp_omega_automaton \<A>))"
  using assms comp_omega_automaton_language_correctness comp_comp_omega_language comp_omega_automaton_alphabet automata_omega_language_are_well_defined by metis

theorem comp_main:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)"
  shows "\<exists> comp_\<A> :: ((('s states \<times> nat) list), 'a) automaton . auto_well_defined comp_\<A> \<and> alphabet comp_\<A> = alphabet \<A> \<and> omega_language_auto comp_\<A> = comp_omega_language (alphabet \<A>) (omega_language_auto \<A>)"
  using comp_omega_automaton_language_correctness well_def_comp_omega_auto comp_omega_automaton_alphabet assms by metis

theorem existence_of_omega_comp_same_type:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> comp_\<A> :: ('s, 'a) automaton . auto_well_defined comp_\<A> \<and> alphabet comp_\<A> = alphabet \<A> \<and> omega_language_auto comp_\<A> = comp_omega_language (alphabet \<A>) (omega_language_auto \<A>)"
  using assms comp_main existence_soft_iso_auto_omega_lang by metis

end