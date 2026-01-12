theory list_and_set_theorems

imports Main

begin

text \<open>Author: Benno Thalmann, last update: 10.11.2025, Addition to masterarbeit_benno_thalmann\<close>

lemma list_with_one_element: "length list = 1 \<and> list ! 0 = x \<Longrightarrow> list = [x] \<and> last list = x \<and> tl list = []"
  by (induction list) auto

lemma list_with_two_elements_suc: "length list = Suc (Suc 0) \<and> list ! 0 = x \<and> list ! (Suc 0) = y \<Longrightarrow> list = [x, y]"
  by (metis Cons_nth_drop_Suc One_nat_def append.right_neutral append_eq_conv_conj drop0 lessI plus_1_eq_Suc zero_less_two)

corollary list_with_two_elements: "length list = 2 \<and> list ! 0 = x \<and> list ! 1 = y \<Longrightarrow> list = [x, y]"
  by (simp add: list_with_two_elements_suc)

lemma merge_one_more:
  assumes "\<forall> i::nat < n - 1 . P i" "P (n - 1)"
  shows "\<forall> i < n . P i"
  using assms Nat.lessE diff_Suc_1 by metis

lemma simple_math: "(n :: nat) > 1 \<Longrightarrow> n - 2 + 1 = n - 1"
  by simp

lemma simple_math2: "i * j + i = i * (Suc j)"
  by simp

lemma list_properties_not_empty: "list \<noteq> [] \<Longrightarrow> list ! 0 = (list @ [x]) ! 0 \<and> list ! 0 = (list @ list2) ! 0 \<and> (list @ [x]) ! (length list - 1) = last list \<and> list ! (length list - 1) = last list \<and> last list = last (x # list) \<and> list = (list ! 0) # (tl list)"
  by (induction list) auto

lemma list_properties_length: "(\<forall> i < length list . list ! i = (list @ [x]) ! i) \<and> (\<forall> i < length list - 1 . list ! i = (list @ [x]) ! i \<and> list ! (i + 1) = (list @ [x]) ! (i + 1))"
proof -
  have prop1: "\<forall> i < length list . list ! i = (list @ [x]) ! i" by (simp add: nth_append)
  hence prop2: "\<forall> i < length list - 1 . list ! i = (list @ [x]) ! i" by auto
  hence "\<forall> i < length list - 1 . list ! (i + 1) = (list @ [x]) ! (i + 1)" using prop1 by auto
  thus ?thesis using prop1 prop2 by blast
qed

lemma last_and_take_list: "list \<noteq> [] \<and> n < length list \<Longrightarrow> last (take (Suc n) list) = (take (Suc n) list) ! n"
  apply(induction list) apply simp using take_Suc_conv_app_nth last_snoc lessI nth_take by metis

lemma take_suc_length:
  assumes "Suc n < length run" "run \<noteq> []" "length run = length word + 1" "Suc n \<le> length word"
  shows "(take (Suc n) run) @ [run ! (Suc n)] = take (Suc (Suc n)) run \<and> (take n word) @ [word ! n] = take (Suc n) word"
  using assms take_Suc_conv_app_nth Suc_le_eq by metis

definition sublist :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where "sublist i j xs = take (j - i) (drop i xs)"

value "take (Suc 2) [0::nat,1,1,0,1,0,0,1]"
value "sublist (Suc 4) (length [0::nat,1,1,0,1,0,0,1]) [0::nat,1,1,0,1,0,0,1]"
value "(take (Suc 2) [0::nat,1,1,0,1,0,0,1]) @ (sublist (Suc 4) (length [0::nat,1,1,0,1,0,0,1]) [0::nat,1,1,0,1,0,0,1])"
value "take 2 [a,a,b,a,b,b,a]"
value "sublist 4 (length [a,a,b,a,b,b,a]) [a,a,b,a,b,b,a]"
value "(take 2 [a,a,b,a,b,b,a]) @ (sublist 4 (length [a,a,b,a,b,b,a]) [a,a,b,a,b,b,a])"

lemma length_sublist1:
  assumes "length run = n" "i < length run \<and> j < length run \<and> i < j"
  shows "length ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) = n + i - j"
proof - 
  have len: "length (take (Suc i) run) = Suc i" using assms by auto
  have "length (sublist (Suc j) (length run) run) = n - Suc j" using assms unfolding sublist_def by auto
  hence "length ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) = Suc i + (n - Suc j)" using len by auto
  thus ?thesis using assms by linarith
qed

lemma length_sublist2:
  assumes "length run = n" "i < length run \<and> j < length run \<and> i < j" "length run = length word + 1"
  shows "length ((take i word) @ (sublist j (length word) word)) = n + i - j - 1"
proof - 
  have len: "length (take i word) = i" using assms by auto
  have "length (sublist j (length word) word) = n - Suc j" using assms unfolding sublist_def by force
  hence "length ((take i word) @ (sublist j (length word) word)) = i + (n - Suc j)" using len by auto
  thus ?thesis using assms by linarith
qed

lemma length_sublist3:
  assumes "length run = n" "i < length run \<and> j < length run \<and> i < j" "n > 0"
  shows "length ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) < n"
proof -
  have "length ((take (Suc i) run) @ (sublist (Suc j) (length run) run)) = n + i - j" using assms length_sublist1 by blast
  thus ?thesis using assms by linarith
qed

lemma list_append_position1:
  assumes "k < length subrun1 - 1" "length (subrun1 @ subrun2) = length (subword1 @ subword2) + 1" "length subrun2 = length subword2"
  shows "(subrun1 @ subrun2) ! k = subrun1 ! k \<and> (subrun1 @ subrun2) ! (k + 1) = subrun1 ! (k + 1) \<and> (subword1 @ subword2) ! k = subword1 ! k"
  using assms by (simp add: nth_append)

lemma list_append_position2:
  assumes "k = length subrun1 - 1" "length (subrun1 @ subrun2) = length (subword1 @ subword2) + 1" "length subrun2 = length subword2" "subword2 \<noteq> []"
  shows "(subrun1 @ subrun2) ! k = last subrun1 \<and> (subrun1 @ subrun2) ! (k + 1) = subrun2 ! 0 \<and> (subword1 @ subword2) ! k = subword2 ! 0"
proof -
  have props: "subrun2 \<noteq> [] \<and> length subrun1 = length subword1 + 1" using assms by force
  have "(subrun1 @ subrun2) ! k = subrun1 ! k" using assms by (simp add: nth_append)
  hence "(subrun1 @ subrun2) ! k = subrun1 ! k \<and> subrun1 \<noteq> [] \<and> k = length subrun1 - 1" using props assms by force
  hence "(subrun1 @ subrun2) ! k = last subrun1" using list_properties_not_empty by metis
  thus ?thesis using assms props by (simp add: nth_append)
qed

lemma list_append_position3:
  assumes "k > length subrun1 - 1 \<and> k < length (subrun1 @ subrun2) - 1" "length (subrun1 @ subrun2) = length (subword1 @ subword2) + 1" "length subrun2 = length subword2" "subword2 \<noteq> []"
  shows "(subrun1 @ subrun2) ! k = subrun2 ! (k - length subrun1) \<and> (subrun1 @ subrun2) ! (k + 1) = subrun2 ! (k + 1 - length subrun1) \<and> (subword1 @ subword2) ! k = subword2 ! (k + 1 - length subrun1)"
  using assms by (simp add: nth_append)

lemma tl_subword: "Suc k < length list \<Longrightarrow> tl (sublist k (length list) list) = sublist (Suc k) (length list) list"
  using drop_Suc drop_take tl_drop unfolding sublist_def by metis

lemma tl_list_run_spezial: "0 < i \<and> i < length list \<Longrightarrow> list ! i = (tl list) ! (i - 1)"
  by (induction list) auto

lemma j_pos_tl: "j < length list - 1 \<Longrightarrow> (tl list) ! j = list ! (j + 1)"
  by (simp add: nth_tl)

lemma tl_empty: "list \<noteq> [] \<Longrightarrow> tl list = [] \<longleftrightarrow> length list = 1"
  by (induction list) auto

lemma tl_more_elements: "length list > 1 \<longleftrightarrow> tl list \<noteq> []"
  by (induction list) auto

lemma tl_more_elements2: "tl list \<noteq> [] \<Longrightarrow> list ! 1 = (tl list) ! 0"
  by (induction list) auto

lemma a_in_set_tl: "a \<in> set (tl ((word @ [a']) @ [a]))"
  by (induction word) auto

lemma nth_list_append1:
  assumes "k < length (list1 @ list2) - 1 \<and> k > length list1 - 1"
  shows "(list1 @ list2) ! (k + 1) = (list2) ! (k - length list1 + 1)"
proof -
  have assm: "k < length (list1 @ list2) - 1 \<and> k \<ge> length list1" using assms by linarith
  hence "k + 1 \<le> length (list1 @ list2) - 1 \<and> k + 1 > length list1" by auto
  thus ?thesis using assm less_not_sym nth_append ordered_cancel_comm_monoid_diff_class.add_diff_assoc2 by metis
qed

lemma nth_list_append2:
  assumes "k < length (list1 @ list2) - 1 \<and> k > length list1 - 1" "length (list3 @ list4) + 1 = length (list1 @ list2) \<and> length list1 = length list3 + 1"
  shows "(list3 @ list4) ! k = (list4) ! (k - length list1 + 1)"
  using Suc_diff_Suc assms by (simp add: nth_append)

lemma list_append_position4:
  assumes "k < length subrun1 - 1"
  shows "(subrun1 @ subrun2) ! k = subrun1 ! k \<and> (subrun1 @ subrun2) ! (k + 1) = subrun1 ! (k + 1)"
  using assms add_lessD1 less_diff_conv by (simp add: nth_append)

lemma list_append_position5:
  assumes "k = length subrun1 - 1" "length subrun1 > 0" "subrun2 \<noteq> []"
  shows "(subrun1 @ subrun2) ! k = last subrun1 \<and> (subrun1 @ subrun2) ! (k + 1) = subrun2 ! 0"
proof -
  have equi: "(subrun1 @ subrun2) ! k = subrun1 ! k" using assms by (simp add: nth_append)
  have "subrun1 ! k = last subrun1" using assms list_properties_not_empty by fast
  hence first: "(subrun1 @ subrun2) ! k = last subrun1" using equi by auto
  have "(subrun1 @ subrun2) ! (k + 1) = subrun2 ! 0" using assms by (simp add: nth_append)
  thus ?thesis using first by auto
qed

lemma list_append_position6_helper:
  assumes "(subrun1 @ subrun2) ! k = subrun2 ! (k - length subrun1)" "k > length subrun1 - 1 \<and> k < length (subrun1 @ subrun2) - 1"
  shows "(subrun1 @ subrun2) ! (k + 1) = subrun2 ! (k + 1 - length subrun1)"
  using assms add.commute add_strict_mono less_diff_conv less_not_refl nth_append by metis

lemma list_append_position6:
  assumes "k > length subrun1 - 1 \<and> k < length (subrun1 @ subrun2) - 1" "length subrun1 > 0"
  shows "(subrun1 @ subrun2) ! k = subrun2 ! (k - length subrun1) \<and> (subrun1 @ subrun2) ! (k + 1) = subrun2 ! (k + 1 - length subrun1)"
proof -
  have "(subrun1 @ subrun2) ! k = subrun2 ! (k - length subrun1)" using assms nth_append One_nat_def Suc_pred not_less_eq by metis
  thus ?thesis using assms list_append_position6_helper by blast
qed

lemma rev_simplifier: "rev list \<noteq> [] \<or> list \<noteq> [] \<Longrightarrow> last (rev list) = list ! 0 \<and> last list = rev list ! 0"
  using Nil_is_rev_conv hd_rev hd_conv_nth last_rev by fastforce

lemma minimal_index_for_element: "x \<in> set list \<longrightarrow> (\<exists> i < length list . list ! i = x \<and> (\<nexists> j . j < i \<and> list ! j = x))"
proof(induction list rule: rev_induct)
  case Nil thus ?case by auto
next
  case (snoc y list)
  consider (case1) "x \<in> set list" | (case2) "x \<notin> set list" by blast
  thus ?case
  proof cases
    case case1
    hence "\<exists> i < length list . list ! i = x \<and> (\<forall> j < i . list ! j \<noteq> x)" using snoc by blast
    then obtain i where i: "i < length list \<and> list ! i = x \<and> (\<forall> j < i . list ! j \<noteq> x)" by blast
    hence len: "i < length (list @ [y])" by simp
    have ith: "(list @ [y]) ! i = x" using i nth_append by metis
    have "(\<forall> j < i . (list @ [y]) ! j \<noteq> x)" using i butlast_snoc less_trans nth_butlast by metis
    hence "\<exists> i < length (list @ [y]) . (list @ [y]) ! i = x \<and> (\<forall> j < i . (list @ [y]) ! j \<noteq> x)" using len ith by blast
    thus ?thesis by blast
  next
    case case2
    consider (case3) "x \<noteq> y" | (case4) "x = y" by blast
    thus ?thesis
    proof cases
      case case3 thus ?thesis using case2 by force
    next
      case case4
      hence ith: "(list @ [y]) ! (length (list @ [y]) - 1) = x" by auto
      have len: "(length (list @ [y]) - 1) < length (list @ [y])" by auto
      have "(\<forall> j < (length (list @ [y]) - 1) . (list @ [y]) ! j \<noteq> x)" using case2 butlast_snoc in_set_conv_nth length_butlast nth_append by metis
      thus ?thesis using ith len by blast
    qed
  qed
qed

lemma maximal_index_for_element: "x \<in> set list \<longrightarrow> (\<exists> i < length list . list ! i = x \<and> x \<notin> set (sublist (Suc i) (length list) list))"
  unfolding sublist_def by (induction list) auto

fun new_butlast :: "'s list \<Rightarrow> 's list" where
  "new_butlast [] = []" |
  "new_butlast list = butlast list"

lemma new_butlast_subset: "list \<noteq> [] \<and> set list \<subseteq> X \<Longrightarrow> set (new_butlast (tl list)) \<subseteq> X"
  using in_set_butlastD list.set_sel(2) new_butlast.elims subset_code(1) by metis

lemma length_new_butlast_empty:
  assumes "list \<noteq> [] \<and> set (new_butlast (tl list)) \<subseteq> {}"
  shows "length list = 1 \<or> length list = 2"
proof(rule ccontr)
  assume "\<not> (length list = 1 \<or> length list = 2)"
  hence "length list > 2 \<or> length list = 0" by linarith
  hence "length list > 2" using assms by simp
  hence "length (tl list) > 1" by simp
  hence "length (new_butlast (tl list)) > 0" using Suc_diff_Suc length_0_conv length_butlast length_greater_0_conv nat.discI new_butlast.elims not_one_less_zero by metis
  thus False using assms by simp
qed

lemma new_butlast_equi: "new_butlast (tl list) = tl (new_butlast list)"
  using butlast.simps(1) butlast_tl new_butlast.elims by metis

lemma sub_set_tl: "set (tl list) \<subseteq> set list"
  using hd_Cons_tl list.set_intros(2) subsetI tl_Nil by metis

lemma length_new_butlast: "list \<noteq> [] \<Longrightarrow> length (new_butlast list) = length list - 1"
  by (induction list) auto

lemma new_butlast_equi2: "k < length list \<Longrightarrow> take k list = new_butlast (take (Suc k) list)"
proof(induction list rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x list)
  then consider (case1) "k < length list" | (case2) "k = length list" by fastforce
  thus ?case
  proof cases
    case case1 thus ?thesis using snoc by fastforce 
  next
    case case2
    hence lists: "take k (list @ [x]) = list \<and> take (Suc k) (list @ [x]) = list @ [x]" by force
    have "new_butlast (list @ [x]) = list" using new_butlast.elims snoc_eq_iff_butlast by metis
    thus ?thesis using lists by argo
  qed
qed

lemma new_butlast_equi3:
  assumes "list \<noteq> []"
  shows "new_butlast list = take (length list - 1) list"
proof -
  have "new_butlast list = butlast list" using assms new_butlast.elims by blast
  thus ?thesis by (simp add: butlast_conv_take)
qed

lemma new_butlast_equi4: "k < length list \<Longrightarrow> sublist k (length prun - 1) prun = new_butlast (sublist k (length prun) prun)"
  using diff_right_commute length_drop nat_le_linear new_butlast.simps(1) new_butlast_equi3 take_all_iff take_eq_Nil unfolding sublist_def by metis

lemma subset_sublist_k: "k < length list \<Longrightarrow> set (tl (sublist k (length list - 1) list)) \<subseteq> set (tl (sublist 0 (length list - 1) list))"
proof(induction list rule: rev_induct)
  case Nil thus ?case by auto
next
  case (snoc s list)
  then consider (case1) "k < length list" | (case2) "k = length list" by fastforce
  thus ?case 
  proof cases
    case case1   
    have equi: "sublist 0 (length (list @ [s]) - 1) (list @ [s]) = list" unfolding sublist_def by simp
    have "set (tl (sublist k (length (list @ [s]) - 1) (list @ [s]))) \<subseteq> set (tl list)" unfolding sublist_def by (simp add: set_drop_subset tl_drop)
    thus ?thesis using equi by argo
  next
    case case2 thus ?thesis unfolding sublist_def by simp
  qed
qed

lemma list_append_new_butlast: "list1 \<noteq> [] \<and> list2 \<noteq> [] \<Longrightarrow> new_butlast (tl (list1 @ list2)) = (tl list1) @ (new_butlast list2)"
  using Nil_is_append_conv butlast_append new_butlast.elims tl_append2 by metis 

lemma new_butlast_not_empty: "length list > 1 \<Longrightarrow> new_butlast list \<noteq> []"
  by (induction list) auto

lemma bigger_set_butlast_tl: "z \<in> set (new_butlast list) \<Longrightarrow> z \<in> set list"
  using in_set_butlastD new_butlast.elims by metis

lemma length_bigger_two:
  assumes "list \<noteq> []" "z \<in> set (new_butlast (tl list))"
  shows "length list > 2"
proof(rule ccontr)
  assume assm: "\<not> length list > 2"
  hence "length list = 0 \<or> length list = 1 \<or> length list = 2" by linarith
  then consider (case1) "length list = 0" | (case2) "length list = 1" | (case3) "length list = 2" by blast
  thus False 
  proof cases
    case case1 thus ?thesis using assms by simp
  next
    case case2 thus ?thesis using assms length_pos_if_in_set less_numeral_extra(3) list.size(3) new_butlast.simps(1) tl_empty by metis
  next
    case case3
    hence len: "length (tl list) = 1" by force
    hence "tl list \<noteq> []" by fastforce
    hence "length (new_butlast (tl list)) = 0" using len length_new_butlast by force
    hence "new_butlast (tl list) = []" by simp
    thus ?thesis using assms by simp
  qed
qed

end