theory automaton_isomorphy

imports Main Nat_Bijection masterarbeit_benno_thalmann

begin

text \<open>Author: Benno Thalmann, last update: 12.1.2026, Addition to masterarbeit_benno_thalmann\<close>

text \<open>We can generalize the concept of state renaming via isomorphy\<close>
definition isomorphic_automata :: "('s, 'a) automaton \<Rightarrow> ('t, 'b) automaton \<Rightarrow> bool" where
  "isomorphic_automata \<A>1 \<A>2 =
    (\<exists> f h . bij_betw f (states \<A>1) (states \<A>2) \<and>
    bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and>
    f (initial_state \<A>1) = initial_state \<A>2 \<and>
    image f (accepting_states \<A>1) = accepting_states \<A>2 \<and>
    image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2)"

text \<open>Properties of Isomorphy\<close>
theorem iso_reflexiv: "isomorphic_automata \<A> \<A>"
  unfolding isomorphic_automata_def by fastforce

theorem iso_transitive:
  assumes "isomorphic_automata \<A>1 \<A>2" "isomorphic_automata \<A>2 \<A>3"
  shows "isomorphic_automata \<A>1 \<A>3"
proof -
  obtain f h where org: "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms unfolding isomorphic_automata_def by presburger
  obtain f' h' where prime: "bij_betw f' (states \<A>2) (states \<A>3) \<and> bij_betw h' (alphabet \<A>2) (alphabet \<A>3) \<and> f' (initial_state \<A>2) = initial_state \<A>3 \<and> image f' (accepting_states \<A>2) = accepting_states \<A>3 \<and> image (\<lambda>(s1, a, s2) . (f' s1, h' a, f' s2)) (transitions \<A>2) = transitions \<A>3" using assms unfolding isomorphic_automata_def by presburger
  let ?f_comp = "f' \<circ> f"
  let ?h_comp = "h' \<circ> h"
  have bij_f_comp: "bij_betw ?f_comp (states \<A>1) (states \<A>3)" using org prime bij_betw_trans by fast
  have bij_h_comp: "bij_betw ?h_comp (alphabet \<A>1) (alphabet \<A>3)" using org prime bij_betw_trans by metis
  have init: "?f_comp (initial_state \<A>1) = initial_state \<A>3" using org prime by auto
  have acc: "image ?f_comp (accepting_states \<A>1) = accepting_states \<A>3" using org prime image_comp by metis
  {
    fix s1 s2 a assume assm: "(s1, a, s2) \<in> transitions \<A>1"
    have "image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2" using org by auto
    hence trans: "(f s1, h a, f s2) \<in> transitions \<A>2" using assm by force
    have "image (\<lambda>(s1, a, s2) . (f' s1, h' a, f' s2)) (transitions \<A>2) = transitions \<A>3" using prime by auto
    hence "(?f_comp s1, ?h_comp a, ?f_comp s2) \<in> transitions \<A>3" using trans by force
  }
  hence left: "image (\<lambda>(s1, a, s2). (?f_comp s1, ?h_comp a, ?f_comp s2)) (transitions \<A>1) \<subseteq> transitions \<A>3" by auto
  {
    fix s1 s2 a assume assm: "(s1, a, s2) \<in> transitions \<A>3"
    have "image (\<lambda>(s1, a, s2) . (f' s1, h' a, f' s2)) (transitions \<A>2) = transitions \<A>3" using prime by auto
    hence "\<exists> (s1', a', s2') \<in> transitions \<A>2 . (s1, a, s2) = (f' s1', h' a', f' s2')" using assm by fast
    then obtain s1' s2' a' where s': "(s1', a', s2') \<in> transitions \<A>2 \<and> s1 = f' s1' \<and> s2 = f' s2' \<and> a = h' a'" by blast
    have "image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2" using org by auto
    hence "\<exists> (s1'', a'', s2'') \<in> transitions \<A>1 . (s1', a', s2') = (f s1'', h a'', f s2'')" using s' by fast
    then obtain s1'' s2'' a'' where s'': "(s1'', a'', s2'') \<in> transitions \<A>1 \<and> s1' = f s1'' \<and> s2' = f s2'' \<and> a' = h a''" by blast
    hence "\<exists> (s1'', a'', s2'') \<in> transitions \<A>1 . (s1, a, s2) = (?f_comp s1'', ?h_comp a'', ?f_comp s2'')" using s' s'' by auto
  }
  hence "transitions \<A>3 \<subseteq> image (\<lambda>(s1, a, s2). (?f_comp s1, ?h_comp a, ?f_comp s2)) (transitions \<A>1)" by force
  hence "image (\<lambda>(s1, a, s2). (?f_comp s1, ?h_comp a, ?f_comp s2)) (transitions \<A>1) = transitions \<A>3" using left by auto
  thus ?thesis using bij_f_comp bij_h_comp init acc unfolding isomorphic_automata_def by blast
qed

theorem iso_preserves_auto_well_defined:
  assumes "auto_well_defined \<A>1" "isomorphic_automata \<A>1 \<A>2"
  shows "auto_well_defined \<A>2"
proof -
  have states: "finite (states \<A>2)" using assms bij_betw_finite unfolding auto_well_defined_def isomorphic_automata_def by fast
  have alphabet: "finite (alphabet \<A>2)" using assms bij_betw_finite unfolding auto_well_defined_def isomorphic_automata_def by auto
  have init: "initial_state \<A>2 \<in> states \<A>2" using bij_betwE assms unfolding auto_well_defined_def isomorphic_automata_def by metis
  {
    fix s1 s2 a assume assm: "(s1, a, s2) \<in> transitions \<A>2"
    have "\<exists> f h . bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms unfolding isomorphic_automata_def by auto
    hence "\<exists> (s1', a', s2') \<in> transitions \<A>1 . (\<exists> f h . bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> (s1, a, s2) = (f s1', h a', f s2'))" using assm by fast
    hence "\<exists> (s1', a', s2') \<in> transitions \<A>1 . s1' \<in> states \<A>1 \<and> s2' \<in> states \<A>1 \<and> a' \<in> alphabet \<A>1 \<and> (\<exists> f h . bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> (s1, a, s2) = (f s1', h a', f s2'))" using assms well_def_trans_components by fast
    then obtain s1' s2' a' where "s1' \<in> states \<A>1 \<and> s2' \<in> states \<A>1 \<and> a' \<in> alphabet \<A>1 \<and> (\<exists> f h . bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> s1 = f s1' \<and> s2 = f s2' \<and> a = h a')" by blast
    hence "s1 \<in> states \<A>2 \<and> s2 \<in> states \<A>2 \<and> a \<in> alphabet \<A>2" using assm bij_betwE by metis
  }
  hence trans: "(\<forall> (s1, a, s2) \<in> transitions \<A>2 . s1 \<in> states \<A>2 \<and> s2 \<in> states \<A>2 \<and> a \<in> alphabet \<A>2)" by blast
  have "accepting_states \<A>1 \<subseteq> states \<A>1 \<and> (\<exists> f . bij_betw f (states \<A>1) (states \<A>2) \<and> image f (accepting_states \<A>1) = accepting_states \<A>2)" using assms unfolding auto_well_defined_def isomorphic_automata_def by auto
  hence "accepting_states \<A>2 \<subseteq> states \<A>2" using bij_betw_imp_surj_on image_mono by fast
  thus ?thesis using states alphabet init trans unfolding auto_well_defined_def by blast
qed

corollary language_well_def_iso_auto:
  assumes "auto_well_defined \<A>1" "isomorphic_automata \<A>1 \<A>2"
  shows "language_well_defined (language_auto \<A>2) (alphabet \<A>2)"
  using iso_preserves_auto_well_defined assms automata_language_are_well_defined by blast

lemma bijection_inverse_special_states:
  assumes "auto_well_defined \<A>1" "bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw f (states \<A>1) (states \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2). (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "(inv_into (states \<A>1) f) (initial_state \<A>2) = initial_state \<A>1 \<and> image (inv_into (states \<A>1) f) (accepting_states \<A>2) = accepting_states \<A>1"
proof -
  have "auto_well_defined \<A>2" using iso_preserves_auto_well_defined assms unfolding isomorphic_automata_def by auto
  hence adds: "initial_state \<A>1 \<in> states \<A>1 \<and> initial_state \<A>2 \<in> states \<A>2 \<and> accepting_states \<A>1 \<subseteq> states \<A>1 \<and> accepting_states \<A>2 \<subseteq> states \<A>2 \<and> (\<forall> (s1, a, s2) \<in> transitions \<A>1 . s1 \<in> states \<A>1 \<and> s2 \<in> states \<A>1) \<and> (\<forall> (s1, a, s2) \<in> transitions \<A>2 . s1 \<in> states \<A>2 \<and> s2 \<in> states \<A>2)" using assms unfolding auto_well_defined_def by fast
  hence init: "inv_into (states \<A>1) f (initial_state \<A>2) = initial_state \<A>1" using assms bij_betw_inv_into_left by metis
  have "image (inv_into (states \<A>1) f)(accepting_states \<A>2) = accepting_states \<A>1" using assms bij_betw_imp_surj_on adds bij_betw_inv_into_subset by metis
  thus ?thesis using init by fast
qed

lemma bijection_inverse_trans:
  assumes "auto_well_defined \<A>1" "bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw f (states \<A>1) (states \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2). (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "image (\<lambda>(s1, a, s2). ((inv_into (states \<A>1) f) s1, (inv_into (alphabet \<A>1) h) a, (inv_into (states \<A>1) f) s2)) (transitions \<A>2) = transitions \<A>1"
proof -
  have "auto_well_defined \<A>2" using iso_preserves_auto_well_defined assms unfolding isomorphic_automata_def by auto
  hence adds: "(\<forall> (s1, a, s2) \<in> transitions \<A>1 . s1 \<in> states \<A>1 \<and> s2 \<in> states \<A>1) \<and> (\<forall> (s1, a, s2) \<in> transitions \<A>2 . s1 \<in> states \<A>2 \<and> s2 \<in> states \<A>2)" using assms unfolding auto_well_defined_def by fast
  let ?g = "inv_into (states \<A>1) f"
  let ?h_inv = "inv_into (alphabet \<A>1) h"
  {
    fix tr assume "tr \<in> image (\<lambda>(s1, a, s2). (?g s1, ?h_inv a, ?g s2)) (transitions \<A>2)"
    then obtain s1 s2 a where tr: "(s1, a, s2) \<in> transitions \<A>2 \<and> tr = (?g s1, ?h_inv a, ?g s2)" by auto
    have "image (\<lambda>(s1, a, s2). (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms by fast
    hence "\<exists> s1' s2' a'. (s1', a', s2') \<in> transitions \<A>1 \<and> (s1, a, s2) = (f s1', h a', f s2')" using tr by fast
    then obtain s1' s2' a' where A1_trans: "(s1', a', s2') \<in> transitions \<A>1 \<and> f s1' = s1 \<and> f s2' = s2 \<and> h a' = a" by blast
    hence "(?g s1, ?h_inv a, ?g s2) = (s1', a', s2')" using assms bij_betw_inv_into_left well_def_trans_components by metis
    hence "tr \<in> transitions \<A>1" using A1_trans tr by auto
  }
  hence sub: "image (\<lambda>(s1, a, s2). (?g s1, ?h_inv a, ?g s2)) (transitions \<A>2) \<subseteq> transitions \<A>1" by blast
  {
    fix s1 s2 a assume assm: "(s1, a, s2) \<in> transitions \<A>1"
    have "image (\<lambda>(s1, a, s2). (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms by argo
    hence "(f s1, h a, f s2) \<in> transitions \<A>2" using assm by force 
    hence image: "(?g (f s1), ?h_inv (h a), ?g (f s2)) \<in> image (\<lambda>(s1, a, s2). (?g s1, ?h_inv a, ?g s2)) (transitions \<A>2)" by force
    hence "?g (f s1) = s1 \<and> ?g (f s2) = s2 \<and> ?h_inv (h a) = a" using bij_betw_inv_into_left adds assms assm well_def_trans_components by metis
    hence "(s1, a, s2) \<in> image (\<lambda>(s1, a, s2). (?g s1, ?h_inv a, ?g s2)) (transitions \<A>2)" using image by argo
  }
  hence "transitions \<A>1 \<subseteq> image (\<lambda>(s1, a, s2). (?g s1, ?h_inv a, ?g s2)) (transitions \<A>2)" by auto
  hence "image (\<lambda>(s1, a, s2). (?g s1, ?h_inv a, ?g s2)) (transitions \<A>2) = transitions \<A>1" using sub by blast
  thus ?thesis by fast
qed

theorem isomorphy_symmetry:
  assumes "auto_well_defined \<A>1" "isomorphic_automata \<A>1 \<A>2"
  shows "isomorphic_automata \<A>2 \<A>1"
proof -
  obtain f h where props: "bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw f (states \<A>1) (states \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2). (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms unfolding isomorphic_automata_def by auto
  let ?g = "inv_into (states \<A>1) f"
  let ?h_inv = "inv_into (alphabet \<A>1) h"
  have bij: "bij_betw ?h_inv (alphabet \<A>2) (alphabet \<A>1) \<and> bij_betw ?g (states \<A>2) (states \<A>1)" using props bij_betw_inv_into by metis
  have first: "?g (initial_state \<A>2) = initial_state \<A>1 \<and> image ?g (accepting_states \<A>2) = accepting_states \<A>1" using assms props bijection_inverse_special_states by metis
  have "image (\<lambda>(s1, a, s2). (?g s1, ?h_inv a, ?g s2)) (transitions \<A>2) = transitions \<A>1" using assms props bijection_inverse_trans by metis
  thus ?thesis using bij first unfolding isomorphic_automata_def by auto
qed

lemma bij_exist:
  assumes "bij_betw f A B" "y \<in> B"
  shows "\<exists> x \<in> A . f x = y"
  using assms bij_betw_imp_surj_on by blast

theorem iso_preserves_DFA_property:
  assumes "auto_well_defined \<A>1" "isomorphic_automata \<A>1 \<A>2" "DFA_property \<A>1"
  shows "DFA_property \<A>2"
proof -
  obtain f h where bij: "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms unfolding isomorphic_automata_def by auto
  {
    fix s1 a assume assm: "s1 \<in> states \<A>2 \<and> a \<in> alphabet \<A>2"
    hence s1': "\<exists> s1' . s1' \<in> states \<A>1 \<and> f s1' = s1" using bij bij_exist by fast
    have "\<exists> a' . a' \<in> alphabet \<A>1 \<and> h a' = a" using bij bij_exist assm by fast
    then obtain s1' a' where var: "s1' \<in> states \<A>1 \<and> a' \<in> alphabet \<A>1 \<and> f s1' = s1 \<and> h a' = a" using s1' by blast
    hence unique: "\<exists>! s2' \<in> states \<A>1 . (s1', a', s2') \<in> transitions \<A>1" using assms unfolding DFA_property_def by auto
    then obtain s2' where "s2' \<in> states \<A>1 \<and> (s1', a', s2') \<in> transitions \<A>1" by auto
    hence "(s1, a, f s2') \<in> transitions \<A>2 \<and> f s2' \<in> states \<A>2" using bij var bij_betwE by force
    hence "\<exists> s2 . (s1, a, s2) \<in> transitions \<A>2 \<and> s2 \<in> states \<A>2" by auto
  }
  hence existence: "\<forall> s1 a . s1 \<in> states \<A>2 \<and> a \<in> alphabet \<A>2 \<longrightarrow> (\<exists> s2 . s2 \<in> states \<A>2 \<and> (s1, a, s2) \<in> transitions \<A>2)" by auto
  {
    fix s1 a s2 y assume assm: "s1 \<in> states \<A>2 \<and> a \<in> alphabet \<A>2 \<and> s2 \<in> states \<A>2 \<and> (s1, a, s2) \<in> transitions \<A>2 \<and> y \<in> states \<A>2 \<and> (s1, a, y) \<in> transitions \<A>2" 
    hence s1': "\<exists> s1' . s1' \<in> states \<A>1 \<and> f s1' = s1" using bij bij_exist by fast
    have s2': "\<exists> s2' . s2' \<in> states \<A>1 \<and> f s2' = s2" using bij bij_exist assm by fast
    have y': "\<exists> y' . y' \<in> states \<A>1 \<and> f y' = y" using bij bij_exist assm by fast
    have "\<exists> a' . a' \<in> alphabet \<A>1 \<and> h a' = a" using bij bij_exist assm by fast
    then obtain s1' s2' y' a' where var: "s1' \<in> states \<A>1 \<and> f s1' = s1 \<and> s2' \<in> states \<A>1 \<and> f s2' = s2 \<and> y' \<in> states \<A>1 \<and> f y' = y \<and> a' \<in> alphabet \<A>1 \<and> h a' = a" using bij s1' s2' y' by blast
    hence "(f s1', h a', f s2') \<in> transitions \<A>2 \<and> (f s1', h a', f y') \<in> transitions \<A>2" using assm by auto
    hence in_image: "(f s1', h a', f s2') \<in> image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) \<and> (f s1', h a', f y') \<in> image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1)" using bij by blast
    hence "(\<exists> s1'' s2'' a'' . (s1'', a'', s2'') \<in> transitions \<A>1 \<and> (f s1'', h a'', f s2'') = (f s1', h a', f s2')) \<and> (\<exists> t1'' y'' b'' . (t1'', b'', y'') \<in> transitions \<A>1 \<and> (f t1'', h b'', f y'') = (f s1', h a', f y'))" using assm var by fastforce
    then obtain s1'' s2'' a'' t1'' y'' b'' where trans: "(s1'', a'', s2'') \<in> transitions \<A>1 \<and> (f s1'', h a'', f s2'') = (f s1', h a', f s2') \<and> (t1'', b'', y'') \<in> transitions \<A>1 \<and> (f t1'', h b'', f y'') = (f s1', h a', f y')" by blast
    hence "f s1'' = f s1' \<and> f s2'' = f s2' \<and> h a'' = h a' \<and> f t1'' = f s1' \<and> f y'' = f y' \<and> h b'' = h a'" by blast
    hence equi: "f s1'' = s1 \<and> f s2'' = s2 \<and> h a'' = a \<and> f t1'' = s1 \<and> f y'' = y \<and> h b'' = a" using var by argo
    have in_states: "s1'' \<in> states \<A>1 \<and> s2'' \<in> states \<A>1 \<and> t1'' \<in> states \<A>1 \<and> y'' \<in> states \<A>1 \<and> a'' \<in> alphabet \<A>1 \<and> b'' \<in> alphabet \<A>1" using assms trans well_def_trans_components by fast
    hence "s1'' = t1'' \<and> a'' = b''" using equi bij bij_betw_inv_into_left by metis
    hence "s2'' = y''" using trans assms in_states unfolding DFA_property_def by blast
    hence "s2 = y" using bij equi by blast
  }
  thus ?thesis using existence unfolding DFA_property_def by blast
qed

text \<open>Isomorphic automata accept the same language with respect to the bijection\<close>
theorem iso_prun_correct:
  assumes "auto_well_defined \<A>1" "bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw f (states \<A>1) (states \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2). (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "(\<forall> prun word s . pseudo_run_well_defined prun \<A>1 s word \<longrightarrow> pseudo_run_well_defined (map f prun) \<A>2 (f s) (map h word)) \<and> (\<forall> prun word s . pseudo_run_well_defined prun \<A>2 s word \<longrightarrow> pseudo_run_well_defined (map (inv_into (states \<A>1) f) prun) \<A>1 (inv_into (states \<A>1) f s) (map (inv_into (alphabet \<A>1) h) word))"
proof -
  {
    fix prun word s assume assm: "pseudo_run_well_defined prun \<A>1 s word"
    hence len: "length (map f prun) = length (map h word) + 1" unfolding pseudo_run_well_defined_def by force
    hence "prun \<noteq> []" by auto
    hence start: "(map f prun) ! 0 = f (prun ! 0)" by auto
    have "prun ! 0 = s \<and> s \<in> states \<A>1" using assm unfolding pseudo_run_well_defined_def by auto
    hence init: "(map f prun) ! 0 = f s \<and> (f s) \<in> states \<A>2" using assms start bij_betw_apply by metis
    {
      fix i assume "i < length (map f prun) - 1"
      hence "i < length prun - 1" using len by auto
      hence trans: "(prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>1" using assm unfolding pseudo_run_well_defined_def by blast
      have "image (\<lambda>(s1, a, s2). (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms by argo
      hence "(f (prun ! i), h (word ! i), f (prun ! (i + 1))) \<in> transitions \<A>2" using trans by force
    }
    hence step: "\<forall> i < length (map f prun) - 1. ((map f prun) ! i, (map h word) ! i, (map f prun) ! (i + 1)) \<in> transitions \<A>2" using len by auto
    hence "pseudo_run_well_defined (map f prun) \<A>2 (f s) (map h word)" using assms len init step unfolding pseudo_run_well_defined_def by blast
  }
  hence impl: "\<forall> prun word s . pseudo_run_well_defined prun \<A>1 s word \<longrightarrow> pseudo_run_well_defined (map f prun) \<A>2 (f s) (map h word)" by blast
  let ?g = "inv_into (states \<A>1) f"
  let ?h_inv = "inv_into (alphabet \<A>1) h"
  have bij: "bij_betw ?h_inv (alphabet \<A>2) (alphabet \<A>1) \<and> bij_betw ?g (states \<A>2) (states \<A>1)" using assms bij_betw_inv_into by metis
  have inv: "image (\<lambda>(s1, a, s2). (?g s1, ?h_inv a, ?g s2)) (transitions \<A>2) = transitions \<A>1" using assms bijection_inverse_trans by simp
  {
    fix prun word s assume assm: "pseudo_run_well_defined prun \<A>2 s word"
    hence len: "length (map ?g prun) = length (map ?h_inv word) + 1" unfolding pseudo_run_well_defined_def by auto
    hence "prun \<noteq> []" by auto
    hence start: "(map ?g prun) ! 0 = ?g (prun ! 0)" by auto
    have "prun ! 0 = s \<and> s \<in> states \<A>2" using assm unfolding pseudo_run_well_defined_def by auto
    hence init: "(map ?g prun) ! 0 = ?g s \<and> (?g s) \<in> states \<A>1" using start bij bij_betw_apply by fast
    {
      fix i assume "i < length (map ?g prun) - 1"
      hence "i < length prun - 1" using len by auto
      hence trans: "(prun ! i, word ! i, prun ! (i + 1)) \<in> transitions \<A>2" using assm unfolding pseudo_run_well_defined_def by blast
      have "image (\<lambda>(s1, a, s2) . (?g s1, ?h_inv a, ?g s2)) (transitions \<A>2) = transitions \<A>1" using inv by blast
      hence "(?g (prun ! i), ?h_inv (word ! i), ?g (prun ! (i + 1))) \<in> transitions \<A>1" using trans by force
    }
    hence step: "\<forall> i < length (map ?g prun) - 1. ((map ?g prun) ! i, (map ?h_inv word) ! i, (map ?g prun) ! (i + 1)) \<in> transitions \<A>1" using len by auto
    hence "pseudo_run_well_defined (map ?g prun) \<A>1 (?g s) (map ?h_inv word)" using assms len init step unfolding pseudo_run_well_defined_def by blast
  }
  hence "\<forall> prun word s .pseudo_run_well_defined prun \<A>2 s word \<longrightarrow> pseudo_run_well_defined (map ?g prun) \<A>1 (?g s) (map ?h_inv word)" by blast
  thus ?thesis using impl by blast
qed

proposition iso_run_correct:
  assumes "auto_well_defined \<A>1" "bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw f (states \<A>1) (states \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2). (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "(\<forall> run word . run_accepting run \<A>1 word \<longrightarrow> run_accepting (map f run) \<A>2 (map h word)) \<and> (\<forall> run word . run_accepting run \<A>2 word \<longrightarrow> run_accepting (map (inv_into (states \<A>1) f) run) \<A>1 (map (inv_into (alphabet \<A>1) h) word))"
proof - 
  have well_def: "auto_well_defined \<A>2" using iso_preserves_auto_well_defined assms unfolding isomorphic_automata_def by auto
  {
    fix run word assume assm: "run_accepting run \<A>1 word"
    hence "pseudo_run_well_defined run \<A>1 (initial_state \<A>1) word \<and> last run \<in> accepting_states \<A>1" unfolding run_accepting_def run_well_defined_def by blast
    hence prun: "pseudo_run_well_defined (map f run) \<A>2 (f (initial_state \<A>1)) (map h word) \<and> last run \<in> accepting_states \<A>1" using assms iso_prun_correct unfolding run_well_defined_def by metis
    hence not_empty: "run \<noteq> []" unfolding pseudo_run_well_defined_def by auto
    hence start: "(map f run) ! 0 = f (run ! 0)" by auto
    have "run ! 0 = initial_state \<A>1" using assm unfolding run_well_defined_def run_accepting_def pseudo_run_well_defined_def by auto
    hence "(map f run) ! 0 = initial_state \<A>2" using assms start by argo
    hence init: "(map f run) ! 0 = initial_state \<A>2 \<and> initial_state \<A>2 \<in> states \<A>2" using well_def unfolding auto_well_defined_def by blast
    have last: "f (last run) = last (map f run)" using not_empty last_map by metis
    have "last run \<in> accepting_states \<A>1" using assm unfolding run_well_defined_def run_accepting_def by blast
    hence "f (last run) \<in> accepting_states \<A>2" using assms by blast
    hence "last (map f run) \<in> accepting_states \<A>2" using last by auto
    hence "run_accepting (map f run) \<A>2 (map h word)" using prun init unfolding run_well_defined_def run_accepting_def pseudo_run_well_defined_def by auto
  }
  hence impl: "\<forall> run word . run_accepting run \<A>1 word \<longrightarrow> run_accepting (map f run) \<A>2 (map h word)" using assms by blast
  let ?g = "inv_into (states \<A>1) f"
  let ?h_inv = "inv_into (alphabet \<A>1) h"
  have inv: "?g (initial_state \<A>2) = initial_state \<A>1 \<and> image ?g (accepting_states \<A>2) = accepting_states \<A>1" using assms bijection_inverse_special_states by metis
  {
    fix run word assume assm: "run_accepting run \<A>2 word"
    hence "pseudo_run_well_defined run \<A>2 (initial_state \<A>2) word \<and> last run \<in> accepting_states \<A>2" unfolding run_accepting_def run_well_defined_def by blast
    hence prun: "pseudo_run_well_defined (map ?g run) \<A>1 (?g (initial_state \<A>2)) (map ?h_inv word) \<and> last run \<in> accepting_states \<A>2" using assms iso_prun_correct unfolding run_well_defined_def by metis
    hence not_empty: "run \<noteq> []" unfolding pseudo_run_well_defined_def by auto
    hence start: "(map ?g run) ! 0 = ?g (run ! 0)" by auto
    have "run ! 0 = initial_state \<A>2" using assm unfolding run_well_defined_def run_accepting_def pseudo_run_well_defined_def by auto
    hence "(map ?g run) ! 0 = initial_state \<A>1" using inv start by argo
    hence init: "(map ?g run) ! 0 = initial_state \<A>1 \<and> initial_state \<A>1 \<in> states \<A>1" using assms unfolding auto_well_defined_def by blast
    have last: "?g (last run) = last (map ?g run)" using not_empty last_map by metis
    have "last run \<in> accepting_states \<A>2" using assm unfolding run_well_defined_def run_accepting_def by blast
    hence "?g (last run) \<in> accepting_states \<A>1" using inv by blast
    hence "last (map ?g run) \<in> accepting_states \<A>1" using last by auto
    hence "run_accepting (map ?g run) \<A>1 (map ?h_inv word)" using prun init unfolding run_well_defined_def run_accepting_def pseudo_run_well_defined_def by auto
  }
  thus ?thesis using impl by blast
qed

lemma map_bij:
  assumes "bij_betw h A B"
  shows "set word \<subseteq> A \<Longrightarrow> map (inv_into A h) (map h word) = word"
  using assms bij_betw_inv_into_left by (induction word rule: rev_induct) auto

theorem closed_under_iso:
  assumes "auto_well_defined \<A>1" "bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw f (states \<A>1) (states \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2). (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "word \<in> language_auto \<A>1 \<longleftrightarrow> word_well_defined word (alphabet \<A>1) \<and> (map h word) \<in> language_auto \<A>2"
proof - 
  have impl: "(\<forall> run word . run_accepting run \<A>1 word \<longrightarrow> run_accepting (map f run) \<A>2 (map h word)) \<and> (\<forall> run word . run_accepting run \<A>2 word \<longrightarrow> run_accepting (map (inv_into (states \<A>1) f) run) \<A>1 (map (inv_into (alphabet \<A>1) h) word))" using assms iso_run_correct by metis
  {
    fix word assume assm: "word \<in> language_auto \<A>1"
    hence l2: "(map h word) \<in> language_auto \<A>2" using impl unfolding language_auto_def by auto
    have "word_well_defined word (alphabet \<A>1)" using assm assms word_in_language_is_well_defined by auto
    hence "(map h word) \<in> language_auto \<A>2 \<and> word_well_defined word (alphabet \<A>1)" using l2 by auto
  }
  hence left: "\<forall> word . (word \<in> language_auto \<A>1 \<longrightarrow> (word_well_defined word (alphabet \<A>1) \<and> (map h word) \<in> language_auto \<A>2))" by auto
  let ?h_inv = "inv_into (alphabet \<A>1) h"
  {
    fix word assume assm: "word_well_defined word (alphabet \<A>1) \<and> (map h word) \<in> language_auto \<A>2"
    hence "(map ?h_inv (map h word)) \<in> language_auto \<A>1" using impl unfolding language_auto_def by blast
    hence "word \<in> language_auto \<A>1" using map_bij assm assms unfolding word_well_defined_def by metis
  }
  thus ?thesis using left by blast
qed

lemma inv_inv:
  assumes "bij_betw h A B" "set word \<subseteq> A"
  shows "map (inv_into B (inv_into A h)) word = map h word"
  using assms inv_into_inv_into_eq by fastforce

text \<open>Main results for isomorphy\<close>
proposition image_language_is_well_defined:
  assumes "auto_well_defined \<A>" 
  shows "language_well_defined (image (map h) (language_auto \<A>)) (image h (alphabet \<A>))"
  using assms automata_language_are_well_defined unfolding language_well_defined_def word_well_defined_def by auto

theorem language_iso_correctness:
  assumes "auto_well_defined \<A>1" "bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw f (states \<A>1) (states \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2). (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "language_auto \<A>2 = image (map h) (language_auto \<A>1)"
proof -
  have well_def: "auto_well_defined \<A>2" using iso_preserves_auto_well_defined assms unfolding isomorphic_automata_def by auto
  have impl: "(\<forall> run word . run_accepting run \<A>1 word \<longrightarrow> run_accepting (map f run) \<A>2 (map h word))\<and> (\<forall> run word . run_accepting run \<A>2 word \<longrightarrow> run_accepting (map (inv_into (states \<A>1) f) run) \<A>1 (map (inv_into (alphabet \<A>1) h) word))" using assms iso_run_correct by metis
  {
    fix word assume assm: "word \<in> language_auto \<A>1"
    hence "(map h word) \<in> language_auto \<A>2" using impl unfolding language_auto_def by auto
  }
  hence left: "image (map h) (language_auto \<A>1) \<subseteq> language_auto \<A>2" unfolding language_auto_def by auto
  let ?h_inv = "inv_into (alphabet \<A>1) h"
  let ?g = "inv_into (states \<A>1) f"
  have bij: "bij_betw ?h_inv (alphabet \<A>2) (alphabet \<A>1) \<and> bij_betw ?g (states \<A>2) (states \<A>1)" using assms bij_betw_inv_into by metis
  {
    fix word assume assm: "word \<in> language_auto \<A>2"
    hence "set word \<subseteq> alphabet \<A>2" using word_in_language_is_well_defined well_def unfolding word_well_defined_def by auto
    hence word: "map (inv_into (alphabet \<A>2) ?h_inv) (map ?h_inv word) = word" using map_bij bij by fast
    have l1: "(map ?h_inv word) \<in> language_auto \<A>1" using impl assm unfolding language_auto_def by blast
    hence "word_well_defined (map ?h_inv word) (alphabet \<A>1)" using word_in_language_is_well_defined assms by auto
    hence "set (map ?h_inv word) \<subseteq> alphabet \<A>1" unfolding word_well_defined_def by auto
    hence h_inv: "map (inv_into (alphabet \<A>2) ?h_inv) (map ?h_inv word) = map h (map ?h_inv word)" using assms inv_inv by metis
    have "(map h) (map ?h_inv word) \<in> image (map h) (language_auto \<A>1)" using l1 by blast
    hence "word \<in> image (map h) (language_auto \<A>1)" using h_inv word by argo
  }
  hence "language_auto \<A>2 \<subseteq> image (map h) (language_auto \<A>1)" unfolding language_auto_def by blast
  thus ?thesis using left by auto
qed

corollary language_iso_correctness_unfold:
  assumes "auto_well_defined \<A>1" "isomorphic_automata \<A>1 \<A>2"
  obtains h where "bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> language_auto \<A>2 = image (map h) (language_auto \<A>1)"
  using language_iso_correctness assms unfolding isomorphic_automata_def by metis



text \<open>Soft Isomorphy between automata with same alphabet, so the  between alphabet1 and alphabet2 is the id\<close> 
definition soft_isomorphic_automata :: "('s, 'a) automaton \<Rightarrow> ('t, 'a) automaton \<Rightarrow> bool" where
  "soft_isomorphic_automata \<A>1 \<A>2 =
    (\<exists> f . bij_betw f (states \<A>1) (states \<A>2) \<and>
    bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and>
    f (initial_state \<A>1) = initial_state \<A>2 \<and>
    image f (accepting_states \<A>1) = accepting_states \<A>2 \<and>
    image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2)"

text \<open>Properties of Soft-Isomorphy\<close>
proposition soft_implies_alphabet:
  assumes "soft_isomorphic_automata \<A>1 \<A>2"
  shows "alphabet \<A>1 = alphabet \<A>2"
  using assms unfolding soft_isomorphic_automata_def bij_betw_def by auto

theorem soft_implies_isomorphic:
  assumes "soft_isomorphic_automata \<A>1 \<A>2"
  shows "isomorphic_automata \<A>1 \<A>2"
  using assms unfolding isomorphic_automata_def soft_isomorphic_automata_def by metis

theorem soft_iso_reflexiv: "soft_isomorphic_automata \<A> \<A>"
  unfolding soft_isomorphic_automata_def by auto

theorem soft_iso_transitive:
  assumes "soft_isomorphic_automata \<A>1 \<A>2" "soft_isomorphic_automata \<A>2 \<A>3"
  shows "soft_isomorphic_automata \<A>1 \<A>3"
proof -
  obtain f where org: "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms unfolding soft_isomorphic_automata_def by presburger
  obtain f' where prime: "bij_betw f' (states \<A>2) (states \<A>3) \<and> bij_betw id (alphabet \<A>2) (alphabet \<A>3) \<and> f' (initial_state \<A>2) = initial_state \<A>3 \<and> image f' (accepting_states \<A>2) = accepting_states \<A>3 \<and> image (\<lambda>(s1, a, s2) . (f' s1, id a, f' s2)) (transitions \<A>2) = transitions \<A>3" using assms unfolding soft_isomorphic_automata_def by presburger
  let ?f_comp = "f' \<circ> f"
  have bij_f_comp: "bij_betw ?f_comp (states \<A>1) (states \<A>3)" using org prime bij_betw_trans by fast
  have "bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw id (alphabet \<A>2) (alphabet \<A>3)" using org prime by blast
  hence bij_h_comp: "bij_betw id (alphabet \<A>1) (alphabet \<A>3)" using bij_betw_trans by fastforce
  have init: "?f_comp (initial_state \<A>1) = initial_state \<A>3" using org prime by auto
  have acc: "image ?f_comp (accepting_states \<A>1) = accepting_states \<A>3" using org prime image_comp by metis
  {
    fix s1 s2 a assume assm: "(s1, a, s2) \<in> transitions \<A>1"
    have "image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2" using org by argo
    hence trans: "(f s1, id a, f s2) \<in> transitions \<A>2" using assm by force
    have "image (\<lambda>(s1, a, s2) . (f' s1, id a, f' s2)) (transitions \<A>2) = transitions \<A>3" using prime by argo
    hence "(f' (f s1), id (id a), f' (f s2)) \<in> transitions \<A>3" using trans by force
    hence "(?f_comp s1, id a, ?f_comp s2) \<in> transitions \<A>3" by auto
  }
  hence left: "image (\<lambda>(s1, a, s2) . (?f_comp s1, id a, ?f_comp s2)) (transitions \<A>1) \<subseteq> transitions \<A>3" by auto
  {
    fix s1 s2 a assume assm: "(s1, a, s2) \<in> transitions \<A>3"
    have "image (\<lambda>(s1, a, s2) . (f' s1, id a, f' s2)) (transitions \<A>2) = transitions \<A>3" using prime by argo
    hence "\<exists> (s1', a', s2') \<in> transitions \<A>2 . (s1, a, s2) = (f' s1', id a', f' s2')" using assm by fast
    then obtain s1' s2' a' where s': "(s1', a', s2') \<in> transitions \<A>2 \<and> s1 = f' s1' \<and> s2 = f' s2' \<and> a = id a'" by fast
    have "image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2" using org by fast
    hence "\<exists> (s1'', a'', s2'') \<in> transitions \<A>1 . (s1', a', s2') = (f s1'', id a'', f s2'')" using s' by fast
    then obtain s1'' s2'' a'' where s'': "(s1'', a'', s2'') \<in> transitions \<A>1 \<and> s1' = f s1'' \<and> s2' = f s2'' \<and> a' = id a''" by blast
    hence "\<exists> (s1'', a'', s2'') \<in> transitions \<A>1 . (s1, a, s2) = (?f_comp s1'', id a'', ?f_comp s2'')" using s' s'' by auto
  }
  hence "transitions \<A>3 \<subseteq> image (\<lambda>(s1, a, s2) . (?f_comp s1, id a, ?f_comp s2)) (transitions \<A>1)" by force
  hence "image (\<lambda>(s1, a, s2) . (?f_comp s1, id a, ?f_comp s2)) (transitions \<A>1) = transitions \<A>3" using left by blast
  thus ?thesis using bij_f_comp bij_h_comp init acc unfolding soft_isomorphic_automata_def by blast
qed

theorem soft_iso_preserves_auto_well_defined:
  assumes "auto_well_defined \<A>1" "soft_isomorphic_automata \<A>1 \<A>2"
  shows "auto_well_defined \<A>2"
  using assms soft_implies_isomorphic iso_preserves_auto_well_defined by auto

corollary language_well_def_soft_iso_auto:
  assumes "auto_well_defined \<A>1" "soft_isomorphic_automata \<A>1 \<A>2"
  shows "language_well_defined (language_auto \<A>2) (alphabet \<A>2)"
  using soft_iso_preserves_auto_well_defined assms automata_language_are_well_defined by blast

lemma soft_bijection_inverse_trans:
  assumes "auto_well_defined \<A>1" "bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw f (states \<A>1) (states \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "image (\<lambda>(s1, a, s2) . ((inv_into (states \<A>1) f) s1, id a, (inv_into (states \<A>1) f) s2)) (transitions \<A>2) = transitions \<A>1"
proof -
  have trans: "image (\<lambda>(s1, a, s2). ((inv_into (states \<A>1) f) s1, (inv_into (alphabet \<A>1) id) a, (inv_into (states \<A>1) f) s2)) (transitions \<A>2) = transitions \<A>1" using assms bijection_inverse_trans by metis
  have id: "\<forall> a \<in> alphabet \<A>2 . (inv_into (alphabet \<A>1) id) a = id a" using assms bij_betw_id_iff bij_betw_inv_into_left id_apply by metis
  have "auto_well_defined \<A>2" using soft_iso_preserves_auto_well_defined assms unfolding soft_isomorphic_automata_def by auto
  hence "\<forall> (s1, a, s2) \<in> transitions \<A>2 . a \<in> alphabet \<A>2" using well_def_trans_components by fast
  hence "\<forall> trans \<in> transitions \<A>2 . (\<lambda>(s1, a, s2). ((inv_into (states \<A>1) f) s1, (inv_into (alphabet \<A>1) id) a, (inv_into (states \<A>1) f) s2)) trans = (\<lambda>(s1, a, s2). ((inv_into (states \<A>1) f) s1, id a, (inv_into (states \<A>1) f) s2)) trans" using id by fast
  thus ?thesis using trans by force
qed

theorem soft_isomorphy_symmetry:
  assumes "auto_well_defined \<A>1" "soft_isomorphic_automata \<A>1 \<A>2"
  shows "soft_isomorphic_automata \<A>2 \<A>1"
proof -
  obtain f where props: "bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw f (states \<A>1) (states \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms unfolding soft_isomorphic_automata_def by force
  let ?g = "inv_into (states \<A>1) f"
  have bij: "bij_betw id (alphabet \<A>2) (alphabet \<A>1) \<and> bij_betw ?g (states \<A>2) (states \<A>1)" using props bij_betw_inv_into bij_betw_id_iff by metis
  have first: "?g (initial_state \<A>2) = initial_state \<A>1 \<and> image ?g (accepting_states \<A>2) = accepting_states \<A>1" using assms props bijection_inverse_special_states by metis
  have "image (\<lambda>(s1, a, s2) . (?g s1, id a, ?g s2)) (transitions \<A>2) = transitions \<A>1" using assms props soft_bijection_inverse_trans by simp
  thus ?thesis using bij first unfolding soft_isomorphic_automata_def by auto 
qed

theorem soft_iso_preserves_DFA_property:
  assumes "auto_well_defined \<A>1" "DFA_property \<A>1""soft_isomorphic_automata \<A>1 \<A>2"
  shows "DFA_property \<A>2"
  using assms soft_implies_isomorphic iso_preserves_DFA_property by auto

text \<open>Soft-Isomorphic automata accept the same language\<close>
theorem soft_iso_prun_correct:
  assumes "auto_well_defined \<A>1" "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2). (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "(\<forall> prun word s . pseudo_run_well_defined prun \<A>1 s word \<longrightarrow> pseudo_run_well_defined (map f prun) \<A>2 (f s) word) \<and> (\<forall> prun word s . pseudo_run_well_defined prun \<A>2 s word \<longrightarrow> pseudo_run_well_defined (map (inv_into (states \<A>1) f) prun) \<A>1 (inv_into (states \<A>1) f s) word)"
proof -
  {
    fix prun word s assume assm: "pseudo_run_well_defined prun \<A>1 s word"
    hence "pseudo_run_well_defined (map f prun) \<A>2 (f s) (map id word)" using assms iso_prun_correct by metis
  }
  hence impl: "\<forall> prun word s . pseudo_run_well_defined prun \<A>1 s word \<longrightarrow> pseudo_run_well_defined (map f prun) \<A>2 (f s) word" by auto
  let ?g = "inv_into (states \<A>1) f"
  let ?h_inv = "inv_into (alphabet \<A>1) id"
  have bij: "alphabet \<A>2 = alphabet \<A>1" using assms unfolding bij_betw_def by auto
  {
    fix prun word s assume assm: "pseudo_run_well_defined prun \<A>2 s word"
    hence prun: "pseudo_run_well_defined (map ?g prun) \<A>1 (?g s) (map (inv_into (alphabet \<A>1) id) word)" using assms iso_prun_correct by metis
    have "auto_well_defined \<A>2" using soft_iso_preserves_auto_well_defined assms unfolding soft_isomorphic_automata_def by auto
    hence "word_well_defined word (alphabet \<A>2)" using assm well_def_implies_word_well_defined by metis
    hence "set word \<subseteq> alphabet \<A>1" using bij unfolding word_well_defined_def by blast
    hence "pseudo_run_well_defined (map ?g prun) \<A>1 (?g s) (map id word)" using prun assms map_bij list.map_id by metis
  }
  hence "\<forall> prun word s .pseudo_run_well_defined prun \<A>2 s word \<longrightarrow> pseudo_run_well_defined (map ?g prun) \<A>1 (?g s) word" by auto
  thus ?thesis using impl by auto
qed

theorem soft_iso_run_correct:
  assumes "auto_well_defined \<A>1" "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "(\<forall> run word . run_accepting run \<A>1 word \<longrightarrow> run_accepting (map f run) \<A>2 word) \<and> (\<forall> run word . run_accepting run \<A>2 word \<longrightarrow> run_accepting (map (inv_into (states \<A>1) f) run) \<A>1 word)"
proof -
  {
    fix prun word assume assm: "run_accepting prun \<A>1 word"
    hence "run_accepting (map f prun) \<A>2 (map id word)" using assms iso_run_correct by metis
  }  
  hence impl: "\<forall> run word . run_accepting run \<A>1 word \<longrightarrow> run_accepting (map f run) \<A>2 word" by auto
  let ?g = "inv_into (states \<A>1) f"
  let ?h_inv = "inv_into (alphabet \<A>1) id"
  have bij: "alphabet \<A>2 = alphabet \<A>1" using assms unfolding bij_betw_def by auto
  {
    fix prun word assume assm: "run_accepting prun \<A>2 word"
    hence prun: "run_accepting (map ?g prun) \<A>1 (map (inv_into (alphabet \<A>1) id) word)" using assms iso_run_correct by metis
    have "auto_well_defined \<A>2" using soft_iso_preserves_auto_well_defined assms unfolding soft_isomorphic_automata_def by auto
    hence "word_well_defined word (alphabet \<A>2)" using assm well_def_implies_word_well_defined unfolding run_accepting_def run_well_defined_def by metis
    hence "set word \<subseteq> alphabet \<A>1" using bij unfolding word_well_defined_def by blast
    hence "run_accepting (map ?g prun) \<A>1 (map id word)" using prun assms map_bij list.map_id by metis  
  }
  hence "\<forall> prun word . run_accepting prun \<A>2 word \<longrightarrow> run_accepting (map ?g prun) \<A>1 word" by auto
  thus ?thesis using impl by auto
qed

theorem closed_under_soft_iso:
  assumes "auto_well_defined \<A>1" "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "word \<in> language_auto \<A>1 \<longleftrightarrow> word \<in> language_auto \<A>2"
proof -
  have "(\<forall> run word . run_accepting run \<A>1 word \<longrightarrow> run_accepting (map f run) \<A>2 word) \<and> (\<forall> run word . run_accepting run \<A>2 word \<longrightarrow> run_accepting (map (inv_into (states \<A>1) f) run) \<A>1 word)" using assms soft_iso_run_correct by metis
  thus ?thesis unfolding language_auto_def by blast
qed

text \<open>Main result for soft_isomorphy\<close>
theorem language_soft_iso_correctness:
  assumes "auto_well_defined \<A>1" "soft_isomorphic_automata \<A>1 \<A>2"
  shows "language_auto \<A>2 = language_auto \<A>1"
proof -
  obtain f where org: "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms unfolding soft_isomorphic_automata_def by presburger 
  thus ?thesis using assms closed_under_soft_iso by auto
qed



text \<open>General type-encoder for same alphabet:\<close>
definition type_encode_automaton :: "('t, 'b) automaton \<Rightarrow> ('t \<Rightarrow> 's) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('s, 'a) automaton"
  where "type_encode_automaton \<A> f_bij h_bij = Automaton
    (image f_bij (states \<A>))
    (image h_bij (alphabet \<A>))
    (image (\<lambda>(s1, a, s2) . (f_bij s1, h_bij a, f_bij s2)) (transitions \<A>))
    (f_bij (initial_state \<A>))
    (image f_bij (accepting_states \<A>))"

proposition type_encode_bij_iso:
  assumes "auto_well_defined \<A>" "bij_betw f_bij (states \<A>) (image f_bij (states \<A>))" "bij_betw h_bij (alphabet \<A>) (image h_bij (alphabet \<A>))"
  shows "isomorphic_automata \<A> (type_encode_automaton \<A> f_bij h_bij)"
proof -
  let ?f = "f_bij"
  let ?\<A> = "type_encode_automaton \<A> f_bij h_bij"
  have h: "bij_betw h_bij (alphabet \<A>) (alphabet ?\<A>)" using assms unfolding type_encode_automaton_def by auto
  have bij: "bij_betw ?f (states \<A>) (states ?\<A>)" using assms unfolding type_encode_automaton_def by auto
  have init: "?f (initial_state \<A>) = initial_state ?\<A>" unfolding type_encode_automaton_def by auto
  have acc: "image ?f (accepting_states \<A>) = accepting_states ?\<A>" unfolding type_encode_automaton_def by auto
  have trans: "image (\<lambda>(S1, a, S2) . (?f S1, h_bij a, ?f S2)) (transitions \<A>) = transitions ?\<A>" unfolding type_encode_automaton_def by auto
  thus ?thesis using bij init acc trans h unfolding isomorphic_automata_def by blast
qed

proposition type_encode_bij_soft_iso:
  assumes "auto_well_defined \<A>" "bij_betw f_bij (states \<A>) (image f_bij (states \<A>))"
  shows "soft_isomorphic_automata \<A> (type_encode_automaton \<A> f_bij id)"
proof -
  let ?f = "f_bij"
  let ?\<A> = "type_encode_automaton \<A> f_bij id"
  have h: "bij_betw id (alphabet \<A>) (alphabet ?\<A>)" using assms unfolding type_encode_automaton_def by auto
  have bij: "bij_betw ?f (states \<A>) (states ?\<A>)" using assms unfolding type_encode_automaton_def by auto
  have init: "?f (initial_state \<A>) = initial_state ?\<A>" unfolding type_encode_automaton_def by auto
  have acc: "image ?f (accepting_states \<A>) = accepting_states ?\<A>" unfolding type_encode_automaton_def by auto
  have trans: "image (\<lambda>(S1, a, S2) . (?f S1, id  a, ?f S2)) (transitions \<A>) = transitions ?\<A>" unfolding type_encode_automaton_def by auto
  thus ?thesis using bij init acc trans h unfolding soft_isomorphic_automata_def by blast
qed

corollary type_encode_preserves_well_def:
  assumes "auto_well_defined \<A>" "bij_betw f_bij (states \<A>) (image f_bij (states \<A>))" "bij_betw h_bij (alphabet \<A>) (image h_bij (alphabet \<A>))"
  shows "auto_well_defined (type_encode_automaton \<A> f_bij h_bij)"
  using assms type_encode_bij_iso iso_preserves_auto_well_defined by blast

corollary language_well_def_type_encode_auto:
  assumes "auto_well_defined \<A>" "bij_betw f_bij (states \<A>) (image f_bij (states \<A>))" "bij_betw h_bij (alphabet \<A>) (image h_bij (alphabet \<A>))"
  shows "language_well_defined (language_auto (type_encode_automaton \<A> f_bij h_bij)) (alphabet (type_encode_automaton \<A> f_bij h_bij))"
  using type_encode_preserves_well_def assms automata_language_are_well_defined by blast

corollary type_encode_preserves_dfa:
  assumes "auto_well_defined \<A>" "DFA_property \<A>" "bij_betw f_bij (states \<A>) (image f_bij (states \<A>))" "bij_betw h_bij (alphabet \<A>) (image h_bij (alphabet \<A>))"
  shows "DFA_property (type_encode_automaton \<A> f_bij h_bij)"
  using assms type_encode_bij_iso iso_preserves_DFA_property by blast

proposition type_encode_preserves_language:
  assumes "auto_well_defined \<A>" "bij_betw f_bij (states \<A>) (image f_bij (states \<A>))" "bij_betw h_bij (alphabet \<A>) (image h_bij (alphabet \<A>))"
  shows "language_auto (type_encode_automaton \<A> f_bij h_bij) = image (map h_bij) (language_auto \<A>)"
proof -
  let ?f = "f_bij"
  let ?\<A> = "type_encode_automaton \<A> f_bij h_bij"
  have well_def: "auto_well_defined (type_encode_automaton \<A> f_bij h_bij)" using assms type_encode_preserves_well_def by blast
  have h: "bij_betw h_bij (alphabet \<A>) (alphabet ?\<A>)" using assms unfolding type_encode_automaton_def by auto
  have bij: "bij_betw ?f (states \<A>) (states ?\<A>)" using assms unfolding type_encode_automaton_def by auto
  have init: "?f (initial_state \<A>) = initial_state ?\<A>" unfolding type_encode_automaton_def by auto
  have acc: "image ?f (accepting_states \<A>) = accepting_states ?\<A>" unfolding type_encode_automaton_def by auto
  have trans: "image (\<lambda>(S1, a, S2) . (?f S1, h_bij a, ?f S2)) (transitions \<A>) = transitions ?\<A>" unfolding type_encode_automaton_def by auto
  thus ?thesis using assms bij init acc trans h well_def language_iso_correctness by metis
qed

corollary type_encode_preserves_same_language:
  assumes "auto_well_defined \<A>" "bij_betw f_bij (states \<A>) (image f_bij (states \<A>))"
  shows "language_auto (type_encode_automaton \<A> f_bij id) = language_auto \<A>" 
  using assms type_encode_bij_soft_iso language_soft_iso_correctness by metis

corollary type_encode_preserves_alphabet: "alphabet (type_encode_automaton \<A> f_bij id) = alphabet \<A>" 
  unfolding type_encode_automaton_def by auto





text \<open>Some application for type nat:\<close>
proposition id_bij_betw: "bij_betw id A (image id A)"
  by fastforce 

proposition prod_encode_bij_betw: "bij_betw prod_encode A (image prod_encode A)"
  using bij_betw_subset bij_prod_encode by blast

corollary existence_prod_encode_auto:
  assumes "auto_well_defined (\<A> :: (nat \<times> nat, 'a) automaton)"
  shows "\<exists> nat_\<A> :: (nat, 'a) automaton . auto_well_defined nat_\<A> \<and> alphabet nat_\<A> = alphabet \<A> \<and> language_auto nat_\<A> = language_auto \<A>"
  using assms prod_encode_bij_betw id_bij_betw type_encode_preserves_well_def type_encode_preserves_same_language type_encode_preserves_alphabet by fast

proposition set_encode_bij_betw:
  assumes "\<forall> a \<in> A . finite a"
  shows "bij_betw set_encode A (image set_encode A)"
  using assms set_encode_inverse unfolding bij_betw_def inj_on_def by metis

corollary existence_set_encode_auto:
  assumes "auto_well_defined (\<A> :: (nat states, 'a) automaton)" "\<forall> S \<in> states \<A> . finite S"
  shows "\<exists> nat_\<A> :: (nat, 'a) automaton . auto_well_defined nat_\<A> \<and> alphabet nat_\<A> = alphabet \<A> \<and> language_auto nat_\<A> = language_auto \<A>"
  using assms set_encode_bij_betw id_bij_betw type_encode_preserves_well_def type_encode_preserves_same_language type_encode_preserves_alphabet by fast

proposition sum_unit_encode_bij_betw: "bij_betw sum_unit_encode A (image sum_unit_encode A)"
  using bij_betw_subset bij_sum_unit_encode by blast

corollary existence_sum_unit_encode_auto:
  assumes "auto_well_defined (\<A> :: (nat + unit, 'a) automaton)"
  shows "\<exists> nat_\<A> :: (nat, 'a) automaton . auto_well_defined nat_\<A> \<and> alphabet nat_\<A> = alphabet \<A> \<and> language_auto nat_\<A> = language_auto \<A>"
  using assms sum_unit_encode_bij_betw id_bij_betw type_encode_preserves_well_def type_encode_preserves_same_language type_encode_preserves_alphabet by fast

proposition cross_sum_unit_encode_bij_betw: "bij_betw cross_sum_unit_encode A (image cross_sum_unit_encode A)"
  using bij_betw_subset bij_cross_sum_unit_encode by blast

corollary existence_cross_sum_unit_encode_auto:
  assumes "auto_well_defined (\<A> :: (nat \<times> nat + unit, 'a) automaton)"
  shows "\<exists> nat_\<A> :: (nat, 'a) automaton . auto_well_defined nat_\<A> \<and> alphabet nat_\<A> = alphabet \<A> \<and> language_auto nat_\<A> = language_auto \<A>"
  using assms cross_sum_unit_encode_bij_betw id_bij_betw type_encode_preserves_well_def type_encode_preserves_same_language type_encode_preserves_alphabet by fast

theorem set_encode_main_DFA:
  assumes "auto_well_defined (\<A> :: (nat states, 'a) automaton)" "DFA_property \<A>" "\<forall> S \<in> states \<A> . finite S"
  shows "\<exists> nat_\<A> :: (nat, 'a) automaton . auto_well_defined nat_\<A> \<and> DFA_property nat_\<A> \<and> alphabet nat_\<A> = alphabet \<A> \<and> language_auto nat_\<A> = language_auto \<A>"
proof - 
  let ?\<A> = "type_encode_automaton \<A> set_encode id"
  have well_def: "auto_well_defined ?\<A>" using assms set_encode_bij_betw id_bij_betw type_encode_preserves_well_def by fast
  have dfa: "DFA_property ?\<A>" using assms set_encode_bij_betw id_bij_betw type_encode_preserves_dfa by fast
  have alpha: "alphabet \<A> = alphabet ?\<A>" unfolding type_encode_automaton_def by auto
  have "language_auto ?\<A> = language_auto \<A>" using  assms set_encode_bij_betw id_bij_betw type_encode_preserves_same_language by fast
  thus ?thesis using well_def dfa alpha by blast
qed

lemma powerset_nat_automaton_states_are_finite:
  assumes "auto_well_defined (\<A> :: (nat, 'a) automaton)"
  shows "\<forall> S \<in> states (powerset_automaton \<A>) . finite S"
  using assms unfolding powerset_automaton_def auto_well_defined_def finite_nat_set_iff_bounded by auto

lemma NFA_to_DFA_nat_set:
  assumes "auto_well_defined (NFA_\<A> :: (nat, 'a) automaton)"
  shows "\<exists> DFA_\<A> :: (nat states, 'a) automaton . auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = alphabet NFA_\<A> \<and> language_auto DFA_\<A> = language_auto NFA_\<A> \<and> (\<forall> S \<in> states DFA_\<A> . finite S)"
  using assms powerset_automaton_correctness powerset_automaton_alphabet well_def_powerset_automaton powerset_nat_automaton_states_are_finite by metis

proposition NFA_to_DFA_nat:
  assumes "auto_well_defined (NFA_\<A> :: (nat, 'a) automaton)"
  shows "\<exists> DFA_\<A> :: (nat, 'a) automaton . auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = alphabet NFA_\<A> \<and> language_auto DFA_\<A> = language_auto NFA_\<A>"
  using NFA_to_DFA_nat_set set_encode_main_DFA assms by metis

text \<open>Main result: Combinations using type nat\<close>
theorem
  assumes "auto_well_defined (\<A>1 :: (nat, 'a) automaton)" "auto_well_defined (\<A>2 :: (nat, 'a) automaton)" "alphabet \<A>1 = alphabet \<A>2"
  shows "(\<exists> comp_\<A> :: (nat, 'a) automaton . auto_well_defined comp_\<A> \<and> alphabet comp_\<A> = alphabet \<A>1 \<and> language_auto comp_\<A> = comp_language (alphabet \<A>1) (language_auto \<A>1)) \<and> (\<exists> inter_\<A> :: (nat, 'a) automaton . auto_well_defined inter_\<A> \<and> alphabet inter_\<A> = alphabet \<A>1 \<and> language_auto inter_\<A> = language_auto \<A>1 \<inter> language_auto \<A>2) \<and> (\<exists> union_\<A> :: (nat, 'a) automaton . auto_well_defined union_\<A> \<and> alphabet union_\<A> = alphabet \<A>1 \<and> language_auto union_\<A> = language_auto \<A>1 \<union> language_auto \<A>2)"
proof -
  obtain \<A>3 :: "(nat, 'a) automaton" where A3: "auto_well_defined \<A>3 \<and> alphabet \<A>3 = alphabet \<A>1 \<and> DFA_property \<A>3 \<and> language_auto \<A>3 = language_auto \<A>1" using assms NFA_to_DFA_nat by fastforce
  hence main1: "\<exists> \<A>4 :: (nat, 'a) automaton . auto_well_defined \<A>4 \<and> alphabet \<A>4 = alphabet \<A>1 \<and> language_auto \<A>4 = comp_language (alphabet \<A>1) (language_auto \<A>1)" using comp_main by metis
  have "\<exists> \<A>5 :: ((nat \<times> nat), 'a) automaton . auto_well_defined \<A>5 \<and> alphabet \<A>5 = alphabet \<A>1 \<union> alphabet \<A>2 \<and> language_auto \<A>5 = language_auto \<A>1 \<inter> language_auto \<A>2" using intersection_main assms by blast
  hence "\<exists> \<A>5 :: ((nat \<times> nat), 'a) automaton . auto_well_defined \<A>5 \<and> alphabet \<A>5 = alphabet \<A>1 \<and> language_auto \<A>5 = language_auto \<A>1 \<inter> language_auto \<A>2" using assms by auto
  hence main2: "\<exists> \<A>6 :: (nat, 'a) automaton . auto_well_defined \<A>6 \<and> alphabet \<A>6 = alphabet \<A>1 \<and> language_auto \<A>6 = language_auto \<A>1 \<inter> language_auto \<A>2" using existence_prod_encode_auto by fast
  obtain \<A>7 :: "(nat, 'a) automaton" where "auto_well_defined \<A>7 \<and> alphabet \<A>7 = alphabet \<A>2 \<and> DFA_property \<A>7 \<and> language_auto \<A>7 = language_auto \<A>2" using NFA_to_DFA_nat assms by metis
  hence "\<exists> \<A>8 :: ((nat \<times> nat), 'a) automaton . auto_well_defined \<A>8 \<and> alphabet \<A>8 = alphabet \<A>1 \<and> language_auto \<A>8 = language_auto \<A>1 \<union> language_auto \<A>2" using A3 union_main assms by metis
  hence "\<exists> \<A>9 :: (nat, 'a) automaton . auto_well_defined \<A>9 \<and> alphabet \<A>9 = alphabet \<A>1 \<and> language_auto \<A>9 = language_auto \<A>1 \<union> language_auto \<A>2" using existence_prod_encode_auto by fast
  thus ?thesis using main1 main2 by auto
qed




text \<open>Re-naming states, such that (states \<A>1) \<inter> (states \<A>2) = {}\<close>
definition cross_renaming_iso :: "nat \<Rightarrow> 's state \<Rightarrow> ('s \<times> nat) state" where "cross_renaming_iso n s = (s, n)"

proposition bij_cross_renaming_iso: "bij_betw (cross_renaming_iso n) (states \<A>) (image (cross_renaming_iso n) (states \<A>))"
  unfolding bij_betw_def cross_renaming_iso_def inj_on_def by auto

proposition cross_renaming_iso_automaton_auto_well_defined:
  assumes "auto_well_defined \<A>"
  shows "auto_well_defined (type_encode_automaton \<A> (cross_renaming_iso n) id)"
  using assms id_bij_betw type_encode_preserves_well_def bij_cross_renaming_iso by blast

lemma DFA_property_cross_renaming_iso_automaton:
  assumes "auto_well_defined \<A>" "DFA_property \<A>"
  shows "DFA_property (type_encode_automaton \<A> (cross_renaming_iso n) id)"
  using assms id_bij_betw type_encode_preserves_dfa bij_cross_renaming_iso by blast

corollary cross_renaming_iso_automaton_same_language:
  assumes "auto_well_defined \<A>"
  shows "language_auto \<A> = language_auto (type_encode_automaton \<A> (cross_renaming_iso n) id)"
  using assms id_bij_betw type_encode_preserves_same_language bij_cross_renaming_iso by fast

proposition cross_renaming_intersection_empty: "states (type_encode_automaton \<A>1 (cross_renaming_iso 1) id) \<inter> states (type_encode_automaton \<A>2 (cross_renaming_iso 2) id) = {}"
  unfolding type_encode_automaton_def cross_renaming_iso_def by auto



text \<open>General type conversion is possible, not only on nat:\<close>
lemma existence_of_equal_set:
  assumes "infinite (UNIV :: 's set)"
  shows "finite (A :: 't set) \<Longrightarrow> \<exists> (B :: 's set) . finite B \<and> card B = card A"
proof(induction "card A" arbitrary: A)
  case 0
  have "finite ({} :: 's set) \<and> card ({} :: 's set) = 0" by auto
  thus ?case using 0 by metis
next
  case (Suc n)
  hence "A \<noteq> {}" by fastforce
  then obtain x where "x \<in> A" by auto
  hence "finite (A - {x}) \<and> card (A - {x}) = n" using Suc by auto
  then obtain B :: "('s set)" where B: "finite B \<and> card B = n" using Suc by blast
  hence "infinite (UNIV - B)" using assms by force
  then obtain x where x: "x \<notin> B" using B ex_new_if_finite by blast
  have fin: "finite (insert x B)" using B by blast
  hence "card (insert x B) = Suc n" using B x by force 
  thus ?case using fin Suc by metis
qed

lemma existence_iso_automaton:
  assumes "auto_well_defined (\<A>1 :: ('t, 'b) automaton)" "infinite (UNIV :: 's set)" "infinite (UNIV :: 'a set)"
  shows "\<exists> \<A>2 :: ('s, 'a) automaton. isomorphic_automata \<A>1 \<A>2"
proof -
  have finite: "finite (states \<A>1)" using assms unfolding auto_well_defined_def by auto
  then obtain B :: "('s set)" where "finite B \<and> card B = card (states \<A>1)" using assms existence_of_equal_set by auto
  then obtain f where f: "bij_betw f (states \<A>1) B" using finite finite_same_card_bij by metis
  hence im: "image f (states \<A>1) = B" using bij_betw_imp_surj_on by metis  
  have fin: "finite (alphabet \<A>1)" using assms unfolding auto_well_defined_def by auto
  then obtain  C :: "('a set)" where "finite C \<and> card C = card (alphabet \<A>1)" using assms existence_of_equal_set by auto
  then obtain h where h: "bij_betw h (alphabet \<A>1) C" using fin finite_same_card_bij by metis
  hence "image h (alphabet \<A>1) = C" using bij_betw_imp_surj_on by metis
  hence "isomorphic_automata \<A>1 (type_encode_automaton \<A>1 f h)" using f h im type_encode_bij_iso assms by metis
  thus ?thesis by fast
qed

lemma existence_soft_iso_automaton:
  assumes "auto_well_defined (\<A>1 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> \<A>2 :: ('s, 'a) automaton. soft_isomorphic_automata \<A>1 \<A>2"
proof -
  have finite: "finite (states \<A>1)" using assms unfolding auto_well_defined_def by auto
  then obtain  B :: "('s set)" where "finite B \<and> card B = card (states \<A>1)" using assms existence_of_equal_set by auto
  then obtain f where f: "bij_betw f (states \<A>1) B" using finite finite_same_card_bij by metis
  hence "image f (states \<A>1) = B" using bij_betw_imp_surj_on by metis  
  hence "soft_isomorphic_automata \<A>1 (type_encode_automaton \<A>1 f id)" using f type_encode_bij_soft_iso assms by metis
  thus ?thesis by fast
qed

corollary existence_soft_iso_auto_lang:
  assumes "auto_well_defined (\<A>1 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> \<A>2 :: ('s, 'a) automaton. auto_well_defined \<A>2 \<and> alphabet \<A>2 = alphabet \<A>1 \<and> language_auto \<A>2 = language_auto \<A>1"
  using assms existence_soft_iso_automaton language_soft_iso_correctness soft_iso_preserves_auto_well_defined soft_implies_alphabet by fast

theorem existence_of_DFA_same_type:
  assumes "auto_well_defined (NFA_\<A> :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> DFA_\<A> :: ('s, 'a) automaton. auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = alphabet NFA_\<A> \<and> language_auto DFA_\<A> = language_auto NFA_\<A>"
  using assms NFA_to_DFA existence_soft_iso_automaton language_soft_iso_correctness soft_iso_preserves_auto_well_defined soft_iso_preserves_DFA_property soft_implies_alphabet by metis

theorem expressive_power_dfa_nfa_main:
  assumes "infinite (UNIV :: 's set)"
  shows "{L . \<exists> (NFA_\<A> :: ('s, 'a) automaton) . auto_well_defined NFA_\<A> \<and> alphabet NFA_\<A> = \<Sigma> \<and> L = language_auto NFA_\<A>} = {L . \<exists> (DFA_\<A> :: ('s, 'a) automaton) . auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = \<Sigma> \<and> L = language_auto DFA_\<A>}"
  using assms existence_of_DFA_same_type by fast

theorem existence_of_sigma_star_same_type:
  assumes "finite \<Sigma>" "infinite (UNIV :: 's set)"
  shows "\<exists> sigma_\<A> :: ('s , 'a) automaton . auto_well_defined sigma_\<A> \<and> alphabet sigma_\<A> = \<Sigma> \<and> language_auto sigma_\<A> = sigma_star \<Sigma>"
  using assms sigma_star_main existence_soft_iso_auto_lang by fast

theorem existence_of_comp_same_type:
  assumes "auto_well_defined (\<A> :: ('s, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> comp_\<A> :: ('s , 'a) automaton . auto_well_defined comp_\<A> \<and> alphabet comp_\<A> = alphabet \<A> \<and> language_auto comp_\<A> = comp_language (alphabet \<A>) (language_auto \<A>)"
  using assms existence_of_DFA_same_type comp_main by metis

theorem existence_of_inter_same_type:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> inter_\<A> :: ('s, 'a) automaton . auto_well_defined inter_\<A> \<and> alphabet inter_\<A> = alphabet \<A>1 \<union> alphabet \<A>2 \<and> language_auto inter_\<A> = language_auto \<A>1 \<inter> language_auto \<A>2"
  using assms intersection_main existence_soft_iso_auto_lang by metis

theorem existence_of_union_same_type:
  assumes "auto_well_defined (\<A>1 :: ('s, 'a) automaton)" "auto_well_defined (\<A>2 :: ('t, 'a) automaton)" "DFA_property \<A>1" "DFA_property \<A>2" "alphabet \<A>1 = alphabet \<A>2" "infinite (UNIV :: 's set)"
  shows "\<exists> union_\<A> :: ('s, 'a) automaton . auto_well_defined union_\<A> \<and> alphabet union_\<A> = alphabet \<A>1 \<and> language_auto union_\<A> = language_auto \<A>1 \<union> language_auto \<A>2"
  using assms union_main existence_soft_iso_auto_lang by metis

end