theory omega_automata_isomorphy

imports Main omega_automata

begin

text \<open>Author: Benno Thalmann, last update: 11.2.2026, Addition to masterarbeit_benno_thalmann\<close>

corollary omega_language_well_def_iso_auto:
  assumes "auto_well_defined \<A>1" "isomorphic_automata \<A>1 \<A>2"
  shows "omega_language_well_defined (omega_language_auto \<A>2) (alphabet \<A>2)"
  using iso_preserves_auto_well_defined assms automata_omega_language_are_well_defined by blast

text \<open>Isomorphic automata accept the same omega_language with respect to the bijection\<close>
theorem omega_iso_prun_correct:
  assumes "auto_well_defined \<A>1" "bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw f (states \<A>1) (states \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "(\<forall> omega_prun omega_word s . omega_pseudo_run_well_defined omega_prun \<A>1 s omega_word \<longrightarrow> omega_pseudo_run_well_defined (f \<circ> omega_prun) \<A>2 (f s) (h \<circ> omega_word)) \<and> (\<forall> omega_prun omega_word s . omega_pseudo_run_well_defined omega_prun \<A>2 s omega_word \<longrightarrow> omega_pseudo_run_well_defined ((inv_into (states \<A>1) f) \<circ> omega_prun) \<A>1 (inv_into (states \<A>1) f s) ((inv_into (alphabet \<A>1) h) \<circ> omega_word))"
proof -
  {
    fix omega_prun omega_word s assume assm: "omega_pseudo_run_well_defined omega_prun \<A>1 s omega_word"
    have start: "(f \<circ> omega_prun) 0 = f (omega_prun 0)" by auto
    have "omega_prun 0 = s \<and> s \<in> states \<A>1" using assm unfolding omega_pseudo_run_well_defined_def by auto
    hence init: "(f \<circ> omega_prun) 0 = f s \<and> (f s) \<in> states \<A>2" using assms start bij_betw_apply by metis
    {
      fix i
      have trans: "(omega_prun i, omega_word i, omega_prun (i + 1)) \<in> transitions \<A>1" using assm unfolding omega_pseudo_run_well_defined_def by blast
      have "image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms by argo
      hence "(f (omega_prun i), h (omega_word i), f (omega_prun (i + 1))) \<in> transitions \<A>2" using trans by force
    }
    hence "\<forall> i . ((f \<circ> omega_prun) i, (h \<circ> omega_word) i, (f \<circ> omega_prun) (i + 1)) \<in> transitions \<A>2" by auto
    hence "omega_pseudo_run_well_defined (f \<circ> omega_prun) \<A>2 (f s) (h \<circ> omega_word)" using assms init unfolding omega_pseudo_run_well_defined_def by blast
  }
  hence impl: "\<forall> omega_prun omega_word s . omega_pseudo_run_well_defined omega_prun \<A>1 s omega_word \<longrightarrow> omega_pseudo_run_well_defined (f \<circ> omega_prun) \<A>2 (f s) (h \<circ> omega_word)" by blast
  let ?g = "inv_into (states \<A>1) f"
  let ?h_inv = "inv_into (alphabet \<A>1) h"
  have bij: "bij_betw ?h_inv (alphabet \<A>2) (alphabet \<A>1) \<and> bij_betw ?g (states \<A>2) (states \<A>1)" using assms bij_betw_inv_into by metis
  have inv: "image (\<lambda>(s1, a, s2) . (?g s1, ?h_inv a, ?g s2)) (transitions \<A>2) = transitions \<A>1" using assms bijection_inverse_trans by simp
  {
    fix omega_prun omega_word s assume assm: "omega_pseudo_run_well_defined omega_prun \<A>2 s omega_word"
    have start: "(?g \<circ> omega_prun) 0 = ?g (omega_prun 0)" by auto
    have "omega_prun 0 = s \<and> s \<in> states \<A>2" using assm unfolding omega_pseudo_run_well_defined_def by auto
    hence init: "(?g \<circ> omega_prun) 0 = ?g s \<and> (?g s) \<in> states \<A>1" using start bij bij_betw_apply by fast
    {
      fix i
      have trans: "(omega_prun i, omega_word i, omega_prun (i + 1)) \<in> transitions \<A>2" using assm unfolding omega_pseudo_run_well_defined_def by blast
      have "image (\<lambda>(s1, a, s2) . (?g s1, ?h_inv a, ?g s2)) (transitions \<A>2) = transitions \<A>1" using inv by blast
      hence "((?g \<circ> omega_prun) i, (?h_inv \<circ> omega_word) i, (?g \<circ> omega_prun) (i + 1)) \<in> transitions \<A>1" using trans by force
    }
    hence step: "\<forall> i . ((?g \<circ> omega_prun) i, (?h_inv \<circ> omega_word) i, (?g \<circ> omega_prun) (i + 1)) \<in> transitions \<A>1" by auto
    hence "omega_pseudo_run_well_defined (?g \<circ> omega_prun) \<A>1 (?g s) (?h_inv \<circ> omega_word)" using assms init step unfolding omega_pseudo_run_well_defined_def by blast
  }
  hence "\<forall> omega_prun omega_word s . omega_pseudo_run_well_defined omega_prun \<A>2 s omega_word \<longrightarrow> omega_pseudo_run_well_defined (?g \<circ> omega_prun) \<A>1 (?g s) (?h_inv \<circ> omega_word)" by blast
  thus ?thesis using impl by blast
qed

proposition omega_iso_run_correct:
  assumes "auto_well_defined \<A>1" "bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw f (states \<A>1) (states \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "(\<forall> omega_run omega_word . omega_run_accepting omega_run \<A>1 omega_word \<longrightarrow> omega_run_accepting (f \<circ> omega_run) \<A>2 (h \<circ> omega_word)) \<and> (\<forall> omega_run omega_word . omega_run_accepting omega_run \<A>2 omega_word \<longrightarrow> omega_run_accepting ((inv_into (states \<A>1) f) \<circ> omega_run) \<A>1 ((inv_into (alphabet \<A>1) h) \<circ> omega_word))"
proof - 
  have well_def: "auto_well_defined \<A>2" using iso_preserves_auto_well_defined assms unfolding isomorphic_automata_def by auto
  {
    fix omega_run omega_word assume assm: "omega_run_accepting omega_run \<A>1 omega_word"
    hence acc: "omega_pseudo_run_well_defined omega_run \<A>1 (initial_state \<A>1) omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>1)" unfolding omega_run_accepting_def omega_run_well_defined_def by blast
    hence omega_prun: "omega_pseudo_run_well_defined (f \<circ> omega_run) \<A>2 (f (initial_state \<A>1)) (h \<circ> omega_word)" using assms omega_iso_prun_correct by metis
    have start: "(f \<circ> omega_run) 0 = f (omega_run 0)" by auto
    have "omega_run 0 = initial_state \<A>1" using assm unfolding omega_run_well_defined_def omega_run_accepting_def omega_pseudo_run_well_defined_def by auto
    hence "(f \<circ> omega_run) 0 = initial_state \<A>2" using assms start by argo
    hence init: "(f \<circ> omega_run) 0 = initial_state \<A>2 \<and> initial_state \<A>2 \<in> states \<A>2" using well_def unfolding auto_well_defined_def by blast
    {
      fix n 
      obtain N where "N > n \<and> omega_run N \<in> accepting_states \<A>1" using acc by blast
      hence "N > n \<and> f (omega_run N) \<in> accepting_states \<A>2" using assms by blast
      hence "\<exists> N > n . f (omega_run N) \<in> accepting_states \<A>2" by blast
    }
    hence "\<forall> n . \<exists> N > n . f (omega_run N) \<in> accepting_states \<A>2" by auto
    hence "omega_run_accepting (f \<circ> omega_run) \<A>2 (h \<circ> omega_word)" using omega_prun init unfolding omega_run_well_defined_def omega_run_accepting_def omega_pseudo_run_well_defined_def by auto
  }
  hence impl: "\<forall> omega_run omega_word . omega_run_accepting omega_run \<A>1 omega_word \<longrightarrow> omega_run_accepting (f \<circ> omega_run) \<A>2 (h \<circ> omega_word)" using assms by blast
  let ?g = "inv_into (states \<A>1) f"
  let ?h_inv = "inv_into (alphabet \<A>1) h"
  have inv: "?g (initial_state \<A>2) = initial_state \<A>1 \<and> image ?g (accepting_states \<A>2) = accepting_states \<A>1" using assms bijection_inverse_special_states by metis
  {
    fix omega_run omega_word assume assm: "omega_run_accepting omega_run \<A>2 omega_word"
    hence acc: "omega_pseudo_run_well_defined omega_run \<A>2 (initial_state \<A>2) omega_word \<and> (\<forall> n . \<exists> N > n . omega_run N \<in> accepting_states \<A>2)" unfolding omega_run_accepting_def omega_run_well_defined_def by blast
    hence omega_prun: "omega_pseudo_run_well_defined (?g \<circ> omega_run) \<A>1 (?g (initial_state \<A>2)) (?h_inv \<circ> omega_word)" using assms omega_iso_prun_correct unfolding run_well_defined_def by metis
    hence start: "(?g \<circ> omega_run) 0 = ?g (omega_run 0)" by auto
    have "omega_run 0 = initial_state \<A>2" using assm unfolding omega_run_well_defined_def omega_run_accepting_def omega_pseudo_run_well_defined_def by auto
    hence "(?g \<circ> omega_run) 0 = initial_state \<A>1" using inv start by argo
    hence init: "(?g \<circ> omega_run) 0 = initial_state \<A>1 \<and> initial_state \<A>1 \<in> states \<A>1" using assms unfolding auto_well_defined_def by blast
    {
      fix n 
      obtain N where "N > n \<and> omega_run N \<in> accepting_states \<A>2" using acc by blast
      hence "N > n \<and> ?g (omega_run N) \<in> accepting_states \<A>1" using inv by blast
      hence "\<exists> N > n . ?g (omega_run N) \<in> accepting_states \<A>1" by blast
    }
    hence "\<forall> n . \<exists> N > n . ?g (omega_run N) \<in> accepting_states \<A>1" by auto
    hence "omega_run_accepting (?g \<circ> omega_run) \<A>1 (?h_inv \<circ> omega_word)" using omega_prun init unfolding omega_run_well_defined_def omega_run_accepting_def omega_pseudo_run_well_defined_def by auto
  }
  thus ?thesis using impl by blast
qed


text \<open>Main results for isomorphy\<close>
definition omega_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a omega_word \<Rightarrow> 'b omega_word" where "omega_map h omega_word = (h \<circ> omega_word)"

lemma omega_word_well_def_image:
  assumes "omega_word_well_defined omega_word \<Sigma>"
  shows "omega_word_well_defined (omega_map h omega_word) (image h \<Sigma>)"
  using assms unfolding omega_word_well_defined_def omega_map_def by force

proposition image_omega_language_is_well_defined:
  assumes "auto_well_defined \<A>"
  shows "omega_language_well_defined (image (omega_map h) (omega_language_auto \<A>)) (image h (alphabet \<A>))"
  using assms automata_omega_language_are_well_defined omega_word_well_def_image unfolding omega_map_def omega_language_well_defined_def by fast

lemma composition_bij:
  assumes "bij_betw h A B"
  shows "\<forall> n . omega_word n \<in> A \<Longrightarrow> (inv_into A h) \<circ> (h \<circ> omega_word) = omega_word"
  using assms bij_betw_inv_into_left by fastforce

lemma inv_inv_composition:
  assumes "bij_betw h A B" "\<forall> n . omega_word n \<in> A"
  shows "(inv_into B (inv_into A h)) \<circ> omega_word = h \<circ> omega_word"
  using assms inv_into_inv_into_eq by fastforce

theorem omega_language_iso_correctness:
  assumes "auto_well_defined \<A>1" "bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> bij_betw f (states \<A>1) (states \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "omega_language_auto \<A>2 = image (omega_map h) (omega_language_auto \<A>1)"
proof -
  have well_def: "auto_well_defined \<A>2" using iso_preserves_auto_well_defined assms unfolding isomorphic_automata_def by auto
  have impl: "(\<forall> omega_run omega_word . omega_run_accepting omega_run \<A>1 omega_word \<longrightarrow> omega_run_accepting (f \<circ> omega_run) \<A>2 (h \<circ> omega_word)) \<and> (\<forall> omega_run omega_word . omega_run_accepting omega_run \<A>2 omega_word \<longrightarrow> omega_run_accepting ((inv_into (states \<A>1) f) \<circ> omega_run) \<A>1 ((inv_into (alphabet \<A>1) h) \<circ> omega_word))" using assms omega_iso_run_correct by metis  
  {
    fix omega_word assume assm: "omega_word \<in> image (omega_map h) (omega_language_auto \<A>1)"
    then obtain omega_word' where word': "omega_word' \<in> omega_language_auto \<A>1 \<and> omega_word = (h \<circ> omega_word')" unfolding omega_map_def by force
    hence "(h \<circ> omega_word') \<in> omega_language_auto \<A>2" using impl unfolding omega_language_auto_def by blast
    hence "omega_word \<in> omega_language_auto \<A>2" using word' by blast
  }
  hence left: "image (omega_map h) (omega_language_auto \<A>1) \<subseteq> omega_language_auto \<A>2" by blast
  let ?h_inv = "inv_into (alphabet \<A>1) h"
  let ?g = "inv_into (states \<A>1) f"
  have bij: "bij_betw ?h_inv (alphabet \<A>2) (alphabet \<A>1) \<and> bij_betw ?g (states \<A>2) (states \<A>1)" using assms bij_betw_inv_into by metis
  {
    fix omega_word assume assm: "omega_word \<in> omega_language_auto \<A>2"
    hence "\<forall> n . omega_word n \<in> alphabet \<A>2" using omega_word_in_omega_language_is_well_defined well_def unfolding omega_word_well_defined_def by auto
    hence omega_word: "(inv_into (alphabet \<A>2) ?h_inv) \<circ> (?h_inv \<circ> omega_word) = omega_word" using bij composition_bij by blast
    have l1: "(?h_inv \<circ> omega_word) \<in> omega_language_auto \<A>1" using impl assm unfolding omega_language_auto_def by blast
    hence "omega_word_well_defined (?h_inv \<circ> omega_word) (alphabet \<A>1)" using omega_word_in_omega_language_is_well_defined assms by auto
    hence "\<forall> n . (?h_inv \<circ> omega_word) n \<in> alphabet \<A>1" unfolding omega_word_well_defined_def by auto
    hence h_inv: "(inv_into (alphabet \<A>2) ?h_inv) \<circ> (?h_inv \<circ> omega_word) = h \<circ> (?h_inv \<circ> omega_word)" using assms inv_inv_composition by metis 
    have "h \<circ> (?h_inv \<circ> omega_word) \<in> image (omega_map h) (omega_language_auto \<A>1)" using l1 unfolding omega_map_def by blast
    hence "omega_word \<in> image (omega_map h) (omega_language_auto \<A>1)" using h_inv omega_word by argo
  }
  hence "omega_language_auto \<A>2 \<subseteq> image (omega_map h) (omega_language_auto \<A>1)" by fast
  thus ?thesis using left by auto
qed

corollary omega_language_iso_correctness_unfold:
  assumes "auto_well_defined \<A>1" "isomorphic_automata \<A>1 \<A>2"
  obtains h where "bij_betw h (alphabet \<A>1) (alphabet \<A>2) \<and> omega_language_auto \<A>2 = image (omega_map h) (omega_language_auto \<A>1)"
  using omega_language_iso_correctness assms unfolding isomorphic_automata_def by metis

proposition type_encode_preserves_omega_language:
  assumes "auto_well_defined \<A>" "bij_betw f_bij (states \<A>) (image f_bij (states \<A>))" "bij_betw h_bij (alphabet \<A>) (image h_bij (alphabet \<A>))"
  shows "omega_language_auto (type_encode_automaton \<A> f_bij h_bij) = image (omega_map h_bij) (omega_language_auto \<A>)"
proof -
  let ?f = "f_bij"
  let ?\<A> = "type_encode_automaton \<A> f_bij h_bij"
  have well_def: "auto_well_defined (type_encode_automaton \<A> f_bij h_bij)" using assms type_encode_preserves_well_def by blast
  have h: "bij_betw h_bij (alphabet \<A>) (alphabet ?\<A>)" using assms unfolding type_encode_automaton_def by auto
  have bij: "bij_betw ?f (states \<A>) (states ?\<A>)" using assms unfolding type_encode_automaton_def by auto
  have init: "?f (initial_state \<A>) = initial_state ?\<A>" unfolding type_encode_automaton_def by auto
  have acc: "image ?f (accepting_states \<A>) = accepting_states ?\<A>" unfolding type_encode_automaton_def by auto
  have trans: "image (\<lambda>(S1, a, S2) . (?f S1, h_bij a, ?f S2)) (transitions \<A>) = transitions ?\<A>" unfolding type_encode_automaton_def by auto
  thus ?thesis using assms bij init acc trans h well_def omega_language_iso_correctness by metis
qed

corollary cross_renaming_iso_automaton_omega_language:
  assumes "auto_well_defined \<A>"
  shows "omega_language_auto \<A> = omega_language_auto (type_encode_automaton \<A> (cross_renaming_iso n) id)"
proof - 
  have "omega_language_auto (type_encode_automaton \<A> (cross_renaming_iso n) id) = image (omega_map id) (omega_language_auto \<A>)" using assms id_bij_betw type_encode_preserves_omega_language bij_cross_renaming_iso by blast
  thus ?thesis unfolding omega_map_def by auto
qed

text \<open>Soft Isomorphy between automata with same alphabet, so the bij between alphabet1 and alphabet2 is the id\<close> 
corollary omega_language_well_def_soft_iso_auto:
  assumes "auto_well_defined \<A>1" "soft_isomorphic_automata \<A>1 \<A>2"
  shows "omega_language_well_defined (omega_language_auto \<A>2) (alphabet \<A>2)"
  using soft_iso_preserves_auto_well_defined assms automata_omega_language_are_well_defined by blast

text \<open>Soft-Isomorphic automata accept the same language\<close>
theorem omega_soft_iso_prun_correct:
  assumes "auto_well_defined \<A>1" "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "(\<forall> omega_prun omega_word s . omega_pseudo_run_well_defined omega_prun \<A>1 s omega_word \<longrightarrow> omega_pseudo_run_well_defined (f \<circ> omega_prun) \<A>2 (f s) omega_word) \<and> (\<forall> omega_prun omega_word s . omega_pseudo_run_well_defined omega_prun \<A>2 s omega_word \<longrightarrow> omega_pseudo_run_well_defined ((inv_into (states \<A>1) f) \<circ> omega_prun) \<A>1 (inv_into (states \<A>1) f s) omega_word)"
proof -
  {
    fix omega_prun omega_word s assume assm: "omega_pseudo_run_well_defined omega_prun \<A>1 s omega_word"
    hence "omega_pseudo_run_well_defined (f \<circ> omega_prun) \<A>2 (f s) (id \<circ> omega_word)" using assms omega_iso_prun_correct by metis
  }
  hence impl: "\<forall> omega_prun omega_word s . omega_pseudo_run_well_defined omega_prun \<A>1 s omega_word \<longrightarrow> omega_pseudo_run_well_defined (f \<circ> omega_prun) \<A>2 (f s) omega_word" by auto
  let ?g = "inv_into (states \<A>1) f"
  let ?h_inv = "inv_into (alphabet \<A>1) id"
  have bij: "alphabet \<A>2 = alphabet \<A>1" using assms unfolding bij_betw_def by auto
  {
    fix omega_prun omega_word s assume assm: "omega_pseudo_run_well_defined omega_prun \<A>2 s omega_word"
    hence "omega_pseudo_run_well_defined (?g \<circ> omega_prun) \<A>1 (?g s) ((inv_into (alphabet \<A>1) id) \<circ> omega_word)" using assms omega_iso_prun_correct by metis
    hence omega_prun: "omega_pseudo_run_well_defined (?g \<circ> omega_prun) \<A>1 (?g s) ((inv_into (alphabet \<A>1) id) \<circ> (id \<circ> omega_word))" by simp
    have "auto_well_defined \<A>2" using soft_iso_preserves_auto_well_defined assms unfolding soft_isomorphic_automata_def by auto
    hence "omega_word_well_defined omega_word (alphabet \<A>2)" using assm well_def_implies_omega_word_well_defined by metis
    hence "\<forall> n . omega_word n \<in> alphabet \<A>1" using bij unfolding omega_word_well_defined_def by blast
    hence "((inv_into (alphabet \<A>1) id) \<circ> (id \<circ> omega_word)) = omega_word" using assms composition_bij by metis     
    hence "omega_pseudo_run_well_defined (?g \<circ> omega_prun) \<A>1 (?g s) (id \<circ> omega_word)" using omega_prun by auto
  }
  hence "\<forall> omega_prun omega_word s .omega_pseudo_run_well_defined omega_prun \<A>2 s omega_word \<longrightarrow> omega_pseudo_run_well_defined (?g \<circ> omega_prun) \<A>1 (?g s) omega_word" by auto
  thus ?thesis using impl by auto
qed

theorem omega_soft_iso_run_correct:
  assumes "auto_well_defined \<A>1" "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "(\<forall> omega_run omega_word . omega_run_accepting omega_run \<A>1 omega_word \<longrightarrow> omega_run_accepting (f \<circ> omega_run) \<A>2 omega_word) \<and> (\<forall> omega_run omega_word . omega_run_accepting omega_run \<A>2 omega_word \<longrightarrow> omega_run_accepting ((inv_into (states \<A>1) f) \<circ> omega_run) \<A>1 omega_word)"
proof -
  {
    fix omega_run omega_word assume assm: "omega_run_accepting omega_run \<A>1 omega_word"
    hence "omega_run_accepting (f \<circ> omega_run) \<A>2 (id \<circ> omega_word)" using assms omega_iso_run_correct by metis
  }  
  hence impl: "\<forall> omega_run omega_word . omega_run_accepting omega_run \<A>1 omega_word \<longrightarrow> omega_run_accepting (f \<circ> omega_run) \<A>2 omega_word" by auto
  let ?g = "inv_into (states \<A>1) f"
  let ?h_inv = "inv_into (alphabet \<A>1) id"
  have bij: "alphabet \<A>2 = alphabet \<A>1" using assms unfolding bij_betw_def by auto
  {
    fix omega_run omega_word assume assm: "omega_run_accepting omega_run \<A>2 omega_word"
    hence "omega_run_accepting (?g \<circ> omega_run) \<A>1 ((inv_into (alphabet \<A>1) id) \<circ> omega_word)" using assms omega_iso_run_correct by metis
    hence omega_run: "omega_run_accepting (?g \<circ> omega_run) \<A>1 ((inv_into (alphabet \<A>1) id) \<circ> (id \<circ> omega_word))" by simp
    have "auto_well_defined \<A>2" using soft_iso_preserves_auto_well_defined assms unfolding soft_isomorphic_automata_def by auto
    hence "omega_word_well_defined omega_word (alphabet \<A>2)" using assm well_def_implies_omega_word_well_defined unfolding omega_run_accepting_def omega_run_well_defined_def by metis
    hence "\<forall> n . omega_word n \<in> alphabet \<A>1" using bij unfolding omega_word_well_defined_def by blast
    hence "((inv_into (alphabet \<A>1) id) \<circ> (id \<circ> omega_word)) = omega_word" using assms composition_bij by metis 
    hence "omega_run_accepting (?g \<circ> omega_run) \<A>1  omega_word" using omega_run by metis  
  }
  hence "\<forall> omega_run omega_word . omega_run_accepting omega_run \<A>2 omega_word \<longrightarrow> omega_run_accepting (?g \<circ> omega_run) \<A>1 omega_word" by auto
  thus ?thesis using impl by auto
qed

theorem omega_closed_under_soft_iso:
  assumes "auto_well_defined \<A>1" "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2"
  shows "omega_word \<in> omega_language_auto \<A>1 \<longleftrightarrow> omega_word \<in> omega_language_auto \<A>2"
proof -
  have "(\<forall> omega_run omega_word . omega_run_accepting omega_run \<A>1 omega_word \<longrightarrow> omega_run_accepting (f \<circ> omega_run) \<A>2 omega_word) \<and> (\<forall> omega_run omega_word . omega_run_accepting omega_run \<A>2 omega_word \<longrightarrow> omega_run_accepting ((inv_into (states \<A>1) f) \<circ> omega_run) \<A>1 omega_word)" using assms omega_soft_iso_run_correct by metis
  thus ?thesis unfolding omega_language_auto_def by blast
qed

text \<open>Main result for soft_isomorphy\<close>
theorem omega_language_soft_iso_correctness:
  assumes "auto_well_defined \<A>1" "soft_isomorphic_automata \<A>1 \<A>2"
  shows "omega_language_auto \<A>2 = omega_language_auto \<A>1"
proof -
  obtain f where org: "bij_betw f (states \<A>1) (states \<A>2) \<and> bij_betw id (alphabet \<A>1) (alphabet \<A>2) \<and> f (initial_state \<A>1) = initial_state \<A>2 \<and> image f (accepting_states \<A>1) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, id a, f s2)) (transitions \<A>1) = transitions \<A>2" using assms unfolding soft_isomorphic_automata_def by presburger 
  thus ?thesis using assms omega_closed_under_soft_iso by auto
qed

corollary existence_soft_iso_auto_omega_lang:
  assumes "auto_well_defined (\<A>1 :: ('t, 'a) automaton)" "infinite (UNIV :: 's set)"
  shows "\<exists> \<A>2 :: ('s, 'a) automaton . auto_well_defined \<A>2 \<and> alphabet \<A>2 = alphabet \<A>1 \<and> omega_language_auto \<A>2 = omega_language_auto \<A>1"
  using assms existence_soft_iso_automaton omega_language_soft_iso_correctness soft_iso_preserves_auto_well_defined soft_implies_alphabet by fast

theorem existence_of_omega_sigma_star_same_type:
  assumes "finite \<Sigma>" "infinite (UNIV :: 's set)"
  shows "\<exists> sigma_\<A> :: ('s , 'a) automaton . auto_well_defined sigma_\<A> \<and> alphabet sigma_\<A> = \<Sigma> \<and> omega_language_auto sigma_\<A> = omega_sigma_star \<Sigma>"
  using assms omega_sigma_star_main existence_soft_iso_auto_omega_lang by fast

theorem NBA_to_DBA: 
  assumes "infinite (UNIV :: 's set)" "infinite (UNIV :: 'a set)"
  shows "\<exists> (NBA_\<A> :: ('s, 'a) automaton) . auto_well_defined NBA_\<A> \<and> (\<nexists> DBA_\<A> :: ('s, 'a) automaton . auto_well_defined DBA_\<A> \<and> DFA_property DBA_\<A> \<and> alphabet DBA_\<A> = alphabet NBA_\<A> \<and> omega_language_auto DBA_\<A> = omega_language_auto NBA_\<A>)"
proof -
  have well_def: "auto_well_defined \<A>_NBA" using well_def_\<A>_NBA by blast
  then obtain \<A>2 :: "('s, 'a) automaton" where iso: "isomorphic_automata \<A>_NBA \<A>2" using assms existence_iso_automaton by blast
  hence well_def2: "auto_well_defined \<A>2" using well_def iso_preserves_auto_well_defined by auto
  obtain f h where fh: "bij_betw f (states \<A>_NBA) (states \<A>2) \<and> bij_betw h (alphabet \<A>_NBA) (alphabet \<A>2) \<and> f (initial_state \<A>_NBA) = initial_state \<A>2 \<and> image f (accepting_states \<A>_NBA) = accepting_states \<A>2 \<and> image (\<lambda>(s1, a, s2) . (f s1, h a, f s2)) (transitions \<A>_NBA) = transitions \<A>2" using iso unfolding isomorphic_automata_def by presburger
  let ?h_inv = "inv_into (alphabet \<A>_NBA) h"
  let ?g = "inv_into (states \<A>_NBA) f"
  have bij1: "bij_betw ?h_inv (alphabet \<A>2) (alphabet \<A>_NBA) \<and> bij_betw ?g (states \<A>2) (states \<A>_NBA)" using fh bij_betw_inv_into by metis
  have bij2: "?g (initial_state \<A>2) = initial_state \<A>_NBA \<and> image ?g (accepting_states \<A>2) = accepting_states \<A>_NBA" using well_def fh bijection_inverse_special_states by metis
  have "image (\<lambda>(s1, a, s2) . (?g s1, ?h_inv a, ?g s2)) (transitions \<A>2) = transitions \<A>_NBA" using well_def assms fh bijection_inverse_trans by metis
  hence props2: "alphabet \<A>_NBA = image ?h_inv (alphabet \<A>2) \<and> omega_language_auto \<A>_NBA = image (omega_map ?h_inv) (omega_language_auto \<A>2)" using well_def2 bij1 bij2 omega_language_iso_correctness unfolding bij_betw_def by metis 
  have "\<nexists> (DFA_\<A> :: ('s, 'a) automaton). auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = alphabet \<A>2 \<and> omega_language_auto DFA_\<A> = omega_language_auto \<A>2"
  proof (rule ccontr)
    assume "\<not> (\<nexists> (DFA_\<A> :: ('s, 'a) automaton). auto_well_defined DFA_\<A> \<and> DFA_property DFA_\<A> \<and> alphabet DFA_\<A> = alphabet \<A>2 \<and> omega_language_auto DFA_\<A> = omega_language_auto \<A>2)"
    then obtain \<A> :: "('s, 'a) automaton" where A: "auto_well_defined \<A> \<and> DFA_property \<A> \<and> alphabet \<A> = alphabet \<A>2 \<and> omega_language_auto \<A> = omega_language_auto \<A>2" by blast
    hence "auto_well_defined \<A> \<and> DFA_property \<A> \<and> bij_betw id (states \<A>) (image id (states \<A>)) \<and> bij_betw ?h_inv (alphabet \<A>) (alphabet \<A>_NBA) \<and> alphabet \<A>_NBA = image ?h_inv (alphabet \<A>)" using bij1 props2 by auto
    hence "auto_well_defined (type_encode_automaton \<A> id ?h_inv) \<and> DFA_property (type_encode_automaton \<A> id ?h_inv) \<and> omega_language_auto (type_encode_automaton \<A> id ?h_inv) = image (omega_map ?h_inv) (omega_language_auto \<A>)" using type_encode_preserves_dfa type_encode_preserves_omega_language type_encode_preserves_well_def by metis
    hence "auto_well_defined (type_encode_automaton \<A> id ?h_inv) \<and> DFA_property (type_encode_automaton \<A> id ?h_inv) \<and> omega_language_auto (type_encode_automaton \<A> id ?h_inv) = omega_language_auto \<A>_NBA" using A props2 by simp
    hence "auto_well_defined (type_encode_automaton \<A> id ?h_inv) \<and> DFA_property (type_encode_automaton \<A> id ?h_inv) \<and> omega_language_auto (type_encode_automaton \<A> id ?h_inv) = omega_language_auto \<A>_NBA \<and> alphabet (type_encode_automaton \<A> id ?h_inv) = image ?h_inv (alphabet \<A>)" unfolding type_encode_automaton_def by auto
    hence propsA: "auto_well_defined (type_encode_automaton \<A> id ?h_inv) \<and> DFA_property (type_encode_automaton \<A> id ?h_inv) \<and> omega_language_auto (type_encode_automaton \<A> id ?h_inv) = omega_language_auto \<A>_NBA \<and> alphabet (type_encode_automaton \<A> id ?h_inv) = alphabet \<A>_NBA" using props2 A by simp
    hence "\<exists> \<A>_nat :: (nat, nat) automaton . soft_isomorphic_automata (type_encode_automaton \<A> id ?h_inv) \<A>_nat" using existence_soft_iso_automaton by blast
    then obtain \<A>_nat :: "(nat, nat) automaton" where "soft_isomorphic_automata (type_encode_automaton \<A> id ?h_inv) \<A>_nat" by blast
    hence "auto_well_defined \<A>_nat \<and> DFA_property \<A>_nat \<and> omega_language_auto \<A>_nat = omega_language_auto \<A>_NBA \<and> alphabet \<A>_nat = alphabet \<A>_NBA" using propsA soft_implies_alphabet soft_iso_preserves_auto_well_defined soft_iso_preserves_DFA_property omega_language_soft_iso_correctness by metis
    thus False using there_is_no_DFA_for_A_NBA by blast
  qed
  thus ?thesis using well_def2 by blast
qed

end