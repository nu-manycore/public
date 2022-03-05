           (*-------------------------------------------*
            |                                           |
            |      LW-CSP-Prover on Isabelle2021        |
            |                                           |
            *-------------------------------------------*)

theory CSP_wfsim
imports  CSP_wsim
begin

(*************************************************************

         1. Weak Simulation
         2. Proposition 3.1 in the ETNET2019 paper 
         3. 
         4. 

 *************************************************************)


(* ----------------------------------------- *
 |              Weak failers simulation      |
 * ----------------------------------------- *)
definition
  weak_failures_sim :: "(('p,'a) proc * ('q,'a) proc) set =>bool"
                 (*    ("(1_ /is-a-weak-simulation)" [1000] 1000)  *)
where
  "weak_failures_sim S == ALL P Q. (P,Q): S --> 
                          (ALL e P'. (P ---e---> P' --> (EX Q'. Q ===^e===> Q' & (P',Q') : S))
                          &((P ---Tau--->+)|(~(P---e--->+) --> ~(Q---e--->+))))"

(* ----------------------------------------- *
 |                    lemmas                 |
 * ----------------------------------------- *)

lemma weak_failures_sim_weak_sim:
  "ALL S. weak_failures_sim S --> weak_sim S"
  apply (simp add: weak_failures_sim_def)
  apply (simp add: weak_sim_def)
  done

 

lemma weak_failures_sim_traces_ref_traces:
  "weak_failures_sim S ==> (P, Q) : S ==> traces P <= traces Q"
  apply (insert weak_failures_sim_weak_sim)
  apply (drule_tac x="S" in spec)
  apply (simp add: weak_sim_traces_ref_traces)
  done


lemma weak_failures_sim_stable:
" weak_failures_sim S ==> (P, Q) : S ==> stable P ==> stable Q"
  apply(simp add: stable_def)
  apply(simp add: weak_failures_sim_def)
  apply(drule_tac x="P" in spec)
  apply(drule_tac x="Q" in spec)
  apply(simp)
  done



lemma inclusive_refs_no_trn:
"weak_failures_sim S ==> (P, Q) : S ==> \<not> P ---(Ev t)--->+ ==> stable P ==> \<not> Q ---(Ev t)--->+"
  apply(simp add: weak_failures_sim_def)
  apply(drule_tac x="P" in spec)
  apply(drule_tac x="Q" in spec)
  apply(simp)
  apply(drule_tac x="Ev t" in spec)
  apply(simp)
  apply(erule conjE)
  apply(erule disjE)
   (*stable case*)
   apply(simp add: stable_def)

  apply(simp)
  done

lemma inclusive_refs_tau_trn:
"weak_failures_sim S \<Longrightarrow> (P, Q) \<in> S \<Longrightarrow> \<not> P ---(Ev t)--->+ \<Longrightarrow> stable P \<Longrightarrow> stable Q"
  apply(simp add: weak_failures_sim_def)
  apply(drule_tac x="P" in spec)
  apply(drule_tac x="Q" in spec)
  apply(simp)
  apply(drule_tac x="Tau" in spec)
  apply(simp add: stable_def)
  done

lemma inclusive_refs:
"ALL S P Q. weak_failures_sim S --> (P,Q):S --> refs(P) <= refs(Q)"
(*"weak_failures_sim S ==> (P,Q):S ==> refs(P) <= refs(Q)"*)
  apply(intro allI)
  apply(intro impI)
(*  apply(simp add: weak_failures_sim_def)*)
  apply(simp add: refs_def)
  apply(simp add: subset_iff)
  apply(rule allI)
  apply(rule impI)
  apply(erule conjE)
  apply(rule conjI)
   apply(simp add: inclusive_refs_no_trn)
  apply(simp add: inclusive_refs_tau_trn)
  done

lemma weak_sim_traces_ref_failures:
  "weak_failures_sim S ==> (P, Q) : S ==> failures P <= failures Q"
  apply (simp add: subset_iff)
  apply (simp add: failures_def)
  apply (intro allI)
  apply (rule impI)
  apply (elim exE conjE)
   (**)
   apply (simp)
  apply (insert weak_sim_seq_trn)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="s" in spec)
  apply (drule_tac x="P" in spec)
  apply (drule_tac x="Q" in spec)
  apply (drule_tac x="P'" in spec)
  apply (simp)
  apply (simp add:weak_failures_sim_weak_sim)
  apply (erule exE)
  apply (erule exE)
  apply (erule conjE)
  apply (erule conjE)
  apply (rule_tac x="t" in exI)
  apply (simp)
  apply (rule_tac x="Q'" in exI)
  apply (simp)
  apply (intro conjI)
   apply (simp add: weak_failures_sim_stable)
  apply (insert inclusive_refs)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="P'" in spec)
  apply (drule_tac x="Q'" in spec)
  apply (simp)
  done



(* ----------------------------------------- *
 |               Proposition 5.1             |
 * ----------------------------------------- *)

theorem wfsim_refF:
  "weak_failures_sim S ==> (P,Q) : S ==> Q [F= P"

  apply (simp add: refF_def)
  apply (simp add: weak_failures_sim_traces_ref_traces)
  apply (simp add: weak_sim_traces_ref_failures)
  done

end
