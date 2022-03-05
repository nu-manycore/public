           (*-------------------------------------------*
            |                                           |
            |      LW-CSP-Prover on Isabelle2021        |
            |                                           |
            *-------------------------------------------*)

theory CSP_wsim
imports CSP_semantics
begin

(*************************************************************

         1. Weak Simulation
         2. Proposition 3.1 in the ETNET2019 paper 
         3. 
         4. 

 *************************************************************)

(* ----------------------------------------- *
 |              Weak simulation              |
 * ----------------------------------------- *)

definition
  weak_sim :: "(('p,'a) proc * ('q,'a) proc) set => bool"
                 (*    ("(1_ /is-a-weak-simulation)" [1000] 1000)  *)
where
  "weak_sim S == ALL P Q. (P,Q): S --> (ALL e P'. 
                P ---e---> P' --> (EX Q'. Q ===^e===> Q' & (P',Q') : S))"

(* ----------------------------------------- *
 |                    lemmas                 |
 * ----------------------------------------- *)

 (*Definition 3.3.2*)
lemma weak_sim_seq_trn:
  "ALL S s P Q P'. (weak_sim S & (P,Q) : S & P ---s--->> P')
   --> (EX t Q'. Q ---t--->> Q' & rem_tau s = rem_tau t & (P',Q') : S)"
  apply (rule allI)
  apply (rule allI)
  apply (induct_tac s)

  (* Nil case *)
    apply (intro allI conjI impI)
    apply (elim conjE)

    apply (rule_tac x="[]" in exI)
    apply (rule_tac x="Q" in exI)
    apply (simp)
    apply (simp add: seq_trn_nil)

  (* Step case *)
  apply (intro allI conjI impI)
  apply (elim conjE)
  apply (simp add: seq_trn_step)
  apply (elim conjE exE)
  apply (subgoal_tac "EX Q1. Q ===^a===> Q1 & (P1,Q1) : S")  (* subgoal 1 *)

   apply (elim conjE exE)
   apply (simp add: weak_tau_trn_seq_trn)
   apply (elim conjE exE)

  apply (drule_tac x="P1" in spec)
  apply (drule_tac x="Q1" in spec)
  apply (drule_tac x="P'" in spec)
  apply (simp)   (* by induction *)
  apply (elim conjE exE)

  apply (rule_tac x="t @ ta" in exI)
  apply (rule_tac x="Q'" in exI)
  apply (simp)

  apply (simp add: rem_tau_append)
  apply (simp add: rem_tau_cons)
  apply (simp add: seq_trn_append)
  apply (rule_tac x="Q1" in exI)
  apply (simp)

 (* subgoal 1*)
  apply (simp add: weak_sim_def)
  done

(* ----------------------------------------- *
 |               Proposition 3.1             |
 * ----------------------------------------- *)
lemma weak_sim_traces_ref_traces:
  "weak_sim S ==> (P,Q) : S ==> traces P <= traces Q"
  apply (simp add: traces_def)
  apply (simp add: subset_iff)

  apply (rule allI)                               
  apply (rule impI)
  apply (erule exE)  
  apply (erule conjE)
  apply (erule exE)

  apply (insert weak_sim_seq_trn)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="s" in spec)
  apply (drule_tac x="P" in spec)
  apply (drule_tac x="Q" in spec)
  apply (drule_tac x="x" in spec)
  apply (simp)

  apply (erule exE)
  apply (erule exE)

  apply (rename_tac t s P' s' Q')

  apply (erule conjE)
  apply (erule conjE)


  apply (rule_tac x="s'" in exI)
  apply (simp)
  apply (rule_tac x="Q'" in exI)
  apply (simp)
  done 


theorem weak_sim_traces_ref:
  "weak_sim S ==> (P,Q) : S ==> Q [T= P"
  apply (simp add: refT_def)
  apply (simp add: weak_sim_traces_ref_traces)
  done
            


end
