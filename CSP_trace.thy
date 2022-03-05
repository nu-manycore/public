            (*-------------------------------------------*
            |                                           |
            |       LW-CSP-Prover on Isabelle2021       |
            |                                           |
            *-------------------------------------------*)

theory CSP_trace
imports Main
begin

(*************************************************************

         1. Event type
         2. Functions on event-lists
         3. 
         4. 

 *************************************************************)

(***********************************************************
                    Definition of traces
 ***********************************************************)

datatype 'a event = Ev 'a | Tau
type_synonym 'a ev_list = "'a event list"           (* synonym *)

(***********************************************************
                       functions
 ***********************************************************)

(* remove Tau *)

primrec
  obs :: "'a event => 'a list"
  where
    "obs (Ev a) = [a]"
  | "obs (Tau) = []"

fun
  rem_tau :: "'a ev_list => 'a list"
  where
    "rem_tau [] = []"
  |"rem_tau (Tau#s) = rem_tau s"
  |"rem_tau (Ev a#s) = a#rem_tau s"


(* ----------------------------------------- *
 |                    lemmas                 |
 * ----------------------------------------- *)

lemma map_list_test:
  "map Ev [1,2,3] = [Ev 1, Ev 2, Ev 3]"
  apply (simp)
  done

lemma eq_rem_tau: 
  "rem_tau(map Ev s) = s"
  apply (induct_tac s)
  apply (simp)
  apply (simp)
  done

lemma ev_or_tau: 
  "ALL e. (EX a. e = Ev a) | e = Tau"
  apply (rule allI)
  apply (induct_tac e)
  apply (simp_all)
  done

lemma rem_tau_append_ALL:
  "ALL s1 s2. rem_tau(s1 @ s2) = rem_tau(s1) @ rem_tau(s2)"
  apply (rule allI)
  apply (induct_tac s1)
    (* nil *)
  apply (simp)

(* step *)
  apply (insert ev_or_tau)
  apply (drule_tac x="a" in spec)
  apply (elim disjE exE conjE)
  apply (simp_all)
  done

lemma rem_tau_append:
  "rem_tau(s1 @ s2) = rem_tau(s1) @ rem_tau(s2)"
  apply (simp add: rem_tau_append_ALL)
  done

lemma rem_tau_obs:
  "rem_tau([e]) = obs e"
  apply (induct_tac e)
  apply (simp)
  apply (simp)
  done

lemma rem_tau_cons:
  "rem_tau(e#s) = (obs e) @ rem_tau(s)"
  apply (insert rem_tau_append[of "[e]" s])
  apply (simp)
  apply (simp add: rem_tau_obs)
  done

lemma rem_tau_ev_only_if:
  "(rem_tau t = [a]) 
   --> (EX s1 s2. t = s1@(Ev a #s2) & rem_tau s1 = [] & rem_tau s2 = [])"
  apply (induct_tac t)
  apply (simp)

  apply (intro impI)
  apply (insert ev_or_tau)
  apply (drule_tac x="aa" in spec)
  apply (elim disjE exE conjE)

  apply (simp)
  apply (rule_tac x="[]" in exI)
  apply (rule_tac x="list" in exI)
  apply (simp)

  apply (simp)
  apply (elim exE conjE)
  apply (simp)
  apply (rule_tac x="Tau # s1" in exI)
  apply (simp)
  done


lemma rem_tau_ev:
  "(rem_tau t = [a]) 
   = (EX s1 s2. t = s1@(Ev a # s2) & rem_tau s1 = [] & rem_tau s2 = [])"
  apply (rule iffI)
  apply (simp add: rem_tau_ev_only_if)
  apply (elim exE conjE)
  apply (simp)
  apply (simp add: rem_tau_append)
  done

lemma rem_asmE: 
  "A ==> R ==> R"
  by simp

end
