            (*-------------------------------------------*
            |                                           |
            |   Basic definitions and lemmas for MBP    |
            |                                           |
            *-------------------------------------------*)

theory MBP_base
imports Main
begin                                      

(*************************************************************

         1. graph
         2. 
         3. 
         4. 

 *************************************************************)

(* events used in MBP *)

datatype Event =  finish | blk nat | com nat nat nat  

                                                      

(* --- graph --- *)

type_synonym nodes = "nat set"
type_synonym edges = "(nat * nat) set"

definition
  no_loop :: "edges => bool"
  where
    no_loop_def : "no_loop r == (ALL m n. (m,n) : r --> ~(m=n))"

definition
  cycle :: "edges => bool"
  where
    cycle_def : "cycle r == (EX m. (m,m) : r^+)"
                                                  
definition
  dg :: "nodes => edges => bool"
  where
    dg_def : "dg e r == (ALL m n. (m,n):r --> (m : e & n : e))"

definition
  dag :: "nodes => edges => bool"
  where
    dag_def : "dag e r == dg e r & ~cycle r"


(* observable evets *)

definition                               
  obsEvent :: "nodes => Event set"
  where                   
    obsEvent_def : "obsEvent Blks == {finish} Un {e. EX n. n:Blks & e = blk n}"
(*   obsEvent_def : "obsEvent Blks == {finish} Un {e. EX n. n:Blks & e = blk n}" *)


(* definition of enable *)

definition
  src :: "nodes => edges => nat => nodes"
where
  src_def : "src Blks Deps n == {m. m : Blks & (m,n) : Deps}"


definition
  enable :: "nodes => edges => nodes => nodes"
  where 
  enable_def : "enable Blks Deps S == {n. n : Blks & (src Blks Deps n) <= S & ~(n : S)}"


definition
  dones :: "Event list => nat => nodes"
  where
  dones_def : "dones t k == {m. EX k'. (k' < k) & ( t!k' = blk m)}"

(* ------------------------------------ *
 |       convenient commands            |
 * ------------------------------------ *)

(* remove assumption *)

lemma rem_asmE: 
  "A ==> R ==> R"
  by simp


(* ------------------------------------ *
 |          lemmas on safe              |
 * ------------------------------------ *)

lemma dones_insert:
"insert n (dones (rem_tau t) k \<union> S) 
 <= dones (blk n # rem_tau t) (Suc k) \<union> S"
  apply(rule subsetI)
  apply (simp)
  apply (elim exE conjE disjE)
  apply (rule disjI1)
    apply (simp add:dones_def)
    apply (rule_tac x="0" in exI)
    apply (simp)

   apply (rule disjI1)
   apply (simp add:dones_def)
   apply (erule exE)
   apply (rule_tac x="Suc k'" in exI)
   apply (simp)

  apply (simp)
  done

(* ------------------------------------ *
 |         lemmas on all-blocks         |
 * ------------------------------------ *)

lemma cycle_subset_FE:
"F <= E ==> cycle F ==> cycle E"
  apply (simp add:cycle_def)
  apply (erule exE)
  apply (rule_tac x="m" in exI)
  apply (simp add:trancl_mono)
  done

lemma not_in_M:
  "ALL E M n. ~cycle E --> M = {m. (m,n):E^+} -->  n ~: M "
  apply (intro allI impI)
  apply (simp add:cycle_def)
  done

lemma M_not_emptyset:
  "ALL  N E M m n .  (EX n'. n':N & (n',n):E) --> M = {m. (m,n):E^+} --> M ~= {}"
  apply (intro allI impI)
  apply (elim exE conjE) 
  apply (simp)
  apply (rule_tac x="n'" in exI)
  apply (simp)
  done

lemma card_M_1:
  "ALL M.  finite M  --> M ~= {} --> card M > 0 "
  apply (auto)
  done


lemma card_M_k:
  "ALL M N n k.  finite N --> card N <= k+1 --> finite M --> M <= N --> n:N --> n~:M -->  card M <= k "
  apply (intro allI impI)
  apply (subgoal_tac "EX N'. N=insert n N' &  n ~: N'")
   apply (elim exE conjE)
   apply (simp)
   apply (subgoal_tac "card M <= card N'")
    apply (simp)
   apply (rule card_mono)
    apply (simp)
   apply (rule subsetI)
   apply (force)
  apply (rule_tac x="N-{n}" in exI)
  apply (force)
  done


lemma dg_subset:
  "ALL F E M N n. dg N E --> M = {m. (m,n):E^+} --> F = E Int (M \<times> M)
--> dg M F <= dg N E"
  apply (simp add:dg_def)
  done

lemma m_exsist_E_test:
  "ALL M m n E N.(ALL n1. n1:N -->(EX n1'. (n1',n1):E & n1':N)) --> (EX n'. n':N & (n',n):E)
--> M = {m. (m,n):E^+} --> m:M --> M <= N 
--> (EX m'. (m',m):E & m':M)"
  apply (intro allI impI)
  apply (elim exE conjE)
  apply (drule_tac x="m" in spec)
  apply (simp add:subset_iff)
  apply (elim exE conjE)
  apply (rule_tac x="n1'" in exI)
  apply (simp)
  done

lemma m_exsist_E:
  "ALL M m n E N.(ALL n1. n1:N -->(EX n1'. (n1',n1):E & n1':N)) --> (EX n'. n':N & (n',n):E) 
--> M = {m. (m,n):E^+} --> m:M --> M <= N 
--> (EX m'. (m',m):E & m':M)"
  apply (intro allI impI)
  apply (elim exE conjE)
  apply (drule_tac x="m" in spec)
  apply (simp add:subset_iff)
  apply (elim exE conjE)
  apply (rule_tac x="n1'" in exI)
  apply (simp)
  done

lemma m_exsist_F:
  "ALL M m m' E F. F = E Int (M \<times> M) --> m:M --> m':M --> (m',m):E --> (m',m):F"
  apply (simp add:subset_iff)
  done

lemma finite_M_test:
  " finite E ==> finite (E\<^sup>+)"
  apply (force)
  done

lemma finite_fst: 
  "finite E ==> finite {m. (m,n) : E}"
  apply(subgoal_tac "{m. (m,n) : E} <= fst ` E")
   apply(subgoal_tac "finite (fst ` E)")
    apply(simp add: finite_subset)
   apply(simp add: finite_image_iff)
  apply (force)
  done

(* finite_cartesian_product *)
lemma finite_dg:
  "finite N ==> dg N E ==> finite E"
  apply (subgoal_tac "E <= N \<times> N")
   apply(simp add: finite_subset)
  apply (simp add:dg_def)
  apply (auto)
  done

lemma finite_M:
  " finite N ==> dg N E ==> finite {m. (m, n) \<in> E\<^sup>+}"
  apply (rule finite_fst)
  apply (rule finite_M_test)
  apply (simp add: finite_dg)
  done

lemma dg_plus:
  "dg N E ==> (m,n):E^+ ==> (m : N & n : N)"
  apply (erule trancl_induct)
   apply (simp add:dg_def)
  apply (simp add:dg_def)
  done

lemma dg_plus1:
  "ALL N E. dg N E --> (ALL m n. (m,n):E^+ --> (m : N & n : N))"
  apply (intro allI impI)
  apply (simp add:dg_plus)
  done

lemma subset_FE:
  "(Restr E {m. (m, n) \<in> E\<^sup>+}) <= E"
  apply (simp)                             
  done



(* ----------------------------------------- *
 |              iwata Lemma 5.1.1            |
 * ----------------------------------------- *)


(* lemma 5.1.1 *)

lemma dag_cycle:
  "\<forall>N E. 
    finite N \<longrightarrow> N \<noteq> {} \<longrightarrow> card N \<le> k \<longrightarrow> dg N E 
    \<longrightarrow> (\<forall>n \<in> N. \<exists>n' \<in> N. (n', n) \<in> E) 
    \<longrightarrow> cycle E"

  apply (induct_tac "k")

  (* base case *)
   apply (simp)

  (* step case *)    
  apply (rename_tac k)
  apply (intro allI impI, simp)

  (* n \<in> N *)
  apply (subgoal_tac "EX n. n:N")
   apply (erule exE)
   apply (drule_tac x="{m. (m,n):E^+}" in spec)
   apply (simp)
   apply (simp add:finite_M)
   apply (drule mp)
    apply (drule_tac x="n" in bspec)
    apply (simp)
    apply (elim bexE conjE)
    apply (rule_tac x="n'" in exI)
    apply (simp)

(* |M|< k*)
   apply (insert card_M_k)
   apply (drule_tac x="{m. (m,n):E^+}" in spec)
   apply (drule_tac x="N" in spec)
   apply (rotate_tac -1)
   apply (drule_tac x="n" in spec)
   apply (rotate_tac -1)
   apply (drule_tac x="k" in spec)
   apply (simp add:finite_M)

(* M\<le>N *)
   apply (rotate_tac -1)
   apply (drule mp)
    apply (insert dg_plus1)
    apply (drule_tac x="N" in spec)
    apply (drule_tac x="E" in spec)
    apply (simp add:subset_iff)
   apply (erule contrapos_pp)
   apply (rotate_tac -3)

   apply (drule mp)
    apply (erule rem_asmE)
    apply (insert not_in_M)
    apply (drule_tac x="E" in spec)
    apply (drule_tac x="{m. (m,n):E^+}" in spec)
    apply (drule_tac x="n" in spec)
    apply (simp)
   apply (rotate_tac -1)
   apply (erule rem_asmE)
   apply (erule rem_asmE)
   apply (erule contrapos_nn)
   apply (simp)
   apply (drule_tac x="E Int ({m. (m,n):E^+} \<times> {m. (m,n):E^+})" in spec)
   apply (simp)

   apply (drule mp)
    apply (simp add:dg_def)

   apply (drule mp)
    apply (intro allI impI conjI)
    apply (insert m_exsist_E)
    apply (drule_tac x="{m. (m,n):E^+}" in spec)
    apply (rotate_tac -1)
    apply (drule_tac x="na" in spec)
    apply (rotate_tac -1)
    apply (drule_tac x="n" in spec)
    apply (drule_tac x="E" in spec)
    apply (drule_tac x="N" in spec)
    apply (simp)
    apply (drule mp)
     apply (intro allI impI conjI)
     apply (drule_tac x="n1" in bspec)
     apply (simp)
     apply (elim bexE conjE)
     apply (rule_tac x="n'" in exI)
     apply (simp)
    apply (drule mp, force)
    apply (drule mp)
     apply (insert dg_plus1)
     apply (drule_tac x="N" in spec)
     apply (drule_tac x="E" in spec)
     apply (simp add:subset_iff)
    apply (elim exE conjE)
    apply (simp) 
    apply (rule_tac x="m'" in exI)
    apply (simp)
   apply (rule cycle_subset_FE)
    defer
    apply (simp)
   apply (force)
  apply (simp)
  done


(* ----------------------------------------- *
 |          iwata Proposition 5.1.2          |
 * ----------------------------------------- *)

theorem enable_nonempty:
  "finite Blks ==> dag Blks Deps ==> S < Blks ==> enable Blks Deps S ~= {}"
  apply (simp add:dag_def)

(*case src Blks Deps n <= S*)
  apply (case_tac "EX n. n : (Blks - S) & src Blks Deps n <= S")
   apply (simp)

   apply (simp add:enable_def)
   apply (elim exE conjE disjE)
   apply (rule_tac x="n" in exI)
   apply (simp)

(*case ~src Blks Deps n <= S*)
  apply (subgoal_tac "ALL m. m : (Blks - S) --> (EX m': (Blks - S). (m',m):Deps)")
   apply (insert dag_cycle[of "card (Blks-S)"])
   apply (drule_tac x="Blks-S" in spec)
   apply (drule_tac x="Deps-((Blks\<times>S)Un(S\<times>Blks))" in spec)
   apply (simp)
   apply (drule mp)
    apply (force)
   apply (drule mp)
    apply (simp add:dg_def)
    apply (force)
   apply (elim exE conjE disjE)
   apply (erule contrapos_np)
   apply (rule cycle_subset_FE)
    defer
    apply (simp)
   apply (simp add:src_def)
   apply (simp add:subset_iff)
   apply (elim exE conjE disjE)
   apply (intro allI impI conjI)
   apply (drule_tac x="m" in spec)
   apply (simp)
   apply (elim exE conjE disjE)
   apply (rule_tac x="t" in bexI)
    apply (simp)
   apply (simp)
  apply (simp)
  done

lemma enable_nonempty_all:
  "ALL S. finite Blks --> dag Blks Deps --> S < Blks --> enable Blks Deps S ~= {}"
  apply (simp add: enable_nonempty)
  done

 end
