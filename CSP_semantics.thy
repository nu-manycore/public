           (*-------------------------------------------*
            |                                           |
            |      LW-CSP-Prover on Isabelle2021        |
            |                                           |
            *-------------------------------------------*)

theory CSP_semantics
imports CSP_syntax CSP_trace
begin

(*************************************************************

         1. Operational semantics of CSP
         2. Traces
         3. Trace refinement
         4. 

 *************************************************************)

(* ----------------------------------------- *
 |       Operational semantics of CSP        |
 |           (all the transitions)           |
 * ----------------------------------------- *)

inductive
   trn :: "('p,'a) proc \<Rightarrow> 'a event \<Rightarrow> ('p,'a) proc \<Rightarrow> bool"
                     ("(1_ /---_---> _)" [60,1000,61] 61)
where
   Prefix:
    "a -> P ---(Ev a)---> P" 
 | ExtCh1:
    "P ---(Ev a)---> P' \<Longrightarrow>
     P [+] Q ---(Ev a)---> P'" 
 | ExtCh2:
    "Q ---(Ev a)---> Q' \<Longrightarrow>
     P [+] Q ---(Ev a)---> Q'" 
 | ExtCh3:
    "P ---Tau---> P' \<Longrightarrow>
     P [+] Q ---Tau---> P' [+] Q" 
 | ExtCh4:
    "Q ---Tau---> Q' \<Longrightarrow>
     P [+] Q ---Tau---> P [+] Q'" 
 | IntCh1:
    "P |~| Q ---Tau---> P" 
 | IntCh2:
    "P |~| Q ---Tau---> Q" 
 | NatExtCh1:
    "Pf n ---(Ev a)---> P' \<and> n \<in> N \<Longrightarrow>
     [nat] :N .. Pf ---(Ev a)---> P'" 
 | NatExtCh2:
    "Pf n ---Tau---> P' \<and> n \<in> N \<Longrightarrow>
     [nat] :N .. Pf ---Tau---> 
     [nat] :N ..(%m. if n=m then P' else Pf m)" 
 | RepIntCh:
    "a \<in> X \<Longrightarrow>
     !! :X .. Pf ---Tau---> Pf a" 
 | If1:
    "P ---e---> P' \<and> b \<Longrightarrow>
     IF b THEN P ELSE Q ---e---> P'" 
 | If2:
    "Q ---e---> Q' \<and> \<not>b \<Longrightarrow>
     IF b THEN P ELSE Q ---e---> Q'" 
 | Para1:
    "P ---e---> P' \<and> e \<notin> Ev ` X \<Longrightarrow>
     P |[X]| Q ---e---> P' |[X]| Q" 
 | Para2:
    "Q ---e---> Q' \<and> e \<notin> Ev ` X \<Longrightarrow>
     P |[X]| Q ---e---> P |[X]| Q'" 
 | Para3:
    "P ---(Ev a)---> P' \<and> Q ---(Ev a)---> Q' \<and> a \<in> X \<Longrightarrow>
     P |[X]| Q ---(Ev a)---> P' |[X]| Q'" 
 | Hide1:
    "P ---e---> P' \<and> e \<notin> Ev ` X \<Longrightarrow>
     P ~~ X ---e---> P' ~~ X" 
 | Hide2:
    "P ---(Ev a)---> P' \<and> a \<in> X \<Longrightarrow>
     P ~~ X ---Tau---> P' ~~ X"
 | Ren1:
    "P ---(Ev a)---> P' \<and> (a,b) \<in> r \<Longrightarrow>
     P [[r]] ---(Ev b)---> P' [[r]]" 
 | Ren2:
    "P ---e---> P' \<and> e \<notin> Ev ` fst ` r \<Longrightarrow>
     P [[r]] ---e---> P' [[r]]" 
 | PName:
    "PNfun p ---e---> P' \<Longrightarrow>
     $p ---e---> P'"

(*OK*)
(* a transition to P' for some P' *)

definition
  trn_ex :: "('p,'a) proc => 'a event => bool"
               ("(1_ /---_--->+)" [60,1000] 61)
where
  "P ---e--->+ == (EX P'. P ---e---> P')" 

(* ----------------------------------------- *
 |              Traces model                 |
 * ----------------------------------------- *)

(* Sequential transition *)

inductive
  seq_trn :: "('p,'a) proc => 'a ev_list => ('p,'a) proc => bool"
                     ("(1_ /---_--->> _)" [60,1000,61] 61)
where
   Nil:
    "P ---[]--->> P" 
 | Base:
    "P ---e---> P' ==>
     P ---[e]--->> P'"
 | Step:
    "(EX P1 e s. P ---e---> P1 & P1 ---s--->> P' & s' = e#s) ==>
     P ---s'--->> P'"

(* the set of traces *)

definition
  traces  :: "('p,'a) proc => 'a list set"
where
  "traces(P) == {t. EX s P'. t = rem_tau(s) & P ---s--->> P'}"

(* trace-refinement *)

definition
  refT :: "('p,'a) proc => ('q,'a) proc => bool"
                               ("(0_ /[T= /_)" [51,50] 50)
  where
  "P1 [T= P2 == traces(P2) <= traces(P1)"
  
definition
  eqT :: "('p,'a) proc => ('q,'a) proc => bool"
                               ("(0_ /=T /_)" [51,50] 50)
  where
  "P1 =T P2 == traces(P1) = traces(P2)"

(* ----------------------------------------- *
 |             failures model                |
 * ----------------------------------------- *)

definition
  stable ::"('p,'a) proc => bool"
where
  "stable(P) == (~ (P ---Tau--->+))"

definition
  refs ::"('p,'a) proc => 'a set"
where
  "refs(P) == {a. ~(P ---(Ev a)--->+) & stable(P)}"

definition
  failures ::"('p,'a) proc => ('a list * 'a set) set"
where
  "failures(P) 
    == {(t,X). EX s P'. t = rem_tau(s) & stable(P') 
                     & P---s--->> P' & X <= refs(P')}"

definition
  refF :: "('p,'a) proc => ('q,'a) proc => bool"
                               ("(0_ /[F= /_)" [51,50] 50)
  where
  "P1 [F= P2 == (  (traces(P2) <= traces(P1)) 
                 & (failures(P2) <= failures(P1)))"


definition
  DeadlockFree ::"('p,'a) proc => 'a set => 'a => bool"
where
  "DeadlockFree P E f
    == ALL t X. (t,X):failures(P) --> ( E ~= X | f : set t)"

(* ----------------------------------------- *
 |           Weak transition (Tau)           |
 * ----------------------------------------- *)

(* tau transition *)

definition
  tau_trn :: "('p,'a) proc => ('p,'a) proc => bool"
                     ("(1_ /====> _)" [60,61] 61)
where
  "P ====> P' == EX s. P ---s--->> P' & rem_tau(s) = []" 

(* weak transition *)

definition
  weak_trn :: "('p,'a) proc => 'a event => ('p,'a) proc => bool"
                     ("(1_ /===_===> _)" [60,1000, 61] 61)
where
  "P ===e===> P' == EX P1 P2. P ====> P1 & P1 ---e---> P2 & P2 ====> P'" 

(* rem weak transition *)

definition
  weak_tau_trn :: "('p,'a) proc => 'a event => ('p,'a) proc => bool"
                     ("(1_ /===^_===> _)" [60,1000, 61] 61)
where
  "P ===^e===> P' == (EX a. P ===(Ev a)===> P' & e = Ev a) | (P ====> P' & e = Tau)"


(* ----------------------------------------- *
 |                    lemmas                 |
 * ----------------------------------------- *)

lemma DeadlockFree_refF:
  "DeadlockFree P1 E f ==> P1 [F= P2 ==> DeadlockFree P2 E f"
  apply (simp add: DeadlockFree_def)
  apply (simp add: refF_def)
  apply (intro allI impI)
  apply (drule_tac x="t" in spec)
  apply (auto)
  done

lemma seq_trn_nil:
  "(P ---[]--->> P') = (P = P')"
  apply (rule iffI)
   (* --> *)
   apply (erule seq_trn.cases)
     apply (simp_all)
   (* <-- *)
   apply (rule seq_trn.intros)
  done


lemma seq_trn_step:
  "(P ---(a#s)--->> P') = 
   (EX P1. P ---a---> P1 & P1---s--->> P')" 
  apply (rule iffI)

   (* --> *)
   apply (erule seq_trn.cases)
     apply (simp_all)

    apply (rule_tac x="P'a" in exI)
    apply (simp)
    apply (rule seq_trn.intros)

   apply (elim exE conjE)
   apply (rule_tac x="P1" in exI)
   apply (simp)

   (* <-- *)

  apply (rule Step)
  apply (elim exE conjE)   (* apply (auto) *)
  apply (simp)
  apply (rule_tac x="P1" in exI)
  apply (simp)
  done

lemma seq_trn_base:
  "(P ---[Ev a]--->> P') = (P ---(Ev a)---> P')"
  apply (insert seq_trn_step[of P "Ev a" "[]" P'])
  apply (simp add: seq_trn_nil) 
  done

lemma seq_trn_append_ALL:
  "ALL s1 s2 P P'.
   (P ---(s1@s2)--->> P') = 
   (EX P1. P ---s1--->> P1 & P1---s2--->> P')"
  apply (rule allI)
  apply (induct_tac s1)

   (* nil case *)
   apply (simp add: seq_trn_nil)

  (* step case *)
  apply (simp)
  apply (intro allI)
  apply (simp add: seq_trn_step)
  apply (rule iffI)

  (* --> *)
   apply (elim exE conjE)
   apply (rule_tac x="P1a" in exI)
   apply (simp)
   apply (rule_tac x="P1" in exI)
   apply (simp)

  (* <-- *)
  apply (elim exE conjE)
  apply (rule_tac x="P1a" in exI)
  apply (simp)
  apply (rule_tac x="P1" in exI)
  apply (simp)
  done

lemma seq_trn_append:
  "(P ---(s1@s2)--->> P') = 
   (EX P1. P ---s1--->> P1 & P1---s2--->> P')"
  apply (simp add: seq_trn_append_ALL)
  done

lemma seq_trn_conc:
  "(P ---(Ev a#s2)--->> P') = 
   (EX P1. P ---(Ev a)---> P1 & P1---s2--->> P')"
  apply (insert seq_trn_append[of P "[Ev a]" "s2" P'])
  apply (simp add: seq_trn_base)
  done

lemma seq_trn_STOP:
  "(STOP ---t--->> P') = (t = [] & P' = STOP)"
  apply (rule iffI)
   (* --> *)
   apply (erule seq_trn.cases, auto)
   apply (erule trn.cases, auto)+
   (* <-- *)
   apply (simp add: seq_trn_nil)
  done


lemma weak_trn_seq_trn:
  "(P ===(Ev a)===> P') = 
   (EX t. P ---t--->> P' & rem_tau t = [a])" 
  apply (simp add: weak_trn_def)
  apply (simp add: tau_trn_def)
  apply (rule iffI)

   (* --> *)
   apply (elim exE conjE)
   apply (rule_tac x="s@[Ev a]@sa" in exI)
   apply (simp add: seq_trn_append)
   apply (simp add: rem_tau_append)
   apply (rule_tac x="P1" in exI)
   apply (simp)
   apply (rule Step)
   apply (simp)
   apply (rule_tac x="P2" in exI)
   apply (simp)

   (* <-- *)
  apply (simp add: rem_tau_ev)
  apply (elim exE conjE)
  apply (simp add: seq_trn_append)
  apply (elim exE conjE)
  apply (simp add: seq_trn_conc)
  apply (elim exE conjE)
  
  apply (rule_tac x="P1" in exI)
  apply (rule conjI)
   apply (rule_tac x="s1" in exI)
   apply (simp)
  apply (rule_tac x="P1a" in exI)
  apply (simp)
  apply (rule_tac x="s2" in exI)
  apply (simp)
  done


lemma weak_tau_trn_seq_trn:
  "(P ===^e===> P') = 
   (EX t. P ---t--->> P' & rem_tau t = obs e)" 
  apply (simp add: weak_tau_trn_def)
  apply (simp add: weak_trn_seq_trn)
  apply (rule iffI)

   (* --> *)
   apply (elim disjE exE conjE)
    apply (rule_tac x="t" in exI)
    apply (simp)

   apply (simp add: tau_trn_def)

   (* <-- *)
  apply (insert ev_or_tau)
  apply (drule_tac x="e" in spec)
  apply (elim disjE exE conjE)

   (* Ev *)
  apply (simp)
   apply (rule_tac x="t" in exI)
   apply (simp)

   (* Tau *)
  apply (simp add: tau_trn_def)
  apply (rule_tac x="t" in exI)
  apply (simp)
  done

lemma weak_tau_trn_id:
  "P ===^Tau===> P" 
  apply (simp add: weak_tau_trn_seq_trn)
  apply (rule_tac x="[]" in exI)
  apply (simp)
  apply (simp add: seq_trn_nil)
  done

lemma stop_trn_asm:
"STOP ---a---> P' ==> x"
  apply (erule trn.cases, auto)
  done

lemma stop_no_trn:
"~(STOP ---a---> P')"
  apply (case_tac "~(STOP ---a---> P')")
   apply (simp)
  apply (simp)
  apply (rule stop_trn_asm)
  apply (simp)
  done

lemma stop_seq_trn:
"ALL t P'. STOP ---t--->> P' --> t = [] & P' = STOP"
  apply (rule allI)
  apply (rule allI)
  apply (induct_tac t)
   apply (simp)
   apply (simp add: seq_trn_nil)

  apply (simp)
  apply (simp add: seq_trn_step)
  apply (rule allI)
  apply (rule impI)
  apply (simp add: stop_no_trn)
  done

end
