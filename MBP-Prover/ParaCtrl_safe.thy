           (*-------------------------------------------*
            |                                           |
            |            Safety of ParaCtrl             |
            |                                           |
            *-------------------------------------------*)

theory ParaCtrl_safe
  imports MBP_algo CSP_wsim SeqCtrl_safe
begin

(*************************************************************

         1. ParaAlgo
         2. 
         3. 
         4. 

 *************************************************************)
definition
  Sim :: "nodes => edges => (nat => nodes) => 
         ((ParaName,Event)proc * (SpecName,Event)proc) set"
  where
    Sim_def : "Sim Blks Deps Asn 
            == {(ParaCtrl Blks Deps Asn,SeqCtrl Blks Deps)}
           Un {PQ. EX P Q S. PQ = (P,Q) &
               P = ($Bfr Blks Deps Asn 1 S |[ComFin]| $Bfr Blks Deps Asn 2 S) ~~ Com &
               Q = $Seq Blks Deps S & S <= Blks}
           Un {PQ. EX P Q S S' n. PQ = (P,Q) &
               P = ($Aft Blks Deps Asn 1 S n|[ComFin]| $Bfr Blks Deps Asn 2 S) ~~ Com &
               Q = $Seq Blks Deps S' & S' = (S Un {n}) & S' <= Blks & ~(n : S) & n : Asn 1}
           Un {PQ. EX P Q S S' m . PQ = (P,Q) &
               P = ($Bfr Blks Deps Asn 1 S |[ComFin]| $Aft Blks Deps Asn 2 S m) ~~ Com &
               Q = $Seq Blks Deps S' & S' = (S Un {m}) & S' <= Blks & ~(m : S) & m : Asn 2} 
           Un {PQ. EX P Q S S' n m. PQ = (P,Q) &
               P = ($Aft Blks Deps Asn 1 S n|[ComFin]| $Aft Blks Deps Asn 2 S m) ~~ Com &
               Q = $Seq Blks Deps S' & S' = (S Un {n,m}) & S' <= Blks & ~(n : S) 
                   & ~(m : S) & n : Asn 1  & m : Asn 2 }
           Un {PQ. EX P Q. PQ = (P,Q) &
               P = (STOP |[ComFin]| STOP) ~~ Com &
               Q = STOP}
"


(* ------------------------------------ *
 |              lemmas                  |
 * ------------------------------------ *)

(*Bfr[]Bfr*)
lemma ParaAlgo_ws_BfrBfr:
  " ALL P e P' S Q.  P ---e---> P' -->
       P = ($Bfr Blks Deps Asn (Suc 0) S |[ComFin]| $Bfr Blks Deps Asn 2 S) ~~ Com & 
       Q = $Seq Blks Deps S & S <= Blks -->
      ( EX Q'. Q ===^e===> Q' & (P', Q') : Sim Blks Deps Asn)"

  apply (simp)
  apply (intro allI impI)
  apply (erule trn.cases,auto)
   apply (erule trn.cases,auto)
     apply (insert ParaAlgo_Bfr_blk[of Blks Deps Asn])

(*subgoal 1*)
     apply (drule_tac x="e" in spec)
     apply (drule_tac x="Suc 0" in spec)
     apply (drule_tac x="S" in spec)
     apply (drule_tac x="P'" in spec)
     apply (simp)
     apply (elim exE conjE)
     apply (simp)
     apply (rule_tac x="$Seq Blks Deps (S Un {n})" in exI)
     apply (rule conjI)
      apply (simp add: weak_tau_trn_seq_trn)
      apply (rule_tac x="[Ev (blk n)]" in exI)
      apply (simp) 
      apply (rule Base)
      apply (simp add: Seq_trn_blk)
 
     apply (simp add: Sim_def)
     apply (rule disjI2)
     apply (simp add: enable_def)


(*subgoal 2*)
    apply (drule_tac x="e" in spec)
    apply (drule_tac x="2" in spec)
    apply (drule_tac x="S" in spec)
    apply (drule_tac x="Q'" in spec)
    apply (simp)
    apply (elim exE conjE)
    apply (simp)
    apply (rule_tac x="$Seq Blks Deps (S Un {n})" in exI)
    apply (rule conjI)
     apply (simp add: weak_tau_trn_seq_trn)
     apply (rule_tac x="[Ev (blk n)]" in exI)
     apply (simp)
     apply (rule Base)
      apply (simp add: Seq_trn_blk)

    apply (simp add: Sim_def)
    apply (rule disjI2)
    apply (simp add: enable_def)

(*subgoal 3*)
   apply (rotate_tac 5)
   apply (erule rem_asmE)
   apply (insert ParaAlgo_Bfr_blk_finish[of Blks Deps Asn])

   apply (drule_tac x="Ev a" in spec)
   apply (drule_tac x="1" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="P'" in spec)

   apply (insert ParaAlgo_Bfr_blk_finish[of Blks Deps Asn])
   apply (drule_tac x="Ev a" in spec)
   apply (drule_tac x="2" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="Q'" in spec)
   apply (rule_tac x="STOP" in exI)
   apply (rule conjI)
    apply (simp add: weak_tau_trn_seq_trn)
    apply (rule_tac x="[Ev finish]" in exI)
    apply (simp)
    apply (rule Base)
    apply (simp add: Seq_trn_finish)

   apply (simp add: Sim_def)
  apply (simp)

(*subgoal 4*)
  apply (rotate_tac 3)
  apply (erule rem_asmE)
  apply (erule rem_asmE)
  apply (erule trn.cases, auto)

    apply (simp add: ComFin_def)
   apply (simp add: ComFin_def)
  apply (insert ParaAlgo_Bfr_blk_com[of Blks Deps Asn])
  apply (drule_tac x="Ev aa" in spec)
  apply (drule_tac x="Suc 0" in spec)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="P'" in spec)
  apply (insert ParaAlgo_Bfr_blk_com[of Blks Deps Asn])
  apply (drule_tac x="Ev aa" in spec)
  apply (drule_tac x="2" in spec)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="Q'" in spec)
  apply (simp)
  apply (elim exE conjE disjE)
  apply (simp)

  done


(*Afr[]Bfr*)
lemma ParaAlgo_ws_AftBfr:
  "ALL P e P' S n Q . P ---e---> P' -->
       P = ($Aft Blks Deps Asn (Suc 0) S n |[ComFin]| $Bfr Blks Deps Asn 2 S) ~~ Com &
       Q = $Seq Blks Deps (insert n S) 
       & n:Blks & S <= Blks & n ~:S & n:Asn(Suc 0) & Asn 1 Int Asn 2 = {} -->
       (EX Q'. Q ===^e===> Q' & (P', Q') : Sim Blks Deps Asn)"

(*subgoal 1*)
  apply (simp)
  apply (intro allI)
  apply (intro impI)
  apply (erule trn.cases,auto)
   apply (erule trn.cases,auto)

(*Hide1, Para1*)
     apply (insert ParaAlgo_Aft_blk[of Blks Deps Asn])
     apply (drule_tac x="e" in spec)
     apply (drule_tac x="1" in spec)
     apply (drule_tac x="S" in spec)
     apply (drule_tac x="n" in spec)
     apply (drule_tac x="P'" in spec)
     apply (simp)
     apply (erule disjE)
      apply (simp add: Com_def)
     apply (erule exE)
     apply (simp add: Com_def)

(*Hide1, Para2*)
    apply (rotate_tac 8)
    apply (erule rem_asmE)
    apply (insert ParaAlgo_Bfr_blk[of Blks Deps Asn])
    apply (drule_tac x="e" in spec)
    apply (drule_tac x="2" in spec)
    apply (drule_tac x="S" in spec)
    apply (drule_tac x="Q'" in spec)
    apply (simp)
    apply (erule exE)
    apply (elim exE conjE)
    apply (simp)
    apply (rule_tac x="$Seq Blks Deps (S Un {na,n})" in exI)
    apply (rule conjI)
     apply (simp add: weak_tau_trn_seq_trn)
     apply (rule_tac x="[Ev (blk na)]" in exI)
     apply (simp) 
     apply (rule Base)
     apply (rule PName)
     apply (simp)
     apply (rule ExtCh2)
     apply (rule If1)
     apply (rule conjI)
      apply (rule NatExtCh1)
      apply (rule conjI)
       apply (simp)
       apply (rule Prefix)
      apply (simp add: enable_def)
      apply (rule conjI)
       apply (simp add: subset_iff)
      apply (force)
     apply (simp add: enable_def)
     apply (force)
    apply (simp add: Sim_def)
    apply (rule disjI2)
    apply (simp add: enable_def)
    apply (force)

(*Hide1, Para3*)
   apply (rotate_tac 9)
   apply (erule rem_asmE)
   apply (erule rem_asmE)
   apply (insert ParaAlgo_Bfr_blk_finish[of Blks Deps Asn])
   apply (drule_tac x="Ev a" in spec)
   apply (drule_tac x="2" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="Q'" in spec)
   apply (simp)

(*Hide2*)
  apply (rotate_tac 7)
  apply (erule rem_asmE)
  apply (erule rem_asmE)
  apply (erule rem_asmE)
  apply (erule trn.cases,auto)

(*Hide2, Para1*)
    apply (simp add: ComFin_def)

(*Hide2, Para2*)
   apply (simp add: ComFin_def)

(*Hide2, Para3*)
  apply (insert ParaAlgo_Aft_blk[of Blks Deps Asn])
  apply (drule_tac x="Ev aa" in spec)
  apply (drule_tac x="1" in spec)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="n" in spec)
  apply (drule_tac x="P'" in spec)
  apply (simp)
  apply (insert ParaAlgo_Bfr_blk_com[of Blks Deps Asn])
  apply (drule_tac x="Ev aa" in spec)
  apply (drule_tac x="2" in spec)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="Q'" in spec)
  apply (simp)

  apply (elim disjE exE conjE)
   apply (simp)
   apply (rule_tac x=" $Seq Blks Deps (insert n S)" in exI)
   apply (simp add: weak_tau_trn_id)
   apply (simp add:Sim_def)
  apply (simp)

  done


(*Bfr[]Aft*)
lemma ParaAlgo_ws_BfrAft:
  "     ALL P e P' S m Q. P ---e---> P' -->
       P = ($Bfr Blks Deps Asn (Suc 0) S  |[ComFin]| $Aft Blks Deps Asn 2 S m) ~~ Com &
       Q = $Seq Blks Deps (insert m S) 
       & m:Blks & S <= Blks & m ~:S & m:Asn 2 & Asn 1 Int Asn 2 = {}-->
       (EX Q'. Q ===^e===> Q' & (P', Q') : Sim Blks Deps Asn)"
  apply (simp)
  apply (intro allI conjI)
  apply (intro impI)
  apply (erule trn.cases,auto)

(*Hide1*)
   apply (erule trn.cases,auto)

(*Hide1, Para1*)
     apply (insert ParaAlgo_Bfr_blk[of Blks Deps Asn])
     apply (drule_tac x="e" in spec)
     apply (drule_tac x="1" in spec)
     apply (drule_tac x="S" in spec)
     apply (drule_tac x="P'" in spec)
     apply (simp)
     apply (elim exE conjE)
     apply (simp)
     apply (rule_tac x="$Seq Blks Deps (insert n (insert m S))" in exI)
     apply (rule conjI)
      apply (simp add: weak_tau_trn_seq_trn)
      apply (rule_tac x="[Ev (blk n)]" in exI)
      apply (simp) 
      apply (rule Base)
      apply (rule PName)
      apply (simp)
      apply (rule ExtCh2)
      apply (rule If1)
      apply (rule conjI)
       apply (rule NatExtCh1)
       apply (rule conjI)
        apply (simp)
        apply (rule Prefix)
       apply (simp add: enable_def)
       apply (rule conjI)
        apply (simp add: subset_iff)
       apply (force)
      apply (simp add: enable_def)
      apply (force)
     apply (simp add: Sim_def)
     apply (rule disjI2)
     apply (simp add: enable_def)

(*Hide1, Para2*)
    apply (rotate_tac 8)
    apply (erule rem_asmE)
    apply (insert ParaAlgo_Aft_blk[of Blks Deps Asn])
    apply (drule_tac x="e" in spec)
    apply (drule_tac x="2" in spec)
    apply (drule_tac x="S" in spec)
    apply (drule_tac x="m" in spec)
    apply (drule_tac x="Q'" in spec)
    apply (simp)
    apply (erule disjE)
     apply (simp add: Com_def)
    apply (erule exE)
    apply (simp add: Com_def)

(*Hide1, Para3*)
   apply (rotate_tac 9)
   apply (erule rem_asmE)
   apply (erule rem_asmE)
   apply (insert ParaAlgo_Bfr_blk_finish[of Blks Deps Asn])
   apply (drule_tac x="Ev a" in spec)
   apply (drule_tac x="1" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="P'" in spec)
   apply (simp)

(*Hide2*)
  apply (rotate_tac 7)
  apply (erule rem_asmE)
  apply (erule rem_asmE)
  apply (erule rem_asmE)
  apply (erule trn.cases,auto)

(*Hide2, Para1*)
    apply (simp add: ComFin_def)

(*Hide2, Para2*)
   apply (simp add: ComFin_def)

(*Hide2, Para3*)
  apply (insert ParaAlgo_Aft_blk[of Blks Deps Asn])
  apply (drule_tac x="Ev aa" in spec)
  apply (drule_tac x="2" in spec)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="m" in spec)
  apply (drule_tac x="Q'" in spec)
  apply (simp)
  apply (insert ParaAlgo_Bfr_blk_com[of Blks Deps Asn])
  apply (drule_tac x="Ev aa" in spec)
  apply (drule_tac x="1" in spec)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="P'" in spec)
  apply (simp)

  apply (elim disjE exE conjE)
   apply (simp)
   apply (rule_tac x=" $Seq Blks Deps (insert m S)" in exI)
   apply (simp add: weak_tau_trn_id)
   apply (simp add:Sim_def)
  apply (simp)

  done


(*Afr[]Afr p13*)
lemma ParaAlgo_ws_AftAft:
"      ALL P e P' S n m Q. P ---e---> P' -->
       P = ($Aft Blks Deps Asn (Suc 0) S n |[ComFin]| $Aft Blks Deps Asn 2 S m) ~~ Com &
       Q = $Seq Blks Deps(insert n (insert m S)) & n:Blks & m:Blks 
       & S <= Blks & n ~:S & m ~:S & n:Asn 1 & m:Asn 2 & Asn 1 Int Asn 2 = {}-->
       (EX Q'. Q ===^e===> Q' & (P', Q') : Sim Blks Deps Asn)"
  apply (simp)
  apply (intro allI conjI impI)
  apply (erule trn.cases,auto)
(*Hide1*)
   apply (erule trn.cases,auto)

(*Hide1, Para1*)
     apply (insert ParaAlgo_Aft_blk[of Blks Deps Asn])
     apply (drule_tac x="e" in spec)
     apply (drule_tac x="1" in spec)
     apply (drule_tac x="S" in spec)
     apply (drule_tac x="n" in spec)
     apply (drule_tac x="P'" in spec)
     apply (simp)
     apply (erule disjE)
      apply (simp add: Com_def)
     apply (erule exE)
     apply (simp add: Com_def)

(*Hide1, Para2*)
    apply (rotate_tac 11)
    apply (erule rem_asmE)
    apply (insert ParaAlgo_Aft_blk[of Blks Deps Asn])
    apply (drule_tac x="e" in spec)
    apply (drule_tac x="2" in spec)
    apply (drule_tac x="S" in spec)
    apply (drule_tac x="m" in spec)
    apply (drule_tac x="Q'" in spec)
    apply (simp)
    apply (erule disjE)
     apply (simp add: Com_def)
    apply (erule exE)
    apply (simp add: Com_def)

(*Hide1, Para3*)

   apply (drule_tac x="Ev a" in spec)
   apply (drule_tac x="1" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="n" in spec)
   apply (drule_tac x="P'" in spec)

   apply (drule_tac x="Ev a" in spec)
   apply (drule_tac x="2" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="m" in spec)
   apply (drule_tac x="Q'" in spec)
   apply (simp)
   apply (elim disjE)
      apply (simp add: Com_def)
     apply (erule exE)
     apply (simp add: Com_def)
    apply (simp add: Com_def)
   apply (erule exE)
   apply (simp add: Com_def)

(*Hide2*)
  apply (rotate_tac 10)
  apply (erule rem_asmE)
  apply (erule rem_asmE)
  apply (erule trn.cases,auto)

(*Hide2, Para1*)
    apply (insert ParaAlgo_Aft_blk[of Blks Deps Asn])
    apply (drule_tac x="Ev a" in spec)
    apply (drule_tac x="1" in spec)
    apply (drule_tac x="S" in spec)
    apply (drule_tac x="n" in spec)
    apply (drule_tac x="P'" in spec)
    apply (simp)
    apply (elim disjE)
     apply (simp add: ComFin_def)
    apply (erule exE)
    apply (simp add: ComFin_def)

(*Hide2, Para2*)
   apply (rotate_tac 11)
   apply (erule rem_asmE)
   apply (insert ParaAlgo_Aft_blk[of Blks Deps Asn])
   apply (drule_tac x="Ev a" in spec)
   apply (drule_tac x="2" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="m" in spec)
   apply (drule_tac x="Q'" in spec)
   apply (simp)
   apply (erule disjE)
    apply (simp add: ComFin_def)
   apply (erule exE)
   apply (simp add: ComFin_def)

(*Hide2, Para3*)

  apply (drule_tac x="Ev aa" in spec)
  apply (drule_tac x="1" in spec)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="n" in spec)
  apply (drule_tac x="P'" in spec)

  apply (drule_tac x="Ev aa" in spec)
  apply (drule_tac x="2" in spec)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="m" in spec)
  apply (drule_tac x="Q'" in spec)
  apply (simp)

  apply (elim disjE)
     apply (simp)
    apply (erule exE)
    apply (rule_tac x="$Seq Blks Deps (insert n (insert m S))" in exI)
    apply (rule conjI)
     apply (simp add: weak_tau_trn_id)
    apply (simp add:Sim_def)
    apply (force)

   apply (erule exE)
   apply (rule_tac x="$Seq Blks Deps (insert n (insert m S))" in exI)
   apply (rule conjI)
    apply (simp add: weak_tau_trn_id)
   apply (simp add:Sim_def)
   apply (force)
  apply (elim exE)
  apply (simp)
  done



(*Para[]Seq*)
lemma ParaAlgo_ws_ParaSeq:
"ALL P e P' Q. P ---e---> P' -->
       P = ParaCtrl Blks Deps Asn  & Q = SeqCtrl Blks Deps -->
      ( EX Q'. Q ===^e===> Q' & (P', Q') : Sim Blks Deps Asn)"
  apply (simp)
  apply (intro allI impI)
  apply (simp add:ParaCtrl_def)
  apply (simp add:SeqCtrl_def)
  apply (insert ParaAlgo_ws_BfrBfr[of Blks Deps Asn])
  apply (drule_tac x="($Bfr Blks Deps Asn (Suc 0) {} |[ComFin]| $Bfr Blks Deps Asn 2 {}) ~~ Com" in spec)
  apply (drule_tac x="e" in spec)
  apply (drule_tac x="P'" in spec)
  apply (drule_tac x="{}" in spec)
  apply (drule_tac x="$Seq Blks Deps {}" in spec)
  apply (simp)
  done



lemma ParaAlgo_ws_sim:
  " ALL P e P' Q. Asn 1 Int Asn 2 = {}  --> P ---e---> P' --> (P, Q) : Sim Blks Deps Asn 
    --> P ---e---> P' --> (EX Q'. Q ===^e===> Q' & (P', Q') : Sim Blks Deps Asn)"
  apply (intro impI allI)
  apply (simp add: Sim_def)
  apply (erule disjE)
   apply (insert ParaAlgo_ws_STST)
   apply (drule_tac x="P" in spec)
   apply (drule_tac x="e" in spec)
   apply (drule_tac x="P'" in spec)
   apply (simp)

  apply (rotate_tac -1)
  apply (erule rem_asmE)
  apply (erule disjE)
   apply (insert ParaAlgo_ws_ParaSeq[of Blks Deps Asn])
   apply (drule_tac x="P" in spec)
   apply (drule_tac x="e" in spec)
   apply (drule_tac x="P'" in spec)
   apply (drule_tac x="Q" in spec)
   apply (simp)
   apply (erule exE)
   apply (rule_tac x="Q'" in exI)
   apply (simp add: Sim_def)

  apply (rotate_tac -1)
  apply (erule rem_asmE)
  apply (erule disjE)
   apply (erule exE)
   apply (insert ParaAlgo_ws_BfrBfr[of Blks Deps Asn])
   apply (drule_tac x="P" in spec)
   apply (drule_tac x="e" in spec)
   apply (drule_tac x="P'" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="Q" in spec)
   apply (simp)
   apply (erule exE)
   apply (rule_tac x="Q'" in exI)
   apply (simp add: Sim_def)

  apply (rotate_tac -1)
  apply (erule rem_asmE)
  apply (erule disjE)
   apply (elim exE)
   apply (insert ParaAlgo_ws_AftBfr[of Blks Deps Asn])
   apply (drule_tac x="P" in spec)
   apply (drule_tac x="e" in spec)
   apply (drule_tac x="P'" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="n" in spec)
   apply (drule_tac x="Q" in spec)
   apply (simp)
   apply (erule exE)
   apply (rule_tac x="Q'" in exI)
   apply (simp add: Sim_def)

  apply (rotate_tac -1)
  apply (erule rem_asmE)
  apply (erule disjE)
   apply (elim exE)
   apply (insert ParaAlgo_ws_BfrAft[of Blks Deps Asn])
   apply (drule_tac x="P" in spec)
   apply (drule_tac x="e" in spec)
   apply (drule_tac x="P'" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="m" in spec)
   apply (drule_tac x="Q" in spec)
   apply (simp)
   apply (erule exE)
   apply (rule_tac x="Q'" in exI)
   apply (simp add: Sim_def)

  apply (rotate_tac -1)
  apply (erule rem_asmE)
  apply (elim exE)
  apply (insert ParaAlgo_ws_AftAft[of Blks Deps Asn])
  apply (drule_tac x="P" in spec)
  apply (drule_tac x="e" in spec)
  apply (drule_tac x="P'" in spec)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="n" in spec)
  apply (drule_tac x="m" in spec)
  apply (drule_tac x="Q" in spec)
  apply (simp)
  apply (erule exE)
  apply (rule_tac x="Q'" in exI)
  apply (simp add: Sim_def)
  done

lemma Sim_weak_sim:
  "Asn 1 \<inter> Asn 2 = {} \<Longrightarrow> weak_sim (Sim Blks Deps Asn)"
  apply (simp add: weak_sim_def)
  apply (intro allI impI)
  apply (insert ParaAlgo_ws_sim[of Asn Blks Deps])
  apply (drule_tac x="P" in spec)
  apply (drule_tac x="e" in spec)
  apply (drule_tac x="P'" in spec)
  apply (drule_tac x="Q" in spec)
  apply (simp)
  done

theorem ParaCtrl_refine_SeqCtrl_traces:
  " Asn 1 Int Asn 2 = {} ==> SeqCtrl Blks Deps [T= ParaCtrl Blks Deps Asn"
  apply (rule weak_sim_traces_ref[of "Sim Blks Deps Asn"])
   apply (simp add:Sim_weak_sim)
  apply (simp add:Sim_def)
  done

theorem Paractrl_safe:
  "Asn 1 Int Asn 2 = {} ==> t:traces(ParaCtrl Blks Deps Asn) ==> k < length(t) 
 ==> (EX n. t!k = blk n & src Blks Deps n <= dones t k)
 | t!k = finish"
  apply (rule Seqctrl_safe)
   apply (insert ParaCtrl_refine_SeqCtrl_traces[of Asn Blks Deps])
   apply (simp)
   apply (simp add:refT_def)
   apply (simp add:subset_iff)
  apply (simp)
  done

end