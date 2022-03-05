            (*-------------------------------------------*
            |                                            |
            |            Liveness of ParaCtrl            |
            |                                            |
            *-------------------------------------------*)

theory ParaCtrl_all
imports ParaCtrl_safe SeqCtrl_all CSP_wfsim
begin

(*************************************************************

         1.ParaAlgo_weak_sim
         2. 
         3. 
         4. 

 *************************************************************)

(* ------------------------------------ *
 |              lemmas                  |
 * ------------------------------------ *)

lemma ParaAlgo_wfs_STST:
  " ALL P Q e.
       P = (STOP |[ComFin]| STOP) ~~ Com --> 
       Q = STOP -->  Asn (Suc 0) Int Asn 2 = {}
     --> Asn (Suc 0) Un Asn 2 = Blks --> Q ---e--->+ --> P ---e--->+"
  apply (simp)
  apply (intro allI impI)
  apply (simp add: trn_ex_def)
  apply (erule exE)
  apply (erule trn.cases,auto)
  done

lemma ParaAlgo_wfs_BfrBfr_ExtCh2:
  " ALL S x n.
(x : Asn (Suc 0) | x : Asn 2)-->
       n : enable (Asn (Suc 0) Un Asn 2) Deps S -->
       S <= Asn (Suc 0) \<union> Asn 2 -->
       Asn (Suc 0) Int Asn 2 = {} -->
       Blks = Asn (Suc 0) Un Asn 2 -->
      ~ x : S -->
      ( EX x. ($Bfr (Asn (Suc 0) \<union> Asn 2) Deps Asn (Suc 0) S |[ComFin]| $Bfr (Asn (Suc 0) \<union> Asn 2) Deps Asn 2 S) ~~ Com 
            ---(Ev (blk n))---> x)"

  apply (intro allI impI)

  apply(case_tac "n : Asn(Suc 0)")
   apply (rule_tac x="($Aft Blks Deps Asn (Suc 0) S n|[ComFin]|$Bfr Blks Deps Asn 2 S)~~Com" in exI)
   apply (simp add: Bfr_Bfr_trn_1)

(* case2 *)
  apply(case_tac "n : Asn 2")
  apply (rule_tac x="($Bfr Blks Deps Asn (Suc 0) S|[ComFin]|$Aft Blks Deps Asn 2 S n)~~Com" in exI)
   apply (simp add: Bfr_Bfr_trn_2)

  apply (simp add: enable_def)
  done


lemma ParaAlgo_wfs_BfrBfr:
  " ALL P S Q e.
       P = ($Bfr Blks Deps Asn (Suc 0) S |[ComFin]| $Bfr Blks Deps Asn 2 S) ~~ Com --> 
       Q = $Seq Blks Deps S --> S <= Blks --> Asn (Suc 0) Int Asn 2 = {}
     --> Asn (Suc 0) Un Asn 2 = Blks --> Q ---e--->+ --> P ---e--->+"
  apply (simp)
  apply (intro allI impI)
  apply (simp add: trn_ex_def)
  apply (erule exE)
  apply (insert Seq_trn[of Blks Deps])
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="e" in spec)
   apply (drule_tac x="P'" in spec)
  apply (simp)
  apply (case_tac "S = Blks")
   apply (simp)

   (* finish *)
     apply (rule_tac x="(STOP|[ComFin]|STOP)~~Com" in exI)
     apply (simp add: Bfr_Bfr_trn_finish)

   (* blk n *)
     apply (simp)
     apply (elim conjE exE)
     apply (simp)

    (* case1 *)
      apply(case_tac "n : Asn(Suc 0)")
      apply (rule_tac x="($Aft Blks Deps Asn (Suc 0) S n|[ComFin]|$Bfr Blks Deps Asn 2 S)~~Com" in exI)
      apply (simp add: Bfr_Bfr_trn_1)

    (* case2 *)
      apply(case_tac "n : Asn 2")
      apply (rule_tac x="($Bfr Blks Deps Asn (Suc 0) S|[ComFin]|$Aft Blks Deps Asn 2 S n)~~Com" in exI)
      apply (simp add: Bfr_Bfr_trn_2)

      apply (simp add: enable_def)
      apply (force)
  done


lemma ParaAlgo_wfs_AftBfr:
  " ALL P S n Q e.
       P = ($Aft Blks Deps Asn (Suc 0) S n |[ComFin]| $Bfr Blks Deps Asn 2 S) ~~ Com --> 
       Q = $Seq Blks Deps (insert n S) --> n : Blks --> ~(n : S) --> n : Asn (Suc 0) --> S <= Blks --> Asn (Suc 0) Int Asn 2 = {}
     --> Asn (Suc 0) Un Asn 2 = Blks --> P ---Tau--->+"

  apply (simp)
  apply (intro allI impI)
  apply (simp add: trn_ex_def)

  apply (rule_tac x="($Bfr (Asn (Suc 0) \<union> Asn 2) Deps Asn (Suc 0) (S Un {n})
            |[ComFin]|$Bfr (Asn (Suc 0) \<union> Asn 2) Deps Asn 2 (S Un {n}))~~Com" in exI)
  apply (rule Hide2)
  apply (rule conjI)
   apply (simp)
   apply (rule Para3)

(* Aft --com--> Bfr*)
   apply (rule conjI)
    apply (rule PName)
    apply (simp)
    apply (rule ExtCh1)
    apply (rule Prefix)

(* Bfr --com--> Bfr*)
   apply (rule conjI)
    apply (rule PName)
    apply (simp)
    apply (rule ExtCh2)
    apply (rule If1)
    apply (rule conjI)
     apply (rule ExtCh2)
     apply (rule NatExtCh1)
     apply (simp add: co_def)
     apply (rule Prefix)
    apply (force)
   apply (simp add: ComFin_def)
   apply (simp add: Com_def)
  apply (simp add: Com_def)
  done



lemma ParaAlgo_wfs_BfrAft:
  " ALL P S m Q e.
       P = ($Bfr Blks Deps Asn (Suc 0) S  |[ComFin]| $Aft Blks Deps Asn 2 S m) ~~ Com --> 
       Q = $Seq Blks Deps (insert m S) --> m : Blks --> ~(m : S) --> m : Asn 2 -->S <= Blks --> Asn (Suc 0) Int Asn 2 = {}
     --> Asn (Suc 0) Un Asn 2 = Blks --> P ---Tau--->+"

  apply (simp)
  apply (intro allI impI)
  apply (simp add: trn_ex_def)

  apply (rule_tac x="($Bfr (Asn (Suc 0) \<union> Asn 2) Deps Asn (Suc 0) (S Un {m})
            |[ComFin]|$Bfr (Asn (Suc 0) \<union> Asn 2) Deps Asn 2 (S Un {m})) ~~ Com" in exI)
  apply (subgoal_tac "S ~= Blks") 
  apply (simp add: Bfr_Aft_trn_tau)
  apply (force)
  done



lemma ParaAlgo_wfs_AftAft:
  " ALL P S n m Q e.
       P = ($Aft Blks Deps Asn (Suc 0) S n |[ComFin]| $Aft Blks Deps Asn 2 S m) ~~ Com --> 
       Q = $Seq Blks Deps (insert n (insert m S)) --> n : Blks --> ~(n : S) --> n : Asn (Suc 0) -->
       m : Blks --> ~(m : S) --> m : Asn 2 -->
       S <= Blks --> Asn (Suc 0) Int Asn 2 = {}
     --> Asn (Suc 0) Un Asn 2 = Blks -->  P ---Tau--->+"

  apply (simp)
  apply (intro allI impI)
  apply (simp add: trn_ex_def)
  apply (rule_tac x="($Bfr (Asn (Suc 0) \<union> Asn 2) Deps Asn (Suc 0) (S Un {n})
            |[ComFin]|$Aft (Asn (Suc 0) \<union> Asn 2) Deps Asn 2 (S Un {n}) m) ~~ Com" in exI)
  apply (simp add: Aft_Aft_trn_tau_1)
  done



lemma ParaAlgo_wfs_ParaSeq:
  " ALL P Q e.
       P =  ParaCtrl Blks Deps Asn --> 
       Q = SeqCtrl Blks Deps -->  Asn (Suc 0) Int Asn 2 = {}
     --> Asn (Suc 0) Un Asn 2 = Blks --> Q ---e--->+ --> P ---e--->+"
  apply (simp)
  apply (intro allI impI)
  apply (simp add:ParaCtrl_def)
  apply (simp add:SeqCtrl_def)
  apply (insert ParaAlgo_wfs_BfrBfr[of Blks Deps Asn])
  apply (drule_tac x="($Bfr Blks Deps Asn (Suc 0) {} |[ComFin]| $Bfr Blks Deps Asn 2 {}) ~~ Com" in spec)
  apply (drule_tac x="{}" in spec)
  apply (drule_tac x="$Seq Blks Deps {}" in spec)
  apply (drule_tac x="e" in spec)
  apply (simp)
  done



lemma ParaAlgo_wfs_sim:
  " ALL P Q e. Asn (Suc 0) \<inter> Asn 2 = {} --> Asn (Suc 0) \<union> Asn 2 = Blks --> (P, Q) \<in> Sim Blks Deps Asn
 --> \<not> P ---e--->+ --> (P ---Tau--->+ | \<not> Q ---e--->+) "
  apply (intro impI allI)
  apply (simp add: Sim_def)

(* STOP[]STOP *)
  apply (erule disjE)
   apply (rule disjI2)
   apply (rotate_tac 2)
   apply (erule contrapos_nn) (*taiguu n,p*)
   apply (insert ParaAlgo_wfs_STST[of Asn Blks])
   apply (drule_tac x="P" in spec)
   apply (drule_tac x="Q" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
  apply (rotate_tac -1)
  apply (erule rem_asmE)

(* Para[]Seq *)
  apply (erule disjE)
   apply (rule disjI2)
   apply (rotate_tac 2)
   apply (erule contrapos_nn)
   apply (insert ParaAlgo_wfs_ParaSeq[of Blks Deps Asn])
   apply (drule_tac x="P" in spec)
   apply (drule_tac x="Q" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
  apply (rotate_tac -1)
  apply (erule rem_asmE)

(* Bfr[]Bfr *)
  apply (erule disjE)
   apply (elim exE conjE)
   apply (rule disjI2)
   apply (erule contrapos_nn)
   apply (insert ParaAlgo_wfs_BfrBfr[of Blks Deps Asn])
   apply (drule_tac x="P" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="Q" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
  apply (rotate_tac -1)
  apply (erule rem_asmE)

(* Aft[]Bfr *)
  apply (erule disjE)
   apply (elim exE conjE)
   apply (rule disjI1)
   apply (insert ParaAlgo_wfs_AftBfr[of Blks Deps Asn])
   apply (drule_tac x="P" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="n" in spec)
   apply (drule_tac x="Q" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
  apply (rotate_tac -1)
  apply (erule rem_asmE)

(* Bfr[]Aft *)
  apply (erule disjE)
   apply (elim exE conjE)
   apply (rule disjI1)
   apply (insert ParaAlgo_wfs_BfrAft[of Blks Deps Asn])
   apply (drule_tac x="P" in spec)
   apply (drule_tac x="S" in spec)
   apply (drule_tac x="m" in spec)
   apply (drule_tac x="Q" in spec)
   apply (drule_tac x="e" in spec)
   apply (simp)
  apply (rotate_tac -1)
  apply (erule rem_asmE)

(* Aft[]Aft *)
  apply (elim exE conjE)
  apply (rule disjI1)
  apply (insert ParaAlgo_wfs_AftAft[of Blks Deps Asn])
  apply (drule_tac x="P" in spec)
  apply (drule_tac x="S" in spec)
  apply (drule_tac x="n" in spec)
  apply (drule_tac x="m" in spec)
  apply (drule_tac x="Q" in spec)
  apply (drule_tac x="e" in spec)
  apply (simp)
  done



(*lemma 5.3.1*)
lemma Sim_wfsim:
  "Asn 1 \<inter> Asn 2 = {} ==> Asn 1 Un Asn 2 = Blks
   ==> weak_failures_sim (Sim Blks Deps Asn)"
  apply (simp add: weak_failures_sim_def)
  apply (intro allI impI conjI)

(* weak_sim *)   
   apply (insert ParaAlgo_ws_sim[of Asn Blks Deps])
   apply (drule_tac x="P" in spec)
   apply (drule_tac x="e" in spec)
   apply (drule_tac x="P'" in spec)
   apply (drule_tac x="Q" in spec)
   apply (simp)
  apply (rotate_tac -1)
  apply (erule rem_asmE)

(* weak_failures_sim *)
  apply (insert ParaAlgo_wfs_sim[of Asn Blks Deps])
  apply (drule_tac x="P" in spec)
  apply (drule_tac x="Q" in spec)
  apply (drule_tac x="e" in spec)
  apply (simp)
  done



(*proposition 5.3.2*)

theorem SeqCtrl_refF_ParaCtrl:
  " Asn 1 \<inter> Asn 2 = {} \<Longrightarrow> Asn 1 \<union> Asn 2 = Blks
    \<Longrightarrow> SeqCtrl Blks Deps [F= ParaCtrl Blks Deps Asn"
  apply (rule wfsim_refF[of "Sim Blks Deps Asn"])
  apply (simp add: Sim_wfsim)
  apply (simp add: Sim_def)
  done


(* ----------------------------------------- *
 |                deadlock free              |
 * ----------------------------------------- *)

theorem ParaCtrl_DeadlockFree:
  "finite Blks ==> dag Blks Deps 
   ==> Asn 1 Int Asn 2 = {} ==> Asn 1 Un Asn 2 = Blks
   ==> DeadlockFree (ParaCtrl Blks Deps Asn) (obsEvent Blks) finish"
  apply (insert SeqCtrl_refF_ParaCtrl[of Asn Blks Deps])
  apply (simp)
  apply (insert SeqCtrl_DeadlockFree[of Blks Deps])
  apply (simp)
  apply (simp add: DeadlockFree_refF)
  done

end
