           (*-------------------------------------------*
            |                                           |
            |         ParaAlgo on LW-CSP-Prover         |
            |                                           |
            *-------------------------------------------*)

theory MBP_algo
imports MBP_base CSP_semantics
begin

(*************************************************************

         1. Spec
         2. 
         3. 
         4. 

 *************************************************************)

(* ----- loop test (process name) ------ *)


datatype ParaName = Bfr nodes edges "nat => nodes"  nat nodes
                    | Aft nodes edges "nat => nodes" nat nodes nat


(*ParaAlgo*)
definition
co :: "nat => nat"
where
co_def : "co c = 3 - c"

definition
Com :: "Event set"
where
Com_def : "Com == {com c c' n| c c' n. True}"
(*Com_def : "Com == {e. EX c c' n. e = com c c' n}"*)

definition
ComFin :: "Event set"
where
ComFin_def : "ComFin == Com Un {finish}"

primrec
  ParaDef :: "ParaName => (ParaName, Event) proc"
  where
  "ParaDef (Bfr Blks Deps Asn c S) 
    = ((S = Blks) &> finish -> STOP)
      [+] (~(S=Blks)) &> 
          ( ( [Nat] n : (enable Blks Deps S Int Asn(c)) .. blk n -> $Aft Blks Deps Asn c S n)
      [+] (com (co(c)) c ? m -> $Bfr Blks Deps Asn c (S Un {m})))"
  |"ParaDef(Aft Blks Deps Asn c S n)
    = (com c (co(c)) ! n -> $Bfr Blks Deps Asn c (S Un {n}))
      [+] (com (co(c)) c ? m  -> $Aft Blks Deps Asn c (S Un {m}) n)"

overloading ParaPNfun ==
  "PNfun :: ParaName => (ParaName, Event) proc"
  begin
definition "PNfun == ParaDef"
end

declare ParaPNfun_def [simp]


definition
  ParaCtrl :: "nodes => edges => (nat => nodes) => (ParaName,Event) proc"
  where
  ParaCtrl_def : "ParaCtrl Blks Deps Asn
                  == ($Bfr Blks Deps Asn 1 {} |[ComFin]| $Bfr Blks Deps Asn 2 {}) ~~ Com"

(* ------------------------------------ *
 |              lemmas                  |
 * ------------------------------------ *)

(*before com1*)
lemma ParaAlgo_Bfr_blk:
  "ALL e c S P'. e ~: Ev`Com & e ~: Ev ` ComFin & $Bfr Blks Deps Asn c S ---e---> P' 
--> (EX n.  n : (enable Blks Deps S Int Asn(c)) & e = Ev (blk n) & P'= $Aft Blks Deps Asn c S n 
 & S ~= Blks)"
  apply (auto)
  apply (erule trn.cases, auto simp add: ComFin_def Com_def)+
  done

(*before finish*)
lemma ParaAlgo_Bfr_blk_finish:
  "ALL e c S P'. e ~: Ev ` Com & e : Ev ` ComFin & $Bfr Blks Deps Asn c S ---e---> P' 
--> ( e = Ev (finish) & P'= STOP & S = Blks)"
  apply (auto)
  apply (erule trn.cases, auto simp add: ComFin_def Com_def)+
  done

(*before com2*)
lemma ParaAlgo_Bfr_blk_com:
  "ALL e c S P'. e : Ev ` Com & $Bfr Blks Deps Asn c S ---e---> P' 
--> (EX m.  e = Ev (com(co(c))c m) & P'= $Bfr Blks Deps Asn c (S Un {m})
 & S ~= Blks)"
  apply (auto)
  apply (erule trn.cases, auto simp add: ComFin_def Com_def)+
  done

(*After*)
lemma ParaAlgo_Aft_blk:
  "ALL e c S n P'.  $Aft Blks Deps Asn c S n ---e---> P' 
-->  e = Ev(com c (co(c)) n)  & P'= $Bfr Blks Deps Asn c (S Un {n}) |
    (EX m.  e = Ev(com (co(c)) c m)  & P'= $Aft Blks Deps Asn c (S Un {m}) n) "
  apply (auto)
  apply (erule trn.cases, auto simp add: ComFin_def Com_def)+
  done

(*STOP[]STOP*)
lemma ParaAlgo_ws_STST:
  "ALL P e P'.  P ---e---> P' -->
       P = (STOP |[ComFin]| STOP) ~~ Com  -->
      False"
  apply (auto)
  apply (erule trn.cases, auto)+
  done

(* existence of transitions *)

lemma Bfr_Bfr_trn_1:
  "n : Asn (Suc 0) ==> n : enable Blks Deps S 
   ==>
    ($Bfr Blks Deps Asn (Suc 0) S 
        |[ComFin]| $Bfr Blks Deps Asn 2 S) ~~ Com 
     ---(Ev (blk n))--->
    ($Aft Blks Deps Asn (Suc 0) S n 
        |[ComFin]| $Bfr Blks Deps Asn 2 S) ~~ Com"
  apply (rule Hide1)
  apply (rule conjI)
   apply (rule Para1)
   apply (rule conjI)
    apply (rule PName)
    apply (simp)
    apply (rule ExtCh2)
    apply (rule If1)
    apply (rule conjI)
     apply (rule ExtCh1)
     apply (rule NatExtCh1) (* ?90 = n <— S b x n *)
     apply (rule conjI)
      apply (rule Prefix)
     apply (simp)
     apply (simp add: enable_def)
    apply(force)
   apply (simp add: ComFin_def)
   apply (simp add:Com_def)
   apply(force)(* Ev ` chutoriaru set sanshou*)
  apply (simp add:Com_def)
  apply(force)    
  done  

lemma Bfr_Bfr_trn_2:
  "n : Asn 2 ==> n : enable Blks Deps S 
   ==>
    ($Bfr Blks Deps Asn (Suc 0) S 
        |[ComFin]| $Bfr Blks Deps Asn 2 S) ~~ Com 
     ---(Ev (blk n))--->
    ($Bfr Blks Deps Asn (Suc 0) S 
        |[ComFin]| $Aft Blks Deps Asn 2 S n) ~~ Com"

  apply (rule Hide1)
  apply (rule conjI)
   apply (rule Para2)
   apply (rule conjI)
    apply (rule PName)
    apply (simp)
    apply (rule ExtCh2)
    apply (rule If1)
    apply (rule conjI)
     apply (rule ExtCh1)
     apply (rule NatExtCh1) (* ?90 = n <— S b x n *)
     apply (rule conjI)
      apply (rule Prefix)
     apply (simp)
     apply (simp add: enable_def)
    apply(force)
   apply (simp add: ComFin_def)
   apply (simp add:Com_def)
   apply(force)(* Ev ` chutoriaru set sanshou*)
  apply (simp add:Com_def)
  apply(force)    
  done  

lemma Bfr_Bfr_trn_finish:
   "($Bfr Blks Deps Asn (Suc 0) Blks 
        |[ComFin]| $Bfr Blks Deps Asn 2 Blks) 
          ~~ Com 
      ---(Ev finish)---> (STOP |[ComFin]| STOP) ~~ Com"
       apply (rule Hide1)
       apply (rule conjI)
        apply (rule Para3)
        apply (simp add: ComFin_def)
        apply (rule conjI)
         apply (rule PName)
         apply (simp)
         apply (rule ExtCh1)
         apply (rule If1)
         apply (rule conjI)
          apply (rule Prefix)
         apply (simp)
        apply (rule PName)
        apply (simp)
        apply (rule ExtCh1)
        apply (rule If1)
        apply (rule conjI)
         apply (rule Prefix)
        apply (simp)

       apply (simp add: Com_def)
       apply (force)
  done

lemma Aft_Bfr_trn_tau:
   "S \<noteq> Blks
    ==> ($Aft Blks Deps Asn (Suc 0) S n
       |[ComFin]| $Bfr Blks Deps Asn 2 S) ~~ Com 
     ---Tau--->
     ($Bfr Blks Deps Asn (Suc 0) (insert n S) 
        |[ComFin]| $Bfr Blks Deps Asn 2 (insert n S)) ~~ Com"
  apply (rule Hide2)
  apply (rule conjI)
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

lemma Bfr_Aft_trn_tau:
   "S \<noteq> Blks
    ==> ($Bfr Blks Deps Asn (Suc 0) S
       |[ComFin]| $Aft Blks Deps Asn 2 S n) ~~ Com 
     ---Tau--->
     ($Bfr Blks Deps Asn (Suc 0) (insert n S) 
        |[ComFin]| $Bfr Blks Deps Asn 2 (insert n S)) ~~ Com"
  apply (rule Hide2)
  apply (rule conjI)
   apply (rule Para3)

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


(* Aft --com--> Bfr*)
   apply (rule conjI)
    apply (rule PName)
    apply (simp)
    apply (rule ExtCh1)
    apply (simp add: co_def)
    apply (rule Prefix)
   apply (simp add: ComFin_def)
   apply (simp add: Com_def)
  apply (simp add: Com_def)
  done

lemma Aft_Aft_trn_tau_1:
 "($Aft Blks Deps Asn (Suc 0) S n
    |[ComFin]| $Aft Blks Deps Asn 2 S m) ~~ Com 
    ---Tau--->
  ($Bfr Blks Deps Asn (Suc 0) (insert n S) 
    |[ComFin]| $Aft Blks Deps Asn 2 (insert n S) m) ~~ Com"
  apply (rule Hide2)
  apply (rule conjI)
   apply (rule Para3)
   apply (rule conjI)

(*Aft --com--> Bfr*)
    apply (rule PName)
    apply (simp)
    apply (rule ExtCh1)
    apply (rule Prefix)

(*Aft --com--> Aft*)
   apply (rule conjI)
    apply (rule PName)
    apply (simp)
    apply (rule ExtCh2)
    apply (rule NatExtCh1)
    apply (simp add: co_def)
    apply (rule Prefix)
   apply (simp add: ComFin_def)
   apply (simp add: Com_def)
  apply (simp add: Com_def)
  done


lemma Aft_Aft_trn_tau_2:
 "($Aft Blks Deps Asn (Suc 0) S n
    |[ComFin]| $Aft Blks Deps Asn 2 S m) ~~ Com 
    ---Tau--->
  ($Aft Blks Deps Asn (Suc 0) (insert m S) n
    |[ComFin]| $Bfr Blks Deps Asn 2 (insert m S)) ~~ Com"
  apply (rule Hide2)
  apply (rule conjI)
   apply (rule Para3)
   apply (rule conjI)

  (*Aft --com--> Aft*)
    apply (rule PName)
    apply (simp)
    apply (rule ExtCh2)
    apply (rule NatExtCh1)
    apply (simp add: co_def)
    apply (rule Prefix)
   apply (simp add: ComFin_def)
   apply (simp add: Com_def)

(*Aft --com--> Bfr*)
    apply (rule PName)
    apply (simp)
    apply (rule ExtCh1)
    apply (simp add: co_def)
    apply (rule Prefix)

  apply (simp add: Com_def)
  done

end
