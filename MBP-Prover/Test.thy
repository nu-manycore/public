           (*-------------------------------------------*
            |                                           |
            |          Test on LW-CSP-Prover            |
            |                                           |
            *-------------------------------------------*)

theory Test
imports CSP_semantics
begin

(*************************************************************

         1. Test
         2. 
         3. 
         4. 

 *************************************************************)

(* test of transition *)

datatype K_Events = lock | unlock | finish
datatype K_PName = Key

primrec
  Def :: "K_PName => (K_PName, K_Events) proc"
  where
  "Def Key = (lock -> unlock -> $Key) [+] (finish -> STOP)"

overloading K_PNfun == 
  "PNfun :: K_PName => (K_PName, K_Events) proc"
  begin definition "PNfun = Def" end
  declare K_PNfun_def [simp]

lemma trn_exists:
  "$Key ---(Ev lock)---> (unlock -> $Key)"
  apply (rule PName, simp)
  apply (rule ExtCh1)
  apply (rule Prefix)
  done

lemma if_trn_exists:
  "$Key ---e---> P' 
   \<Longrightarrow>   (e = (Ev lock) \<and> P' = unlock -> $Key)
       \<or> (e = (Ev finish) \<and> P' = STOP)"
  apply (erule trn.cases, auto)+
  done



(* test of transition *)

datatype FW_Events = in1 | in2 | out1 | out2
datatype FW_PName = FW

primrec
  FW_Def :: "FW_PName => (FW_PName, FW_Events) proc"
  where
  "FW_Def FW = (in1 -> out1 -> $FW) [+] (in2 -> out2 -> $FW)"

overloading FW_PNfun == 
  "PNfun :: FW_PName => (FW_PName, FW_Events) proc"
  begin definition "PNfun = FW_Def" end
  declare FW_PNfun_def [simp]

lemma fw_trn_exists:
  "$FW ---(Ev in1)---> (out1 -> $FW)"
  apply (rule PName, simp)
  apply (rule ExtCh1)
  apply (rule Prefix)
  done

lemma fw_if_trn_exists:
  "$FW ---e---> P' 
   ==>   (e = Ev in1 & P' = out1 -> $FW)
       | (e = Ev in2 & P' = out2 -> $FW)"
  apply (erule trn.cases, auto)+
  done

lemma trn_exists_STOP:
  "(in1 -> out1 -> STOP) [+] (in2 -> out2 -> STOP)
   ---(Ev in1)---> (out1 -> STOP)"
  apply (rule ExtCh1)
  apply (rule Prefix)
  done

lemma if_trn_exists_STOP:
  "(in1 -> out1 -> STOP) [+] (in2 -> out2 -> STOP)
   ---e---> P' 
   ==>   (e = Ev in1 & P' = out1 -> STOP)
       | (e = Ev in2 & P' = out2 -> STOP)"
  apply (erule trn.cases, auto)+
  done

datatype Events2 = put | pass | get

lemma ex1_transition:
  "((get -> pass -> STOP) |[{pass}]| (pass -> put -> STOP)) ~~ {pass}
   ---(Ev get)---> 
   ((pass -> STOP) |[{pass}]| (pass -> put -> STOP)) ~~ {pass}"
  apply (rule Hide1, auto)
  apply (rule Para1, auto)
  apply (rule Prefix)
  done

lemma ex2_transition:
  "((pass -> STOP) |[{pass}]| (pass -> put -> STOP)) ~~ {pass}
   ---Tau---> 
   (STOP |[{pass}]| (put -> STOP)) ~~ {pass}"
  apply (intro Hide2 Para3 Prefix, auto?)+
  done

lemma ex3_transition:
  "(STOP |[{pass}]| (put -> STOP)) ~~ {pass}
   ---(Ev put)---> 
   (STOP |[{pass}]| STOP) ~~ {pass}"
  apply (intro Hide1 Para2 Prefix, auto?)+
  done

lemma ex4_transition:
  "((get -> pass -> STOP) |[{pass}]| (pass -> put -> STOP)) ~~ {pass}
   ---e---> P'
   ==> e = Ev get & 
       P' = ((pass -> STOP) |[{pass}]| (pass -> put -> STOP)) ~~ {pass}"
  apply (erule trn.cases, auto?)+
  done





lemma ex1_transition_manual_proof:
  "((a -> STOP) [+] P) ||| Q ---(Ev a)---> STOP ||| Q"
  apply (rule Para1)
  apply (rule conjI)
  apply (rule ExtCh1)
  apply (rule Prefix)
  apply (simp)
  done

lemma ex2_transition_auto_proof:
  "((a -> STOP) [+] P) ||| Q ---(Ev a)---> STOP ||| Q"
  apply (auto intro: trn.intros)
  done

lemma ex3_decomposition_of_transition:
  "((a -> STOP) [+] (b -> STOP)) ||| Q ---(Ev c)---> STOP ||| Q
   ==> a = c | b = c"
  apply (erule trn.cases)   (* all cases are checked for ||| *)
  apply (auto)
  apply (erule trn.cases)   (* all cases are checked for [+] *)
  apply (auto)
  apply (erule trn.cases)   (* all cases are checked for a -> *)
  apply (auto)
  apply (erule trn.cases)   (* all cases are checked for b -> *)
  apply (auto)
  done



(* ----- loop test (process name) ------ *)

datatype Event = act1 | act2
datatype Name = Ptest

primrec
  Def2 :: "Name => (Name, Event) proc"
  where
  "Def2 Ptest = act1 -> $Ptest [+] act2 -> STOP"

overloading Test_PNfun == 
  "PNfun :: Name => (Name, Event) proc"
  begin
    definition "PNfun == Def2"
  end

declare Test_PNfun_def [simp]

lemma ex4_loop_transition_manual_proof:
  "$Ptest ---(Ev act1)---> $Ptest"
  apply (rule PName)
  apply (simp)
  apply (rule ExtCh1)
  apply (rule Prefix)
  done

lemma ex4_loop_transition_auto_proof:
  "$Ptest ---(Ev act1)---> $Ptest"
  apply (intro trn.intros)
  apply (simp)
  apply (intro trn.intros)
  done


(* test of sequential transition *)

lemma ex5_seq_transition_manual_proof:
  "a ~= b ==> c ~= b
   ==> (a -> b -> c -> STOP) ~~ {b} ---[Ev a, Tau, Ev c]--->> STOP ~~ {b}"
  apply (rule Step)
  apply (rule_tac x="(b -> c -> STOP) ~~ {b}" in exI)
  apply (rule_tac x="Ev a" in exI)
  apply (rule_tac x="[Tau,Ev c]" in exI)
  apply (rule conjI)
   apply (rule Hide1)
   apply (rule conjI)
    apply (rule Prefix)
   apply (simp)
  apply (rule conjI)
   apply (rule Step)
   apply (rule_tac x="(c -> STOP) ~~ {b}" in exI)
   apply (rule_tac x="Tau" in exI)
   apply (rule_tac x="[Ev c]" in exI)
   apply (rule conjI)
    apply (rule Hide2)
    apply (rule conjI)
     apply (rule Prefix)
    apply (simp)
   apply (rule conjI)
    apply (rule Base)
    apply (rule Hide1)
    apply (rule conjI)
     apply (rule Prefix)
    apply (simp)
   apply (simp)
  apply (simp)
  done

(* test of traces *)

lemma ex6_traces_manual_proof:
  "[| a ~= b; c ~= b |]
   ==> [a,c] : traces((a -> b -> c -> STOP) ~~ {b})"
  apply (simp add: traces_def)
  apply (rule_tac x="[Ev a, Tau, Ev c]" in exI)
  apply (rule conjI)
   apply (simp)
  apply (rule_tac x="STOP ~~ {b}" in exI)
  apply (simp add: ex5_seq_transition_manual_proof)
  done



end
