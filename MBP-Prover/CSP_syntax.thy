           (*-------------------------------------------*
            |                                           |
            |       LW-CSP-Prover on Isabelle2021       | 
            |                                           |
           *-------------------------------------------*)

theory CSP_syntax
imports Main
begin

(*************************************************************

         1. Syntax of CSP
         2. Syntactic sugar
         3. 
         4. 

 *************************************************************)

(*-----------------------------------------------------------*
 |                                                           |
 |    Process Type Definitions                               |
 |                                                           |
 |             'a proc : type of process expressions         |
 |                       'n : process name                   |
 |                       'a : event                          |
 |                                                           |
 *-----------------------------------------------------------*)

(*********************************************************************
                       process expression
 *********************************************************************)

datatype 
 ('p,'a) proc
    = STOP

    | Prefix   "'a" "('p,'a) proc"      ("(1_ /-> _)" [150,80] 80)

    | ExtCh    "('p,'a) proc" "('p,'a) proc"  
                                               ("(1_ /[+] _)" [72,73] 72)
    | IntCh    "('p,'a) proc" "('p,'a) proc"  
                                               ("(1_ /|~| _)" [64,65] 64)
    | NatExtCh "nat set" "nat => ('p,'a) proc"
                                               ("(1[nat] :_ .. /_)" [900,75] 75) 
    | RepIntCh "'a set" "'a => ('p,'a) proc"
                                               ("(1!! :_ .. /_)" [900,68] 68) 
    | If       "bool" "('p,'a) proc" "('p,'a) proc"
                                 ("(0IF _ /THEN _ /ELSE _)" [900,88,88] 88)
    | Para     "('p,'a) proc" "'a set" "('p,'a) proc"  
                                               ("(1_ /|[_]| _)" [76,0,77] 76)
    | Hide     "('p,'a) proc" "'a set"   ("(1_ /~~ _)" [84,85] 84)

    | Ren      "('p,'a) proc" "('a * 'a) set"
                                               ("(1_ /[[_]])" [84,0] 84)
    | PName    "'p"                      ("$_" [900] 90)

(*--------------------------------------------------------------------*
 |                                                                    |
 | binding power:                                                     |
 |      PName > If > {Hide, Ren} > Prefix > Para >                    |
 |      NatExtCh > ExtCh >  RepIntCh > IntCh                          |
 |                                                                    |
 *--------------------------------------------------------------------*)

(*---------------------------------------*
 |           Syntactic Sugars            |
 *---------------------------------------*)

(*** nat external choice ***)

syntax
  "@Nat_ext_choice"  :: "pttrn => nat set => ('p,'a) proc 
                => ('p,'a) proc"  ("(1[Nat] _:_ .. _)" [900,900,75] 75)
  "@Nat_Univ_ext_choice"  :: "pttrn => ('p,'a) proc 
                => ('p,'a) proc"  ("(1[Nat] _ .. _)" [900,75] 75)
translations
  "[Nat] n:N .. P"  == "[nat] :N .. (%n. P)"
  "[Nat] n .. P"  == "[Nat] n:(CONST UNIV) .. P"

(*** replicated internal choice ***)

syntax
  "@Rep_int_choice"  :: "pttrn => 'a set => ('p,'a) proc 
                => ('p,'a) proc"  ("(1!! _:_ .. _)" [900,900,68] 68)
  "@Rep_Univ_int_choice"  :: "pttrn => ('p,'a) proc 
                => ('p,'a) proc"  ("(1!! _ .. _)" [900,68] 68)
translations
  "!! a:X .. P"  == "!! :X .. (%a. P)"
  "!! a .. P"  == "!! a:(CONST UNIV) .. P"

(*** sending ***)

abbreviation
  Send_prefix :: "('x => 'a) => 'x => ('p,'a) proc => ('p,'a) proc" 
                                      ("(1_ ! _ /-> _)" [900,990,80] 80)
  where
  "a ! x -> P    == a x -> P"

(*** receiving on nat ***)

abbreviation
  Rec_prefix  :: "(nat => 'a) => nat set => 
                  (nat => ('p,'a) proc) => ('p,'a) proc" 
  where
  "Rec_prefix a N Pf == [nat] : N .. (%n. a n -> Pf n)"

(* rec set *)

syntax
  "@Rec_nat_prefix"  :: "(nat => 'a) => pttrn => nat set => ('p,'a) proc 
                => ('p,'a) proc"   ("(1_ ? _:_ /-> _)" [900,990,1000,75] 75)
  "@Rec_nat_Univ_prefix"  :: "(nat => 'a) => pttrn => ('p,'a) proc 
                => ('p,'a) proc"   ("(1_ ? _ /-> _)" [900,990,75] 75)
translations
  "a ? n:N -> P" == "CONST Rec_prefix a N (%n. P)"   
  "a ? n -> P"   == "a ? n:(CONST UNIV) -> P"

(*** interleaving ***)

abbreviation
   Interleave :: "('p,'a) proc => ('p,'a) proc
                    => ('p,'a) proc"  ("(1_ /||| _)" [76,77] 76)
where "P ||| Q == P |[{}]| Q"

(*** guard ***)

abbreviation
   Guard :: "bool => ('p,'a) proc
                  => ('p,'a) proc"  ("(1_ /&> _)" [150,80] 80)  (* ? *)
where "b &> P == IF b THEN P ELSE STOP"

(* renaming *)

abbreviation
  Ren_pair  :: "'a => 'a => ('a * 'a) set" ("_ <- _" [900,900] 900)
  where
  "a <- b == {(a,b)}"

(* test of syntactic sugars *)

lemma test_send_rec_syntax:
  "a ? n -> (b ! n -> STOP) = [Nat] n .. a n -> b n -> STOP"
  apply (simp)
  done
lemma test_renaming_syntax:
  "(a -> STOP)[[a <- b]] = (a -> STOP)[[{(a,b)}]]"
  apply (simp)
  done

(*  We assume that a process-name-function PNfun is given  *)
(*  for defining the meaning of each process-name.         *)

type_synonym ('p,'a) pnfun = "'p => ('p,'a) proc"
consts PNfun :: "('p,'a) pnfun"  (* Definition of process names *)

end
