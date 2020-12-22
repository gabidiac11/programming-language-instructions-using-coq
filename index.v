(* Since the variable names are now strings, we need to import the required libraries *)
Require Import Strings.String.
Local Open Scope string_scope. 

Scheme Equality for string.

Require Import Coq.Arith.PeanoNat.
Require Coq.Init.Nat.




(* ERROR IMPLEMENTATION ---------------------------- *)
Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat
  | empty_arr: ErrorNat
  | array_num : ErrorNat -> ErrorNat -> ErrorNat.

Coercion num: nat >-> ErrorNat.

(* ARRAY IMPLEMENTATION ---------------------------- *)
Local Open Scope list_scope.
Notation "[ ]" := empty_arr: list_scope.
Notation "[ x ]" := (array_num x empty_arr) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (array_num x (array_num y .. (array_num z empty_arr) ..)) : list_scope. 

Definition exm_nat_1 := [ 1 ; 2 ; 3 ].
Check []. 

Fixpoint length_array (l: ErrorNat) : nat :=
match l with
    | array_num number next => 1 + (length_array next)
    | _ => 0
end.
(* 

Fixpoint remove_val (x : nat) (l: array_) : array_ :=
match l with
    | empty => empty
    | node number (node number2 next3) => if (Nat.eq_dec x y) then node number next3 else node number (remove x (node number2 next3))
end.
 *)

(* ARRAY IMPLEMENTATION - end ---------------------------- *)


Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Coercion boolean: bool >-> ErrorBool.


(* A general type which includes all kind of types *)
Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result.
Scheme Equality for Result.



(* An environment which maps variable names (strings) to the Result type *)
Definition Env := string -> Result.

(* Initial environment *)
Definition env : Env := fun x => err_undecl.

(* Initially each variable is undeclared *)
(* Compute (env "x"). *)
(* 
Definition check_eq_over_types (t1 : Result) (t2 : Result) : bool :=
  match t1 with
  | err_undecl => match t2 with 
                     | err_undecl => true
                     | _ => false
                     end
  | err_assign => match t2 with 
                     | err_assign => true
                     | _ => false
                     end
  | default => match t2 with 
                     | default => true
                     | _ => false
                     end
  | res_nat (num n) => match t2 with 
                     | res_nat (num n') => true
                     | _ => false
                     end
  | res_nat error_nat => match t2 with 
                     | res_nat error_nat => true
                     | _ => false
                     end
  | res_nat (array_num n) => match t2 with 
                     | res_nat (array_num m) => true
                     | _ => false
                     end
  | res_bool (boolean n) => match t2 with 
                     | res_bool (boolean n') => true
                     | _ => false
                     end
  | res_bool error_bool => match t2 with 
                     | res_bool error_bool => true
                     | _ => false
                     end
  end. *)

(* ERROR IMPLEMENTATION - end ---------------------------- *)



Definition update (env : Env) (x : string) (v : Result) : Env :=
  fun y =>
    if (eqb y x)
    then v
    else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 0).

(* Compute ((update (update (update env "y" default) "y" (res_nat 10)) "y" (res_bool true)) "y"). *)

Inductive AExp :=
| avar: string -> AExp (* Var ~> string *)
| anum: ErrorNat -> AExp
| aplus: AExp -> AExp -> AExp
| asub: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp
| adiv: AExp -> AExp -> AExp
| amod: AExp -> AExp -> AExp
| aaray_nth: AExp -> AExp -> AExp
| aaray_rm: AExp -> AExp -> AExp.

(* Coercions for numerical constants and variables *)
Coercion anum: ErrorNat >-> AExp.
Coercion avar: string >-> AExp.

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).
Notation "'lookAt(' A  B ')'" := (aaray_nth A B)(at level 45, left associativity).
Notation "'removeVal(' A  B ')'" := (aaray_rm A B)(at level 45, left associativity).

(* Notatations used for the Big-Step semantics *)
Reserved Notation "A =[ S ]=> N" (at level 60).
Reserved Notation "B ={ S }=> B'" (at level 70).


(* ERROR SIMPLE CALCULATION IMPLEMENTATION ---------------------------- *)
Definition plus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    | _, _ => error_nat
    end.

Definition sub_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else num (n1 - n2)
    | _, _ => error_nat
    end.

Definition mul_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    | _, _ => error_nat
    end.

Definition div_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (Nat.div v1 v2)
    | _, _ => error_nat
    end.

Definition mod_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    | _, _ => error_nat
    end.
(* ERROR SIMPLE CALCULATION IMPLEMENTATION - end ---------------------------- *)

(* ERROR ARRAY ---------------------------- *)
Fixpoint array_ErrorLookAt (a1:ErrorNat) (a2: ErrorNat) : ErrorNat :=
    match a1, a2 with
      | error_nat, _ => error_nat
      | _, error_nat => error_nat
      | num n, array_num val next => match n, val with    
                | O, num number => number
                | _, empty_arr => error_nat
                | S m, _ => array_ErrorLookAt m next
                | _, _ => error_nat
      end
      |_, _ => error_nat
    end.
(* ERROR ARRAY ---------------------------- *)

Fixpoint aeval_fun (a : AExp) (env : Env) : ErrorNat :=
  match a with
  | avar v => match (env v) with
                | res_nat n => n
                | _ => error_nat
                end
  | anum v => v
  | aplus a1 a2 => (plus_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amul a1 a2 => (mul_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | asub a1 a2 => (sub_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | adiv a1 a2 => (div_ErrorNat  (aeval_fun a1 env) (aeval_fun a2 env))
  | amod a1 a2 => (mod_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | aaray_nth a1 a2 => (array_ErrorLookAt (aeval_fun a1 env) (aeval_fun a2 env)) 
  | aaray_rm a1 a2 => (plus_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  end.

Inductive BExp :=
| berror
| btrue
| bfalse
| bvar: string -> BExp (* Variables of type bool *)
| blt : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.

(* Notations used for boolean operations *)
Notation "A <' B" := (blt A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

Definition lt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v1 v2)
    | _, _ => error_bool
    end.

Definition eq_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.eqb v1 v2)
    | _, _ => error_bool
    end.

Definition not_ErrorBool (n :ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.

Definition and_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Definition or_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.

Fixpoint beval_fun (a : BExp) (envnat : Env) : ErrorBool :=
  match a with
  | btrue => true
  | bfalse => false
  | berror => error_bool
  | bvar v => match (env v) with
                | res_bool n => n
                | _ => error_bool
                end
  | blt a1 a2 => (lt_ErrorBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  | bnot b1 => (not_ErrorBool (beval_fun b1 envnat))
  | band b1 b2 => (and_ErrorBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  | bor b1 b2 => (or_ErrorBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  end.


(* Statements *)
Inductive Stmt :=
  | nat_decl: string -> AExp -> Stmt (* Declaration Stmt for variables of type nat *)
  | bool_decl: string -> BExp -> Stmt (* Declaration Stmt for variables of type bool *)
  | nat_assign : string -> AExp -> Stmt (* Assignment Stmt for variables of type nat *)
  | bool_assign : string -> BExp -> Stmt (* Assignment Stmt for variables of type nat *)
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | empty_case
  | case: AExp -> Stmt -> Stmt -> Stmt
  | switch : AExp -> Stmt -> Stmt. 

Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "'iNat' X ::= A" := (nat_decl X A)(at level 90).
Notation "'iBool' X ::= A" := (bool_decl X A)(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'fors' ( A ~ B ~ C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Check (switch 1 empty_case ).

Check (switch 2 (case 2 (iNat "x" ::= 2) empty_case) ).

Local Open Scope list_scope.

Notation "'switchs' A []" := (switch A empty_case): list_scope.
Notation "'switchs' A [ B { C } ]" := (switch A (case B C empty_case) ) : list_scope.
Notation "'switchs' A [ B { C } ;; B2 { C2 } ]" := (switch A (case B C ( case B2 C2 empty_case)) ) : list_scope.

Definition statement1 := iNat "sum" ::= "sum".
Definition statement2 := iNat "sum" ::= "sum".
Definition case1 := 1.
Definition case2 := 2.

(* Definition switchs2 := (switch case2 (case case1 statement1 ( case case2 statement2 empty_case)) ). *)

(* Definition switchs3 := ( switchs 1 [ case1 { statement1 } ] ).*)

Fixpoint switch_match (e: AExp) (s : Stmt) (env : Env) : Stmt :=
match s with 
| empty_case => statement2
| case e2 S1 next_case =>  match eq_ErrorBool (aeval_fun e env) (aeval_fun e2 env) with 
                                                         | boolean true => S1
                                                         | _ => switch_match e next_case env
                                                          end  
| _ => statement1
end.

Fixpoint eval_fun (s : Stmt) (env : Env) (gas: nat) : Env :=
    match gas with
    | 0 => env
    | S gas' => match s with
                | sequence S1 S2 => eval_fun S2 (eval_fun S1 env gas') gas'
                | nat_decl a aexp => update (update env a default) a (res_nat (aeval_fun aexp env))
                | bool_decl b bexp => update (update env b default) b (res_bool (beval_fun bexp env))
                | nat_assign a aexp => update env a (res_nat (aeval_fun aexp env))
                | bool_assign b bexp => update env b (res_bool (beval_fun bexp env))
                | ifthen cond s' => 
                    match (beval_fun cond env) with
                    | error_bool => env
                    | boolean v => match v with
                                 | true => eval_fun s' env gas'
                                 | false => env
                                 end
                    end
                | ifthenelse cond S1 S2 => 
                    match (beval_fun cond env) with
                        | error_bool => env
                        | boolean v  => match v with
                                 | true => eval_fun S1 env gas'
                                 | false => eval_fun S2 env gas'
                                 end
                         end
                | while cond s' => 
                    match (beval_fun cond env) with
                        | error_bool => env
                        | boolean v => match v with
                                     | true => eval_fun (s' ;; (while cond s')) env gas'
                                     | false => env
                                     end
                        end
               | switch e acase =>  eval_fun (switch_match e acase env) env gas'
| _ => env
               end
    end.

Definition while_stmt :=
    iNat "i" ::= 0 ;;
    iNat "sum" ::= 0 ;;
    while 


        ("i" <' 6) 
        (
           "sum" :n= "sum" +' "i" ;;
           "i" :n= "i" +' 1
        ).

Compute (eval_fun while_stmt env 100) "sum".

Definition for_stmt :=
    iNat "sum" ::= 0 ;;
    fors ( iNat "i" ::= 0 ~ "i" <' 6 ~ "i" :n= "i" +' 1 ) {
      "sum" :n= "sum" +' "i"
    }.


Compute (eval_fun for_stmt env 100) "sum".


