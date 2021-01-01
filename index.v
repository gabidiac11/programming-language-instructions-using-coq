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
  | empty_arr
  | array_num : ErrorNat -> ErrorNat -> ErrorNat.

Coercion num: nat >-> ErrorNat.

(* ARRAY IMPLEMENTATION ---------------------------- *)
Local Open Scope list_scope.
Notation "[ ]" := empty_arr: list_scope.
Notation "[ x ]" := (array_num x empty_arr) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (array_num x (array_num y .. (array_num z empty_arr) ..)) : list_scope.

Definition exm_nat_1 := [ 1 ; 2 ; 3 ].

Fixpoint length_array (l: ErrorNat) : nat :=
match l with
    | array_num number next => 1 + (length_array next)
    | _ => 0
end.

(* INDUCTIVE DEFINITIONS ----------------------------------------------*)
Inductive AExp :=
| avar: string -> AExp (* Var ~> string *)
| anum: ErrorNat -> AExp
| aplus: AExp -> AExp -> AExp
| asub: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp
| adiv: AExp -> AExp -> AExp
| amod: AExp -> AExp -> AExp
| array_index: string -> AExp -> AExp.
Coercion anum: ErrorNat >-> AExp.
Coercion avar: string >-> AExp.

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).

Inductive BExp :=
| berror
| btrue
| bfalse
| bvar: string -> BExp (* Variables of type bool *)
| blt : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.
Notation "A <' B" := (blt A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

Inductive FunctionParam :=
| empty_param
| param : string -> FunctionParam -> FunctionParam.

Inductive Function :=
| func: string -> FunctionParam -> Function.

Inductive Stmt :=
  | nat_decl: string -> AExp -> Stmt 
  | bool_decl: string -> BExp -> Stmt 
  | nat_assign : string -> AExp -> Stmt 
  | bool_assign : string -> BExp -> Stmt 
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  (* switch *)
  | empty_case
  | case_val: AExp -> Stmt -> Stmt
  | case: Stmt -> Stmt -> Stmt (* value then statement else next *)
  | switch : AExp -> Stmt -> Stmt
  (*function *)
  | end_func
  | func_declare: Function -> Stmt -> Stmt
  | func_call: string -> FunctionParam -> Stmt -> Stmt
  (* array *)
  | array_decl: string -> ErrorNat -> Stmt 
  | array_assign: string -> ErrorNat -> Stmt
  | array_update: string -> AExp -> AExp-> Stmt
.

Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "'iNat' X ::= A" := (nat_decl X A)(at level 90).
Notation "'iBool' X ::= A" := (bool_decl X A)(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'fors' ( A ~ B ~ C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

(* UPDATE -----------------------------------------------------------------------------------*)
Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Coercion boolean: bool >-> ErrorBool.

Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | err_func : Result
  | err_func_param_undeclared: Result
  | err_func_param_insuficient: Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result
  | code : FunctionParam -> Stmt -> Result.

Scheme Equality for Result.

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
  | err_func => match t2 with 
                     | err_func => true
                     | _ => false
                     end
  | err_func_param_undeclared => match t2 with 
                     | err_func_param_undeclared => true
                     | _ => false
                     end
  | err_func_param_insuficient => match t2 with 
                     | err_func_param_insuficient => true
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
  | res_bool (boolean n) => match t2 with 
                     | res_bool (boolean n') => true
                     | _ => false
                     end
  | res_bool error_bool => match t2 with 
                     | res_bool error_bool => true
                     | _ => false
                     end
  | code p1 c1 => match t2 with 
                     | code p2 c2 => true
                     | _ => false
                     end
  | res_nat (array_num n m) => match t2 with 
                     | res_nat empty_arr => true
                     | res_nat (array_num n' m') => true
                     | _ => false
                     end
  | res_nat empty_arr => match t2 with 
                     | res_nat empty_arr => true
                     | res_nat (array_num n m) => true
                     | _ => false
                     end
  end.  

(* An environment which maps variable names (strings) to the Result type *)
Definition Env := string -> Result.

Inductive EnvStack :=
| env_empty 
| env_stack: Env -> EnvStack -> EnvStack.

(* Initial environment *)
Definition envIni : Env := fun x => err_undecl.

(* Initial environment stack*)
Definition envStackIni : EnvStack := (env_stack envIni env_empty).


Fixpoint topEnv (env_s : EnvStack) : Env := 
match env_s with
      | env_stack env_val any => env_val
      | env_empty => envIni
 end.

Fixpoint stackLength (env_s : EnvStack) (n : nat) : nat :=
match env_s with
      | env_stack env_val next => stackLength next n + 1
      | empty_env => n
 end.

Fixpoint findEnv (env_s : EnvStack) (n : nat) : Env :=
match n with
      | 0 => match env_s with
                | env_stack env_val next => env_val
                | empty_env => envIni 
                end
      | S m => match env_s with
                | env_stack env_val next => findEnv next m
                | empty_env => envIni 
                end
 end.

Fixpoint globalEnv (env_s : EnvStack) : Env := findEnv env_s ((stackLength env_s 0)-1).

Fixpoint pushEnvStack (env_s : EnvStack) (env_new : Env) : EnvStack := 
match env_s with
      | env_stack env_val next =>  env_stack env_new  (env_stack env_val next)
      | env_empty => env_stack env_new env_empty
 end.

Fixpoint updateEnvStack (env_s : EnvStack) (env_new : Env) : EnvStack := 
match env_s with
      | env_stack env_val next => env_stack env_new next
      | env_empty => env_stack env_new env_empty
 end.

Definition update (env : Env) (x : string) (v : Result) : Env :=
  fun y =>
    if (eqb y x)
    then 
        (* var not initially declared - is err_undecl and is not default *)
        if(andb (check_eq_over_types err_undecl (env y)) (negb (check_eq_over_types default v)))
        then err_undecl
        (* var declaration - is err_undecl but will be assigned with a defautl value *)
        else if(andb (check_eq_over_types err_undecl (env y)) (check_eq_over_types default v))
          then default
          else
            (* declared - has a default val or any val *)
            if(orb (check_eq_over_types default (env y)) (check_eq_over_types v (env y)))
            then v
            else err_assign
    else (env y).

(* CALCULATION ---------------------------- *)
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
(* CALCULATION - end ---------------------------- *)


Notation "S [ V /' X ]" := (update S X V) (at level 0).

(* Compute ((update (update (update env "y" default) "y" (res_nat 10)) "y" (res_bool true)) "y"). *)

(* Notatations used for the Big-Step semantics *)
Reserved Notation "A =[ S ]=> N" (at level 60).
Reserved Notation "B ={ S }=> B'" (at level 70).

(* Array FUNCTIONS ----------------------------------------------------------------------*)
(*
Fixpoint remove_val (x : nat) (l: array_) : array_ :=
match l with
    | empty => empty
    | node number (node number2 next3) => if (Nat.eq_dec x y) then node number next3 else node number (remove x (node number2 next3))
end.
*)

Definition eq_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.eqb v1 v2)
    | _, _ => error_bool
    end.


(* Fixpoint array_ErrorRemove_val (a1:ErrorNat) (a2: ErrorNat) : ErrorNat :=
    match a1, a2 with
      | error_nat, _ => error_nat
      | _, error_nat => error_nat
      | num n, empty_arr => empty_arr
      | num n, array_num val empty_arr => match (eq_ErrorBool n val) with 
                                         | boolean true => empty_arr
                                         | _ => array_num val empty_arr
                                         end
      | num n, array_num val next => match (eq_ErrorBool n val) with 
                                         | boolean true => array_ErrorRemove_val a1 next
                                         | _ => array_num val (array_ErrorRemove_val a1 next)
                                         end
      |_, _ => error_nat
    end. *)

(* Fixpoint array_ErrorLookAt (a1:ErrorNat) (a2: ErrorNat) : ErrorNat :=
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
    end. *)

Fixpoint indexOfArray (arrayValue: ErrorNat) (n: nat) : ErrorNat :=
match n, arrayValue with
  | _, empty_arr => error_nat
  | O, array_num value next => value
  | S m, array_num value next => indexOfArray next m
  |_, _ => error_nat
end.

(* AExp FUNCTIONS ---------------------------------------------------------------------- ###eval*)
Fixpoint aeval_fun (a : AExp) (envStack : EnvStack) : ErrorNat :=
  match a with
  | avar v => match ((topEnv envStack) v) with
                | res_nat n => n
                 (*get the value from global scope (the first env in the stack) if is not found in current env*)
                | _ => match ((globalEnv envStack) v) with
                                         | res_nat n => n
                                         | _ => error_nat
                                         end
                end
  | anum v => v
  | aplus a1 a2 => (plus_ErrorNat (aeval_fun a1 envStack) (aeval_fun a2 envStack))
  | amul a1 a2 => (mul_ErrorNat (aeval_fun a1 envStack) (aeval_fun a2 envStack))
  | asub a1 a2 => (sub_ErrorNat (aeval_fun a1 envStack) (aeval_fun a2 envStack))
  | adiv a1 a2 => (div_ErrorNat  (aeval_fun a1 envStack) (aeval_fun a2 envStack ))
  | amod a1 a2 => (mod_ErrorNat (aeval_fun a1 envStack) (aeval_fun a2 envStack ))
  | array_index arrayName index =>  match ((topEnv envStack) arrayName) with
                                                        | res_nat arrayValue =>  match index with
                                                                                | num n => indexOfArray arrayValue n
                                                                                | _ => error_nat
                                                                                end
                                                         (*get the value from global scope (the first env in the stack) if is not found in current env*)
                                                        | _ => match ((globalEnv envStack) arrayName) with
                                                                                 | res_nat arrayValue => match index with
                                                                                                          | num n => indexOfArray arrayValue n
                                                                                                          | _ => error_nat
                                                                                                          end
                                                                                 | _ => error_nat
                                                                                 end
                                                       
                                  end 
  end.

(* BExp FUNCTIONS ---------------------------------------------------------------------- ###eval*)
Definition lt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v1 v2)
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

  Fixpoint beval_fun (a : BExp) (envStackNat : EnvStack) : ErrorBool :=
  match a with
  | btrue => true
  | bfalse => false
  | berror => error_bool
  | bvar v => match (envIni v) with
                | res_bool n => n
                | _ => error_bool
                end
  | blt a1 a2 => (lt_ErrorBool (aeval_fun a1 envStackNat) (aeval_fun a2 envStackNat))
  | bnot b1 => (not_ErrorBool (beval_fun b1 envStackNat))
  | band b1 b2 => (and_ErrorBool (beval_fun b1 envStackNat) (beval_fun b2 envStackNat))
  | bor b1 b2 => (or_ErrorBool (beval_fun b1 envStackNat) (beval_fun b2 envStackNat))
  end.

(* Stmt functions -------------------------------------------------------------------------------*)
Fixpoint switch_match2 (e: AExp) (s : Stmt) (envStack : EnvStack) : Stmt :=
match s with 
| empty_case => empty_case
| case caseValue next_case => 
                            match caseValue with
                            | case_val e2 S1 => match eq_ErrorBool (aeval_fun e envStack) (aeval_fun e2 envStack) with 
                                                                                     | boolean true => S1
                                                                                     | _ => switch_match2 e next_case envStack
                                                                                      end
                            | _ => empty_case
                            end
| _ => empty_case
end.
Fixpoint switch_match (e: AExp) (s : Stmt) (envStack : EnvStack) : Stmt :=
match s with 
| empty_case => empty_case
| case caseValue next_case => 
                            match caseValue with
                            | case_val e2 S1 => match eq_ErrorBool (aeval_fun e envStack) (aeval_fun e2 envStack) with 
                                                                                     | boolean true => S1
                                                                                     | _ => switch_match e next_case envStack
                                                                                      end  
                            | _ => empty_case
                            end
| _ => empty_case
end.

Fixpoint checkParamLength (paramValues: FunctionParam) (myFuncParams: FunctionParam) : bool := 
match paramValues, myFuncParams with
| empty_param, empty_param => true
| param name next, param name2 next2 => checkParamLength next next2
| _, _ => false
end.

Fixpoint valuesAreDeclared (paramValues: FunctionParam) (thisEnv: Env) : bool := 
match paramValues with
| empty_param => true
| param name next => match (thisEnv name) with
                                | default => valuesAreDeclared next thisEnv
                                | res_nat n => valuesAreDeclared next thisEnv
                                | res_bool  b=> valuesAreDeclared next thisEnv
                                | _ => false
                                end
end.

Fixpoint functionCallOk (paramValues: FunctionParam) (myFuncParams: FunctionParam) (thisEnv: Env) : Result := 
match (checkParamLength paramValues myFuncParams) with
| true => match valuesAreDeclared paramValues thisEnv with
              | true => res_nat (num 1)
              | _ => err_func_param_undeclared
              end
| _ =>  err_func_param_insuficient
end.


(* create a new stack with a new env updated with params corresponding to the the values of previous env*)
Fixpoint copyParamToEnv  (paramValues : FunctionParam) (prevEnv : Env) (newEnv: Env) : Env :=  
match paramValues with
| empty_param => newEnv
| param name next => copyParamToEnv next prevEnv  (
      update (update newEnv name default) name (newEnv name)
)
end.

Fixpoint createStack  (paramValues : FunctionParam) (envStack : EnvStack) : EnvStack := pushEnvStack envStack (copyParamToEnv paramValues (topEnv envStack) envIni).

Definition evn2 := update (update envIni "x" default) "x" ( res_nat 55).
Definition evn3 := update (update envIni "x" default) "x" ( res_nat 7).
Definition evn4 := update (update envIni "x" default) "x" ( res_nat 8).

Definition envStack5 := (env_stack evn2 (env_stack evn3 (env_stack evn4 env_empty))).

Fixpoint popStack (stack: EnvStack) : EnvStack :=
match stack with
| env_stack prevEnv (env_stack currentEnv next) => env_stack currentEnv next
| env_stack currentEnv env_empty => stack
| env_empty => envStackIni
end. 

Fixpoint updateEnvStackAtIndex (env_s : EnvStack) (newEnv: Env) (n: nat) : EnvStack :=
match n with
      | 0 => match env_s with
                | env_stack env_val next => env_stack newEnv next
                | empty_env => env_stack newEnv empty_env 
                end
      | S m => match env_s with
                | env_stack env_val next => env_stack env_val (updateEnvStackAtIndex next newEnv m)
                | empty_env => env_stack newEnv empty_env 
                end
 end.

Fixpoint updateArrayAt2 (arr : ErrorNat) (index: nat) ( newValue : ErrorNat)  : ErrorNat := 
match index, arr with
 | O, array_num value next => array_num newValue next
 | S m, array_num value next => array_num value (updateArrayAt2 next m newValue)
 |  _ , empty_array => empty_arr 
end.

Fixpoint updateArrayAt (arr2 : Result) (index: ErrorNat) ( newValue : ErrorNat)  : ErrorNat := 
match index with
| num n => match arr2 with
                | res_nat arr => updateArrayAt2 arr n newValue
                | _ => empty_arr
              end
| _ => empty_arr
end.
(* Compute (topEnv 1 envStack5) "x" . *)

Fixpoint eval_fun2 (s : Stmt) (envStack : EnvStack) (gas: nat) : EnvStack := 
    match gas with
    | 0 => envStack
    | S gas' => match s with
                | sequence S1 S2 => eval_fun2 S2 (eval_fun2 S1 envStack gas') gas'
                | nat_decl a aexp => updateEnvStack envStack (update (update (topEnv envStack) a default) a (res_nat (aeval_fun aexp envStack)))
                
                | bool_decl b bexp => updateEnvStack envStack (update (update (topEnv envStack) b default) b (res_bool (beval_fun bexp envStack)))
                
                | nat_assign a aexp => match ((topEnv envStack) a) with
                                                | res_nat n => updateEnvStack envStack ( update (topEnv envStack) a (res_nat (aeval_fun aexp envStack)) )
                                                | default => updateEnvStack envStack ( update (topEnv envStack) a (res_nat (aeval_fun aexp envStack)) )          
                                               (*update the global scope if it's nothing on the local level*)                                     
                                                | _ => updateEnvStackAtIndex envStack (update (globalEnv envStack) a (res_nat (aeval_fun aexp envStack))) ((stackLength envStack 0) -1)
                                                end
                | bool_assign b bexp => match ((topEnv envStack) b) with
                                                | res_nat n => updateEnvStack envStack ( update (topEnv envStack) b (res_bool (beval_fun bexp envStack)) )
                                                | default => updateEnvStack envStack ( update (topEnv envStack) b (res_bool (beval_fun bexp envStack)) )                                              
                                                (*update the global scope if it's nothing on the local level*) 
                                                | _ => updateEnvStackAtIndex envStack ( update (globalEnv envStack) b (res_bool (beval_fun bexp envStack)) ) ((stackLength envStack 0) -1)
                                                end
                | ifthen cond s' => 
                    match (beval_fun cond envStack) with
                    | error_bool => envStack
                    | boolean v => match v with
                                 | true => eval_fun2 s' envStack gas'
                                 | false => envStack
                                 end
                    end
                | ifthenelse cond S1 S2 => 
                    match (beval_fun cond envStack) with
                        | error_bool => envStack
                        | boolean v  => match v with
                                 | true => eval_fun2 S1 envStack gas'
                                 | false => eval_fun2 S2 envStack gas'
                                 end
                         end
                | while cond s' => 
                    match (beval_fun cond envStack) with
                        | error_bool => envStack
                        | boolean v => match v with
                                     | true => eval_fun2 (s' ;; (while cond s')) envStack gas'
                                     | false => envStack
                                     end
                        end
              (* SWITCH STMS ----------------------------------------*)
               | switch e cases =>  match (switch_match e cases envStack) with
                                          | empty_case => envStack
                                          | _ => eval_fun2 (switch_match e cases envStack) envStack gas' 
                                          end
                | empty_case => envStack
                | case_val axpr s1 => envStack
                | case s1 s2 =>  envStack
                (* FUNCTION STMS ----------------------------------------*)
                (* check if params is a list of string *)
                | func_declare myFunction S1 => match myFunction with
                                                                | func name params => updateEnvStack envStack (update ( (* update the env ${function name} - code sequence ${params}-${actual-function-statements} *)
                                                                          update (topEnv envStack) name default
                                                                            ) 
                                                                            name 
                                                                            (code params S1))
                                                                    end
                (* check if params is a list of string *)                                   
               | func_call name paramValues EndStmt => match ((globalEnv envStack) name) with 
                                                                              (*check if call is valid -> return res_nat num 1 if ok, error else*)
                                        | code myFuncParams S1 => match (functionCallOk paramValues myFuncParams (topEnv envStack)) with 
                                                                                 | res_nat n => eval_fun2 EndStmt (eval_fun2 S1 (createStack paramValues envStack) gas') gas'
                                                                                 | _  => envStack
                                                                                end
                                        |  _ => envStack
                                      end
              | end_func =>popStack envStack
              (* ARRAY STMS ----------------------------------------*)
                | array_decl a myArray =>  updateEnvStack envStack ( update (update (topEnv envStack) a default) a (res_nat myArray) )
                | array_assign a myArray => match ((topEnv envStack) a) with
                                                | res_nat n => updateEnvStack envStack ( update (topEnv envStack) a (res_nat myArray) )
                                                | default => updateEnvStack envStack ( update (topEnv envStack) a (res_nat myArray) )                                                 
                                               (*update the global scope if it's nothing on the local level*)  
                                                | _ => updateEnvStackAtIndex envStack (
                                                                    update (globalEnv envStack) a (res_nat myArray)
                                                            ) ((stackLength envStack 0) -1)
                                                end
                | array_update a index value =>  match ((topEnv envStack) a) with
                                                | res_nat n => updateEnvStack envStack ( update (topEnv envStack) a (res_nat  ( 
                                                                                  updateArrayAt ((topEnv envStack) a) (aeval_fun index envStack) (aeval_fun value envStack) ) 
                                                  ) 
                                                  )
                                                | default => updateEnvStack envStack ( update (topEnv envStack) a (res_nat ( 
                                                                                    updateArrayAt ((topEnv envStack) a) (aeval_fun index envStack) (aeval_fun value envStack) ) 
                                                  )
                                                  )                                                 
                                                (*update the global scope if it's nothing on the local level*)                                                
                                                | _ => updateEnvStackAtIndex envStack (
                                                                    update (globalEnv envStack) a (res_nat (
                                                                                     updateArrayAt ((topEnv envStack) a) (aeval_fun index envStack) (aeval_fun value envStack) ) 
                                                )
                                                ) ((stackLength envStack 0) -1)
                                                end

               end
    end.


(*EXEMPLES GLOBAL/LOCAL VARIABLES .....................................................................................................*) 
(* pe modelul javscript (parametrii non strong type, variabilele locale se pot redecla local separat)*) 
Definition exmpleProgram := 
    iNat "a" ::= 4 ;;
    "a" :n= "a" +' 4 ;;
    
    func_declare (func "myFunction" empty_param) ("a" :n= "a" +' 5 ) ;;
    func_call "myFunction" empty_param end_func ;;
    func_call "myFunction" empty_param end_func ;;
    func_call "myFunction" empty_param end_func ;;

    iNat "b" ::= 7 ;;
    iNat "result2" ::= 0 ;;
    func_declare (func "myFunction2" (param "b"  empty_param)) ("result2" :n= "b" +' 2 ) ;;
    func_call "myFunction2" (param "b"  empty_param) end_func
.

Definition resultExempleProgram := (globalEnv (eval_fun2 exmpleProgram envStackIni 1000)).

(*----- exemplu variabila locala: b initializata prin parametru cu valoarea b  din scopul global, var globala b ramane neschimbat fiind distinca de in function2 ca variabila locala
  ---- rezultatul functiei este plasat in result2 
*)

(*     Compute resultExempleProgram "result2".
    Compute resultExempleProgram "b". *)

(*EXEMPLES RECURSIVE FUNCTIONS .....................................................................................................*) 
Definition recursiveProgram :=  (
    iNat "result" ::= 0 ;;

    func_declare (func "myFunction" ( empty_param)) (
          ifthen ("result" <' 8) (
                  "result" :n= "result" +' 1 ;;
                 func_call "myFunction" (empty_param) end_func ;;
                 func_call "myFunction" (empty_param) end_func
             )
   ) ;;
    func_call "myFunction" (empty_param) end_func
).
Definition resultRecursiveProgram := (globalEnv (eval_fun2 recursiveProgram envStackIni 1000)).
Compute resultRecursiveProgram "result".

(*EXEMPLES SWITCH STMT .....................................................................................................*) 
Definition switchProgram := (
              iNat "x" ::= 5 ;;
              switch "x" (
                  case (
                      case_val 7 
                        ("x" :n= 21)) (
                  case (
                     case_val 5 
                    ("x" :n= 221)
                  ) 
                  empty_case
                
                  ) )
).
Definition switchProgramResult := (globalEnv (eval_fun2 switchProgram envStackIni 1000)).
(* Compute switchProgramResult "x". *)

(*EXEMPLES ARRAY STMT .....................................................................................................*) 
Definition arrayProgram := (
              iNat "x" ::= 2 ;;
              iNat "value" ::= 20 ;;
               array_decl "arw" ([1 ; 2; 3 ; 4]) ;;
             "x" :n= (array_index "arw" 2 ) ;;
              array_update "arw" 2 "value"
).
Definition arrayProgramResult := (globalEnv (eval_fun2 arrayProgram envStackIni 1000)).
(* Compute arrayProgramResult "arw". 
 *)



Definition for_stmt :=
    iNat "sum" ::= 0 ;;
    fors ( iNat "i" ::= 0 ~ "i" <' 6 ~ "i" :n= "i" +' 1 ) {
      "sum" :n= "sum" +' "i"
    }.



(* BIG STEP *)
Inductive aeval : AExp -> Env -> ErrorNat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=>  match (sigma v) with
                                              | res_nat x => x
                                              | _ => error_nat
                                              end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (plus_ErrorNat i1 i2) ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mul_ErrorNat i1 i2) ->
    a1 *' a2 =[sigma]=> n
| substract : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (sub_ErrorNat i1 i2) ->
    a1 -' a2 =[sigma]=> n
| division : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (div_ErrorNat  i1 i2) ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mod_ErrorNat i1 i2) ->
    a1 %' a2 =[sigma]=> n
(* | aaray_nth: forall a1 a2 i1 i2 sigma n,
      a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (array_ErrorLookAt i1 i2) ->
    (lookAt(a1  a2)) =[sigma]=> n *)

(* | aaray_rm: AExp -> AExp -> AExp. *)
where "a =[ sigma ]=> n" := (aeval a sigma n).








