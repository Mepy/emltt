open Syntax

(* 由于 variable 而卡住的 application *)
type neutral = 
  | Ne_Var of string
  | Ne_App of neutral * value

(* 先引入 value, 再 dequote *)
and value = 
  | V_Ne of neutral
  | V_Type of int
  
  (*
    V_Fun(param_type, func), 其中 func : value -> value 是 Higher Order Abstract Syntax(HOAS)
    大声讲: 多谢 OCaml!!  
   *)
  | V_Fun of value * (value->value)

  (*
    \Pi (x:A) B 中 B 也是 (x:A) 的一个函数
    V_FunType(param_type, func)
  *)
  | V_FunType of value * (value->value)

let rec eval (env : value StringMap.t) (expr : expr) : value = 
  match expr with
  | Var name -> StringMap.find name env
  | Type universe -> V_Type universe
  | FunType(param_name, param_type, return_type) ->
    let value_of_return_type arg_value = 
      eval (StringMap.add param_name arg_value env) return_type
    in
    V_FunType(eval env param_type, value_of_return_type)
  | Fun(param_name, param_type, body) ->
    let value_function arg_value = 
      eval (StringMap.add param_name arg_value env) body
    in
    V_Fun(eval env param_type, value_function)
  | App(func, arg) -> 
    match eval env func with
    | V_Fun(_, f) -> f (eval env arg)
    
    (* 已经因为变量卡住了 *)
    | V_Ne neutral -> V_Ne (Ne_App(neutral, eval env arg))
    | _ -> failwith "runtime error"


(* 
(* 不能用 int ref 自增, 因为需要额外处理 alpha_equiv *)
let fresh_name =
  let index = ref 0 in
  fun () -> 
    let i = !index in
    index := i + 1;
    let name = "x" ^ string_of_int i in
    name
*)
(* 需要 names 也因为, 在 env/Gamma 非空的时候, 会有 named variables *)
let generate_name names = 
  let rec try_xi i =
    let name = "x" ^ string_of_int i in
    if List.mem name names 
    then try_xi (i+1)
    else name
  in try_xi 0


(* dequote *)
let rec value_to_expr (names : string list) (value : value) : expr =
  match value with
  | V_Ne neutral -> neutral_to_expr names neutral
  | V_Type universe -> Type universe
  | V_FunType(param_type, func) -> 
    let param_name = generate_name names in
    Fun(param_name,
      value_to_expr names param_type,
      value_to_expr (param_name :: names) (func (V_Ne (Ne_Var param_name))))
  | V_Fun(param_type, func) ->
    let param_name = generate_name names in
    Fun(param_name,
      value_to_expr names param_type,
      value_to_expr (param_name :: names) (func (V_Ne (Ne_Var param_name))))
and neutral_to_expr (names) (neutral : neutral) : expr =
  match neutral with
  | Ne_Var name -> Var name
  | Ne_App(func, arg) -> App (neutral_to_expr names func, value_to_expr names arg)


let normalization (env:value StringMap.t) (expr:expr) : expr =
  let value = eval env expr in
  let names_in_env = List.map fst (StringMap.bindings env) in 
  value_to_expr names_in_env value

(* 
  这里转回 expr 再进行比较, 由于使用相同的 names, 可以忽略 alpha_equiv
  另外, 可以直接在 value 上进行比较, 但这得把 HOAS 解开
*)
let types_are_equal names (typ1:value) (typ2:value) =
  value_to_expr names typ1 = value_to_expr names typ2