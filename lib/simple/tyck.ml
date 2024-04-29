[@@@warning "-27"]
open Syntax


let sorry () = failwith "摆烂了"
module TryFail = struct
let rec infer (env:typ StringMap.t) (expr:expr) = 
  let check_expr_is_type env expr = 
    match infer env expr with
    | Type universe -> universe (* U_i *)
    | _ -> failwith "not a type" 
  in
  match expr with
  | Var name -> StringMap.find name env
  | Type universe -> Type (universe+1)
  | FunType(param_name, param_type, return_type) -> 
    let universe_of_param_type = check_expr_is_type env param_type in
    let universe_of_return_type = check_expr_is_type (StringMap.add param_name param_type env) return_type in
    Type (max universe_of_param_type universe_of_return_type)
  | Fun(param_name, param_type, body) ->
    let _ = check_expr_is_type env param_type in
    let return_type = infer (StringMap.add param_name param_type env) body in
    FunType(param_name, param_type, return_type)
  | App(func, arg) ->
    let func_type = infer env func in
    let arg_type = infer env arg in
    match func_type with
    | FunType(param_name, param_type, return_type) ->
      if param_type <> arg_type then failwith "type mismatch" else
      (* 需要 normalization!!! *)
      let result_type = sorry () in
      result_type

      (* 这里也需要 normalization, 可能 normalize 之后才形如 func *)
    | _ -> failwith "not a function" 

    let types_are_equal (typ1:typ) (typ2:typ) : bool = sorry()
    let subst (var:string) (map_to:expr) (target:expr) : expr = sorry()
end

module Subst = struct
let x = "不想抄了, NbE万岁"
end

open Nbe
type env = 
  { typs : value StringMap.t (* 直接用 value 作为 type *)
  ; values : value StringMap.t
  ; names : string list
  }

let add_var name typ env = 
  let value = V_Ne (Ne_Var name) in
  { typs = StringMap.add name typ env.typs
  ; values = StringMap.add name value env.values
  ; names = name :: env.names
  }

(* 直接用 value 作为 type *)
let rec infer (env:env) (expr:expr) : value = 
  let check_expr_is_type env expr =
    match infer env expr with
    | V_Type universe -> universe
    | _ -> failwith "not a type"
  in 
  match expr with
  | Var name -> StringMap.find name env.typs
  | Type universe -> V_Type (universe+1)
  | FunType(param_name, param_type, return_type) ->
    let universe_of_param_type = check_expr_is_type env param_type in
    let param_type_value = eval env.values param_type in
    let universe_of_return_type = 
      check_expr_is_type (add_var param_name param_type_value env) return_type
    in
    V_Type(max universe_of_param_type universe_of_return_type)
  | Fun(param_name, param_type, body) ->
    let _ = check_expr_is_type env param_type in
    let param_type_value = eval env.values param_type in
    let body_env = add_var param_name param_type_value env in
    
    let return_type_value = infer body_env body in
    let return_type = value_to_expr body_env.names return_type_value in
    V_FunType(param_type_value,
      fun param_value -> eval (StringMap.add param_name param_value env.values) return_type
    )
  | App(func, arg) ->
    let func_type = infer env func in
    let arg_type = infer env arg in
    match func_type with
    | V_FunType(param_type, return_type) -> 
      if not (types_are_equal env.names param_type arg_type) then
        failwith "type mismatch"
      else return_type (eval env.values arg)
    | _ -> failwith "not a function"
