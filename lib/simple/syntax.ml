type expr = 
  | Var of string
  | Type of int
  | FunType of string * expr * expr
  | Fun of string * expr * expr
  | App of expr * expr

type typ = expr

module StringMap = Map.Make(String)