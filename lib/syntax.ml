(* we do namelessly *)
type expr =
  | Index of int (* DeBruijn index *)
  | Level of int (* DeBruijn level, NOT use when construct AST *)
  | Type of int (* universe i *)
  | Let of expr * typ * (* BINDS *) expr (* let _0 : typ = expr in expr *)

  | Pi of typ * (* BINDS *) typ (* Pi A x.B *)
  | Lam of (* BINDS *) expr (* lam A, x.V *)
  (* We write let f:Pi T x.A = lam x.M, NO param type *)
  | App of expr * expr (* f x *)

  | Sigma of expr * (* BINDS *) expr (* Sigma T x.A *)
  | Pair of expr * expr (* (x, y) : Sigma(x:T) A *)
  | Fst of expr (* e.1 *)
  | Snd of expr (* e.2 *)

  | Void    (* False, \{  \}  *)
  | Exfalso of expr * expr (* Exfalso(falsehood, T) : T *)

  | Unit    (* True,  \{ * \} *)
  | Trivial (* () : Unit *)
  | Singleton of expr * (* BINDS *) expr *  expr  (* Singleton(e, x.A, a:A[*/x])*)

  (* Bool might be simpler than Sum, thanks to Sigma types *)
  | Bool
  | True
  | False
  (* if V then W1 else W2 as A end, W1:A, W2:A *)
  | If of expr * expr * expr * typ

  | Id of expr * expr * expr (* Id(A, a, a') *)
  | Refl of expr (* Refl(a) : a=a *)
  | J of expr * (* BINDS 3 *) expr * (* BINDS *) expr (* J(path:a=a', a.a'.A.t, x.refl) *)

  | Underline of ctyp (* U uC, underline set/forgetful function U *)
  | Thunk of comp (* thunk M *)
  (* computation as followed: *)
  | Free of typ (* F uC *)
  | Force of expr (* force(V) *)
  | Return of expr (* return V *)
  | Compose of comp * typ * ctyp * (* BINDS *) comp  (* Compose(M, A, uC, x.N) *)
  (* return V to x:A. M = M[V/x] *)
  | CPi of typ * (* BINDS *) comp (* Pi(A, x.M) *)
  | CLam of (* BINDS *) comp (* CLam(A, x.M) *)
  | CApp of comp * expr (* M V *)
  | Get of expr (* Get(loc) *)
  | Put of expr * expr (* Put(loc, val) *)

and typ = expr (* value type *)
and comp = expr (* comp term *)
and ctyp = comp (* comp type *)
[@@deriving show]


(** todo: maybe, we need No levelize if we have no W-induction, just remain here *)
(** size is the length of env *)
let rec levelize (size:int) (depth:int) (expr:expr) : expr =
  (* when BINDS, depth+=1 *)
  match expr with
  | Index i -> if i < depth then Index i else Level (size-(depth-i)-1)
  | Level l -> Level l
  | Type universe -> Type universe
  | Let (e1, t, e2) -> Let(levelize size depth e1, levelize size depth t, levelize size (depth+1) e2)
  | Pi (e1, e2) -> Pi(levelize size depth e1, levelize size (depth+1) e2)
  | Lam e -> Lam (levelize size (depth+1) e)
  | App (e1, e2) -> App(levelize size depth e1, levelize size depth e2)
  | Sigma (e1, e2) -> Sigma(levelize size depth e1, levelize size (depth+1) e2)
  | Pair (e1, e2) -> Pair (levelize size depth e1, levelize size depth e2)
  | Fst e -> Fst (levelize size depth e)
  | Snd e -> Snd (levelize size depth e)
  | Void -> Void
  | Exfalso (e1, e2) -> Exfalso (levelize size depth e1, levelize size depth e2)
  | Unit -> Unit
  | Trivial -> Trivial
  | Singleton (e1, e2, e3) -> Singleton (levelize size depth e1, levelize size (depth+1) e2, levelize size depth e3)
  | Bool -> Bool
  | True -> True
  | False -> False
  | If (e1, e2, e3, e4) -> If (levelize size depth e1, levelize size depth e2, levelize size depth e3, levelize size depth e4)
  | Id (e1, e2, e3) -> Id (levelize size depth e1, levelize size depth e2, levelize size depth e3)
  | Refl e -> Refl (levelize size depth e)
  | J (e1, e2, e3) -> J (levelize size depth e1, levelize size (depth+3) e2, levelize size (depth+1) e3)
  | _ -> failwith "todo"
