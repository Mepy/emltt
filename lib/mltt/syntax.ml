(* we do namelessly *)
type expr =
  | Index of int (* DeBruijn index *)
  | Level of int (* DeBruijn level, NOT use when construct AST *)
  | Type of int (* universe i *)
  | Let of expr * (* BINDS *) expr (* let _0 = expr in expr *)

  | Pi of expr * (* BINDS *) expr (* Pi T x.A *)
  | Lam of (* BINDS *) expr (* lam x.M *)
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

  (* 
    | Sum of expr * expr (* A + B *)
    | Inl of expr * expr (* inl(a, A+B) *)
    | Inr of expr * expr (* inr(b, A+B) *)
    (* case e with | inl(x1) -> e1 | inr(x2) -> e2 *)
    | Case of expr * (* string * BINDS *) expr * (* string * BINDS *) expr 
  *)
  (* Bool might be simpler than Sum, thanks to Sigma types *)
  | Bool
  | True
  | False
  (* if bb as x.typ then tt else ff, tt:typ[true/x], ff:typ[false/x] *)
  | If of expr * (* BINDS *) expr * expr * expr

  | Id of expr * expr * expr (* Id(A, a, a') *)
  | Refl of expr (* Refl(a) : a=a *)
  | J of expr * (* BINDS 3 *) expr * (* BINDS *) expr (* J(path:a=a', a.a'.A.t, x.refl) *)

  (* TODO: W types *)
  (* | W of string * expr * expr 
    string is for surface syntax, ...   
  *)
  (* W (x:A) B *)
  | W of expr * (* BINDS *) expr (* W(A, B) *)
  | Tree of expr * (* BINDS *) expr 
    (* tree(a, b.subtree)
      a : A, b:B(a).subtree : W(x:A)B(x)   
    *)
  | Ind of expr * (* BINDS *) expr * (* BINDS 3 *) expr 
    (* Ind(tree, t.C, a.s.h.c) *)
  (* induct term at t:W -> C with
     a:A s:B(a)->W h:Pi(b:B(a))C(s(b)) -> c : C[t|->tree(a, s)] 
  *)
  (* TODO: We might need to define Abs Binding Tree
    (c.f. PFPL of Robert Harper)
    which is also the style of MLTT-Lock  
    Ind(tree, x:A.u:B(x)->W.v:Pi(y:B(x))C(u(y)). c(x, u, v) : C(tree))
    where C is the result type of induction
    c.f. https://arxiv.org/pdf/1201.3898
  *)
[@@deriving show]

type typ = expr

(** size is the length of env *)
let rec levelize (size:int) (depth:int) (expr:expr) : expr = 
  (* when BINDS, depth+=1 *)
  match expr with
  | Index i -> if i < depth then Index i else Level (size-(depth-i)-1)
  | Level l -> Level l
  | Type universe -> Type universe
  | Let (e1, e2) -> Let(levelize size depth e1, levelize size (depth+1) e2)
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
  | If (e1, e2, e3, e4) -> If (levelize size depth e1, levelize size (depth+1) e2, levelize size depth e3, levelize size depth e4)
  | Id (e1, e2, e3) -> Id (levelize size depth e1, levelize size depth e2, levelize size depth e3)
  | Refl e -> Refl (levelize size depth e)
  | J (e1, e2, e3) -> J (levelize size depth e1, levelize size (depth+3) e2, levelize size (depth+1) e3)
  | W (e1, e2) -> W (levelize size depth e1, levelize size (depth+1) e2)
  | Tree (e1, e2) -> Tree (levelize size depth e1, levelize size (depth+1) e2)
  | Ind (e1, e2, e3) -> Ind (levelize size depth e1, levelize size (depth+1) e2, levelize size (depth+3) e3)