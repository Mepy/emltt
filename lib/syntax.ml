(* we do namelessly *)
type expr =
  | Var of int (* DeBruijn index *)
  | Type of int (* universe i *)
  | Let of expr * expr (* let _0 = expr in expr *)

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
  (* if bb then tt else ff as typ, tt:typ, ff:typ *)
  | If of expr * expr * expr * expr

  | Id of expr * expr * expr (* Id(A, a, a') *)
  | Refl of expr (* Refl(a) : a=a *)
  | J of expr * expr * expr (* J(path:a=a', a.a'.A.t, refl) *)

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
