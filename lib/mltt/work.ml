[@@@warning "-27"]
[@@@warning "-11"]
module ConcreteSyntax = struct

end

module S = Syntax

module Nbe = struct

type env = value list
and clos = | Clos of {expr:S.expr; env:env}
and clos2 = | Clos2 of {expr:S.expr; env:env}
and clos3 = | Clos3 of {expr:S.expr; env:env}

and value =
  | Type of int (* universe *)
  | Lam of clos
  | Neutral of {typ:value; term:neutral}
  | Pi of value * clos
  | Sigma of value * clos
  | Pair of value * value
  | Void
  | Unit
  | Trivial
  | Bool
  | True
  | False
  | Refl of value
  | Id of value * value * value
  | W of value * clos
  | Tree of value * clos

and neutral = 
  | Level of int (* DeBruijn level *)
  | App of neutral * normal
  | Fst of neutral
  | Snd of neutral
  | Exfalso of neutral * value
  | Singleton of neutral * clos * value
  | If of neutral * clos * value * value
  | J of neutral * clos3 * clos * value * value * value
  | Ind of neutral * value * clos * clos * clos3 
and normal = | Normal of {typ:value; value:value}
[@@deriving show]

let mk_var typ level = Neutral {typ; term=Level level}

module S = Syntax
let rec eval (env:env) (expr:S.expr) : value = 
  match expr with
  | S.Index i -> List.nth env i
  | S.Level l -> List.nth env (List.length env -l-1)
  | S.Type universe -> Type universe
  | S.Let (def, body) -> 
    let env' = (eval env def) :: env in
    eval env' body
  | S.Pi (src, dst) -> Pi (eval env src, Clos {expr=dst; env})
  | S.Lam (body) -> Lam (Clos {expr=body; env})
  | S.App (func, arg) -> 
    let func = eval env func in
    let arg = eval env arg in
    eval_app func arg
  | S.Sigma (e1, e2) -> Sigma (eval env e1, Clos {expr=e2; env})
  | S.Pair (e1, e2) -> Pair (eval env e1, eval env e2)
  | S.Fst expr -> eval_fst (eval env expr)
  | S.Snd expr -> eval_snd (eval env expr)
  | S.Void -> Void
  | S.Exfalso (falsehood, typ) -> eval_exfalso (eval env falsehood) (eval env typ)
  | S.Unit -> Unit
  | S.Trivial -> Trivial
  | S.Singleton(e, a_typ, a) -> eval_singleton (eval env e) (Clos{expr=a_typ; env}) (eval env a)
  | S.Bool -> Bool
  | S.True -> True
  | S.False -> False
  | S.If(bb, typ, tt, ff) -> 
    eval_if env bb typ tt ff
  | S.Id (typ, left, right) -> Id (eval env typ, eval env left, eval env right) 
  | S.Refl expr -> Refl (eval env expr)
  | S.J (path, mot, refl) ->
    eval_j (Clos3 {expr=mot; env}) (Clos {expr=refl; env}) (eval env path)
  | S.W(a, b) -> W(eval env a, Clos {expr=b; env})
  | S.Tree(a, s) -> Tree(eval env a, Clos {expr=s; env})
  | S.Ind(t, c_typ, c) -> eval_ind env t c_typ c
  

and eval_app (func:value) (arg:value) =
  match func with
  | Lam clos -> eval_clos clos arg
  | Neutral {typ; term} -> (
    match typ with
    | Pi (src, dst) -> 
      let dst = eval_clos dst arg in
      Neutral {typ=dst; term=App(term, Normal {typ=src; value=arg})}
    | _ -> failwith "app not_a_pi_type_func _"
  )
  | _ -> failwith "app not_a_func _"
and eval_clos (clos:clos) (arg:value) : value =
  match clos with
  | Clos {expr; env} -> 
    let env' = arg::env in (* add arg into env here *)
    eval env' expr
  (* | ConstClos value -> value *)
and eval_clos2 (Clos2{expr; env}:clos2) (arg1:value) (arg2:value) : value =
  let env' = arg2::arg1::env in
  eval env' expr
and eval_clos3 (Clos3{expr; env}:clos3) (arg1:value) (arg2:value) (arg3:value) : value =
  let env' = arg3::arg2::arg1::env in
  eval env' expr 

and eval_fst (pair:value) : value =
  match pair with
  | Pair (fst, _) -> fst
  | Neutral {typ=Sigma(fst_typ, _); term=neutral} ->
    Neutral {typ=fst_typ; term=Fst neutral}
  | _ -> failwith "fst not_a_pair"
and eval_snd (pair:value) : value =
  match pair with
  | Pair (_, snd) -> snd
  | Neutral {typ=Sigma(_, snd_typ_clos); term=neutral} ->
    let fst = eval_fst pair in
    let snd_typ = eval_clos snd_typ_clos fst in
    Neutral {typ=snd_typ; term=Snd neutral}
  | _ -> failwith "snd not_a_pair"
and eval_exfalso (falsehood:value) (typ:value) : value =
  match falsehood with
  | Neutral {typ=Void; term=neutral} ->
    Neutral {typ; term=Exfalso(neutral, typ)}
  | _ -> failwith ("exfalso " ^ (show_value falsehood) ^ " not_a_void")
and eval_singleton (e:value) (a_typ:clos) (a:value) : value = 
  match e with
  | Trivial -> failwith "todo"
  | Neutral {typ=Unit; term=neutral} -> 
    let typ = eval_clos a_typ a in
    Neutral {typ; term=Singleton(neutral, a_typ, a) }
  | _ -> failwith ("singleton " ^ (show_value a) ^ " not_a_unit")
and eval_if (env:env) (bb:S.expr) (typ: (* BINDS *) S.expr) (tt:S.expr) (ff:S.expr) : value =
  match eval env bb with
  | True -> eval env tt
  | False -> eval env ff
  | Neutral {typ=Bool; term=neutral} as bb -> 
    Neutral {typ=eval (bb::env) typ; term=If (neutral, Clos{env; expr=typ}, eval env tt, eval env ff) }
  | _ -> failwith "if not_a_bool"
and eval_j (mot:clos3) (refl:clos) (path:value) : value =
  match path with
  | Refl value -> eval_clos refl value
  | Neutral {typ; term} -> (
    match typ with
    | Id (typ, left, right) -> Neutral 
      { typ =eval_clos3 mot left right path
      ; term=J(term, mot, refl, typ, left, right) }
    | _ -> failwith "j not_an_id_type"
  )
  | _ -> failwith "j not_a_path"
and eval_ind (env:env) (t:S.expr) (c_typ:S.expr) (c:S.expr) : value =
  match eval env t with
  | Tree(a, s) -> 
    let Clos{expr=s_expr; env=s_env} = s in
    
    (* h = \ b. ind (s b) -> C with c *)
    (* (* old one *)
    let h = (Lam (* b. *) 
      (Clos{env; expr= (* env from env, because we eval it with env *)
      S.Ind((* b. *) s_expr, c_typ, c)})
    ) in 
    *)
    (*
    let rec shift (expr:S.expr) : S.expr =
      let open S in
      match expr with
      | Index i -> if i < 3 then Index i else Index (i+1)
      | Type universe -> Type universe
      | Let (e1, e2) -> Let(shift e1, shift e2)
      | Pi (e1, e2) -> Pi(shift e1, shift e2)
      | Lam e -> Lam (shift e)
      | App (e1, e2) -> App(shift e1, shift e2)
      | Sigma (e1, e2) -> Sigma(shift e1, shift e2)
      | Pair (e1, e2) -> Pair (shift e1, shift e2)
      | Fst e -> Fst (shift e)
      | Snd e -> Snd (shift e)
      | Void -> Void
      | Exfalso (e1, e2) -> Exfalso (shift e1, shift e2)
      | Unit -> Unit
      | Trivial -> Trivial
      | Singleton (e1, e2, e3) -> Singleton (shift e1, shift e2, shift e3)
      | Bool -> Bool
      | True -> True
      | False -> False
      | If (e1, e2, e3, e4) -> If (shift e1, shift e2, shift e3, shift e4)
      | Id (e1, e2, e3) -> Id (shift e1, shift e2, shift e3)
      | Refl e -> Refl (shift e)
      | J (e1, e2, e3) -> J (shift e1, shift e2, shift e3)
      | W (e1, e2) -> W (shift e1, shift e2)
      | Tree (e1, e2) -> Tree (shift e1, shift e2)
      | Ind (e1, e2, e3) -> Ind (shift e1, shift e2, shift e3)
    in 
    let h = eval env (S.Lam (S.Ind(s_expr, shift c_typ, shift c))) in
    *)
    let h' = 
      let size = List.length env in 
      if size = 0 then (S.Lam (S.Ind(s_expr, c_typ, c))) 
      else S.Lam (* due to this *) (S.Ind(s_expr, 
        S.levelize size 1 c_typ, 
        S.levelize size 3 c)
      ) (* if exists closure variable, use level *)
    in
    let h = eval env h' in 
    eval_clos3 (Clos3{expr=c; env}) a (Lam s) h
  | Neutral {typ; term} -> (
    match typ with
    | W (a, b) -> 
      let c_typ = Clos{expr=c_typ; env} in
      let c= Clos3{expr=c; env} in 
      Neutral 
      { typ = eval_clos c_typ typ
      ; term=Ind(term, a, b, c_typ, c) }
    | _ -> failwith "ind not_a_W_type"
  )
  | _ -> failwith "ind not_a_tree"

let rec quote (size:int) (Normal{typ; value}:normal): S.expr =
  match typ, value with
  | Type _, typ -> quote_typ size typ
  | Pi(src, dst), func -> 
    let arg = mk_var src size in
    let normal = Normal {typ=eval_clos dst arg; value=eval_app func arg} in
    S.Lam (quote (size+1) normal)
  | Sigma(fst_typ, snd_typ_clos), pair ->
    let fst = eval_fst pair in
    let snd_typ = eval_clos snd_typ_clos fst in
    let snd = eval_snd pair in
    S.Pair ( quote size (Normal{typ=fst_typ; value=fst})
           , quote size (Normal{typ=snd_typ; value=snd}) )
  | _, Trivial -> S.Trivial
  | _, True -> S.True
  | _, False -> S.False
  | Id(a_typ, _, _), Refl(a) -> S.Refl(quote size (Normal{typ=a_typ; value=a}))
  | W(a_typ, b_typ_clos), Tree(a, s) ->
    let b_typ = eval_clos b_typ_clos a in
    let b = mk_var b_typ size in
    let normal = Normal {typ=W(a_typ, b_typ_clos); value=eval_clos s b} in
    let s_expr = quote (size+1) normal in
    S.Tree(quote size (Normal{typ=a_typ; value=a}), s_expr)
  | _, Neutral {term=neutral; _} -> quote_ne size neutral
  | _ -> 
    print_endline ((show_value value) ^ " : " ^(show_value typ));
    failwith "???unknown"

and quote_typ (size:int) (typ:value) : S.expr = 
  match typ with
  | Type universe -> S.Type universe
  | Pi (src, dst) -> 
    let var = mk_var src size in
    S.Pi(quote_typ size src, quote_typ (size+1) (eval_clos dst var))
  | Sigma (fst, snd) ->
    let var = mk_var fst size in
    S.Sigma(quote_typ size fst, quote_typ (size+1) (eval_clos snd var))
  | Void -> S.Void
  | Unit -> S.Unit
  | Bool -> S.Bool
  | Id (typ, left, right) ->
    S.Id( quote_typ size typ
        , quote size (Normal{typ; value=left})
        , quote size (Normal{typ; value=right}) )
  | Neutral {term; _} -> quote_ne size term
  | W(a_typ, b) -> 
    let a = mk_var a_typ size in
    S.W(quote_typ size a_typ, quote_typ (size+1) (eval_clos b a))
  | _ -> failwith "quote_typ not_a_type"
and quote_ne (size:int) (neutral:neutral) : S.expr =
  match neutral with
  | Level level -> S.Index (size-(level+1)) (* index = size-(level+1) *)
  | App(neutral, arg) -> S.App (quote_ne size neutral, quote size arg)
  | Fst(neutral) -> S.Fst(quote_ne size neutral)
  | Snd(neutral) -> S.Snd(quote_ne size neutral)
  | Exfalso(neutral, typ) -> S.Exfalso(quote_ne size neutral, quote_typ size typ)
  | Singleton(neutral, a_typ, a) -> 
    let var = mk_var Unit size in 
    let a_typ' = quote_typ (size+1) (eval_clos a_typ var) in
    let a' = quote size (Normal{typ=eval_clos a_typ Trivial; value=a}) in
    S.Singleton(quote_ne size neutral, a_typ', a')
  | If(bb, typ_clos, tt, ff) -> 
    let var = mk_var Bool size in
    let typ' = quote_typ (size+1) (eval_clos typ_clos var) in 
    S.If(quote_ne size bb, typ',
    quote size (Normal{typ=eval_clos typ_clos True; value=tt}), 
    quote size (Normal{typ=eval_clos typ_clos False; value=ff}))
  | J (path, mot, refl, typ, left, right) -> 
    let path' = quote_ne size path in
    let mot_var1 = mk_var typ size in
    let mot_var2 = mk_var typ (size+1) in 
    let mot_var3 = mk_var (Id (typ, left, right)) (size+2) in
    let mot' = quote_typ (size+3) 
      (eval_clos3 mot mot_var1 mot_var2 mot_var3) in
    let refl_var = mk_var typ size in
    let refl' = quote (size+1) 
      (Normal { typ=eval_clos3 mot refl_var refl_var (Refl refl_var)
              ; value=eval_clos refl refl_var}) in
    S.J (path', mot', refl')
  | Ind(neutral, a_typ, b_typ_clos, c_typ_clos, c) -> 
    let w_typ = W(a_typ, b_typ_clos) in
    let tree = mk_var w_typ size in
    let c_typ = (eval_clos c_typ_clos tree) in
    let c_typ' = quote_typ (size+1) c_typ in

    let a = mk_var a_typ size in
    let b_typ = (eval_clos b_typ_clos a) in
    let w_typ' = quote_typ size w_typ in
    let s_typ = Pi(b_typ, Clos{env=[]; expr=w_typ'}) in
    let s = mk_var s_typ (size+1) in
    let h_typ = Pi(b_typ, Clos{env=s::a::[] (* todo *)
        ; expr=quote_typ (size+2)
        (eval_clos c_typ_clos (Neutral{typ=w_typ;
        term=App((* s *) Level (size+1), 
          Normal{typ=b_typ;value=Neutral{typ=b_typ;
            term=Level 0 (* todo : level ?0 *)}})
          })
        )
    }) in
    
  

    let c_t_a_s = (
      let s' = S.Lam(S.App(S.Level(size+1), S.Index 0)) in
      let Clos{env; expr} = c_typ_clos in
      let env' = Tree(a, Clos{env=a::env; expr=s'})::s::a::env in
      eval env' expr
    ) in
    
   (* let env' = s::a::env in
    let vv = eval (Tree(a, Clos{env=a::env (* todo *); expr=s'})::env') expr in
    let c_typ' = quote_typ (size+2) vv in
    print_endline (S.show_expr c_typ'); *)
    let h = mk_var h_typ (size+2) in
    (* 这里的类型好复杂, 或许要写入 syntax *)
    (* print_endline (show_value (eval_clos3 c a s h)); *)
    print_endline (show_value (eval_clos3 c a s h));
    let c' = quote (size+3) 
      (Normal{typ=c_t_a_s; 
        value=(eval_clos3 c a s h)})
    in
    
    S.Ind(quote_ne size neutral, c_typ', c')
  | _ -> failwith "todo"

let rec initial_env (env:S.typ list) : env * int =
  match env with
  | [] -> ([], 0)
  | typ::env ->
    let (env', level) = initial_env env in
    let value = Neutral {typ=eval env' typ; term=Level level} in 
    (value::env', level + 1)

let normalize (env:S.typ list) (expr:S.expr) (typ:S.typ) : S.expr = 
  let (env', size) = initial_env env in
  let typ = eval env' typ in
  let value = eval env' expr in
  let normal = Normal {typ; value} in
  quote size normal
end