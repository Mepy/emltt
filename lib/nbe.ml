[@@@warning "-27"]

module S = Syntax


type env = value list
and clos = | Clos of {expr:S.expr; env:env}
and clos2 = | Clos2 of {expr:S.expr; env:env}
and clos3 = | Clos3 of {expr:S.expr; env:env}

and value =
  | Neutral of {typ:value; term:neutral}
  | Type of int (* universe *)
  | Lam of clos
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

  | Underline of value
  | Free of value

  | Force of value
  | Thunk of value
  | Return of value 
  | Compose of value * value * clos * value
  | CLam of clos
  | CPi of value * clos
  | Get of value 
  | Put of value * value
  
and neutral = 
  | Level of int (* DeBruijn level *)
  | App of neutral * normal
  | Fst of neutral
  | Snd of neutral
  | Exfalso of neutral * value
  | Singleton of neutral * clos * value
  | If of neutral * value * value * value
  | J of neutral * clos3 * clos * value * value * value

  
  | CApp of neutral * normal
  
and normal = | Normal of {typ:value; value:value}
[@@deriving show]

let mk_var typ level = Neutral {typ; term=Level level}


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
  | S.If(bb, tt, ff, typ) -> 
    eval_if env bb tt ff typ 
  | S.Id (typ, left, right) -> Id (eval env typ, eval env left, eval env right) 
  | S.Refl expr -> Refl (eval env expr)
  | S.J (path, mot, refl) ->
    eval_j (Clos3 {expr=mot; env}) (Clos {expr=refl; env}) (eval env path)

  | S.CPi (src, dst) -> CPi (eval env src, Clos {expr=dst; env})
  | S.CLam (body) -> CLam (Clos {expr=body; env})
  | S.CApp (comp, expr) -> eval_capp (eval env comp) (eval env expr)
  | S.Free (typ) -> Free (eval env typ)
  | S.Underline (typ) -> Underline(eval env typ)
  | S.Force (expr) -> eval_force (eval env expr)
  | S.Thunk (comp) -> eval_thunk (eval env comp)
  | S.Get (loc) -> Get (eval env loc)
  | S.Put (loc, v) -> Put (eval env loc, eval env v)
  | S.Compose (comp, typ, cont, ctyp) -> eval_compose (eval env comp) (eval env typ) (Clos{expr=cont; env}) (eval env ctyp)
  | S.Return value -> Return (eval env value)
and eval_compose (comp:value) (typ:value) (cont:clos) (ctyp:value) =
  match comp with
  | Return value -> eval_clos cont value
  | _ -> Compose (comp, typ, cont, ctyp)

and eval_force (expr:value) =
  match expr with
  | Thunk comp -> comp (* force thunk M = M *)
  | _ -> Force expr
and eval_thunk (comp:value) =
  match comp with
  | Force value -> value (* thunk force V = V *)
  | _ -> Thunk comp
and eval_capp (func:value) (arg:value) =
  match func with
  | CLam clos -> eval_clos clos arg
  | Neutral {typ; term} -> (
    match typ with
    | CPi (src, dst) -> 
      let dst = eval_clos dst arg in
      Neutral {typ=dst; term=App(term, Normal {typ=src; value=arg})}
    | _ -> failwith "app not_a_cpi_type_func _"
  )
  | _ -> failwith "app not_a_compfunc _"
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
and eval_if (env:env) (bb:S.expr) (tt:S.expr) (ff:S.expr) (typ:S.typ) : value =
  match eval env bb with
  | True -> eval env tt
  | False -> eval env ff
  | Neutral {typ=Bool; term=neutral} -> 
    Neutral {typ=eval env typ; term=If (neutral, eval env tt, eval env ff, eval env typ) }
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
  (* todo : Unit, Trivial -> S.Trivial ??? *)
  | _, Trivial -> S.Trivial
  | _, True -> S.True
  | _, False -> S.False
  | Id(a_typ, _, _), Refl(a) -> S.Refl(quote size (Normal{typ=a_typ; value=a}))
  | uC, Force (value) -> S.Force (quote size (Normal{typ=Underline(uC); value}))
  | Underline(uC), Thunk (value) -> S.Thunk (quote size (Normal{typ=uC; value}))
  | typ, Thunk (value) -> S.Thunk (quote size (Normal{typ=Free(typ); value}))
  | _, Get (loc) -> S.Get(quote size (Normal{typ=Bool; value=loc}))
  | _, Put (loc, v) -> S.Put(quote size (Normal{typ=Bool; value=loc}), quote size (Normal{typ=Bool; value=v}))
  | CPi(src, dst), cfunc -> 
    let arg = mk_var src size in
    let normal = Normal {typ=eval_clos dst arg; value=eval_capp cfunc arg} in
    S.CLam (quote (size+1) normal)
  | Free(typ), Return(value) -> S.Return(quote size (Normal{typ; value}))
  | _, Compose(comp, typ, cont, ctyp) -> 
    let comp' = quote size (Normal{typ=Free typ; value=comp}) in
    let typ' = quote_typ size typ in
    let arg = mk_var typ size in
    let cont' = quote (size+1) (Normal{typ=ctyp; value=eval_clos cont arg}) in
    let ctyp' = quote_typ size ctyp in
    S.Compose(comp', typ', cont', ctyp')
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
  | Underline (typ) -> S.Underline(quote_typ size typ)
  | Free (typ) -> S.Free(quote_typ size typ)
  | CPi (src, dst) -> 
    let var = mk_var src size in
    S.CPi(quote_typ size src, quote_typ (size+1) (eval_clos dst var))
  | Neutral {term; _} -> quote_ne size term
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
  | If(bb, tt, ff, typ) -> 
    let typ' = quote_typ size typ in 
    S.If(quote_ne size bb, typ',
    quote size (Normal{typ; value=tt}), 
    quote size (Normal{typ; value=ff}))
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
  | CApp(neutral, arg) -> S.App (quote_ne size neutral, quote size arg)

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
