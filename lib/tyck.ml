module Syn = Syntax

(* [(Val, Typ)] *)
type env = (Nbe.value * Nbe.value) list

type error =
  | CannotSynth of Syn.expr
  | Mismatch of { found : string; expect : string }
  | UnboundVar of { index : int; env : env }

exception TypeError of error

let type_error (err : error) = raise (TypeError err)
let to_nbe_env (env : env) = List.map fst env

let assert_value_type (typ : Nbe.value) =
  match typ with
  | Pi _ | Sigma _ | Pair _ | Void | Unit | Bool | Id _ | Underline _ -> ()
  | _ ->
      type_error
        (Mismatch { found = Nbe.show_value typ; expect = "value type" })

let assert_comp_type (typ : Nbe.value) =
  match typ with
  | Free _ | CPi _ (* ?? *) -> ()
  | _ ->
      type_error (Mismatch { found = Nbe.show_value typ; expect = "comp type" })

let rec is_equal_typ ~(size : int) ~(l : Nbe.value) ~(r : Nbe.value) =
  match (l, r) with
  | Nbe.Neutral { term = l; _ }, Nbe.Neutral { term = r; _ } ->
      is_equal_ne ~size ~l ~r
  | Nbe.Type _, Nbe.Type _
  | Nbe.Void, Nbe.Void
  | Nbe.Unit, Nbe.Unit
  | Nbe.Bool, Nbe.Bool ->
      true
  | Nbe.Pi (lt_l, rt_l), Nbe.Pi (lt_r, rt_r)
  | Nbe.Sigma (lt_l, rt_l), Nbe.Sigma (lt_r, rt_r)
  | Nbe.CPi (lt_l, rt_l), Nbe.CPi (lt_r, rt_r) ->
      let l_l = Nbe.mk_var lt_l size in
      let l_r = Nbe.mk_var lt_r size in
      is_equal_typ ~size ~l:lt_l ~r:lt_r
      && is_equal_typ ~size:(size + 1) ~l:(Nbe.eval_clos rt_l l_l)
           ~r:(Nbe.eval_clos rt_r l_r)
  | Nbe.Id (t_l, l_l, r_l), Nbe.Id (t_r, l_r, r_r) ->
      is_equal_typ ~size ~l:t_l ~r:t_r
      && is_equal_nf ~size
           ~l:(Nbe.Normal { typ = t_l; value = l_l })
           ~r:(Nbe.Normal { typ = t_r; value = l_r })
      && is_equal_nf ~size
           ~l:(Nbe.Normal { typ = t_l; value = r_l })
           ~r:(Nbe.Normal { typ = t_r; value = r_r })
  | Nbe.Underline l, Nbe.Underline r | Nbe.Free l, Nbe.Free r ->
      is_equal_typ ~size ~l ~r
  | _ -> false

and is_equal_ne ~(size : int) ~(l : Nbe.neutral) ~(r : Nbe.neutral) =
  match (l, r) with
  | Nbe.Level l, Nbe.Level r -> l == r
  | Nbe.App (f_l, a_l), Nbe.App (f_r, a_r)
  | Nbe.CApp (f_l, a_l), Nbe.CApp (f_r, a_r) ->
      is_equal_ne ~size ~l:f_l ~r:f_r && is_equal_nf ~size ~l:a_l ~r:a_r
  | Nbe.Fst l, Nbe.Fst r | Nbe.Snd l, Nbe.Snd r -> is_equal_ne ~size ~l ~r
  | Nbe.Exfalso (target_l, mot_l), Nbe.Exfalso (target_r, mot_r) ->
      is_equal_typ ~size ~l:mot_l ~r:mot_r
      && is_equal_ne ~size ~l:target_l ~r:target_r
  | ( Nbe.Singleton (target_l, mot_l, base_l),
      Nbe.Singleton (target_r, mot_r, base_r) ) ->
      let x = Nbe.mk_var Nbe.Unit size in
      is_equal_typ ~size:(size + 1) ~l:(Nbe.eval_clos mot_l x)
        ~r:(Nbe.eval_clos mot_r x)
      && is_equal_typ ~size ~l:base_l ~r:base_r
      && is_equal_ne ~size ~l:target_l ~r:target_r
  | Nbe.If (target_l, tt_l, ff_l, mot_l), Nbe.If (target_r, tt_r, ff_r, mot_r)
    ->
      is_equal_typ ~size ~l:mot_l ~r:mot_r
      && is_equal_nf ~size
           ~l:(Nbe.Normal { typ = mot_l; value = tt_l })
           ~r:(Nbe.Normal { typ = mot_r; value = tt_r })
      && is_equal_nf ~size
           ~l:(Nbe.Normal { typ = mot_l; value = ff_l })
           ~r:(Nbe.Normal { typ = mot_r; value = ff_r })
      && is_equal_ne ~size ~l:target_l ~r:target_r
  | ( Nbe.J (target_l, mot_l, base_l, typ_l, l_l, r_l),
      Nbe.J (target_r, mot_r, base_r, typ_r, l_r, r_r) ) ->
      is_equal_typ ~size ~l:typ_l ~r:typ_r
      && is_equal_nf ~size
           ~l:(Nbe.Normal { typ = typ_l; value = l_l })
           ~r:(Nbe.Normal { typ = typ_r; value = l_r })
      && is_equal_nf ~size
           ~l:(Nbe.Normal { typ = typ_l; value = r_l })
           ~r:(Nbe.Normal { typ = typ_r; value = r_r })
      &&
      let l = Nbe.mk_var typ_l size in
      let r = Nbe.mk_var typ_l (size + 1) in
      let p = Nbe.mk_var (Nbe.Id (typ_l, l_l, r_l)) (size + 2) in
      is_equal_typ ~size:(size + 3)
        ~l:(Nbe.eval_clos3 mot_l l r p)
        ~r:(Nbe.eval_clos3 mot_r l r p)
      &&
      let x = l in
      is_equal_nf ~size:(size + 1)
        ~l:
          (Nbe.Normal
             {
               typ = Nbe.eval_clos3 mot_l x x (Nbe.Refl x);
               value = Nbe.eval_clos base_l x;
             })
        ~r:
          (Nbe.Normal
             {
               typ = Nbe.eval_clos3 mot_r x x (Nbe.Refl x);
               value = Nbe.eval_clos base_r x;
             })
      && is_equal_ne ~size ~l:target_l ~r:target_r
  | _ -> false

and is_equal_nf ~(size : int) ~(l : Nbe.normal) ~(r : Nbe.normal) =
  match (l, r) with
  | ( Nbe.Normal { typ = Nbe.Neutral _; value = Nbe.Neutral { term = l; _ } },
      Nbe.Normal { typ = Nbe.Neutral _; value = Nbe.Neutral { term = r; _ } } )
    ->
      is_equal_ne ~size ~l ~r
  | ( Nbe.Normal { typ = Nbe.Type _; value = l },
      Nbe.Normal { typ = Nbe.Type _; value = r } ) ->
      is_equal_typ ~size ~l ~r
  | ( Nbe.Normal { typ = Nbe.Pi (xt, b_l); value = l },
      Nbe.Normal { typ = Nbe.Pi (_, b_r); value = r } )
  | ( Nbe.Normal { typ = Nbe.CPi (xt, b_l); value = l },
      Nbe.Normal { typ = Nbe.CPi (_, b_r); value = r } ) ->
      let x = Nbe.mk_var xt size in
      let b_l = Nbe.eval_clos b_l x in
      let b_r = Nbe.eval_clos b_r x in
      let l = Nbe.eval_app l x in
      let r = Nbe.eval_app r x in
      is_equal_nf ~size:(size + 1)
        ~l:(Nbe.Normal { typ = b_l; value = l })
        ~r:(Nbe.Normal { typ = b_r; value = r })
  | ( Nbe.Normal { typ = Nbe.Sigma (l_l, r_l); value = p_l },
      Nbe.Normal { typ = Nbe.Sigma (l_r, r_r); value = p_r } ) ->
      let fst_l = Nbe.eval_fst p_l in
      let fst_r = Nbe.eval_fst p_r in
      is_equal_nf ~size
        ~l:(Nbe.Normal { typ = l_l; value = fst_l })
        ~r:(Nbe.Normal { typ = l_r; value = fst_r })
      &&
      let r_l = Nbe.eval_clos r_l fst_l in
      let r_r = Nbe.eval_clos r_r fst_r in
      let snd_l = Nbe.eval_snd p_l in
      let snd_r = Nbe.eval_snd p_r in
      is_equal_nf ~size
        ~l:(Nbe.Normal { typ = r_l; value = snd_l })
        ~r:(Nbe.Normal { typ = r_r; value = snd_r })
  | ( Nbe.Normal { typ = Nbe.Void; value = _ },
      Nbe.Normal { typ = Nbe.Void; value = _ } ) ->
      true
  | ( Nbe.Normal { typ = Nbe.Unit; value = _ },
      Nbe.Normal { typ = Nbe.Unit; value = _ } ) ->
      true
  | ( Nbe.Normal { typ = Nbe.Bool; value = Nbe.True },
      Nbe.Normal { typ = Nbe.Bool; value = Nbe.True } )
  | ( Nbe.Normal { typ = Nbe.Bool; value = Nbe.False },
      Nbe.Normal { typ = Nbe.Bool; value = Nbe.False } ) ->
      true
  | ( Nbe.Normal { typ = Nbe.Bool; value = Nbe.Neutral { term = l; _ } },
      Nbe.Normal { typ = Nbe.Bool; value = Nbe.Neutral { term = r; _ } } ) ->
      is_equal_ne ~size ~l ~r
  | ( Nbe.Normal { typ = Nbe.Id (typ, _, _); value = Nbe.Refl l },
      Nbe.Normal { typ = Nbe.Id _; value = Nbe.Refl r } ) ->
      is_equal_nf ~size
        ~l:(Nbe.Normal { typ; value = l })
        ~r:(Nbe.Normal { typ; value = r })
  | ( Nbe.Normal { typ = Nbe.Id _; value = Nbe.Neutral { term = l; _ } },
      Nbe.Normal { typ = Nbe.Id _; value = Nbe.Neutral { term = r; _ } } ) ->
      is_equal_ne ~size ~l ~r
  | ( Nbe.Normal { typ = Nbe.Underline typ; value = Nbe.Thunk l },
      Nbe.Normal { typ = Nbe.Underline _; value = Nbe.Thunk r } ) ->
      is_equal_nf ~size
        ~l:(Nbe.Normal { typ; value = l })
        ~r:(Nbe.Normal { typ; value = r })
  | ( Nbe.Normal { typ = Nbe.Underline _; value = Nbe.Neutral { term = l; _ } },
      Nbe.Normal { typ = Nbe.Underline _; value = Nbe.Neutral { term = r; _ } }
    ) ->
      is_equal_ne ~size ~l ~r
  | ( Nbe.Normal { typ = Nbe.Free typ; value = Nbe.Force l },
      Nbe.Normal { typ = Nbe.Free _; value = Nbe.Force r } ) ->
      is_equal_nf ~size
        ~l:(Nbe.Normal { typ = Nbe.Underline typ; value = l })
        ~r:(Nbe.Normal { typ = Nbe.Underline typ; value = r })
  | ( Nbe.Normal { typ = Nbe.Free typ; value = Nbe.Return l },
      Nbe.Normal { typ = Nbe.Free _; value = Nbe.Return r } ) ->
      is_equal_nf ~size
        ~l:(Nbe.Normal { typ; value = l })
        ~r:(Nbe.Normal { typ; value = r })
  | ( Nbe.Normal { typ = Nbe.Free Nbe.Bool (* Val *); value = Nbe.Get l },
      Nbe.Normal { typ = Nbe.Free Nbe.Bool (* Val *); value = Nbe.Get r } ) ->
      is_equal_nf ~size
        ~l:(Nbe.Normal { typ = Nbe.Bool (* Loc *); value = l })
        ~r:(Nbe.Normal { typ = Nbe.Bool (* Loc *); value = r })
  | ( Nbe.Normal { typ = Nbe.Free Nbe.Unit; value = Nbe.Put (l_l, v_l) },
      Nbe.Normal { typ = Nbe.Free Nbe.Unit; value = Nbe.Put (l_r, v_r) } ) ->
      is_equal_nf ~size
        ~l:(Nbe.Normal { typ = Nbe.Bool (* Loc *); value = l_l })
        ~r:(Nbe.Normal { typ = Nbe.Bool (* Loc *); value = l_r })
      && is_equal_nf ~size
           ~l:(Nbe.Normal { typ = Nbe.Bool (* Val *); value = v_l })
           ~r:(Nbe.Normal { typ = Nbe.Bool (* Val *); value = v_r })
  | ( Nbe.Normal { typ = Nbe.Free _; value = Nbe.Neutral { term = l; _ } },
      Nbe.Normal { typ = Nbe.Free _; value = Nbe.Neutral { term = r; _ } } ) ->
      is_equal_ne ~size ~l ~r
  | _ -> false

let rec check ~(env : env) ~(size : int) ~(term : Syn.expr) ~(typ : Nbe.value) =
  let assert_equal size l r typ =
    if
      not
        (is_equal_nf ~size
           ~l:(Nbe.Normal { typ; value = l })
           ~r:(Nbe.Normal { typ; value = r }))
    then
      type_error
        (Mismatch { found = Nbe.show_value l; expect = Nbe.show_value r })
  in
  let assert_type size l r =
    if not (is_equal_typ ~size ~l ~r) then
      type_error
        (Mismatch { found = Nbe.show_value l; expect = Nbe.show_value r })
  in
  match term with
  | Syn.Let (def, def_t, body) ->
      let def_t = Nbe.eval (to_nbe_env env) def_t in
      check ~env ~size ~term:def ~typ:def_t;
      let def = Nbe.eval (to_nbe_env env) def in
      check ~env:((def, def_t) :: env) ~size:(size + 1) ~term:body ~typ
  | Syn.Lam body -> (
      match typ with
      | Nbe.Pi (lt, rt) ->
          let l = Nbe.mk_var lt size in
          let rt = Nbe.eval_clos rt l in
          check ~env:((l, lt) :: env) ~size:(size + 1) ~term:body ~typ:rt
      | _ ->
          type_error
            (Mismatch
               { found = Syn.show_expr term; expect = Nbe.show_value typ }))
  | Syn.Pair (l, r) -> (
      match typ with
      | Nbe.Sigma (lt, rt) ->
          check ~env ~size ~term:l ~typ:lt;
          let l = Nbe.eval (to_nbe_env env) l in
          let rt = Nbe.eval_clos rt l in
          check ~env ~size ~term:r ~typ:rt
      | _ ->
          type_error
            (Mismatch
               { found = Syn.show_expr term; expect = Nbe.show_value typ }))
  | Syn.Refl v -> (
      match typ with
      | Nbe.Id (t, l, r) ->
          check ~env ~size ~term:v ~typ:t;
          let v = Nbe.eval (to_nbe_env env) v in
          assert_equal size v l t;
          assert_equal size v r t
      | _ ->
          type_error
            (Mismatch
               { found = Syn.show_expr term; expect = Nbe.show_value typ }))
  | Syn.Thunk c -> (
      match typ with
      | Nbe.Underline ct -> check ~env ~size ~term:c ~typ:ct
      | _ ->
          type_error
            (Mismatch
               { found = Syn.show_expr term; expect = Nbe.show_value typ }))
  | Syn.Force uc -> (
      match typ with
      | Nbe.Free _ | Nbe.Neutral _ ->
          check ~env ~size ~term:uc ~typ:(Nbe.Underline typ)
      | _ ->
          type_error
            (Mismatch
               { found = Syn.show_expr term; expect = Nbe.show_value typ }))
  | Syn.Return v -> (
      match typ with
      | Nbe.Free vt -> check ~env ~size ~term:v ~typ:vt
      | _ ->
          type_error
            (Mismatch
               { found = Syn.show_expr term; expect = Nbe.show_value typ }))
  | Syn.CLam body -> (
      match typ with
      | Nbe.CPi (lt, rt) ->
          let l = Nbe.mk_var lt size in
          let rt = Nbe.eval_clos rt l in
          check ~env:((l, lt) :: env) ~size:(size + 1) ~term:body ~typ:rt
      | _ ->
          type_error
            (Mismatch
               { found = Syn.show_expr term; expect = Nbe.show_value typ }))
  | _ -> assert_type size (synth ~env ~size ~term) typ

and synth ~(env : env) ~(size : int) ~(term : Syn.expr) =
  match term with
  | Syn.Index i -> (
      match List.nth_opt env i with
      | Some (_, typ) -> typ
      | _ -> type_error (UnboundVar { index = i; env }))
  | Syn.Level i -> synth ~env ~size ~term:(Syn.Index (size - i - 1))
  | Syn.Type _ | Syn.Void | Syn.Unit | Syn.Bool -> Nbe.Type 0
  | Syn.Pi (lt, rt) | Syn.Sigma (lt, rt) ->
      check ~env ~size ~term:lt ~typ:(Nbe.Type 0);
      let lt = Nbe.eval (to_nbe_env env) lt in
      assert_value_type lt;
      let l = Nbe.mk_var lt size in
      let renv = (l, lt) :: env in
      check ~env:renv ~size ~term:rt ~typ:(Nbe.Type 0);
      let rt = Nbe.eval (to_nbe_env renv) rt in
      assert_value_type rt;
      Nbe.Type 0
  | Syn.App (f, a) -> (
      match synth ~env ~size ~term:f with
      | Nbe.Pi (lt, rt) ->
          check ~env ~size ~term:a ~typ:lt;
          let a = Nbe.eval (to_nbe_env env) a in
          Nbe.eval_clos rt a
      | _ -> type_error (Mismatch { found = Syn.show_expr f; expect = "Π" }))
  | Syn.Fst p -> (
      match synth ~env ~size ~term:p with
      | Nbe.Sigma (lt, _) -> lt
      | _ -> type_error (Mismatch { found = Syn.show_expr p; expect = "Σ" }))
  | Syn.Snd p -> (
      match synth ~env ~size ~term:p with
      | Nbe.Sigma (_, rt) ->
          let l = Nbe.eval (to_nbe_env env) (Syn.Fst p) in
          Nbe.eval_clos rt l
      | _ -> type_error (Mismatch { found = Syn.show_expr p; expect = "Σ" }))
  | Syn.Exfalso (target, mot) ->
      check ~env ~size ~term:target ~typ:Nbe.Void;
      check ~env ~size ~term:mot ~typ:(Nbe.Type 0);
      Nbe.eval (to_nbe_env env) mot
  | Syn.Trivial -> Nbe.Unit
  | Syn.Singleton (target, mot, base) ->
      check ~env ~size ~term:target ~typ:Nbe.Unit;
      let x = Nbe.mk_var Nbe.Unit size in
      check ~env:((x, Nbe.Unit) :: env) ~size:(size + 1) ~term:mot
        ~typ:(Nbe.Type 0);
      let bt = Nbe.eval (Nbe.Trivial :: to_nbe_env env) mot in
      check ~env ~size ~term:base ~typ:bt;
      let target = Nbe.eval (to_nbe_env env) target in
      Nbe.eval (target :: to_nbe_env env) mot
  | Syn.True | Syn.False -> Nbe.Bool
  | Syn.If (target, tt, ff, mot) ->
      check ~env ~size ~term:target ~typ:Nbe.Bool;
      check ~env ~size ~term:mot ~typ:(Nbe.Type 0);
      let typ = Nbe.eval (to_nbe_env env) mot in
      check ~env ~size ~term:tt ~typ;
      check ~env ~size ~term:ff ~typ;
      typ
  | Syn.Id (t, l, r) ->
      check ~env ~size ~term:t ~typ:(Nbe.Type 0);
      let t = Nbe.eval (to_nbe_env env) t in
      assert_value_type t;
      check ~env ~size ~term:l ~typ:t;
      check ~env ~size ~term:r ~typ:t;
      Nbe.Type 0
  | Syn.J (target, mot, base) -> (
      match synth ~env ~size ~term:target with
      | Nbe.Id (typ, l, r) ->
          let x = Nbe.mk_var typ size in
          let bt = Nbe.eval (Nbe.Refl x :: x :: x :: to_nbe_env env) mot in
          check ~env:((x, typ) :: env) ~size:(size + 1) ~term:base ~typ:bt;
          let target = Nbe.eval (to_nbe_env env) target in
          Nbe.eval (target :: r :: l :: to_nbe_env env) mot
      | _ ->
          type_error (Mismatch { found = Syn.show_expr target; expect = "Id" }))
  | Syn.Underline ct ->
      let ct = Nbe.eval (to_nbe_env env) ct in
      assert_comp_type ct;
      Nbe.Type 0
  | Syn.Free vt ->
      check ~env ~size ~term:vt ~typ:(Nbe.Type 0);
      let vt = Nbe.eval (to_nbe_env env) vt in
      assert_value_type vt;
      Nbe.Type 0
  | Syn.Compose (c1, v1t, c2t, c2) ->
      check ~env ~size ~term:v1t ~typ:(Nbe.Type 0);
      let v1t = Nbe.eval (to_nbe_env env) v1t in
      assert_value_type v1t;
      check ~env ~size ~term:c1 ~typ:(Nbe.Free v1t);
      check ~env ~size ~term:c2t ~typ:(Nbe.Type 0);
      let c2t = Nbe.eval (to_nbe_env env) c2t in
      assert_comp_type c2t;
      let x = Nbe.mk_var v1t size in
      check ~env:((x, v1t) :: env) ~size:(size + 1) ~term:c2 ~typ:c2t;
      c2t
  | Syn.CPi (lt, rt) ->
      check ~env ~size ~term:lt ~typ:(Nbe.Type 0);
      let lt = Nbe.eval (to_nbe_env env) lt in
      assert_value_type lt;
      let l = Nbe.mk_var lt size in
      let renv = (l, lt) :: env in
      check ~env:renv ~size ~term:rt ~typ:(Nbe.Type 0);
      let rt = Nbe.eval (to_nbe_env renv) rt in
      assert_comp_type rt;
      Nbe.Type 0
  | Syn.CApp (f, a) -> (
      match synth ~env ~size ~term:f with
      | Nbe.CPi (lt, rt) ->
          check ~env ~size ~term:a ~typ:lt;
          let a = Nbe.eval (to_nbe_env env) a in
          Nbe.eval_clos rt a
      | _ -> type_error (Mismatch { found = Syn.show_expr f; expect = "Π̱" }))
  | Syn.Get l ->
      check ~env ~size ~term:l ~typ:Nbe.Bool (* Loc *);
      Nbe.Free Nbe.Bool (* Val *)
  | Syn.Put (l, v) ->
      check ~env ~size ~term:l ~typ:Nbe.Bool (* Loc *);
      check ~env ~size ~term:v ~typ:Nbe.Bool (* Val *);
      Nbe.Free Nbe.Unit
  | _ -> type_error (CannotSynth term)
