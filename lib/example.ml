open Syntax
let loc_typ = Bool
let val_typ = Bool

(* axioms : 

a0 : (uC:U<0>) -> (k:Unit->U uC) -> (l:Loc) ->
Id(U uC, thunk (get(l) to x:Val.put(l, x) to _. force (k unit)), k unit)

*)
module Axioms = struct
let a0_typ = Pi((* uC: *)Type(0), 
  Pi((* k : *) Pi((* _ : *)Unit, Underline(Index(1))), 
  Pi((* l : *) loc_typ, 
    Id(Underline(Index(2)), 
    Thunk( 
      Compose(Get(Index(0)), val_typ, Index(2), (* x:Bool *) 
      Compose(Put(Index(1), Index(0)), Unit, Index(3), (* _:Unit *) Force(App(Index(3), Trivial))   
    ))),
    (App(Index(1), Trivial)) (* k unit *)
    )
  )))
(* 

a1 : (uC:U<0>) -> (k:Val->U uC) -> (l:Loc) -> (v:Val) ->
Id(U uC, 
  thunk (put(l, v) to _:Unit. get(l) to v:Val force (k v)), 
  thunk (put(l, v) to _:Unit. force (k v))
)

*)
let a1_typ = Pi((* uC: *)Type(0), 
  Pi((* k : *) Pi((* _ : *)Unit, Underline(Index(1))), 
  Pi((* l : *) loc_typ, 
  Pi((* v : *) val_typ,
    Id(Underline(Index(3)), 
    Thunk(
      Compose(Put(Index(1), Index(0)), Unit, Index(3), (* _:Unit *) 
      Compose(Get(Index(2)), val_typ, Index(4), (* v:Val *) Force(App(Index(4), Trivial)))
      )
    ),
    Thunk(
      Compose(Put(Index(1), Index(0)), Unit, Index(3), (* _:Unit *) Force(App(Index(3), Trivial)))
    )
    )
  ))))

(*
a2 : (uC:U<0>) -> (k:Unit->U uC) -> (l:Loc) -> (v1:Val) -> (v2:Val) ->
Id(U uC, 
  thunk (put(l, v1) to _:Unit. put(l, v2) to _:Unit force (k unit)), 
  thunk (put(l, v2) to _:Unit. force (k unit))
)   
*)
let a2_typ = Pi((* uC: *)Type(0), 
  Pi((* k : *) Pi((* _ : *)Unit, Underline(Index(1))), 
  Pi((* l : *) loc_typ, 
  Pi((* v1 : *) val_typ,
  Pi((* v2 : *) val_typ,
    Id(Underline(Index(4)), 
    Thunk(
      Compose(Put(Index(2), Index(1)), Unit, Index(4), (* _:Unit *) 
      Compose(Put(Index(3), Index(1)), Unit, Index(5), (* _:Unit *)
        Force(App(Index(5), Trivial))
      ))
    ),
    Thunk(
      Compose(Put(Index(2), Index(0)), Unit, Index(3), (* _:Unit *) 
        Force(App(Index(4), Trivial))
      )
    )
    )
  )))))
(* 

a3 : (uC:U<0>) -> (k:Val->Val->U uC) -> (l1:Loc) -> (l2:Loc) ->
Id(U uC, 
  thunk (get(l1) to v1:Val. get(l2) to v2:Val. force (k v1 v2)), 
  thunk (get(l2) to v2:Val. get(l1) to v1:Val. force (k v1 v2)), 
)

*)
let a3_typ = Pi((* uC: *)Type(0), 
  Pi((* k : *) Pi((* _ : *)val_typ, Pi((* _ : *) val_typ, Underline(Index(2)))), 
  Pi((* l1 : *) loc_typ, 
  Pi((* l2 : *) val_typ,
    Id(Underline(Index(3)), 
    Thunk(
      Compose(Get(Index(1)), val_typ, Index(3), (* v1:Val *) 
      Compose(Get(Index(1)), val_typ, Index(4), (* v2:Val *)
        Force(App(App(Index(4), Index(1)), Index(0)))
      ))
    ),
    Thunk(
      Compose(Get(Index(0)), val_typ, Index(3), (* v2:Val *) 
      Compose(Get(Index(2)), val_typ, Index(4), (* v1:Val *)
        Force(App(App(Index(4), Index(0)), Index(1)))
      ))
    )
    )
  ))))

(*
a4 : (uC:U<0>) -> (k:Unit->U uC) -> (l1:Loc) -> (l2:Loc) -> (v1:Val) -> (v2:Val) ->
(Id(Loc, l1, l2) -> Void) ->
Id(U uC, 
  thunk (put(l1, v1) to _:Unit. put(l2, v2) to _:Unit. force (k unit)), 
  thunk (put(l2, v2) to _:Unit. put(l1, v1) to _:Unit. force (k unit))
)
*)
let a4_typ = Pi((* uC: *)Type(0), 
  Pi((* k : *) Pi((* _ : *)Unit, Underline(Index(1))), 
  Pi((* l1 : *) loc_typ, 
  Pi((* l2 : *) loc_typ, 
  Pi((* v1 : *) val_typ,
  Pi((* v2 : *) val_typ,
  Pi((* dis : *) Pi(Id(loc_typ, Index(3), Index(2)), Void),
    Id(Underline(Index(6)), 
    Thunk(
      Compose(Put(Index(4), Index(2)), Unit, Index(6), (* _:Unit *) 
      Compose(Put(Index(4), Index(2)), Unit, Index(7), (* _:Unit *)
        Force(App(Index(7), Trivial))
      ))
    ),
    Thunk(
      Compose(Put(Index(3), Index(1)), Unit, Index(6), (* _:Unit *) 
      Compose(Put(Index(5), Index(3)), Unit, Index(7), (* _:Unit *)
        Force(App(Index(7), Trivial))
      ))
    )
    )
  )))))))

end

module Base = struct 

(*
let subst : (A : U<0>) (B: A->U<0>) (a1 : A) (a2 : A) -> Id(A, a1, a2) -> (B a1) -> (B a2) =
  fun A B a1 a2 path ->
  match path at x y p -> (B x) -> (B y) with
  | refl _ -> fun x -> x   
*)
let subst_typ = 
  Pi((* A : *) Type 0, 
  Pi((* B : *) Pi(Index(0), Type 0),
  Pi((* a1 : A*) Index(1),
  Pi((* a2 : A*) Index(2),
  Pi((* path : *) Id(Index(3), Index(1), Index(0)),
  Pi((* b1 : *) App(Index(3), Index(2)), 
    App(Index(4), Index(2))
  ))))))

let subst = Lam((* A *) Lam((* B *) 
  Lam((* a1 *) Lam((* a2 *) Lam((* path *) Lam((* b1 *)
  J(Index(1), 
    (* x y p. *) Pi((* bx *) App(Index(7), Index(2)), App(Index(7), Index(1))), 
    (* _ *) Lam((* x *) Index(0))
  )
  ))))))

let subst_help a_typ b_typ a1 a2 path b1 = 
  App(App(App(App(App(App(subst, a_typ), b_typ), a1), a2), path), b1)
let rewrite_typ =   
  Pi((* A : *) Type 0, 
  Pi((* B : *) Type 0,
  Pi((* F : *) Pi((*_:*)Index(1), Index(1)),
  Pi((* a1 : A*) Index(1),
  Pi((* a2 : A*) Index(2),
  Pi((* p : *) Id(Index(4), Index(1), Index(0)),
  Id(Index(4), App(Index(3), Index(2)), App(Index(3), Index(1)))
  ))))))

let rewrite = Lam((* A *) Lam((* B *) Lam ((* F *) 
  Lam((* a1 *) Lam((* a2 *) Lam((* path *) 
  (* 
  App(App(App(App(App(App(subst, Index(5)), 
    Lam((* a *) Id(Index(5), App(Index(4), Index(3)), App(Index(4), Index(0))))),
    Index(2)),
    Index(1)),
    Index(0)),
    Refl(App(Index(3), Index(2)))
  )
  *)
  subst_help (Index 5) 
    (Lam((* a *) Id(Index(5), App(Index(4), Index(3)), App(Index(4), Index(0)))))
    (Index 2) (Index 1) (Index 0) (Refl(App(Index 3, Index 2)))
  ))))))

let rewrite_helper a_typ b_typ f a1 a2 p =
  App(App(App(App(App(App(rewrite, a_typ), b_typ), f), a1), a2), p)

end


(* 
let swap : (uC : U<0>) -> (k:U uC) -> uC =
  fun uC k -> 
    get(true)  to (x:Bool). as uC 
    get(false) to (y:Bool). as uC
    put(true,  y) to (_:Unit). as uC
    put(false, x) to (_:Unit). as uC
    force k
*)
let swap_typ = CPi((* uC : *)Type(0), 
  CPi((* k : *)Underline(Index(0)), Index(1)))
let swap = CLam((* uC *) CLam((* k *)
    Compose(Get(True), Bool, Index(1), (* x *) 
    Compose(Get(False), Bool, Index(2), (* y *) 
    Compose(Put(True, Index(0)), Unit, Index(3), (* _ *)
    Compose(Put(False, Index(2)), Unit, Index(4), (* _ *)
    Force(Index(4))
    ))))
))
let test = CApp(CApp(swap, Free(Bool)), Thunk(Get(True)))
let left_typ = CPi((* uC : *)Type(0), 
  CPi((* k : *)Underline(Index(0)), Index(1)))
let left = CLam((* uC *) CLam((* k *)
  CApp(CApp(swap, Index(1)), 
    Thunk(CApp(CApp(swap, Index(1)), Index(0)))
  )
))
let right_typ = CPi((* uC : *)Type(0), 
  CPi((* k : *)Underline(Index(0)), Index(1)))
let right = CLam((* uC *) CLam((* k *)
  Force(Index(0))
))

let example_typ = Pi((* uC : *)Type(0), Pi((* k : *) Underline(Index(0)),
  Id(Underline(Index(1)),
  Thunk(CApp(CApp(left, Index(1)), Index(0))),
  Thunk(CApp(CApp(right, Index(1)), Index(0)))
  )
))

let example = Lam((* uC *)Lam((* k *)
    Trivial (* todo *)
))