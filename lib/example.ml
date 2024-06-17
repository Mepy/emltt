open Syntax
let loc_typ = Bool
let val_typ = Bool


let ap f a = App(f, a)
let ap2 f a1 a2 = App(App(f, a1), a2)

let ap3 f a1 a2 a3 = App(App(App(f, a1), a2), a3)
let ap4 f a1 a2 a3 a4 = App(App(App(App(f, a1), a2), a3), a4)
let ap5 f a1 a2 a3 a4 a5 = App(App(App(App(App(f, a1), a2), a3), a4), a5)
let ap6 f a1 a2 a3 a4 a5 a6 = App(App(App(App(App(App(f, a1), a2), a3), a4), a5), a6)
let ap7 f a1 a2 a3 a4 a5 a6 a7 = App(App(App(App(App(App(App(f, a1), a2), a3), a4), a5), a6), a7)

module Axioms = struct
(* 
a0 : (uC:U<0>) -> (k:Unit->U uC) -> (l:Loc) ->
Id(U uC, thunk (get(l) to x:Val.put(l, x) to _. force (k unit)), k unit)

*)
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
let a0 uC k l = ap3 (Level 0) uC k l
let a0_left = Lam((* uC: Type(0), *)
  Lam((* k : Pi((* _ : *)Unit, Underline(Index(1))), *) 
  Lam((* l : loc_typ, *)
    Thunk( 
      Compose(Get(Index(0)), val_typ, Index(2), (* x:Bool *) 
      Compose(Put(Index(1), Index(0)), Unit, Index(3), (* _:Unit *) 
        Force(App(Index(3), Trivial)) 
    )))
  )))
let a0_right = Lam((* uC: Type(0), *)
  Lam((* k : Pi((* _ : *)Unit, Underline(Index(1))), *) 
  Lam((* l : loc_typ, *)
    (App(Index(1), Trivial))
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
let a1 uC k l v = ap4 (Level 1) uC k l v
let a1_left = Lam((* uC: Type(0), *)
  Lam((* k : Pi((* _ : *)Unit, Underline(Index(1))), *)
  Lam((* l : loc_typ, *)
  Lam((* v : val_typ, *)
    Thunk(
      Compose(Put(Index(1), Index(0)), Unit, Index(3), (* _:Unit *) 
      Compose(Get(Index(2)), val_typ, Index(4), (* v:Val *) Force(App(Index(4), Trivial)))
      )
    )
  ))))
let a1_right = Lam((* uC: Type(0), *)
  Lam((* k : Pi((* _ : *)Unit, Underline(Index(1))), *)
  Lam((* l : loc_typ, *)
  Lam((* v : val_typ, *)
    Thunk(
      Compose(Put(Index(1), Index(0)), Unit, Index(3), (* _:Unit *) Force(App(Index(3), Trivial)))
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
let a2 uC k l v1 v2 = ap5 (Level 2) uC k l v1 v2
let a2_left = Lam((* uC: Type(0), *)
  Lam((* k : Pi((* _ : *)Unit, Underline(Index(1))), *)
  Lam((* l : loc_typ, *)
  Lam((* v1 : val_typ, *)
  Lam((* v2 : val_typ, *)
    Thunk(
      Compose(Put(Index(2), Index(1)), Unit, Index(4), (* _:Unit *) 
      Compose(Put(Index(3), Index(1)), Unit, Index(5), (* _:Unit *)
        Force(App(Index(5), Trivial))
      ))
    )
  )))))
let a2_right = Lam((* uC: Type(0), *)
  Lam((* k : Pi((* _ : *)Unit, Underline(Index(1))), *)
  Lam((* l : loc_typ, *)
  Lam((* v1 : val_typ, *)
  Lam((* v2 : val_typ, *)
    Thunk(
      Compose(Put(Index(2), Index(0)), Unit, Index(3), (* _:Unit *) 
        Force(App(Index(4), Trivial))
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
let a3 uC k l1 l2 = ap4 (Level 3) uC k l1 l2
let a3_left = 
  Lam((* uC: Type(0), *)
  Lam((* k : Pi((* _ : *)val_typ, Pi((* _ : *) val_typ, Underline(Index(2)))), *)
  Lam((* l1 : loc_typ, *)
  Lam((* l2 : val_typ, *)
    Thunk(
      Compose(Get(Index(1)), val_typ, Index(3), (* v1:Val *) 
      Compose(Get(Index(1)), val_typ, Index(4), (* v2:Val *)
        Force(App(App(Index(4), Index(1)), Index(0)))
      ))
    )
  ))))

let a3_right = 
  Lam((* uC: Type(0), *)
  Lam((* k : Pi((* _ : *)val_typ, Pi((* _ : *) val_typ, Underline(Index(2)))), *)
  Lam((* l1 : loc_typ, *)
  Lam((* l2 : val_typ, *)
    Thunk(
      Compose(Get(Index(0)), val_typ, Index(3), (* v2:Val *) 
      Compose(Get(Index(2)), val_typ, Index(4), (* v1:Val *)
        Force(App(App(Index(4), Index(0)), Index(1)))
      ))
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

let a4 uC k l1 l2 v1 v2 dis = ap7 (Level 4) uC k l1 l2 v1 v2 dis
let a4_left = Lam((* uC: Type(0), *)
  Lam((* k : Pi((* _ : *)Unit, Underline(Index(1))), *)
  Lam((* l1 : loc_typ, *)
  Lam((* l2 : loc_typ, *)
  Lam((* v1 : val_typ, *)
  Lam((* v2 : val_typ, *)
  Lam((* dis : Pi(Id(loc_typ, Index(3), Index(2)), Void), *)
    Thunk(
      Compose(Put(Index(4), Index(2)), Unit, Index(6), (* _:Unit *) 
      Compose(Put(Index(4), Index(2)), Unit, Index(7), (* _:Unit *)
        Force(App(Index(7), Trivial))
      ))
    )
  )))))))

let a4_right = Lam((* uC: Type(0), *)
  Lam((* k : Pi((* _ : *)Unit, Underline(Index(1))), *)
  Lam((* l1 : loc_typ, *)
  Lam((* l2 : loc_typ, *)
  Lam((* v1 : val_typ, *)
  Lam((* v2 : val_typ, *)
  Lam((* dis : Pi(Id(loc_typ, Index(3), Index(2)), Void), *)
    Thunk(
      Compose(Put(Index(3), Index(1)), Unit, Index(6), (* _:Unit *) 
      Compose(Put(Index(5), Index(3)), Unit, Index(7), (* _:Unit *)
        Force(App(Index(7), Trivial))
      ))
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

let subst5 a_typ b_typ a1 a2 path = 
    App(App(App(App(App(subst, a_typ), b_typ), a1), a2), path)
  
let subst6 a_typ b_typ a1 a2 path b1 = 
  App(App(App(App(App(App(subst, a_typ), b_typ), a1), a2), path), b1)

(*
let dis : Id (Bool, tt, ff) -> Void =
  let large_elim : Bool -> U<0> = 
      fun x -> if x then Id(Bool, tt, tt) else Void end 
      (* Id(Bool, tt, tt) : U<0>, Void : U<0> *)
  in fun path -> subst Bool large_elim tt ff refl(tt)

*)
let dis_typ = Pi(Id(Bool, True, False), Void)
let dis = Lam((* path : Id(Bool, True, False) *)
  subst5 Bool (Lam(* x:Bool *) (If(Index 0, Id(Bool, True, True), Void, Type 0)))
  True False (Refl True)
  )

(* 
let rewrite : (A : U<0>) -> (B : U<0>) -> (F : A -> B) ->
  (a1 : A) -> (a2 : A) -> Id(A, a1, a2) -> Id(B, F a1, F a2) =
  fun A B F a1 a2 path ->
  subst A (fun a -> Id(B, F a1, F a)) a1 a2 path refl(F a1)  
*)
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
  subst6 (Index 5) 
    (Lam((* a *) Id(Index(5), App(Index(4), Index(3)), App(Index(4), Index(0)))))
    (Index 2) (Index 1) (Index 0) (Refl(App(Index 3, Index 2)))
  ))))))

let rewrite6 a_typ b_typ f a1 a2 p =
  App(App(App(App(App(App(rewrite, a_typ), b_typ), f), a1), a2), p)

(*
let symm : (A : U<0>) (a1:A) (a2:A) ->
  Id(A, a1, a2) -> Id(A, a2, a1) =
  fun A a1 a2 path ->
  subst A (fun a -> Id(A, a, a1)) a1 a2 path refl(a1)
   
*)
let symm_typ = 
  Pi((* A : *) Type 0, 
  Pi((* a1 : A*) Index(0),
  Pi((* a2 : A*) Index(1),
  Pi((* path : *) Id(Index(2), Index(1), Index(0)),
    Id(Index(3), Index(1), Index(2))
  ))))

let symm = Lam((* A *) Lam((* a1 *) Lam((* a2 *) Lam((* path *)
  subst6 (Index 3) 
    (Lam (* a *)(Id(Index 4, Index 0, Index 3)))
    (Index 2) (Index 1) (Index 0) (Refl (Index 2))
  ))))

let symm4 a_typ a1 a2 path = App(App(App(App(symm, a_typ), a1), a2), path)

(* 
let tran : (A : U<0>) (a1:A) (a2:A) (a3:A) -> 
  Id(A, a1, a2) -> Id(A, a2, a3) -> Id(A, a1, a3) =
  fun A a1 a2 a3 path ->
  let path' : Id(A, a2, a1) = symm A a1 a2 path in
  subst A (fun a -> Id(A, a, a3)) a1 a2 path'
*)
let tran_typ = 
  Pi((* A : *) Type 0, 
  Pi((* a1 : A*) Index(0),
  Pi((* a2 : A*) Index(1),
  Pi((* a3 : A*) Index(1),
  Pi((* p12 : *) Id(Index(3), Index(2), Index(1)),
  Pi((* p23 : *) Id(Index(4), Index(2), Index(1)),
    Id(Index(5), Index(4), Index(2))
  ))))))
  

let tran = Lam((* A *) Lam((* a1 *) Lam((* a2 *) Lam((* a3*) Lam((* p12 *)
  subst5 (Index 4) 
    (Lam (* a *) (Id(Index 5, Index 0, Index 2)))
    (Index 3) (Index 2)
    (symm4 (Index 4) (Index 3) (Index 2) (Index 0))
  )))))

let tran6 a_typ a1 a2 a3 p12 p23 = App(App(App(App(App(App(tran, a_typ), a1), a2), a3), p12), p23)


end


module Swap = struct 

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

(* to prove example, we assume (uC:U<0>) -> (k:U uC) -> *)
let uC = Index 1
let uuC = Underline uC
let k = Index 0

let tm0 = Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
  Compose (Put (True , Index 0 (* y *)), Unit, Index 3, (* _ : Val *)
  Compose (Put (False, Index 2 (* x *)), Unit, Index 4, (* _ : Val *)
  Compose (Get True , val_typ, Index 5, (* x' : Val *)
  Compose (Get False, val_typ, Index 6, (* y' : Val *)
  Compose (Put (True , Index 0 (* y' *)), Unit, Index 7, (* _ : Val *)
  Compose (Put (False, Index 2 (* x' *)), Unit, Index 8, (* _ : Val *)
    Force (Index 8)
  )))))))))
  (* Axioms.a3 *)

let step0 = (* uC:U<0>. k:U uC. *)
( let h = Base.rewrite6 uuC uuC (Lam (* k : U uC *) (Thunk(
  Compose (Get True , val_typ, Index 2,  (* x : Val *)
  Compose (Get False, val_typ, Index 3,  (* y : Val *)
  Compose (Put (True , Index 0), Unit, Index 4, (* _ : Val *)
  Compose (Put (False, Index 2), Unit, Index 5, (* _ : Val *)
    Force (Index 4)
  ))))))) in
  let k (* : Val -> Val -> U uC *) = Lam (* v1 *) (Lam (* v2 *) (Thunk (
  Compose (Put (True , Index 0), Unit, Index 9, (* _ : Val *)
  Compose (Put (False, Index 2), Unit, Index 10, (* _ : Val *)
    Force (Index 10)
  ))))) in
  h
  (ap4 Axioms.a3_left uC k True False) 
  (ap4 Axioms.a3_right uC k True False)
  (Axioms.a3 uC k True False)
)

let tm1 = Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
  Compose (Put (True , Index 0 (* y *)), Unit, Index 3, (* _ : Val *)
  Compose (Put (False, Index 2 (* x *)), Unit, Index 4, (* _ : Val *)
  Compose (Get False, val_typ, Index 5, (* y' : Val *)
  Compose (Get True , val_typ, Index 6, (* x' : Val *)
  Compose (Put (True , Index 1 (* y' *)), Unit, Index 7, (* _ : Val *)
  Compose (Put (False, Index 1 (* x' *)), Unit, Index 8, (* _ : Val *)
    Force (Index 8)
  )))))))))

  (* Axioms.a1, FREE VAR NEEDED *)
(* todo a1 *)
let step1 =(* uC:U<0>. k:U uC. *)
( let h = Base.rewrite6 uuC uuC (Lam (* k : U uC *) (Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
  Compose (Put (False, Index 1 (* x *)), Unit, Index 3, (* _ : Val *)
    Force (Index 3)
  )))))) in
  let k (* : Val -> U uC *) = Lam (* v:Val *) (Thunk (
    Compose (Get True , val_typ, Index 7, (* x' : Val *)
    Compose (Put (True , Index 0 (* y'=v *)), Unit, Index 8, (* _ : Val *)
    Compose (Put (False, Index 1 (* x' *)), Unit, Index 9, (* _ : Val *)
      Force (Index 9)
    ))))) in
  h
  (ap4 Axioms.a1_left uC k False (Index 2)) 
  (ap4 Axioms.a1_right uC k False (Index 2))
  (Axioms.a1 uC k False (Index 2) )
)
let tm2 = Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
  Compose (Put (True , Index 0 (* y *)), Unit, Index 3, (* _ : Val *)
  Compose (Put (False, Index 2 (* x *)), Unit, Index 4, (* _ : Val *)
  Compose (Get True , val_typ, Index 5, (* x' : Val *)
  Compose (Put (True , Index 4 (* y'=x *)), Unit, Index 6, (* _ : Val *)
  Compose (Put (False, Index 1 (* x' *)), Unit, Index 7, (* _ : Val *)
    Force (Index 7)
  ))))))))

(* Axioms.a4 , FREE VAR NEEDED *)
let step2 = (* uC:U<0>. k:U uC. *)
( let h = Base.rewrite6 uuC uuC (Lam (* k : U uC *) (Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
    Force (Index 2)
  ))))) in
  let k (* : Unit -> U uC *) = Lam (* _:Unit *) (Thunk (
    Compose (Get True , val_typ, Index 6, (* x' : Val *)
    Compose (Put (True , Index 5 (* y'=x *)), Unit, Index 7, (* _ : Val *)
    Compose (Put (False, Index 1 (* x' *)), Unit, Index 8, (* _ : Val *)
      Force (Index 8) (* outer k *)
    ))))) in
  let dis = Base.dis in
  h
  (ap7 Axioms.a4_left uC k True False (Index 0) (Index 2) dis) 
  (ap7 Axioms.a4_right uC k True False (Index 0) (Index 2) dis)
  (Axioms.a4 uC k True False (Index 0) (Index 2) dis)
)
let tm3 = Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
  Compose (Put (False, Index 1 (* x *)), Unit, Index 3, (* _ : Val *)
  Compose (Put (True , Index 1 (* y *)), Unit, Index 4, (* _ : Val *)
  Compose (Get True , val_typ, Index 5, (* x' : Val *)
  Compose (Put (True , Index 4 (* y'=x *)), Unit, Index 6, (* _ : Val *)
  Compose (Put (False, Index 1 (* x' *)), Unit, Index 7, (* _ : Val *)
    Force (Index 7)
  ))))))))

(* Axioms.a1 , FREE VAR NEEDED *)
let step3 = (* uC:U<0>. k:U uC. *)
( let h = Base.rewrite6 uuC uuC (Lam (* k : U uC *) (Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
  Compose (Put (False, Index 1 (* x *)), Unit, Index 3, (* _ : Val *)
  Compose (Put (True , Index 1 (* y *)), Unit, Index 4, (* _ : Val *)
    Force (Index 4)
  ))))))) in
  let k (* : Val -> U uC *) = Lam (* v:Val *) (Thunk (
  Compose (Put (False, Index 0 (* v:Val *)), Unit, Index 8 (* uC *), (* _ : Unit *)
    Force (Index 8) (* outer k *)
  ))) in
  h
  (ap4 Axioms.a1_left uC k True (Index 4)) 
  (ap4 Axioms.a1_right uC k True (Index 4))
  (Axioms.a1 uC k True (Index 4) )
)
let tm4 = Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
  Compose (Put (False, Index 1 (* x *)), Unit, Index 3, (* _ : Val *)
  Compose (Put (True , Index 1 (* y *)), Unit, Index 4, (* _ : Val *)
  Compose (Put (True , Index 3 (* y'=x *)), Unit, Index 5, (* _ : Val *)
  Compose (Put (False, Index 3 (* x'=y *)), Unit, Index 6, (* _ : Val *)
    Force (Index 6)
  )))))))

(* Axioms.a2 , FREE VAR NEEDED *)
let step4 = (* uC:U<0>. k:U uC. *)
( let h = Base.rewrite6 uuC uuC (Lam (* k : U uC *) (Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
  Compose (Put (False, Index 1 (* x *)), Unit, Index 3, (* _ : Val *)
    Force (Index 3)
  )))))) in
  let k (* : Unit -> U uC *) = Lam (* _:Unit *) (Thunk (
  Compose (Put (False, Index 4 (* y : Val *)), Unit, Index 7 (* uC *), (* _ : Unit *)
    Force (Index 7) (* outer k *)
  ))) in
  h
  (ap5 Axioms.a2_left uC k True (Index 1) (Index 3)) 
  (ap5 Axioms.a2_right uC k True (Index 1) (Index 3))
  (Axioms.a2 uC k True (Index 1) (Index 3)) (* metaprogramming TODO: begin from h/k *)
)
let tm5 = Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
  Compose (Put (False, Index 1 (* x *)), Unit, Index 3, (* _ : Val *)
  Compose (Put (True , Index 2 (* y'=x *)), Unit, Index 4, (* _ : Val *)
  Compose (Put (False, Index 2 (* x'=y *)), Unit, Index 5, (* _ : Val *)
    Force (Index 5)
  ))))))

(* Axioms.a4 , FREE VAR NEEDED *)
let step5 = (* uC:U<0>. k:U uC. *)
( let h = Base.rewrite6 uuC uuC (Lam (* k : U uC *) (Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
  Compose (Put (False, Index 1 (* x *)), Unit, Index 3, (* _ : Val *)
    Force (Index 3)
  )))))) in
  let k (* : Unit -> U uC *) = Lam (* _:Unit *) (Index 6) in
  let dis = Base.dis in
  h
  (ap7 Axioms.a4_left uC k True False (Index 2) (Index 2) dis) 
  (ap7 Axioms.a4_right uC k True False (Index 2) (Index 2) dis)
  (Axioms.a4 uC k True False (Index 2) (Index 2) dis)
)
let tm6 = Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
  Compose (Put (False, Index 1 (* x *)), Unit, Index 3, (* _ : Val *)
  Compose (Put (False, Index 1 (* x'=y *)), Unit, Index 4, (* _ : Val *)
  Compose (Put (True , Index 3 (* y'=x *)), Unit, Index 5, (* _ : Val *)
    Force (Index 5)
  ))))))

(* Axioms.a2 , FREE VAR NEEDED *)
let step6 = (* uC:U<0>. k:U uC. *)
( let h = Base.rewrite6 uuC uuC (Lam (* k : U uC *) (Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
    Force (Index 2)
  ))))) in
  (* TODO : make a2 : put; put; k = put; return (); k *)
  let k (* : Unit -> U uC *) = Lam (* _:Unit *) (Thunk (
  Compose (Put (True, Index 4 (* x : Val *)), Unit, Index 6 (* uC *), (* _ : Unit *)
    Force (Index 6) (* outer k *)
  ))) in
  h
  (ap5 Axioms.a2_left uC k False (Index 1) (Index 1)) 
  (ap5 Axioms.a2_right uC k False (Index 1) (Index 1))
  (Axioms.a2 uC k False (Index 1) (Index 1))
)
let tm7 = Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Get False, val_typ, Index 2,  (* y : Val *)
  Compose (Put (False, Index 0 (* x'=y *)), Unit, Index 3, (* _ : Unit *)
  Compose (Put (True , Index 2 (* y'=x *)), Unit, Index 4, (* _ : Unit *)
    Force (Index 4)
  )))))

(* Axioms.a0 *)
  (* a0 : (uC:U<0>) -> (k:Unit->U uC) -> (l:Loc) ->
  Id(U uC, thunk (get(l) to x:Val.put(l, x) to _. force (k unit)), k unit)
   *)
let step7 = (* uC:U<0>. k:U uC. *)
( let h = Base.rewrite6 uuC uuC (Lam (* k : U uC *) (Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Force (Index 1)
  )))) in
  (* TODO : make a0 : get;put; k = return (); return (); k *)
  let k (* : Unit -> U uC *) = Lam (* _:Unit *) (Thunk (
  Compose (Put (False, Index 3 (* x : Val *)), Unit, Index 5 (* uC *), (* _ : Unit *)
    Force (Index 5) (* outer k *)
  ))) in
  h
  (ap3 Axioms.a0_left uC k True) 
  (ap3 Axioms.a0_right uC k True)
  (Axioms.a0 uC k True)
)

let tm8 = Thunk(
  Compose (Get True , val_typ, Index 1,  (* x : Val *)
  Compose (Put (True , Index 2 (* y'=x *)), Unit, Index 2, (* _ : Val *)
    Force (Index 2)
  )))


(* Axioms.a0 *)
let step8 = (* uC:U<0>. k:U uC. *)
    Axioms.a0 uC (Lam (* _ : Unit *) (Index 1)) True

let tm9 = (Index 0)

let example = Lam((* uC *)Lam((* k *)
  (Base.tran6 uuC tm0 tm1 tm9 step0 
  (Base.tran6 uuC tm1 tm2 tm9 step1
  (Base.tran6 uuC tm2 tm3 tm9 step2
  (Base.tran6 uuC tm3 tm4 tm9 step3
  (Base.tran6 uuC tm4 tm5 tm9 step4
  (Base.tran6 uuC tm5 tm6 tm9 step5 
  (Base.tran6 uuC tm6 tm7 tm9 step6 
  (Base.tran6 uuC tm7 tm8 tm9 step7 step8
  ))))))))
))

end