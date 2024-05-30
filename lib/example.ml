open Syntax
(* axioms : 

a0 : (uC:U<0>) -> (k:Unit->U uC) -> (l:Bool) ->
Id(U uC, thunk (get(l) to x:Bool.put(l, x) to _. force (k unit)), k unit)

*)

let a0_typ = Pi((* uC: *)Type(0), 
  Pi((* k : *) Pi((* _ : *)Unit, Underline(Index(1))), 
  Pi((* l : *) Bool, 
    Id(Underline(Index(2)), 
    Thunk( 
      Compose(Get(Index(0)), Bool, Index(2), (* x:Bool *) 
      Compose(Put(Index(1), Index(0)), Unit, Index(3), (* _:Unit *) Force(App(Index(3), Trivial))   
    ))),
    (App(Index(1), Trivial)) (* k unit *)
    )
  )))

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