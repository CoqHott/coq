(* #7329 *)

Set Primitive Projections.

Module M.
  Record Box := box { unbox : Type }.

  Axiom foo : Box.
  Axiom baz : unbox foo -> unbox foo.
End M.

Include M.
