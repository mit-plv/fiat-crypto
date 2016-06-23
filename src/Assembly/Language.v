
Module Type Language.
  Parameter Params: Type.
  Parameter Program: Params -> Type.
  Parameter State: Params -> Type.

  Parameter evaluatesTo: forall x: Params, Program x -> State x -> State x -> Prop.
End Language.
