
Module Type Language.
  Parameter Program: Type.
  Parameter State: Type.

  Parameter evaluatesTo: Program -> State -> State -> Prop.
End Language.
