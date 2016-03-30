
Module Type Language.
  Parameter Program: Type.
  Parameter State: Type.

  Parameter eval: Program -> State -> option State.
End Language.
