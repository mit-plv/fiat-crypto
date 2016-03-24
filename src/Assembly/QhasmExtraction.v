


(*
- Define an evaluation function over the QH type, which can be terribly inefficient. This function will be parametrized in the following way:  
  
    evalReg x InputRegs OutputRegs
    evalStack x InputStack OutputStack

Then, produce a lemma which shows that evaluating a given QH will perform an appropriate register operation. This will not check side-effects, which should be okay since we’re synthesizing in a very controlled manner.

- Work on {x: QH | eval x _ _ = AST}, like the bounding code  

- Introduce all Inputs as StackX 

- Replace upward as:  

    + Lifted functions by lemma (as above)
    + Conditionals as QCond, by lemma

- Then we can convert to string:  

    + We can introduce stack inputs, etc. by traversing the AST
    + QSeq, QStatement, QAssign are convertible directly
    + QCond, QWhile are fixed assembly wrappers *)