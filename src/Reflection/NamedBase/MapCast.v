Require Import Coq.Bool.Sumbool.
Require Import Crypto.Reflection.NamedBase.Syntax.
(*Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.*)

Local Open Scope nexpr_scope.
Section language.
  Context {base_type_code : Type}
          {Name : Type}
          {interp_base_type_bounds : base_type_code -> Type}
          (interp_op_bounds : forall src1 src2 dst, interp_base_type_bounds src1 -> interp_base_type_bounds src2 -> interp_base_type_bounds dst)
          (pick_typeb : forall t, interp_base_type_bounds t -> base_type_code)
          (cast_op : forall t1 t2 tR arg1_bs arg2_bs
                            (arg1v : exprf base_type_code Name (pick_typeb _ arg1_bs))
                            (arg2v : exprf base_type_code Name (pick_typeb _ arg2_bs)),
              exprf base_type_code Name (pick_typeb _ (interp_op_bounds t1 t2 tR arg1_bs arg2_bs)))
          {Context : Context Name interp_base_type_bounds}.

  Fixpoint mapf_cast
           (ctx : Context)
           {t} (e : exprf base_type_code Name t)
           {struct e}
    : option { bounds : interp_base_type_bounds t
                        & exprf base_type_code Name (pick_typeb _ bounds) }
    := match e in exprf _ _ t return option { bounds : interp_base_type_bounds t
                                                       & exprf base_type_code Name (pick_typeb _ bounds) } with
       | Var t x
         => option_map
              (fun bounds => existT _ bounds (Var x))
              (lookupb (t:=t) ctx x)
       | LetIn tx n ex tC eC
         => match @mapf_cast ctx _ ex with
            | Some (existT x_bounds ex')
              => @mapf_cast (extendb (t:=tx) ctx n x_bounds) _ eC
            | None => None
            end
       | BinOp t1 t2 tR arg1 arg2
         => match @mapf_cast ctx _ arg1, @mapf_cast ctx _ arg2 with
            | Some (existT arg1_bounds arg1'),
              Some (existT arg2_bounds arg2')
              => Some (existT _ _ (cast_op _ _ _ _ _ arg1' arg2'))
            | None, _ | _, None => None
            end
       end.
End language.
