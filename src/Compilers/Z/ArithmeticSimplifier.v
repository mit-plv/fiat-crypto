(** * SimplifyArith: Remove things like (_ * 1), (_ + 0), etc *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Rewriter.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Equality.
Require Import Crypto.Util.ZUtil.Definitions.

Section language.
  Context (convert_adc_to_sbb : bool).
  Local Notation exprf := (@exprf base_type op).
  Local Notation Expr := (@Expr base_type op).

  Section with_var.
    Context {var : base_type -> Type}.

    Inductive inverted_expr t :=
    | const_of (v : Z)
    | gen_expr (e : exprf (var:=var) (Tbase t))
    | neg_expr (e : exprf (var:=var) (Tbase t)).

    Fixpoint interp_as_expr_or_const {t} (x : exprf (var:=var) t)
      : option (interp_flat_type inverted_expr t)
      := match x in Syntax.exprf _ _ t return option (interp_flat_type _ t) with
         | Op t1 (Tbase _) opc args
           => Some (match opc in op src dst
                          return exprf dst
                                 -> exprf src
                                 -> match dst with
                                    | Tbase t => inverted_expr t
                                    | Prod _ _ => True
                                    | _ => inverted_expr TZ
                                    end
                    with
                    | OpConst _ z => fun _ _ => const_of _ z
                    | Opp TZ TZ => fun _ args => neg_expr _ args
                    | MulSplit _ _ _ _ _ => fun _ _ => I
                    | AddWithGetCarry _ _ _ _ _ _ => fun _ _ => I
                    | SubWithGetBorrow _ _ _ _ _ _ => fun _ _ => I
                    | _ => fun e _ => gen_expr _ e
                    end (Op opc args) args)
         | TT => Some tt
         | Var t v => Some (gen_expr _ (Var v))
         | Op _ _ _ _
         | LetIn _ _ _ _
           => None
         | Pair tx ex ty ey
           => match @interp_as_expr_or_const tx ex, @interp_as_expr_or_const ty ey with
              | Some vx, Some vy => Some (vx, vy)
              | _, None | None, _ => None
              end
         end.

    Fixpoint uninterp_expr_or_const {t} : interp_flat_type inverted_expr t -> exprf (var:=var) t
      := match t with
         | Tbase T => fun e => match e with
                               | const_of v => Op (OpConst v) TT
                               | gen_expr e => e
                               | neg_expr e => Op (Opp _ _) e
                               end
         | Unit => fun _ => TT
         | Prod A B => fun (ab : interp_flat_type _ A * interp_flat_type _ B)
                       => Pair (@uninterp_expr_or_const A (fst ab))
                               (@uninterp_expr_or_const B (snd ab))
         end.

    Definition simplify_op_expr {src dst} (opc : op src dst)
      : exprf (var:=var) src -> exprf (var:=var) dst
      := match opc in op src dst return exprf src -> exprf dst with
         | Add TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (const_of v, gen_expr e)
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | Some (const_of v, neg_expr e)
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (Opp _ _) e
                      else Op opc args
                 | Some (gen_expr ep, neg_expr en)
                 | Some (neg_expr en, gen_expr ep)
                   => Op (Sub _ _ _) (Pair ep en)
                 | _ => Op opc args
                 end
         | Add T1 T2 Tout as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of v, gen_expr e)
                   => if (v =? 0)%Z
                      then match base_type_eq_semidec_transparent T2 Tout with
                           | Some pf => eq_rect _ (fun t => exprf (Tbase t)) e _ pf
                           | None => Op opc args
                           end
                      else Op opc args
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then match base_type_eq_semidec_transparent T1 Tout with
                           | Some pf => eq_rect _ (fun t => exprf (Tbase t)) e _ pf
                           | None => Op opc args
                           end
                      else Op opc args
                 | _ => Op opc args
                 end
         | Sub TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (Opp _ _) e
                      else Op opc args
                 | Some (gen_expr e1, neg_expr e2)
                   => Op (Add _ _ _) (Pair e1 e2)
                 | Some (neg_expr e1, neg_expr e2)
                   => Op (Sub _ _ _) (Pair e2 e1)
                 | _ => Op opc args
                 end
         | Mul TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (const_of v, gen_expr e)
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else if (v =? 1)%Z
                           then e
                           else if (v =? -1)%Z
                                then Op (Opp _ _) e
                                else Op opc args
                 | Some (const_of v, neg_expr e)
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else if (v =? 1)%Z
                           then Op (Opp _ _) e
                           else if (v =? -1)%Z
                                then e
                                else if (v >? 0)%Z
                                     then Op (Opp _ _) (Op opc (Pair (Op (OpConst v) TT) e))
                                     else Op opc args
                 | Some (gen_expr e1, neg_expr e2)
                 | Some (neg_expr e1, gen_expr e2)
                   => Op (Opp _ _) (Op (Mul _ _ TZ) (Pair e1 e2))
                 | Some (neg_expr e1, neg_expr e2)
                   => Op (Mul _ _ _) (Pair e1 e2)
                 | _ => Op opc args
                 end
         | Mul (TWord bw1 as T1) (TWord bw2 as T2) (TWord bwout as Tout) as opc
           => fun args
              => let sz1 := (2^Z.of_nat (2^bw1))%Z in
                 let sz2 := (2^Z.of_nat (2^bw2))%Z in
                 let szout := (2^Z.of_nat (2^bwout))%Z in
                 match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (((Z.max 0 l mod sz1) * (Z.max 0 r mod sz2)) mod szout)%Z) TT
                 | Some (const_of v, gen_expr e)
                   => if ((Z.max 0 v mod sz1) mod szout =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else if ((Z.max 0 v mod sz1) mod szout =? 1)%Z
                           then match base_type_eq_semidec_transparent T2 Tout with
                                | Some pf => eq_rect _ (fun t => exprf (Tbase t)) e _ pf
                                | None => Op opc args
                                end
                           else Op opc args
                 | Some (gen_expr e, const_of v)
                   => if ((Z.max 0 v mod sz2) mod szout =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else if ((Z.max 0 v mod sz2) mod szout =? 1)%Z
                           then match base_type_eq_semidec_transparent T1 Tout with
                                | Some pf => eq_rect _ (fun t => exprf (Tbase t)) e _ pf
                                | None => Op opc args
                                end
                           else Op opc args
                 | _ => Op opc args
                 end
         | Shl TZ TZ TZ as opc
         | Shr TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (Opp _ _) e
                      else Op opc args
                 | _ => Op opc args
                 end
         | Land TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (const_of v, gen_expr _)
                 | Some (gen_expr _, const_of v)
                 | Some (const_of v, neg_expr _)
                 | Some (neg_expr _, const_of v)
                   => if (v =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else Op opc args
                 | _ => Op opc args
                 end
         | Lor TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (const_of v, gen_expr e)
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | Some (const_of v, neg_expr e)
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (Opp _ _) e
                      else Op opc args
                 | _ => Op opc args
                 end
         | Opp TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of v)
                   => Op (OpConst (interp_op _ _ opc v)) TT
                 | Some (neg_expr e)
                   => e
                 | _
                   => Op opc args
                 end
         | MulSplit bitwidth (TWord bw1 as T1) (TWord bw2 as T2) (TWord bwout1 as Tout1) (TWord bwout2 as Tout2) as opc
           => fun args
              => let sz1 := (2^Z.of_nat (2^bw1))%Z in
                 let sz2 := (2^Z.of_nat (2^bw2))%Z in
                 let szout1 := (2^Z.of_nat (2^bwout1))%Z in
                 let szout2 := (2^Z.of_nat (2^bwout2))%Z in
                 match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => let '(a, b) := Z.mul_split_at_bitwidth bitwidth (Z.max 0 l mod sz1) (Z.max 0 r mod sz2) in
                      Pair (Op (OpConst (a mod szout1)%Z) TT)
                           (Op (OpConst (b mod szout2)%Z) TT)
                 | Some (const_of v, gen_expr e)
                   => let v' := (Z.max 0 v mod sz1)%Z in
                      if (v' =? 0)%Z
                      then Pair (Op (OpConst 0%Z) TT) (Op (OpConst 0%Z) TT)
                      else if ((v' =? 1) && (2^Z.of_nat (2^bw2) <=? 2^bitwidth))%Z%bool
                           then match base_type_eq_semidec_transparent T2 Tout1 with
                                | Some pf => Pair (eq_rect _ (fun t => exprf (Tbase t)) e _ pf)
                                                  (Op (OpConst 0%Z) TT)
                                | None => Op opc args
                                end
                           else Op opc args
                 | Some (gen_expr e, const_of v)
                   => let v' := (Z.max 0 v mod sz2)%Z in
                      if (v' =? 0)%Z
                      then Pair (Op (OpConst 0%Z) TT) (Op (OpConst 0%Z) TT)
                      else if ((v' =? 1) && (2^Z.of_nat (2^bw1) <=? 2^bitwidth))%Z%bool
                           then match base_type_eq_semidec_transparent T1 Tout1 with
                                | Some pf => Pair (eq_rect _ (fun t => exprf (Tbase t)) e _ pf)
                                                  (Op (OpConst 0%Z) TT)
                                | None => Op opc args
                                end
                           else Op opc args
                 | _ => Op opc args
                 end
         | IdWithAlt (TWord _ as T1) _ (TWord _ as Tout) as opc
           => fun args
              => match base_type_eq_semidec_transparent T1 Tout with
                 | Some pf
                   => match interp_as_expr_or_const args with
                      | Some (const_of c, _)
                        => Op (OpConst c) TT
                      | Some (neg_expr e, _)
                        => Op (Opp _ _) e
                      | Some (gen_expr e, _)
                        => eq_rect _ (fun t => exprf (Tbase t)) e _ pf
                      | None
                        => Op opc args
                      end
                 | None
                   => Op opc args
                 end
         | IdWithAlt TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (gen_expr e1, gen_expr e2)
                   => match invert_Op e1, invert_Op e2 with
                      | Some (existT _ (Add TZ TZ TZ as opc1, args1)),
                        Some (existT _ (Add TZ TZ TZ as opc2, args2))
                      | Some (existT _ (Sub TZ TZ TZ as opc1, args1)),
                        Some (existT _ (Sub TZ TZ TZ as opc2, args2))
                      | Some (existT _ (Mul TZ TZ TZ as opc1, args1)),
                        Some (existT _ (Mul TZ TZ TZ as opc2, args2))
                        => match interp_as_expr_or_const args1, interp_as_expr_or_const args2 with
                           | Some (gen_expr e1, const_of c1),
                             Some (gen_expr e2, const_of c2)
                             => if Z.eqb c1 c2
                                then Op opc1 (Op opc (e1, e2), Op (OpConst c1) TT)%expr
                                else Op opc args
                           | _, _
                             => Op opc args
                           end
                      | _, _
                        => Op opc args
                      end
                 | Some (neg_expr e1, neg_expr e2)
                   => Op (Opp _ _) (Op opc (e1, e2)%expr)
                 | Some (const_of c1, const_of c2)
                   => Op (OpConst c1) TT
                 | _
                   => Op opc args
                 end
         | IdWithAlt _ _ (TWord _ as Tout) as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (gen_expr e1, _)
                   => match invert_Op e1 with
                      | Some (existT _ (Add (TWord _) (TWord _) TZ as opc1, args1))
                        => Op (Add _ _ Tout) args1
                      | Some (existT _ (Sub (TWord _) (TWord _) TZ as opc1, args1))
                        => Op (Sub _ _ Tout) args1
                      | Some (existT _ (Mul (TWord _) (TWord _) TZ as opc1, args1))
                        => Op (Mul _ _ Tout) args1
                      | _
                        => Op opc args
                      end
                 | _
                   => Op opc args
                 end
         | Zselect TZ TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of c, x, y)
                   => match (c =? 0)%Z, x, y with
                      | true, const_of c, _
                      | false, _, const_of c
                        => Op (OpConst c) TT
                      | true, gen_expr e, _
                      | false, _, gen_expr e
                        => e
                      | true, neg_expr e, _
                      | false, _, neg_expr e
                        => Op (Opp TZ TZ) e
                      end
                 | Some (neg_expr e, x, y)
                   => let x := uninterp_expr_or_const (t:=Tbase _) x in
                      let y := uninterp_expr_or_const (t:=Tbase _) y in
                      Op (Zselect TZ TZ TZ TZ) (e, x, y)%expr
                 | _ => Op opc args
                 end
         | AddWithCarry TZ TZ TZ TZ as opc
           => fun args
              => let first_pass
                     := match interp_as_expr_or_const args with
                        | Some (const_of c, const_of x, const_of y)
                          => Some (Op (OpConst (interp_op _ _ opc (c, x, y))) TT)
                        | Some (gen_expr e, const_of c1, const_of c2)
                        | Some (const_of c1, gen_expr e, const_of c2)
                        | Some (const_of c1, const_of c2, gen_expr e)
                          => if (c1 + c2 =? 0)%Z
                             then Some e
                             else None
                        | _ => None
                        end in
                 match first_pass with
                 | Some e => e
                 | None
                   => if convert_adc_to_sbb
                      then match interp_as_expr_or_const args with
                           | Some (const_of c, const_of x, const_of y)
                             => Op (OpConst (interp_op _ _ opc (c, x, y))) TT
                           | Some (c, gen_expr x, y)
                             => let y' := match y with
                                          | const_of y => if (y <? 0)%Z
                                                          then Some (Op (OpConst (-y)) TT)
                                                          else None
                                          | neg_expr y => Some y
                                          | gen_expr _ => None
                                          end in
                                match y' with
                                | Some y => Op (SubWithBorrow TZ TZ TZ TZ)
                                               (match c with
                                                | const_of c => Op (OpConst (-c)) TT
                                                | neg_expr c => c
                                                | gen_expr c => Op (Opp TZ TZ) c
                                                end,
                                                x, y)%expr
                                | None => Op opc args
                                end
                           | _ => Op opc args
                           end
                      else Op opc args
                 end
         | AddWithGetCarry bw TZ TZ TZ TZ TZ as opc
           => fun args
              => if convert_adc_to_sbb
                 then match interp_as_expr_or_const args with
                      | Some (const_of c, const_of x, const_of y)
                        => let '(v, c) := interp_op _ _ opc (c, x, y) in
                           (Op (OpConst v) TT, Op (OpConst c) TT)%expr
                      | Some (c, gen_expr x, y)
                        => let y' := match y with
                                     | const_of y => if (y <? 0)%Z
                                                     then Some (Op (OpConst (-y)) TT)
                                                     else None
                                     | neg_expr y => Some y
                                     | gen_expr _ => None
                                     end in
                           let c' := match c with
                                     | const_of c => if (c <? 0)%Z
                                                     then Some (Op (OpConst (-c)) TT)
                                                     else None
                                     | neg_expr c => Some c
                                     | gen_expr _ => None
                                     end in
                           match c', y' with
                           | _, Some y => LetIn (Op (SubWithGetBorrow bw TZ TZ TZ TZ TZ)
                                                    (match c with
                                                     | const_of c => Op (OpConst (-c)) TT
                                                     | neg_expr c => c
                                                     | gen_expr c => Op (Opp TZ TZ) c
                                                     end,
                                                     x, y)%expr)
                                                (fun '(v, c) => (Var v, Op (Opp TZ TZ) (Var c))%expr)
                           | Some c, _ => LetIn (Op (SubWithGetBorrow bw TZ TZ TZ TZ TZ)
                                                    (c,
                                                     x,
                                                     match y with
                                                     | const_of y => Op (OpConst (-y)) TT
                                                     | neg_expr y => y
                                                     | gen_expr y => Op (Opp TZ TZ) y
                                                     end)%expr)
                                                (fun '(v, c) => (Var v, Op (Opp TZ TZ) (Var c))%expr)
                           | None, None => Op opc args
                           end
                      | Some (c, const_of x, y)
                        => let y' := match y with
                                     | const_of y => if (y <? 0)%Z
                                                     then Some (Op (OpConst (-y)) TT)
                                                     else None
                                     | neg_expr y => Some y
                                     | gen_expr _ => None
                                     end in
                           let c' := match c with
                                     | const_of c => if (c <? 0)%Z
                                                     then Some (Op (OpConst (-c)) TT)
                                                     else None
                                     | neg_expr c => Some c
                                     | gen_expr _ => None
                                     end in
                           match c', y' with
                           | _, Some y => LetIn (Op (SubWithGetBorrow bw TZ TZ TZ TZ TZ)
                                                    (match c with
                                                     | const_of c => Op (OpConst (-c)) TT
                                                     | neg_expr c => c
                                                     | gen_expr c => Op (Opp TZ TZ) c
                                                     end,
                                                     Op (OpConst x) TT, y)%expr)
                                                (fun '(v, c) => (Var v, Op (Opp TZ TZ) (Var c))%expr)
                           | Some c, _ => LetIn (Op (SubWithGetBorrow bw TZ TZ TZ TZ TZ)
                                                    (c,
                                                     Op (OpConst x) TT,
                                                     match y with
                                                     | const_of y => Op (OpConst (-y)) TT
                                                     | neg_expr y => y
                                                     | gen_expr y => Op (Opp TZ TZ) y
                                                     end)%expr)
                                                (fun '(v, c) => (Var v, Op (Opp TZ TZ) (Var c))%expr)
                           | None, None => Op opc args
                           end
                      | _ => Op opc args
                      end
                 else Op opc args
         | AddWithGetCarry bw (TWord bw1 as T1) (TWord bw2 as T2) (TWord bw3 as T3) (TWord bwout as Tout) Tout2 as opc
           => fun args
              => let pass0
                     := if ((0 <=? bw)%Z && (2^Z.of_nat (2^bw1) + 2^Z.of_nat (2^bw2) + 2^Z.of_nat (2^bw3) - 3 <=? 2^bw - 1)%Z)%nat%bool
                        then Some (Pair (LetIn args (fun '(a, b, c) => Op (Add _ _ _) (Pair (Op (Add _ _ Tout) (Pair (Var a) (Var b))) (Var c))))
                                        (Op (OpConst 0) TT))
                        else None
                 in
                 match pass0 with
                 | Some e => e
                 | None
                   => match interp_as_expr_or_const args with
                      | Some (const_of c, const_of x, const_of y)
                        => if ((c =? 0) && (x =? 0) && (y =? 0))%Z%bool
                           then Pair (Op (OpConst 0) TT) (Op (OpConst 0) TT)
                           else Op opc args
                      | Some (gen_expr e, const_of c1, const_of c2)
                        => match base_type_eq_semidec_transparent T1 Tout with
                           | Some pf
                             => if ((c1 =? 0) && (c2 =? 0) && (2^Z.of_nat bw1 <=? bw))%Z%bool
                                then Pair (eq_rect _ (fun t => exprf (Tbase t)) e _ pf) (Op (OpConst 0) TT)
                                else Op opc args
                           | None
                             => Op opc args
                           end
                      | Some (const_of c1, gen_expr e, const_of c2)
                        => match base_type_eq_semidec_transparent T2 Tout with
                           | Some pf
                             => if ((c1 =? 0) && (c2 =? 0) && (2^Z.of_nat bw2 <=? bw))%Z%bool
                                then Pair (eq_rect _ (fun t => exprf (Tbase t)) e _ pf) (Op (OpConst 0) TT)
                                else Op opc args
                           | None
                             => Op opc args
                           end
                      | Some (const_of c1, const_of c2, gen_expr e)
                        => match base_type_eq_semidec_transparent T3 Tout with
                           | Some pf
                             => if ((c1 =? 0) && (c2 =? 0) && (2^Z.of_nat bw3 <=? bw))%Z%bool
                                then Pair (eq_rect _ (fun t => exprf (Tbase t)) e _ pf) (Op (OpConst 0) TT)
                                else Op opc args
                           | None
                             => Op opc args
                           end
                      | _ => Op opc args
                      end
                 end
         | SubWithBorrow TZ TZ TZ TZ as opc
           => fun args
              => if convert_adc_to_sbb
                 then match interp_as_expr_or_const args with
                      | Some (const_of c, const_of x, const_of y)
                        => Op (OpConst (interp_op _ _ opc (c, x, y))) TT
                      | Some (c, gen_expr x, y)
                        => let y' := match y with
                                     | const_of y => if (y <? 0)%Z
                                                     then Some (Op (OpConst (-y)) TT)
                                                     else None
                                     | neg_expr y => Some y
                                     | gen_expr _ => None
                                     end in
                           match y' with
                           | Some y => Op (AddWithCarry TZ TZ TZ TZ)
                                          (match c with
                                           | const_of c => Op (OpConst (-c)) TT
                                           | neg_expr c => c
                                           | gen_expr c => Op (Opp TZ TZ) c
                                           end,
                                           x, y)%expr
                           | None => Op opc args
                           end
                      | _ => Op opc args
                      end
                 else Op opc args
         | SubWithGetBorrow bw TZ TZ TZ TZ TZ as opc
           => fun args
              => if convert_adc_to_sbb
                 then match interp_as_expr_or_const args with
                      | Some (const_of c, const_of x, const_of y)
                        => let '(v, c) := interp_op _ _ opc (c, x, y) in
                           (Op (OpConst v) TT, Op (OpConst c) TT)%expr
                      | Some (c, gen_expr x, y)
                        => let y' := match y with
                                     | const_of y => if (y <? 0)%Z
                                                     then Some (Op (OpConst (-y)) TT)
                                                     else None
                                     | neg_expr y => Some y
                                     | gen_expr _ => None
                                     end in
                           match y' with
                           | Some y => LetIn (Op (AddWithGetCarry bw TZ TZ TZ TZ TZ)
                                                 (match c with
                                                  | const_of c => Op (OpConst (-c)) TT
                                                  | neg_expr c => c
                                                  | gen_expr c => Op (Opp TZ TZ) c
                                                  end,
                                                  x, y)%expr)
                                             (fun '(v, c) => (Var v, Op (Opp TZ TZ) (Var c))%expr)
                           | None => Op opc args
                           end
                      | _ => Op opc args
                      end
                 else Op opc args
         | Sub _ _ _ as opc
         | Mul _ _ _ as opc
         | Shl _ _ _ as opc
         | Shr _ _ _ as opc
         | Land _ _ _ as opc
         | Lor _ _ _ as opc
         | OpConst _ _ as opc
         | Opp _ _ as opc
         | IdWithAlt _ _ _ as opc
         | Zselect _ _ _ _ as opc
         | MulSplit _ _ _ _ _ as opc
         | AddWithCarry _ _ _ _ as opc
         | AddWithGetCarry _ _ _ _ _ _ as opc
         | SubWithBorrow _ _ _ _ as opc
         | SubWithGetBorrow _ _ _ _ _ _ as opc
           => Op opc
         end.
  End with_var.

  Definition SimplifyArith {t} (e : Expr t) : Expr t
    := @RewriteOp base_type op (@simplify_op_expr) t e.
End language.
