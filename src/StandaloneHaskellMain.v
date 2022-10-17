Require Export Coq.extraction.Extraction.
Require Export Coq.extraction.ExtrHaskellBasic.
Require Export Coq.extraction.ExtrHaskellString.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Crypto.Util.Strings.String.
Require Import Crypto.CLI.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope string_scope.

Global Set Warnings Append "-extraction-opaque-accessed".
Extraction Language Haskell.
Global Unset Extraction Optimize.

(** We pull a hack to get coqchk to not report these as axioms; for
    this, all we care about is that there exists a model. *)
Module Type HaskellPrimitivesT.
  Axiom IO_unit : Set.
  Axiom _IO : Set -> Set.
  Axiom Handle : Set.
  Axiom stdin : Handle.
  Axiom stdout : Handle.
  Axiom stderr : Handle.
  Axiom hPutStr : Handle -> string -> _IO unit.
  Axiom getArgs : _IO (list string).
  Axiom getProgName : _IO string.
  Axiom raise_failure : string -> _IO unit.
  Axiom _IO_bind : forall A B, _IO A -> (A -> _IO B) -> _IO B.
  Axiom _IO_return : forall A : Set, A -> _IO A.
  Axiom cast_io : _IO unit -> IO_unit.
  Axiom uncast_io : IO_unit -> _IO unit.
  Axiom getContents : _IO string.
  Axiom readFile : string -> _IO string.
  Axiom writeFile : string (* fname *) -> string (* contents *) -> _IO unit.
End HaskellPrimitivesT.

Module Export HaskellPrimitives : HaskellPrimitivesT.
  Definition IO_unit : Set := unit.
  Definition _IO : Set -> Set := fun T => T.
  Definition Handle : Set := unit.
  Definition stdin : Handle := tt.
  Definition stdout : Handle := tt.
  Definition stderr : Handle := tt.
  Definition hPutStr : Handle -> string -> _IO unit := fun _ _ => tt.
  Definition getArgs : _IO (list string) := nil.
  Definition getProgName : _IO string := "".
  Definition raise_failure : string -> _IO unit := fun _ => tt.
  Definition _IO_bind : forall A B, _IO A -> (A -> _IO B) -> _IO B := fun A B x f => f x.
  Definition _IO_return : forall A : Set, A -> _IO A := fun A x => x.
  Definition cast_io : _IO unit -> IO_unit := fun x => x.
  Definition uncast_io : IO_unit -> _IO unit := fun x => x.
  Definition getContents : _IO string := "".
  Definition readFile : string -> _IO string := fun _ => "".
  Definition writeFile : string -> string -> _IO unit := fun _ _ => tt.
End HaskellPrimitives.

Extract Constant _IO "a" => "GHC.Base.IO a".
Extract Inlined Constant Handle => "System.IO.Handle".
Extract Inlined Constant stdin => "System.IO.stdin".
Extract Inlined Constant stdout => "System.IO.stdout".
Extract Inlined Constant stderr => "System.IO.stderr".
Extract Inlined Constant hPutStr => "System.IO.hPutStr".
Extract Inlined Constant getArgs => "System.Environment.getArgs".
Extract Inlined Constant getProgName => "System.Environment.getProgName".
Extract Constant raise_failure => "\x -> Prelude.error x".
Extract Inlined Constant _IO_bind => "(Prelude.>>=)".
Extract Inlined Constant _IO_return => "GHC.Base.return".
Extract Inlined Constant IO_unit => "GHC.Base.IO ()".
Extract Inlined Constant cast_io => "".
Extract Inlined Constant uncast_io => "".
Extract Inlined Constant getContents => "Prelude.getContents".
Extract Inlined Constant readFile => "Prelude.readFile".
Extract Inlined Constant writeFile => "Prelude.writeFile".
(* COQBUG(https://github.com/coq/coq/issues/12258) *)
Extract Inlined Constant String.eqb => "((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)".

Local Notation "x <- y ; f" := (_IO_bind _ _ y (fun x => f)).

Definition raise_failure (msg : list String.string) : _IO unit
  := (_ <- hPutStr stdout (String.concat String.NewLine msg);
      raise_failure "Synthesis failed").

Global Instance HaskellIODriver : ForExtraction.IODriverAPI (_IO unit)
  := {
       ForExtraction.error := raise_failure
       ; ForExtraction.ret 'tt := _IO_return _ tt
       ; ForExtraction.with_read_stdin k :=
           (lines <- getContents;
           k (String.split String.NewLine lines))
       ; ForExtraction.write_stdout_then lines k
         := (_ <- hPutStr stdout (String.concat "" lines);
            k tt)
       ; ForExtraction.write_stderr_then lines k
         := (_ <- hPutStr stdout (String.concat "" lines);
            k tt)
       ; ForExtraction.with_read_file fname k
         := (lines <- readFile fname;
            k (String.split String.NewLine lines))
       ; ForExtraction.write_file_then fname lines k
         := (_ <- writeFile fname (String.concat "" lines);
            k tt)
    }.

Definition main_gen
           {supported_languages : ForExtraction.supported_languagesT}
           (PipelineMain : forall (A := _)
                                  (argv : list String.string),
               A)
  : IO_unit
  := cast_io
       (argv <- getArgs;
       prog <- getProgName;
       PipelineMain
         (prog::argv)).

Local Existing Instance ForExtraction.default_supported_languages.

Module UnsaturatedSolinas.
  Definition main : IO_unit
    := main_gen ForExtraction.UnsaturatedSolinas.PipelineMain.
End UnsaturatedSolinas.

Module WordByWordMontgomery.
  Definition main : IO_unit
    := main_gen ForExtraction.WordByWordMontgomery.PipelineMain.
End WordByWordMontgomery.

Module SaturatedSolinas.
  Definition main : IO_unit
    := main_gen ForExtraction.SaturatedSolinas.PipelineMain.
End SaturatedSolinas.

Module SolinasReduction.
  Definition main : IO_unit
    := main_gen ForExtraction.SolinasReduction.PipelineMain.
End SolinasReduction.

Module BaseConversion.
  Definition main : IO_unit
    := main_gen ForExtraction.BaseConversion.PipelineMain.
End BaseConversion.
