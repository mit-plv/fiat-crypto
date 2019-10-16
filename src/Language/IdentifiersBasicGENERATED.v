Require Import Crypto.Language.PreExtra.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.IdentifierParameters.
Require Import Rewriter.Language.IdentifiersBasicGenerate.
Require Import Rewriter.Util.plugins.RewriterBuild.

Module Compilers.
  Import IdentifiersBasicLibrary.Compilers.Basic.
  Import IdentifiersBasicGenerate.Compilers.Basic.

  Local Unset Decidable Equality Schemes.
  Local Unset Boolean Equality Schemes.
  Rewriter Emit Inductives From Scraped
           {| ScrapedData.base_type_list_named := base_type_list_named ; ScrapedData.all_ident_named_interped := all_ident_named_interped |}
           As base ident raw_ident pattern_ident.

  Definition package : GoalType.package_with_args scraped_data var_like_idents base ident.
  Proof. Tactic.make_package. Defined.

  Global Strategy -1000 [base_interp ident_interp].
End Compilers.
