Require Import Crypto.Util.TagList.

Module Type PrePackage.
  Parameter package : Tag.Context.
End PrePackage.

Module MakePackageBase (PKG : PrePackage).
  Ltac get_package _ := eval hnf in PKG.package.
  Ltac get key :=
    let pkg := get_package () in
    Tag.get pkg key.
End MakePackageBase.
