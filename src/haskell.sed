s/import qualified Prelude/import qualified Prelude\nimport qualified Data.Bits\nimport qualified Data.Char\nimport qualified Text.Printf\nimport qualified System.Environment\n/g
s/import qualified GHC.Base/import qualified GHC.Base\n#if __GLASGOW_HASKELL__ >= 900\nimport qualified GHC.Exts\n#endif\n#if __GLASGOW_HASKELL__ >= 802\nimport qualified GHC.Types\n#endif/g
s/unsafeCoerce = GHC.Base.unsafeCoerce#/#if __GLASGOW_HASKELL__ >= 900\nunsafeCoerce = GHC.Exts.unsafeCoerce#\n#else\nunsafeCoerce = GHC.Base.unsafeCoerce#\n#endif/g
s/\(OPTIONS_GHC [^#]*\) /\1 -XNoPolyKinds /g
