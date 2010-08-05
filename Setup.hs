import System

import Data.List

import Distribution.Simple
import Distribution.Simple.UserHooks
import Distribution.PackageDescription
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup


-- All right. So, if we want to compile that damned thing, we have to
-- call |src/Makefile|. We don't do that because we are sadic, we do
-- it because we are masochist. Indeed, She needs a special treatment
-- in order to compile. For now, only a Makefile can make it.

-- Therefore, we overwrite the |buildHook| of |Cabal| by our own junk
-- calling the Makefile and copying the binary at the excepted
-- place. We extract the dependencies from the package description and
-- pass it along.

callMake :: PackageDescription -> LocalBuildInfo -> UserHooks -> BuildFlags -> IO ()
callMake pkgDesc buildInfo userHooks buildFlags = do
  let pkgs =  "HC_CABAL_PACKAGE=\"" ++ 
              (intercalate " "
              (map (\(Dependency (PackageName name) _) -> "-package " ++ name) $ 
               buildDepends pkgDesc))
              ++ "\""
  exit <- system $ "cd src; make clean dep " ++ pkgs
  if exit /= ExitSuccess
    then exitFailure
    else return ()
  exit <- system $ "cd src; make Pig " ++ pkgs
  if exit /= ExitSuccess
    then exitFailure
    else return ()
  system $ "mkdir -p dist/build/Pig/"
  system $ "cp -f src/Pig dist/build/Pig/Pig"
  return ()

-- An obvious question remain: We've stripped the package
-- dependencies, good. But is there anything else we should care
-- about? No clue.


-- Let's compile, whohoooooo!

main = defaultMainWithHooks $
       simpleUserHooks { buildHook = callMake }
