\section{Dumb Term Translation}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE TypeOperators, GADTs #-}

> module DisplayLang.DumbTrans where

> import Control.Applicative
> import Data.Traversable
> import Data.Char

> import Kit.MissingLibrary
> import Kit.Parsley
> import Kit.NatFinVec
> import Kit.BwdFwd

> import DisplayLang.DisplayTm
> import DisplayLang.Name
> import DisplayLang.Scheme
> import DisplayLang.Lexer
> import DisplayLang.TmParse

> import Evidences.Tm


> import ProofState.Structure.Developments
> import ProofState.Structure.Entries
> import ProofState.Edition.ProofState
> import ProofState.Edition.GetSet

%endif

> dumb :: String -> Either String EXP
> dumb s = 
>   case parse tokenize s of
>     Right t -> case parse pDInTm t of
>       Right u -> dumbDInTm u [] [] V0
>       Left _ -> Left "Blah"
>     Left _ -> Left "halB"

> dumbPS :: DInTmRN -> ProofState EXP
> dumbPS t = do
>   glog <- getDefsInScope
>   glob <- getParamsInScope 
>   case dumbDInTm t glog (map (\(a,b,c) -> (b,c)) glob) V0 of
>     Left s -> fail s
>     Right e -> return e

> dumbDInTm :: DInTmRN -> [ DEF ] -> [ (String, TY) ] -> 
>              Vec {n} String -> Either String (Tm {Body, Exp, n})
> dumbDInTm (DL (s ::. t)) glog glob loc = (| (L ENil s) (dumbDInTm t glog glob (s :>>: loc)) |)
> dumbDInTm (DL (DK t)) glog glob loc = (| LK (dumbDInTm t glog glob loc) |)
> dumbDInTm (DC c as) glog glob loc = (| (c :-) (traverse (\x -> dumbDInTm x glog glob loc) as) |)
> dumbDInTm (DN e) glog glob loc = dumbDExTm e glog glob loc
> dumbDInTm (DQ _) glog glob loc = Left "Too dumb to know what a question mark is"
> dumbDInTm DU glog glob loc = Left "Too dumb to work out that underscore"

> dumbDExTm :: DExTmRN -> [ DEF ] -> [ (String, TY) ] -> 
>              Vec {n} String -> Either String (Tm {Body, Exp, n})
> dumbDExTm (head ::$ spine) glog glob loc = 
>   (| (dumbDHead head glog glob loc) :$ (dumbDSpine spine glog glob loc) |)

> dumbDHead :: DHEAD -> [ DEF ] -> [ (String, TY) ] -> 
>              Vec {n} String -> Either String (Tm {Head, Exp, n})
> dumbDHead (DP [(x, Rel o)]) glog glob loc = case lookupBoyLoc (x, o) loc of
>   Right i  ->  (| (V i) |)
>   Left o   ->  (| P (lookupBoyGlob (x, o) glob) |)  
> dumbDHead (DP rnom) glog glob loc = case unabs rnom of
>     Just nom  -> (| (\x -> ENil :/ D x S0 (defOp x)) (lookupGirl nom glog) |)
>     Nothing   -> Left "Name resolution FAIL"
>   where unabs [] = (| [] |)
>         unabs ((s, Abs a) : rnom) = (| ((s, a) :) (unabs rnom) |)
>         unabs _ = Nothing

> lookupBoyLoc :: (String, Int) -> Vec {n} String -> Either Int (Fin {n})
> lookupBoyLoc (s, 0) (t :>>: _)     | s == t  = Right Fz 
> lookupBoyLoc (s, o) (t :>>: loc')  | s == t  = 
>   either Left (Right . Fs) (lookupBoyLoc (s, o-1)  loc') 
> lookupBoyLoc (s, o) (t :>>: loc')            = 
>   either Left (Right . Fs) (lookupBoyLoc (s, o)    loc') 
> lookupBoyLoc (s, o) V0                       = Left o

> lookupBoyGlob :: (String, Int) -> [ (String , TY) ] -> Either String (Int, String, TY)
> lookupBoyGlob (s, 0) ((t, ty) : glob') | s == t = Right (length glob', t, ty)
> lookupBoyGlob (s, o) ((t, ty) : glob') | s == t = lookupBoyGlob (s, o-1) glob' 
> lookupBoyGlob (s, o) (_ : glob') = lookupBoyGlob (s, o) glob'
> lookupBoyGlob (s, o) [] = Left $ "Failed to find a boy of name \"" ++ s ++ "\" ):"

> lookupGirl :: Name -> [ DEF ] -> Either String DEF
> lookupGirl nom (def : glog') | nom == defName def  = (| def |)
> lookupGirl nom (_ : glog')                         = lookupGirl nom glog'
> lookupGirl nom _                                   = 
>   Left $ "Couldn't find a definition with name \"" ++ showName nom ++ "\""

> dumbDSpine :: DSPINE -> [ DEF ] -> [ (String, TY) ] -> 
>               Vec {n} String -> Either String (Bwd (Elim (Tm {Body, Exp, n})))
> dumbDSpine spine glog glob loc = 
>   (| bwdList (traverse (traverse (\x -> dumbDInTm x glog glob loc)) spine) |)

