> module DescStrat where

> import System
> import System.IO
> import System.Console.GetOpt

> import Data.List

> data Options = MakeUpTo Int
>              | Help
>
> options :: [OptDescr Options]
> options = [ Option ['m'] ["make"]  (ReqArg (MakeUpTo . read) "n")  "Tower of Desc from N"
>           , Option ['h'] ["help"]  (NoArg Help)                    "Help! Help!"
>           ]

> message = "Desc Tower Generator\n" ++
>           "--------------------\n" ++
>           "Usage:\n" ++
>           "\tDescStrat -m N\n\n" ++
>           "Options: "

> main :: IO ()
> main = do
>        argv <- System.getArgs
>        case getOpt RequireOrder options argv of
>          -- Help:
>          (Help : _, _, [])            -> do
>            putStrLn $ usageInfo message options
>          -- Make the stuff:
>          (MakeUpTo n : _, _, [])   -> do
>            mkFiles n
>          -- Default behavior:
>          ([],_,_)                   -> do
>            mkFiles 42
>          -- Error:
>          (_,_,errs)                   -> do
>            ioError (userError (concat errs ++
>                                usageInfo message options))

> mkFiles :: Int -> IO ()
> mkFiles n = do
>     let equipment = mkEquipment n 
>         descStrat = mkDescStrat n 
>     writeFile "StratSigma.agda" equipment
>     writeFile "DescStrat.agda" descStrat



> mkEquipment :: Int -> String
> mkEquipment n = 
>     "module StratSigma where\n" ++
>     "\n" ++ 
>     (intercalate "\n" $ map skeletonEquipment [0 .. n])

> skeletonEquipment :: Int -> String
> skeletonEquipment level = 
>     let n = show level in
>     "data Sigma" ++ n ++
>         " (A : Set" ++ n ++ ") (B : A -> Set" ++ n ++
>         ") : Set" ++ n ++ " where\n" ++
>     "    _,_ : (x : A) (y : B x) -> Sigma" ++ n ++ " A B\n" ++
>     "\n" ++
>     "_*" ++ n ++ "_ : (A : Set" ++ n ++ ")" ++ 
>         "(B : Set" ++ n ++") -> Set" ++ n ++ "\n" ++
>     "A *" ++ n ++ " B = Sigma" ++ n ++ " A \\_ -> B\n" ++
>     "\n" ++
>     "fst" ++ n ++ " : {A : Set" ++ n ++ "}" ++
>         "{B : A -> Set" ++ n ++ "} -> Sigma" ++ n ++ " A B -> A\n" ++
>     "fst" ++ n ++ " (a , _) = a\n" ++
>     "\n" ++
>     "snd" ++ n ++ " : {A : Set" ++ n ++ "}" ++ 
>         "{B : A -> Set" ++ n ++ "}" ++
>         " (p : Sigma" ++ n ++ " A B) -> B (fst" ++ n ++" p)\n" ++
>     "snd" ++ n ++ " (a , b) = b\n" ++
>     "\n" ++
>     "data Zero" ++ n ++ " : Set" ++ n ++ " where\n" ++
>     "\n" ++
>     "data Unit" ++ n ++ " : Set" ++ n ++ " where\n" ++
>     "    Void : Unit" ++ n  ++ "\n"


> mkDescStrat :: Int -> String
> mkDescStrat n = 
>     "module DescStrat where\n" ++
>     "\n" ++
>     "open import StratSigma\n" ++
>     "\n" ++
>     skeletonHardDesc n ++ 
>     "\n" ++
>     (intercalate "\n" $ map skeletonLevDesc $ reverse [0 .. (n-1)] )

> skeletonHardDesc :: Int -> String
> skeletonHardDesc level =
>     let n = show level
>         np1 = show (level + 1) 
>     in
>     "data Desc" ++ n ++ " : Set" ++ np1 ++ " where\n" ++
>     "    id" ++ n ++" : Desc" ++ n ++ "\n" ++
>     "    const" ++ n ++ " : Set" ++ n ++ " -> Desc" ++ n ++ "\n" ++
>     "    prod" ++ n ++ " : Desc" ++ n ++ " -> Desc" ++ n ++ " -> Desc" ++ n ++ "\n" ++
>     "    sigma" ++ n ++" : (S : Set" ++ n ++ ")" ++ 
>         " -> (S -> Desc" ++ n ++ ") -> Desc" ++ n ++ "\n" ++
>     "    pi" ++ n ++ " : (S : Set" ++ n ++ ") " ++ 
>         "-> (S -> Desc" ++ n ++ ") -> Desc" ++ n ++ "\n" ++
>     "\n" ++
>     "[|_|]" ++ n ++ "_ : Desc" ++ n ++ 
>         " -> Set" ++ n ++ " -> Set" ++ n ++ "\n" ++
>     "[| id" ++ n ++ " |]" ++ n ++ " Z        = Z\n" ++ 
>     "[| const" ++ n ++ " X |]" ++ n ++ " Z   = X\n" ++
>     "[| prod" ++ n ++ " D D' |]" ++ n ++ " Z = " ++
>         "[| D |]" ++ n ++ " Z *" ++ n ++ " [| D' |]" ++ n ++" Z\n" ++
>     "[| sigma" ++ n ++ " S T |]" ++ n ++ " Z = " ++ 
>         "Sigma" ++ n ++ " S (\\s -> [| T s |]" ++ n ++ " Z)\n" ++
>     "[| pi" ++ n ++ " S T |]" ++ n ++ " Z    = (s : S) -> [| T s |]" ++ n ++ " Z\n" ++
>     "\n" ++
>     "data Mu" ++ n ++ " (D : Desc" ++ n ++ ") : Set" ++ n ++ " where\n" ++
>     "    con : [| D |]" ++ n ++ " (Mu" ++ n ++ " D) -> Mu" ++ n ++ " D\n"

> skeletonLevDesc :: Int -> String
> skeletonLevDesc level = 
>     let n = show level 
>         np = show (level + 1)
>     in
>     "data DescDef" ++ n ++ " : Set" ++ np ++ " where\n" ++
>     "    DescId" ++ n ++ " : DescDef" ++ n ++ "\n" ++
>     "    DescConst" ++ n ++ " : DescDef" ++ n ++ "\n" ++
>     "    DescProd" ++ n ++ " : DescDef" ++ n ++ "\n" ++
>     "    DescSigma" ++ n ++ " : DescDef" ++ n ++ "\n" ++
>     "    DescPi" ++ n ++ " : DescDef" ++ n ++ "\n" ++
>     "\n" ++
>     "data Lift" ++ n ++
>         " (A : Set" ++ n ++ ") : Set" ++ np ++ " where\n" ++
>     "    lifter : A -> Lift" ++ n ++ " A\n" ++
>     "\n" ++
>     "unlift" ++ n ++ " : {A : Set" ++ n ++ "}" ++ 
>         " -> Lift" ++ n ++ " A -> A\n" ++
>     "unlift" ++ n ++ " (lifter a) = a\n" ++
>     "\n" ++
>     "descCases" ++ n ++ " : DescDef" ++ n ++ " -> Desc" ++ np ++ "\n" ++
>     "descCases" ++ n ++ " DescId" ++ n ++ " = " ++ 
>         "const" ++ np ++ " Unit" ++ np ++ "\n" ++
>     "descCases" ++ n ++ " DescConst" ++ n ++ " =" ++ 
>         " sigma" ++ np ++ " Set" ++ n ++ 
>         " (\\_ -> const" ++ np ++ " Unit" ++ np ++ ")\n" ++
>     "descCases" ++ n ++ " DescProd" ++ n ++ " = " ++
>         "prod" ++ np ++ " id" ++ np ++ 
>         " (prod" ++ np ++ " id" ++ np ++ 
>         " (const" ++ np ++ " Unit" ++ np ++"))\n" ++
>     "descCases" ++ n ++ " DescSigma" ++ n ++ " = " ++ 
>         "sigma" ++ np ++ " Set" ++ n ++ 
>         " (\\S -> prod" ++ np ++ " (pi" ++ np ++ " (Lift" ++ n ++ " S) " ++ 
>         " (\\_ -> id" ++ np ++ ")) (const" ++ np ++ " Unit" ++ np ++ "))\n" ++
>     "descCases" ++ n ++ " DescPi" ++ n ++ " = " ++ 
>         "sigma" ++ np ++ " Set" ++ n ++ 
>         " (\\S -> prod" ++ np ++ " (pi" ++ np ++ " (Lift" ++ n ++ " S)" ++ 
>         " (\\_ -> id" ++ np ++ ")) (const" ++ np ++ " Unit" ++ np ++ "))\n" ++
>     "\n" ++
>     "DescD" ++ n ++ " : Desc" ++ np ++ "\n" ++
>     "DescD" ++ n ++ " = sigma" ++ np ++ " DescDef" ++ n ++ 
>         " descCases" ++ n ++ "\n" ++
>     "\n" ++
>     "Desc" ++ n ++ " : Set" ++ np ++ "\n" ++
>     "Desc" ++ n ++ " = Mu" ++ np ++ " DescD" ++ n ++ "\n" ++
>     "\n" ++
>     "id" ++ n ++ " : Desc" ++ n ++ "\n" ++
>     "id" ++ n ++ " = con (DescId" ++ n ++ " , Void)\n" ++
>     "\n" ++
>     "const" ++ n ++ " : Set" ++ n ++ " -> Desc" ++ n ++ "\n" ++
>     "const" ++ n ++ " K = con (DescConst" ++ n ++ " , (K , Void))\n" ++
>     "\n" ++
>     "prod" ++ n ++ " : (D D' : Desc" ++ n ++ ") -> Desc" ++ n ++ "\n" ++
>     "prod" ++ n ++ " D D' = " ++ 
>         "con (DescProd" ++ n ++ " , (D , ( D' , Void )))\n" ++
>     "\n" ++
>     "sigma" ++ n ++ " : (S : Set" ++ n ++ ")" ++
>         "(D : S -> Desc" ++ n ++ ") -> Desc" ++ n ++ "\n" ++
>     "sigma" ++ n ++ " S D = con (DescSigma" ++ n ++ " , " ++ 
>         "(S , ((\\s -> D (unlift" ++ n ++ " s)) , Void )))\n" ++ 
>     "\n" ++
>     "pi" ++ n ++ " : (S : Set" ++ n ++ ")" ++ 
>         "(D : S -> Desc" ++ n ++ ") -> Desc" ++ n ++ "\n" ++
>     "pi" ++ n ++ " S D = con (DescPi" ++ n ++ " , " ++ 
>         "(S , ((\\s -> D (unlift" ++ n ++ " s)) , Void )))\n" ++
>     "\n" ++
>     "[|_|]" ++ n ++ "_ : Desc" ++ n ++
>         " -> Set" ++ n ++ " -> Set" ++ n ++ "\n" ++
>     "[| con (DescId" ++ n ++ " , Void) |]" ++ n ++ " Z = Z\n" ++
>     "[| con (DescConst" ++ n ++ " , ( S , Void)) |]" ++ n ++ " Z = S\n" ++
>     "[| con (DescProd" ++ n ++ 
>         " , (D , ( D' , Void ))) |]" ++ n ++ " Z = " ++ 
>         "[| D |]" ++ n ++ " Z *" ++ n ++ " [| D' |]" ++ n ++ " Z\n" ++
>     "[| con (DescSigma" ++ n ++
>         " , (S , (T , Void))) |]" ++ n ++ " Z = " ++ 
>         " Sigma" ++ n ++ " S (\\s -> [| T (lifter s) |]" ++ n ++ " Z )\n" ++
>     "[| con (DescPi" ++ n ++ " , (S , (T , Void))) |]" ++ n ++ " Z = " ++
>         " (s : S) -> [| T (lifter s) |]" ++ n ++ " Z\n" ++
>     "\n" ++
>     "data Mu" ++ n ++ " (D : Desc" ++ n ++ ") : Set" ++ n ++ " where\n" ++
>     "    con : [| D |]" ++ n ++ " (Mu" ++ n ++" D) -> Mu" ++ n ++ " D\n"
