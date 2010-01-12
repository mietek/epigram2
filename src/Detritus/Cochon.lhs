


> data NavC  =  InC | OutC
>            |  Up | Down | Top | Bottom 
>            |  RootC
>            |  Prev | Next | First | Last
>     deriving Show

> data ShowC x = Auncles | Context | Dump | Hypotheses | StateC | Term x
>     deriving (Show, Functor, Foldable, Traversable)

> data Command x  =  Apply
>                 |  DoneC
>                 |  Elaborate x
>                 |  Compile x String
>                 |  Give x
>                 |  Go NavC
>                 |  Infer x
>                 |  Jump x
>                 |  Lambda String
>                 |  Make String (Maybe x :<: x)
>                 |  ModuleC String
>                 |  PiBoy String x
>                 |  Quit
>                 |  Select x
>                 |  Show (ShowC x)
>                 |  Undo
>                 |  Ungawa
>                 |  Elim x
>     deriving Show

> instance Traversable Command where
>     traverse f Apply                = (| Apply |)
>     traverse f (Compile x fn)       = (| Compile (f x) ~fn |)
>     traverse f DoneC                = (| DoneC |)
>     traverse f (Elaborate x)        = (| Elaborate (f x) |)
>     traverse f (Give x)             = (| Give (f x) |)
>     traverse f (Go d)               = (| (Go d) |)
>     traverse f (Infer x)            = (| Infer (f x) |)
>     traverse f (Jump x)             = (| Jump (f x) |)
>     traverse f (Lambda s)           = (| (Lambda s) |)
>     traverse f (Make s (md :<: x))  = (| (Make s) (| (traverse f md) :<: (f x) |) |)
>     traverse f (ModuleC s)          = (| (ModuleC s) |)
>     traverse f (PiBoy s x)          = (| (PiBoy s) (f x) |)
>     traverse f Quit                 = (| Quit |)
>     traverse f (Select x)           = (| Select (f x) |)
>     traverse f (Show sx)            = (| Show (traverse f sx) |)
>     traverse f Undo                 = (| Undo |)
>     traverse f Ungawa               = (| Ungawa |)
>     traverse f (Elim x)             = (| Elim (f x) |)

> instance Functor Command where
>     fmap = fmapDefault

> instance Foldable Command where
>     foldMap = foldMapDefault

> pCommand :: Parsley Token (Command InDTmRN)
> pCommand = do
>     x <- ident
>     case x of
>         "apply"    -> (| Apply |)
>         "bottom"   -> (| (Go Bottom) |)
>         "compile"  -> (| Compile (| DN (|DP nameParse|) |) pFileName |)
>         "done"     -> (| DoneC |)
>         "down"     -> (| (Go Down) |)
>         "elab"     -> (| Elaborate pInDTm |)
>         "first"    -> (| (Go First) |)
>         "give"     -> (| Give pInDTm |)
>         "in"       -> (| (Go InC) |)
>         "infer"    -> (| Infer pInDTm |)
>         "jump"     -> (| Jump (| DN (|DP nameParse|) |) |)
>         "lambda"   -> (| Lambda ident |)
>         "last"     -> (| (Go Last) |)
>         "make"     -> (| Make ident (%keyword ":"%) (| ~Nothing :<: pInDTm |)
>                        | Make ident (%keyword ":="%) maybeAscriptionParse
>                        |)
>         "module"   -> (| ModuleC ident |)
>         "next"     -> (| (Go Next) |)
>         "out"      -> (| (Go OutC) |)
>         "pi"       -> (| PiBoy ident (%keyword ":"%) pInDTm |)
>         "prev"     -> (| (Go Prev) |)
>         "root"     -> (| (Go RootC) |)
>         "quit"     -> (| Quit |)
>         "select"   -> (| Select (| DN (|DP nameParse|) |) |)
>         "show"     -> (| Show pShow |)
>         "top"      -> (| (Go Top) |)
>         "undo"     -> (| Undo |)
>         "ungawa"   -> (| Ungawa |)
>         "up"       -> (| (Go Up) |)
>         "elim"     -> (| Elim (| DN (|DP nameParse|) |)|)
>         _          -> empty

> pFileName :: Parsley Token String
> pFileName = ident

> pShow :: Parsley Token (ShowC InDTmRN)
> pShow = do
>     s <- ident
>     case s of
>         "auncles"  -> (| Auncles |)
>         "context"  -> (| Context |)
>         "dump"     -> (| Dump |)
>         "hyps"     -> (| Hypotheses |)
>         "state"    -> (| StateC |)
>         "term"     -> (| Term pInDTm |)
>         _          -> empty

> evalCommand :: Command INDTM -> ProofState String
> evalCommand Apply           = apply             >> return "Applied."
> evalCommand DoneC           = done              >> return "Done."
> evalCommand (Elaborate tm)  = infoElaborate tm
> evalCommand (Give tm)       = elabGiveNext tm   >> return "Thank you."
> evalCommand (Go InC)        = goIn              >> return "Going in..."
> evalCommand (Go OutC)       = goOut             >> return "Going out..."
> evalCommand (Go Up)         = goUp              >> return "Going up..."
> evalCommand (Go Down)       = goDown            >> return "Going down..."
> evalCommand (Go Top)        = many goUp         >> return "Going to top..."
> evalCommand (Go Bottom)     = many goDown       >> return "Going to bottom..."
> evalCommand (Go Prev)       = prevGoal          >> return "Searching for previous goal..."
> evalCommand (Go RootC)      = many goOut        >> return "Going to root..."
> evalCommand (Go Next)       = nextGoal          >> return "Searching for next goal..."
> evalCommand (Go First)      = some prevGoal     >> return "Searching for first goal..."
> evalCommand (Go Last)       = some nextGoal     >> return "Searching for last goal..."
> evalCommand (Infer tm)      = infoInfer tm
> evalCommand (Jump (DN (DP (n := _)))) = do
>     much goOut
>     goTo n
>     return ("Going to " ++ showName n ++ "...")
> evalCommand (Lambda x)      = lambdaBoy x       >> return "Made lambda boy!"
> evalCommand (Make x (mtm :<: ty)) = do
>     elabMake (x :<: ty)
>     goIn
>     case mtm of
>         Nothing  -> return "Appended goal!"
>         Just tm  -> elabGive tm >> return "Yessir."
> evalCommand (ModuleC s)     = makeModule s      >> return "Made module."
> evalCommand (PiBoy x ty)    = elabPiBoy (x :<: ty)  >> return "Made pi boy!"
> evalCommand (Select (DN (DP r)))      = select (N (P r))          >> return "Selected."
> evalCommand (Show Auncles)     = infoAuncles
> evalCommand (Show Context)     = infoContext 
> evalCommand (Show Dump)        = infoDump
> evalCommand (Show Hypotheses)  = infoHypotheses
> evalCommand (Show StateC)       = prettyProofState 
> evalCommand (Show (Term x))    = return (show x)
> evalCommand Ungawa          = ungawa            >> return "Ungawa!"
> evalCommand (Elim (DN r)) = do 
>     (elimTy :>: e) <- elabInfer r
>     elimTyTm <- bquoteHere elimTy
>     elim Nothing ((elimTyTm :=>: elimTy) :>: (N e :=>: (evTm (N e))))
>     return ("Elimination occured. Subgoals awaiting work...")


> doCommand :: Command InDTmRN -> ProofState String
> doCommand c = do
>     aus <- getAuncles
>     c' <- traverse (resolve aus) c
>               `catchEither` "doCommand: could not resolve names in command."
>     evalCommand c'

> doCommands :: [Command InDTmRN] -> ProofState [String]
> doCommands cs = sequenceA (map doCommand cs)

> doCommandsAt :: [(Name, [Command InDTmRN])] -> ProofState ()
> doCommandsAt [] = return ()
> doCommandsAt ((_, []):ncs) = doCommandsAt ncs
> doCommandsAt ((n, cs):ncs) = much goOut >> goTo n >> doCommands cs >> doCommandsAt ncs
