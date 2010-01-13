> instance Show x => Show (InDTm x) where
>   show (DL s)       = "DL (" ++ show s ++ ")"
>   show (DC c)       = "DC (" ++ show c ++ ")"
>   show (DN n)       = "DN (" ++ show n ++ ")"
>   show (DQ s)       = "?" ++ s
>   show (DI s)       = "_" ++ s
>   show (DT t)       = "DT (" ++ show t ++ ")"
>   show Dum          = "Dum"

> instance Show x => Show (ExDTm x) where
>   show (DP x)       = "DP (" ++ show x ++ ")"
>   show (DV i)       = "DV " ++ show i
>   show (n ::$ e)    = "(" ++ show n ++ " ::$ " ++ show e ++ ")"
>   show (op ::@ vs)  = "(" ++ opName op ++ " ::@ " ++ show vs ++ ")"
>   show (t ::? y)    = "(" ++ show t ++ " ::? " ++ show y ++ ")"
>
> instance Show x => Show (DScope x) where
>   show (x ::. t)   = show x ++ " :. " ++ show t
>   show (DK t) = "DK (" ++ show t ++")"



> instance Functor DScope where
>   fmap = fmapDefault
> instance Foldable DScope where
>   foldMap = foldMapDefault
> instance Traversable DScope where
>   traverse f (x ::. t)   = (|(x ::.) (traverse f t)|)
>   traverse f (DK t)      = (|DK (traverse f t)|) 


> instance Functor InDTm where
>   fmap = fmapDefault
> instance Foldable InDTm where
>   foldMap = foldMapDefault
> instance Traversable InDTm where
>   traverse f (DL sc)     = (|DL (traverse f sc)|)
>   traverse f (DC c)      = (|DC (traverse (traverse f) c)|)
>   traverse f (DN n)      = (|DN (traverse f n)|)
>   traverse f (DQ s)      = pure (DQ s)
>   traverse f (DI s)      = pure (DI s)
>   traverse f (DT t)      = (|DT (traverse f t)|)
>   traverse f Dum         = (|Dum|) 

> instance Functor ExDTm where
>   fmap = fmapDefault
> instance Foldable ExDTm where
>   foldMap = foldMapDefault
> instance Traversable ExDTm where
>   traverse f (DP x)      = (|DP (f x)|)
>   traverse f (DV i)      = pure (DV i)
>   traverse f (t ::$ u)   = (|(::$) (traverse f t) (traverse (traverse f) u)|)
>   traverse f (op ::@ ts) = (|(op ::@) (traverse (traverse f) ts)|)
>   traverse f (tm ::? ty) = (|(::?) (traverse f tm) (traverse f ty)|) 