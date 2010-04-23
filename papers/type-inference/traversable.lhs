> {-

\subsection{Traversable Foldable Functors}

This is all just boilerplate. Roll on GHC 6.12!

> instance Traversable Ty where
>     traverse g (V x)      = V <$> (g x)
>     traverse g (s :-> t)  = (:->) <$> (traverse g s) <*> (traverse g t)
>
> instance Functor Ty where
>     fmap = fmapDefault
>
> instance Foldable Ty where
>     foldMap = foldMapDefault


> instance Functor Tm where
>     fmap g (X x)           = X (g x)
>     fmap g (f :$ a)        = fmap g f :$ fmap g a
>     fmap g (Lam x t)       = Lam (g x) (fmap g t)
>     fmap g (Let x s t)     = Let (g x) (fmap g s) (fmap g t)


> instance Traversable Index where
>     traverse f Z      = pure Z
>     traverse f (S a)  = S <$> f a
>
> instance Functor Index where
>     fmap = fmapDefault
> 
> instance Foldable Index where
>     foldMap = foldMapDefault


> instance Traversable Schm where
>     traverse f (Type tau)   = Type <$> traverse f tau
>     traverse f (All sigma)  = All <$> traverse (traverse f) sigma
>     traverse f (LetS sigma sigma') = LetS  <$> traverse f sigma 
>                                            <*> traverse (traverse f) sigma'
>
> instance Functor Schm where
>     fmap = fmapDefault
>
> instance Foldable Schm where
>     foldMap = foldMapDefault

> instance Functor Fwd where
>     fmap = fmapDefault

> instance Foldable Fwd where
>     foldMap = foldMapDefault

> instance Traversable Fwd where
>     traverse f F0 = pure F0
>     traverse f (e :> es) = (:>) <$> f e <*> traverse f es

> -}