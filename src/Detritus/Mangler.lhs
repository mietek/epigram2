Dead code, waiting to be burried

\subsection{The Capture mangler}

Given a list |xs| of |String| parameter names, the |capture| function produces a mangle
that captures those parameters as de Brujin indexed variables.
\question{Do we ever need to do this?}

< capture :: Bwd String -> Mangle Identity String String
< capture xs = Mang
<   {  mangP = \ x ies  -> (|(either P V (h xs x) $:$) ies|)
<   ,  mangV = \ i ies  -> (|(V i $:$) ies|)
<   ,  mangB = \ x -> capture (xs :< x)
<   } where
<   h B0         x  = Left x
<   h (ys :< y)  x
<     | x == y      = Right 0
<     | otherwise   = (|succ (h ys y)|)
