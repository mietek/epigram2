\section{Relative Names}

%if False

> {-# OPTIONS_GHC -F -pgmF she #-}

> module DisplayLang.Name where

> import Data.List

> import NameSupply.NameSupply

> import Evidences.Tm

> import DisplayLang.DisplayTm

%endif


For display and storage purposes, we have a system of local longnames
for referring to entries. Any component of a local name may have a
\textasciicircum|n| or |_n| suffix, where |n| is an integer,
representing a relative or absolute offset. A relative offset
\textasciicircum|n| refers to the $n^\mathrm{th}$ occurrence of the
name encountered when searching upwards, so |x|\textasciicircum|0|
refers to the same reference as |x|, but |x|\textasciicircum|1| skips
past it and refers to the next thing named |x|.  An absolute offset
|_n|, by contrast, refers to the exact numerical component of the
name.

> data Offs = Rel Int | Abs Int deriving (Show, Eq)
> type RelName = [(String,Offs)]

As a consequence, there is whole new family of objects: terms which
variables are relative names. So it goes:

> type InTmRN = InTm RelName
> type ExTmRN = ExTm RelName
> type DInTmRN = DInTm REF RelName
> type DExTmRN = DExTm REF RelName
> type DSPINE = DSpine REF RelName
> type DHEAD = DHead REF RelName
> type DSCOPE = DScope REF RelName



\subsection{Names to strings}

The |showRelName| function converts a relative name to a string by
inserting the appropriate punctuation.

> showRelName :: RelName -> String
> showRelName = intercalate "." . map showOffName
>     where showOffName (x, Rel 0) = x
>           showOffName (x, Rel i) = x ++ "^" ++ show i
>           showOffName (x, Abs i) = x ++ "_" ++ show i

The |showName| function converts an absolute name to a string
absolutely. 

> showName :: Name -> String
> showName = showRelName . map (\(x, i) -> (x, Abs i))
