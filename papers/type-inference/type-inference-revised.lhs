\documentclass[authoryear,preprint]{sigplanconf}

%options ghci

%include lhs2TeX.fmt
%include lhs2TeX.sty

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\mathsf{" a "}"

%format <-  = "\leftarrow "
%format :-> = "\arrow "
%format <>< = "<\!>\!< "
%format <>> = "<\!>\!> "
%format <+> = "\oplus "
%format <*> = "\varoast "
%format <$> = "<\!\!\$\!\!> "
%format :$  = ":\!\!\$\ "
%format ::: = "\asc "
%format >=> = "\genarrow "
%format <?  = "\in "
%format ... = "\ldots "
%format >-  = "\Yright "
%format .   = "\,\circ\, "

%format F0  = "\emptycontext"
%format B0  = "\emptycontext"

% %format Lam (x) (b) = "\lambda" x "." b
% %format Let (x) (s) (t) = "\letIn{" x "}{" s "}{" t "} "
%format LetGoal = "\letGoal "

%format Hole = "? "
%format Some = "!\!"

%format alpha  = "\alpha"
%format alpha0
%format alpha1
%format alpha'
%format alphaD = "\alpha\!D"
%format beta   = "\beta"
%format beta0
%format beta1
%format gamma  = "\gamma"
%format _Gamma  = "\Gamma"
%format _Gamma0
%format _Gamma1
%format delta  = "\delta"
%format delta0
%format delta1
%format nu     = "\nu"
%format sigma  = "\sigma"
%format sigma0
%format sigma1
%format sigma'
%format tau    = "\tau"
%format tau0
%format tau1
%format tau'
%format rho = "\rho"
%format upsilon = "\upsilon"
%format upsilon0
%format upsilon1
%format chi = "\chi"
%format _Xi = "\Xi"
%format _Xi0
%format _Xi1

\newcommand{\ident}[1]{\mathsf{#1}}
%format return          = "\ident{return}"
%format put             = "\ident{put}"
%format any             = "\ident{any}"
%format fst             = "\ident{fst}"
%format snd             = "\ident{snd}"
%format get             = "\ident{get}"
%format fmap            = "\ident{fmap}"
%format gets            = "\ident{gets}"
%format succ            = "\ident{succ}"
%format fail            = "\ident{fail}"
%format error           = "\ident{error}"
%format otherwise       = "\ident{otherwise}"
%format occurs          = "\ident{occurs}"
%format fresh           = "\ident{fresh}"
%format getContext      = "\ident{getContext}"
%format putContext      = "\ident{putContext}"
%format modifyContext   = "\ident{modifyContext}"
%format onTop           = "\ident{onTop}"
%format restore         = "\ident{restore}"
%format replace         = "\ident{replace}"
%format unify           = "\ident{unify}"
%format solve           = "\ident{solve}"
%format specialise      = "\ident{specialise}"
%format unpack          = "\ident{unpack}"
%format fromS           = "\ident{fromS}"
%format generaliseOver  = "\ident{generaliseOver}"
%format skimContext     = "\ident{skimContext}"
%format find            = "\ident{find}"
%format help            = "\ident{help}"
%format extract         = "\ident{extract}"
%format infer           = "\ident{infer}"
%format bind            = "\ident{bind}"

\usepackage{color}
\definecolor{red}{rgb}{1.0,0.0,0.0}
\newcommand{\TODO}[1]{\NotForPublication{\textcolor{red}{#1}}}
\newcommand{\NotForPublication}[1]{}

% Boxes and inference rules
\newcommand{\mathframe}[1]{\framebox{\ensuremath{#1}}}
\newcommand{\boxrule}[1]{\begin{center}\mathframe{#1}\end{center}}
\newcommand{\boxrules}[2]{\begin{center}\mathframe{#1}\quad\mathframe{#2}\end{center}}
\newcommand{\boxruless}[3]{\begin{center}\mathframe{#1}\quad\mathframe{#2}\quad\mathframe{#3}\end{center}}
\newcommand{\name}[1]{\textsc{#1}}
\newcommand{\namer}[1]{\ensuremath{\mathrm{\name{#1}} \;}}
\newcommand{\side}[1]{\ensuremath{\; #1}}
\newcommand{\br}[2]{\genfrac{}{}{0pt}{0}{#1}{#2}}
\newcommand{\BigRule}[3]{\ensuremath{\Rule{\br{#1}{#2}}{#3}}}

% Text
\newcommand{\define}[1]{\emph{#1}}
\newcommand{\scare}[1]{`#1'}
\newcommand{\W}{\ensuremath{\mathcal{W}}}
\newcommand{\AlgorithmW}{Algorithm~\W}
\newcommand{\hindleymilner}{Hindley-Milner}
\newcommand{\hindleymilnershort}{HM}

% Substitutions
\newcommand{\eqsubst}{\equiv}
\newcommand{\compose}{\cdot}
\newcommand{\subst}[3]{[#1/#2]#3}
\newcommand{\restrict}[2]{#1 ||_{#2}}

% Sets and sorts
\newcommand{\V}{\mathcal{V}}
\newcommand{\D}{\mathcal{D}}
\newcommand{\Ss}{\mathcal{S}}
\newcommand{\K}{\mathcal{K}}
\newcommand{\TY}{\mathrm{\textsc{TY}}}
\newcommand{\TM}{\mathrm{\textsc{TM}}}

% Context bits
\newcommand{\entails}{\ensuremath{\vdash}}
\newcommand{\entailsN}{\ensuremath{\Vdash}}
\newcommand{\emptycontext}{\ensuremath{\mathcal{E}}}
\newcommand{\letGoal}{\ensuremath{\fatsemi}}
\newcommand{\defn}{\ensuremath{\!:=\!}}
\newcommand{\asc}{\ensuremath{~\hat{::}~}}
\newcommand{\hole}[1]{\ensuremath{#1 \!:= ?}}
\newcommand{\decl}[2]{#1 #2}

% Statements
\newcommand{\type}{\ensuremath{~\mathbf{type}}}
\newcommand{\scheme}{\ensuremath{~\mathbf{scheme}}}
\newcommand{\valid}{\ensuremath{\mathbf{valid}}}
\newcommand{\Sbind}[2]{#1 \Yright #2}
\newcommand{\hasscheme}{\ensuremath{::}}
\newcommand{\Pinf}[2]{#1 : #2}
\newcommand{\Psch}[2]{#1 \hasscheme #2}
\newcommand{\Puni}[2]{#1 \equiv #2}
\newcommand{\sanity}{sanity condition}
\newcommand{\Sanity}{Sanity condition}

% Types, terms and schemes
\newcommand{\arrow}{\ensuremath{\triangleright}}
\newcommand{\letIn}[3]{\ensuremath{\mathrm{let}\; #1 \!:=\! #2 \;\mathrm{in}\; #3}}
\newcommand{\letS}[3]{\ensuremath{(!#1 \!:=\! #2 ~\mathrm{in}~ #3)}}
\newcommand{\genarrow}{\ensuremath{\Uparrow}}
\newcommand{\gen}[2]{\ensuremath{(#1 \genarrow #2)}}
\newcommand{\gendot}[1]{\ensuremath{.{#1}}}

% Maps
\newcommand{\tyvars}[1]{\ensuremath{\V_\TY(#1)}}
\newcommand{\FTV}[1]{\ensuremath{\mathit{FTV}(#1)}}
\newcommand{\sem}[1]{\ensuremath{\llbracket #1 \rrbracket}}
\newcommand{\ok}{\ensuremath{~\mathbf{ok}}}
\newcommand{\forget}[1]{\ensuremath{\lfloor #1 \rfloor}}
\newcommand{\semidrop}{\downharpoonright}

% Relations between contexts
\newcommand{\lei}{\ensuremath{\preceq}}
\newcommand{\LEI}{\ensuremath{~\hat\lei~}}
\newcommand{\leiR}{\ensuremath{\sqsubseteq}}
\newcommand{\LEIR}{\ensuremath{~\hat\sqsubseteq~}}
\newcommand{\transto}{\ensuremath{\twoheadrightarrow}}

\newcommand{\leiStmt}[3]{\ensuremath{#1 \lei #3 \vdash #2}}
\newcommand{\LEIStmt}[3]{\ensuremath{#1 \LEI #3 \vdash #2}}
\newcommand{\leiParam}[4]{(#1, #2) \lei (#3, #4)}
\newcommand{\leiRParam}[4]{(#1, #2) \leiR (#3, #4)}
\newcommand{\LEIProb}[4]{#1 \,? #2 \LEI #3 \,!\, #4}
\newcommand{\LEIRProb}[4]{#1 \,? #2 \LEIR #3 \,!\, #4}
\newcommand{\LEIUnify}[4]{\leiStmt{#1}{#2 \equiv #3}{#4}}
\newcommand{\LEIInfer}[4]{\LEIProb{#1}{(#2 :)}{#4}{#3}}
\newcommand{\LEIInferScheme}[4]{\LEIProb{#1}{(#2 \hasscheme)}{#4}{#3}}
\newcommand{\LEIRInfer}[4]{\LEIRProb{#1}{(#2 :)}{#4}{#3}}

\newcommand{\alg}[3]{\ensuremath{#1 \transto #3 \entails #2}}
\newcommand{\algUnify}[4]{\alg{#1}{#2 \equiv #3}{#4}}
\newcommand{\algInstantiate}[5]{\alg{#1 ~||~ #4}{\Puni{#2}{#3}}{#5}}
\newcommand{\algInfer}[4]{\alg{#1}{\Pinf{#2}{#3}}{#4}}
\newcommand{\algInferScheme}[4]{\alg{#1}{\Psch{#2}{#3}}{#4}}

% Problem bits
\newcommand{\leParam}[3]{#1 \entails #2 \subset #3}
\newcommand{\pconj}[3]{\Sigma #1~#2.#3}
\newcommand{\Qbind}[2]{#1 \bullet \Yright #2}



\usepackage{amsthm}
\usepackage{amsmath}
\usepackage{enumerate}
\usepackage{eucal}
\usepackage{natbib}
\usepackage[T1]{fontenc}
\usepackage{subfigure}
\usepackage[colorlinks,draft=false]{hyperref}

\newcommand{\fixpars}{\setlength{\parskip}{5pt}\setlength{\parindent}{0pt}}
\fixpars

\newtheorem{lemma}{Lemma}
\newcommand{\proofsux}{\vspace*{-0.2in}}

\include{macros}
\setlength{\rulevgap}{0.05in}

\hyphenpenalty=5000
\tolerance=1000


%if showCode

> {-# LANGUAGE  DeriveFunctor, DeriveFoldable,
>               FlexibleInstances, TypeSynonymInstances,
>               TypeFamilies, StandaloneDeriving, TypeOperators #-}

> import Prelude hiding (any)
> import Control.Monad.State (StateT, get, gets, put, runStateT)
> import Data.Foldable (Foldable, any, foldMap)
> import Data.Monoid (Monoid, mappend, mempty)

%endif



\begin{document}

\conferenceinfo{MSFP '10}{September 25, Baltimore, Maryland, USA.} 
\copyrightyear{2010} 
\copyrightdata{} 

\titlebanner{\NotForPublication{REVISED DRAFT}}

\title{Type inference in context}
\authorinfo{Adam Gundry\thanks{Adam Gundry was supported by Microsoft Research through its PhD Scholarship
Programme.} \and Conor McBride}
           {University of Strathclyde, Glasgow}
           {\{adam.gundry,conor.mcbride\} at cis.strath.ac.uk}
\authorinfo{James McKinna}
           {Radboud University, Nijmegen}
           {james.mckinna at cs.ru.nl}

\maketitle

\begin{abstract}
\input{abstract.ltx}
\end{abstract}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction\label{sec:intro}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% \subsection{\AlgorithmW}

\AlgorithmW\ is a well-known type inference algorithm for the \hindleymilner\ type
system \citep{milner_theory_1978, damas_principal_1982} (henceforth: \scare{\hindleymilnershort}), based on
\citeauthor{robinson_machine-oriented_1965}'s Unification Algorithm
\citeyearpar{robinson_machine-oriented_1965}. The system consists of
simply-typed $\lambda$-calculus with \scare{let-expressions} for polymorphic
definitions.
For example, %%% the term
$$\letIn{i}{\lambda x . x}{i\:i}$$
is well-typed: $i$ is given a polymorphic type that is instantiated in two
different ways. The syntax of types is
$$\tau ::= \alpha ~||~ \tau \arrow \tau.$$
For simplicity, the function arrow $\arrow$ is our only type constructor.
We let $\alpha$ and $\beta$ range over type variables and $\tau$ and $\upsilon$
over types.

Most presentations of \AlgorithmW\ have treated the underlying unification
algorithm as a \scare{black box}, but by considering both together we can give a
more elegant type inference algorithm.  In particular, the generalisation step
(used when inferring the type of a let-expression) becomes straightforward
(Section \ref{sec:tyinf}).

\subsection{Motivating context}

Why revisit \AlgorithmW? 
%%%This is 
   As 
a first step towards a longer-term goal:
%%%to explain the elaboration of 
   explaining how to elaborate 
high-level \emph{dependently typed} programs into fully explicit calculi. 
Just as \W\ specialises polymorphic type schemes, 
elaboration involves inferring \emph{implicit arguments} by solving constraints, but
with fewer algorithmic guarantees. Pragmatically, 
   we need to account for
stepwise progress in problem solving from states of partial knowledge.
We 
%%%wish to identify 
   seek  
local correctness criteria for type inference 
%%%that guarantee 
   guaranteeing 
global correctness.


In contrast to other presentations of unification and \hindleymilnershort\ type
inference, our algorithm is based on contexts carrying variable definitions as
well as declarations. This avoids having to consider substitutions, or
morphisms between contexts, explicitly.
(We do use substitution in reasoning about the system.)

This paper has been a long time brewing. 
   Its origins lie in a constraint
%%%It originates in a con-straint
engine cannibalised by McBride from an implementation of
\citeauthor{miller:mixed}'s \scare{mixed prefix}
unification~\citeyearpar{miller:mixed}, mutating the quantifier prefix into a
context. \citeauthor{mcbride:thesis}'s thesis~\citeyearpar{mcbride:thesis} gives
an early account of using typing contexts to represent the state of an
interactive construction system, \scare{holes} in programs and proofs being 
specially designated variables. Contexts carry an information order: increase of
information preserves typing and equality judgments; proof tactics are
admissible context validity rules which increase information; unification is
specified as a tactic which increases information to make an equation hold, but
its imple-mentation is not discussed. This view of construction underpinned the
implementation of Epigram~\citep{mcbride.mckinna:view-from-the-left} and informed
\citeauthor{norell:agda}'s 
%%%implementation of Agda~\citeyearpar{norell:agda}. 
   Agda implementation~\citeyearpar{norell:agda}.
It is high time we began to explain how it works and perhaps to understand it.

We are grateful to an anonymous referee for pointing out the work of
\citet{dunfield_polymorphism_2009} on polymorphism in a bidirectional type system.
Dunfield uses well-founded contexts that contain existential type variables
(amongst other things). These variables can be solved, and there is an informal
notion of information increase between input and output contexts, though this is
used for different purposes. 

However, our concerns are different: whilst Dunfield elaborates a
particular approach to bidirectional polymorphic checking to a larger
class of type theories, here we pursue a methodological understanding
of the problem-solving strategy in \hindleymilnershort\ type inference.

%%%\TODO{More crunchiness: forward pointers to claims and contributions}

This paper is literate Haskell, with full source code available at
\footnotesize\url{http://personal.cis.strath.ac.uk/~adam/type-inference/}\normalsize.

\subsection{The occurs check}

Testing whether a variable occurs in a term is used by both Robinson unification
and \AlgorithmW. In unification, the check is (usually)
necessary to ensure termination, let alone correctness: the equation
$\alpha \equiv \alpha \arrow \beta$ has no (finite) solution because the
right-hand side depends on the left, so it does not make a good definition.

In \AlgorithmW, the occurs check is used to discover type dependencies just in
time for generalisation. When inferring the type of the let-expression
$\letIn{x}{e'}{e}$, the type of $e'$ must first be inferred, then
quantified over \scare{generic} type variables, i.e.\ those involved with $e'$
but not the enclosing bindings. 
The rule in question, as presented by \citet{clment_simple_1986}, is:
$$
\Rule{A \entails e' : \tau'  \qquad  A_x \cup \{ x : \sigma \} \entails e : \tau}
     {A \entails \letIn{x}{e'}{e} : \tau}
\side{\sigma = gen(A, \tau')}
$$
$$gen(A, \tau) = \begin{cases}
    \forall \vec{\alpha_i} . \tau  &
        (FV(\tau) \setminus FV(A) = \{ \alpha_1, \cdots, \alpha_n \})  \\
    \tau &
        (FV(\tau) \setminus FV(A) = \emptyset)
\end{cases}
$$
Here, the typing context is an unordered set of type scheme assignments,
with \(A_x\) denoting `\(A\) with any \(x\) assignments removed': contexts are
not designed to reflect lexical scope, so shadowing requires deletion and
reinsertion.

The `let' rule is the only real complexity in \AlgorithmW,
and as \citet{milner_theory_1978} wrote, ``the
reader may still feel that our rules are arbitrarily chosen and only partly
supported by intuition.'' Experience has shown the rules to be well-chosen
indeed; perhaps we can recover the intuition.

In both cases, the occurs check is used to detect dependencies between variables.
Type variables are traditionally left floating in space and given meaning by
substitution, but by exposing structure we can manage definitions and
dependencies as we go. Recording type variables in the context is natural when
dealing with dependent types, since there is no distinction between type and term
variables. Even in a simply-typed setting, however, this approach has advantages.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Unification over a context\label{sec:unif}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We begin %%%our study of type inference 
by revisiting unification for
type expressions containing free variables. Let us equip ourselves to
address the problem---solving equations---by explaining which types
are considered equal, raising the question of which things a given
context admits as types, and 
%%%in turn, 
   hence, 
which contexts make sense in the first place.

\begin{figure}[ht]
\[\begin{array}{c}
\mathframe{\Gamma \entails \valid} \smallskip \\
\Axiom{\emptycontext \entails \valid}
\qquad
\Rule{\Gamma \entails \valid}
     {\Gamma, \hole{\alpha} \entails \valid}
\side{\alpha \notin \Gamma}
\smallskip \\
\Rule{\Gamma \entails \valid    \quad    \Gamma \entails \tau \type}
     {\Gamma, \alpha \defn \tau \entails \valid}
\side{\alpha \notin \Gamma}

\bigskip \\

\mathframe{\Gamma \entails \tau \type} \smallskip \\
\Rule{\Gamma, \alpha \defn \_, \Gamma' \entails \valid}
     {\Gamma, \alpha \defn \_, \Gamma' \entails \alpha \type}
\qquad
\Rule{\Gamma \entails \tau \type   \quad   \Gamma \entails \upsilon \type}
     {\Gamma \entails \tau \arrow \upsilon \type}.

\bigskip \\

\mathframe{\Gamma \entails \tau \equiv \upsilon} \smallskip \\
\Rule{\Gamma, \alpha \defn \tau, \Gamma' \entails \valid}
     {\Gamma, \alpha \defn \tau, \Gamma' \entails \alpha \equiv \tau}
\qquad
\Rule{\Gamma \entails \tau \type}
     {\Gamma \entails \tau \equiv \tau}
\qquad
\Rule{\Gamma \entails \upsilon \equiv \tau}
     {\Gamma \entails \tau \equiv \upsilon}
\smallskip \\
\Rule{\Gamma \entails \tau_0 \equiv \upsilon_0
      \quad
      \Gamma \entails \tau_1 \equiv \upsilon_1}
     {\Gamma \entails \tau_0 \arrow \tau_1 \equiv \upsilon_0 \arrow \upsilon_1}
\qquad
\Rule{\Gamma \entails \tau_0 \equiv \tau_1
      \quad
      \Gamma \entails \tau_1 \equiv \tau_2}
     {\Gamma \entails \tau_0 \equiv \tau_2}
\end{array}\]
\caption{Rules for validity, types and type equivalence}
\label{fig:oldRules}
\end{figure}

The rules in Figure~\ref{fig:oldRules} define a context as a left-to-right list
of type variables, each of which may be 
\define{declared} unknown (written $\hole{\alpha}$) or
\define{defined} (written $\alpha \defn \tau$). 
A context is \define{valid} if the type \(\tau\) in
every definition makes sense in its preceding context.
For example, the context
$\hole{\alpha}, \hole{\beta}, \gamma \defn \alpha \arrow \beta$
is valid, while %%%but the context
$\alpha \defn \beta, \hole{\beta}$
is not, because $\beta$ is not in scope for the definition of $\alpha$.
This topological sorting of the dependency graph means that 
entries on the right are harder to depend on, and correspondingly easier to
generalise, just by discharging them as hypotheses, as usual.

Definitions in the context induce a nontrivial equational theory on types,
starting with $\alpha \equiv \tau$ for every definition $\alpha \defn \tau$ in
the context, then taking the congruence closure.
Unification is the problem of making variable definitions (increasing
information) to solve an equation.
The idea is that we decompose constraints on the syntactic structure of types
until we reach variables, then move through the context and update it to solve
the equation. 

For example, we might start in context
$\hole{\alpha}, \hole{\beta}, \gamma \defn \alpha \arrow \beta$
aiming to solve the equation $\beta \arrow \alpha \equiv \gamma$.
%
% The definition of $\gamma$ tells us that we must
% solve $\beta \arrow \alpha \equiv \alpha \arrow \beta$ over the context
% $\hole{\alpha}, \hole{\beta}$. This constraint decomposes to
% $\beta \equiv \alpha$ and $\alpha \equiv \beta$, which are easily solved by
% defining $\beta \defn \alpha$, giving the final judgment
%
It suffices to define $\beta \defn \alpha$, giving as final judgment
$$\hole{\alpha}, \beta \defn \alpha, \gamma \defn \alpha \arrow \beta
    \entails \beta \arrow \alpha \equiv \gamma.$$

A context thus contains a substitution, applied on demand, 
in `triangular form'~\cite{DBLP:books/el/RV01/BaaderS01}, 
but that need not be all. As we proceed with the development,
the context structure will evolve to hold a variety of information
about variables of all sorts and some control markers, managing the
generalisation process.

\subsection{Implementation of unification}

\begin{figure*}[p]

\begin{minipage}[t]{0.5\linewidth}

\subfigure[][Types, type variables, occurs check]{\frame{\parbox{\textwidth}{\fixpars\medskip

> data Ty a  =  V a |  Ty a :-> Ty a
>     deriving (Functor, Foldable)

%if showCode

> infixr 5 :->

%endif

> type TyName  = Integer
> type Type    = Ty TyName


> class FTV a where
>     (<?) :: TyName -> a -> Bool

> instance FTV TyName where
>     (<?) = (==)

> instance  (Foldable t, FTV a) => FTV (t a) where
>     alpha <? t = any (alpha <?) t

\label{subfig:typeCode}
}}}

\subfigure[][Context and suffixes]{\frame{\parbox{\textwidth}{\fixpars\medskip

> data TyDecl   =  Some Type | {-"\;"-} Hole
> data TyEntry  =  TyName := TyDecl

> instance FTV TyEntry where
>    alpha <? (_ := Some tau)  = alpha <? tau
>    alpha <? (_ := Hole)      = False

< data Entry    = TY TyEntry | ...
< type Context  = Bwd Entry
< type Suffix   = Fwd TyEntry

%if False

> -- so we can line up the two previous lines
> type Context  = Bwd Entry
> type Suffix   = Fwd TyEntry

%endif

> (<><) :: Context -> Suffix -> Context
> _Gamma <>< F0                   = _Gamma
> _Gamma <>< (alpha := d :> _Xi)  = _Gamma :< TY (alpha := d) <>< _Xi

%if False

> infixl 8 <><

%endif

\label{subfig:contextCode}
}}}

\subfigure[][Context manipulation monad]{\frame{\parbox{\linewidth}{\fixpars\medskip

> type Contextual  = StateT (TyName, Context) Maybe

> fresh :: TyDecl -> Contextual TyName
> fresh d = do   (beta, _Gamma) <- get
>                put (succ beta, _Gamma :< TY (beta := d))
>                return beta

> getContext :: Contextual Context
> getContext = gets snd
>
> putContext :: Context -> Contextual ()
> putContext _Gamma = do  beta <- gets fst
>                         put (beta, _Gamma)
>
> modifyContext :: (Context -> Context) -> Contextual ()
> modifyContext f = getContext >>= putContext . f

\label{subfig:monadCode}
}}}

\end{minipage}
\hspace{\medskipamount}
\begin{minipage}[t]{0.5\linewidth}

\subfigure[][Processing the context]{\frame{\parbox{\linewidth}{\fixpars\medskip

> data Extension = Restore | Replace Suffix

> onTop ::  (TyEntry -> Contextual Extension)
>             -> Contextual ()
> onTop f = do
>     _Gamma :< vD <- getContext
>     putContext _Gamma
>     case vD of
>         TY alphaD    -> do  m <- f alphaD
>                             case m of
>                                 Replace _Xi  -> modifyContext (<>< _Xi)
>                                 Restore      -> modifyContext (:< vD)
>         _            -> onTop f >> modifyContext (:< vD)

> restore :: Contextual Extension
> restore = return Restore

> replace :: Suffix -> Contextual Extension
> replace = return . Replace

\label{subfig:onTopCode}
}}}

\subfigure[][Unification]{\frame{\parbox{\linewidth}{\fixpars\medskip

> unify :: Type -> Type -> Contextual ()
> unify (tau0 :-> tau1)  (upsilon0 :-> upsilon1)  = unify tau0 upsilon0 >> unify tau1 upsilon1
> unify (V alpha)        (V beta)                 = onTop $
>   \ (gamma := d) -> case
>           (gamma == alpha,  gamma == beta,  d         ) of
>           (True,            True,           _         )  ->  restore                                 
>           (True,            False,          Hole      )  ->  replace (alpha := Some (V beta) :> F0)  
>           (False,           True,           Hole      )  ->  replace (beta := Some (V alpha) :> F0)  
>           (True,            False,          Some tau  )  ->  unify (V beta)   tau       >> restore   
>           (False,           True,           Some tau  )  ->  unify (V alpha)  tau       >> restore   
>           (False,           False,          _         )  ->  unify (V alpha)  (V beta)  >> restore   
> unify (V alpha)        tau                               =   solve alpha F0 tau
> unify tau              (V alpha)                         =   solve alpha F0 tau    

> solve :: TyName -> Suffix -> Type -> Contextual ()
> solve alpha _Xi tau = onTop $
>   \ (gamma := d) -> let occurs = gamma <? tau || gamma <? _Xi in case
>     (gamma == alpha,  occurs,  d             ) of
>     (True,            True,    _             )  ->  fail "Occurrence detected!"
>     (True,            False,   Hole          )  ->  replace (_Xi <+> (alpha := Some tau :> F0))
>     (True,            False,   Some upsilon  )  ->  modifyContext (<>< _Xi)
>                                                 >>  unify upsilon tau
>                                                 >>  restore
>     (False,           True,    _             )  ->  solve alpha (gamma := d :> _Xi) tau
>                                                 >>  replace F0   
>     (False,           False,   _             )  ->  solve alpha _Xi tau
>                                                 >>  restore

\label{subfig:unifyCode}
}}}

\end{minipage}

\caption{Haskell implementation of unification}
\label{fig:unifyCode}
\end{figure*}

Figure~\ref{fig:unifyCode} renders our unification algorithm in Haskell. 
%%%\citeauthor{NaraschewskiN-JAR} formally proved correctness of \AlgorithmW\ 
   \AlgorithmW\ has been formally verified 
in Isabelle/HOL using a counter for fresh 
%%%variable 
   name 
generation and a monad to propagate failure \citep{NaraschewskiN-JAR}; 
we use similar techniques here.

Figure~\ref{subfig:typeCode} implements types as a foldable functor
parameterised by a type |TyName| of type variable names;  
   for simplicity, we use integers.
We compute free type variables using the typeclass |FTV| with membership
function |(<?)|. 
We can simply
derive the required typeclass instances 
using |Foldable|, 
thanks to a language
extension in GHC 6.12 \citep{ghc_team_glorious_2009}. 
%%%Thanks to a language
%%%extension in GHC 6.12 \citep{ghc_team_glorious_2009} we can simply
%%%derive the required typeclass instances. 
%%%For simplicity, we use integers as names.
%%%We can find free type variables using the typeclass |FTV| with membership
%%%function |(<?)|. We get most of the required instances for free using |Foldable|.

Figure~\ref{subfig:contextCode} defines context entries, contexts and suffixes.
The types |Bwd| and |Fwd|, whose definitions are omitted, are backwards and forwards lists
with |B0| for 
%%%both empty lists 
   the empty list 
and |:<| and |:>| for snoc and cons respectively.
Lists are monoids for the append operator |<+>|; the \scare{fish}
operator |(<><)| appends a suffix to a context. We %%%will 
later extend |Entry| to
handle term variables, so this definition is incomplete.

Figure~\ref{subfig:monadCode} defines the |Contextual| monad of computations which mutate
the context or fail. The |TyName| component is the next fresh 
%%%type variable name 
   name 
to use; it is an implementation detail not mentioned in the typing
rules. The |fresh| function generates a 
%%%fresh variable name and appends a 
   fresh name and appends its
declaration to the context. Our choice of |TyName| makes it easy to
choose a name fresh with respect to a |Context|.

Figure~\ref{subfig:onTopCode} implements |onTop|, which delivers the
typical access pattern for contexts, locally bringing the top variable
declaration into focus and working over the remainder.  The local
operation \(f\), passed as an argument, may |restore| the previous entry, or
it may return a context extension (containing at least as much
information as the entry that has been removed) with which to
|replace| it.

Figure~\ref{subfig:unifyCode} gives the actual implementations of unification
and solution. Unification proceeds structurally over types. If it reaches a pair
of variables, it examines the context, using the operator |onTop| to pick out
a variable declaration to consider. Depending on the variables, it %%%will
then either succeeds, restoring the old entry or replacing it with a new one, 
or continues %%%unifying 
with an updated constraint.

The |solve| function is called when a variable must be unified with a non-variable type.
It works similarly to unification of variables, but must accumulate a list of
the type's dependencies and push them left through the context. It also performs
the occurs check and invokes the monadic failure command if an illegal occurrence
(which would lead to an infinite type) is detected.

As an example, consider the behaviour of the algorithm when |unify| is called
to solve $\alpha \arrow \beta \equiv \alpha' \arrow (\gamma \arrow \gamma)$:
%
% in the context $\hole{\alpha}, \hole{\beta}, \alpha' \defn \beta, \hole{\gamma}$.
% The first case matches, decomposing the constraint structurally and first
% invoking unify on $\alpha$ and $\alpha'$. The algorithm then traverses the
% context, ignoring $\gamma$, then moving past $\alpha'$ by unifying $\alpha$ and
% $\beta$. This succeds by defining $\beta$ to be $\alpha$, giving the context
% $\hole{\alpha}, \beta \defn \alpha, \alpha' \defn \beta, \hole{\gamma}$.
%
% The second part of the structural decomposition now unifies $\beta$ with
% $\gamma \arrow \gamma$. This calls |solve|, which collects $\gamma$ in the
% dependency suffix, ignores $\alpha'$ and moves past $\beta$ by unifying
% $\alpha$ and $\gamma \arrow \gamma$. Again this succeeds, giving the context
% $\hole{\gamma}, \alpha \defn \gamma \arrow \gamma, \beta \defn \alpha,
% \alpha' \defn \beta$.
%
\newcommand{\grot}[1]{\multicolumn{2}{@@{}l@@{}}{\ensuremath{[#1]}}}
\[\begin{array}{@@{}c@@{}l@@{\,}l@@{\,}l@@{\,}l@@{\,}ll}
         &\hole{\alpha},& \hole{\beta},& \alpha' \defn \beta,&
     \hole{\gamma}&                     &\textrm{initially}
\smallskip\\
 &
  \hole{\alpha},& \hole{\beta},& \alpha' \defn \beta,& \hole{\gamma},&
     [\alpha\equiv\alpha'] \\
 &
  \hole{\alpha},& \hole{\beta},& \alpha' \defn \beta,&
     [\alpha\equiv\alpha'],& \hole{\gamma} \\
 &
  \hole{\alpha},& \hole{\beta},&
     [\alpha\equiv\beta],& \alpha' \defn \beta,& \hole{\gamma}
\smallskip \\
\transto~ &\hole{\alpha},&
    \multicolumn{2}{@@{}c@@{\,}}{\beta \defn \alpha,\;\;}&
    \alpha' \defn \beta,&
    \hole{\gamma}                       &\alpha \equiv \alpha'
\smallskip \\
 &
  \hole{\alpha},& \beta\defn\alpha,& \alpha' \defn \beta,& \hole{\gamma},&
     [\beta\equiv\gamma\arrow\gamma] \\
 &
  \hole{\alpha},& \beta\defn\alpha,& \alpha' \defn \beta,&
     \grot{ \hole{\gamma} \mid \beta\equiv\gamma\arrow\gamma} \\
 &
  \hole{\alpha},& \beta\defn\alpha,&
     \grot{ \hole{\gamma} \mid \beta\equiv\gamma\arrow\gamma},&
     \alpha' \defn \beta \\
 &
  \hole{\alpha},&
     \grot{\hole{\gamma} \mid \alpha\equiv\gamma\arrow\gamma},&
     \alpha' \defn \beta,& \beta\defn\alpha
\smallskip \\
\transto~ &\hole{\gamma},&
 \multicolumn{2}{@@{}c@@{\,}}{\alpha \defn \gamma \arrow \gamma,}&
 \beta \defn \alpha,& \alpha' \defn \beta   &\beta \equiv \gamma \arrow \gamma 
\end{array}\]
The constraint decomposes into two constraints on variables. The first ignores
$\gamma$, moves past $\alpha'$ by updating the constraint to
$\alpha \equiv \beta$, then defines $\beta \defn \alpha$.
The second calls |solve|, which collects $\gamma$ in the dependency suffix,
ignores $\alpha'$, moves past $\beta$ by updating the constraint to
$\alpha \equiv \gamma \arrow \gamma$, then defines $\alpha$ after pasting in
$\gamma$.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Modelling statements-in-context\label{sec:stmts}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Having seen an implementation of unification, let us try to understand it.
We would like to give a general picture of \scare{statements-in-context} which
allows us to view unification and type inference in a uniform setting.
What is the common structure?

A \define{context} is a list of \define{declarations} assigning
\define{properties} to
%%%variables (here, in particular, type variables). 
   names (in particular, those of type variables). 
We let $\Gamma, \Delta, \Theta$ range over contexts.
The empty context is written $\emptycontext$. 
Let $\V_\TY$ be a set of type
variables and $\D_\TY$ the properties 
%%%that may be given to them
   assignable to them: 
the 
%%%\scare{unknown variable} 
   \scare{unknown} 
property $\,\hole{}$ and 
%%%\scare{defined variable} 
   \scare{defined}
properties $\,\defn{\tau}$, one for each type $\tau$.

Later we %%%will 
introduce corresponding definitions for term variables. Where
needed we let $K \in \{ \TY, \TM \}$ represent an arbitrary sort of variable.
We write $\decl{x}{D}$ for an arbitrary property, with $x \in \V_K$ and
$D \in \D_K$. The set of variables of $\Gamma$ with sort $K$ is written
$\V_K(\Gamma)$.

We will build a set $\Ss$ of \define{statements}, assertions which can be judged
in contexts. For now, the grammar of statements will be
$$S ::=~ \valid
    ~||~ \tau \type
    ~||~ \tau \equiv \upsilon
    ~||~ S \wedge S$$
meaning, respectively, that the context is valid, $\tau$ is a type, the types
$\tau$ and $\upsilon$ are equivalent, and both conjuncts hold.
%%%Note that $\valid$ and $\wedge$ give a unit and product for statements.

A statement has zero or more
\define{parameters}, each of which has an associated \define{\sanity}, 
i.e.\ a statement whose truth is presupposed for the problem to make sense.
The $\valid$ statement has no parameter and hence no \sanity s.
In $\tau \type$, the parameter $\tau$ has \sanity\  $\valid$.
The type equivalence statement $\tau \equiv \upsilon$ has two parameters; the
\sanity s are $\tau \type$ and $\upsilon \type$ respectively.
Finally, $S \wedge S'$ has parameters (and \sanity s) taken from $S$ and
$S'$.

Each declaration in the context causes some statement to hold.
We maintain a map $\sem{\cdot}_K : \V_K \times \D_K \rightarrow \Ss$
from declarations to statements. (Typically we will omit the subscript $K$.)
The idea is that $\sem{\decl{x}{D}}$ is the statement that holds by virtue of the
declaration $\decl{x}{D}$ in the context. For type variables, we define
\[\begin{array}{r@@{\,}l}
\sem{\hole{\alpha}} &= \alpha \type \\
\sem{\alpha \defn \tau} &= \alpha \type \wedge \alpha \equiv \tau.
\end{array}\]

We can inspect the context in derivations using the inference rule
$$\namer{Lookup}
  \Rule{\decl{x}{D} \in \Gamma}
       {\Gamma \entailsN \sem{\decl{x}{D}}}.$$
Note the different turnstile symbol in the conclusion of this rule.
We write the \define{normal judgment} $\Gamma \entails S$
to mean that the declarations in $\Gamma$ support the statement $S \in
\Ss$.  We write the \define{neutral judgment} $\Gamma \entailsN S$ to
mean that $S$ follows directly from applying a fact in $\Gamma$.
Neutral judgments capture exactly the legitimate appeals to assumptions
in the context, just as \scare{neutral terms} in $\lambda$-calculus are
applied variables. Variables are the \scare{atoms} of symbols, and appeals
to declarations in the context are the atoms of derivations.

The \name{Lookup} rule is our only means to extract information from the
context, so we omit contextual plumbing (almost) everywhere else.
%%%
For example, embedding neutral judgments into the normal:
$$\namer{Neutral}
  \Rule{\entailsN S}
       {\entails S}.$$

\subsection{Validity of contexts}

It is not enough for contexts to be lists of declarations: they must
be well-founded, that is, each declaration should make sense in
\emph{its} context.  A context is \define{valid} if it declares each name
at most once, and the assigned property \(D\) is meaningful in the
preceding context. Rules for the context validity statement
$\valid$ are given in Figure~\ref{fig:contextValidityRules}.

\begin{figure}[ht]
\[\begin{array}{c}
\mathframe{\Gamma \entails \valid}
\smallskip\\
\Axiom{\emptycontext \entails \valid}
\qquad
\Rule{\Gamma \entails \valid    \quad    \Gamma \entails \ok_K D}
     {\Gamma, \decl{x}{D} \entails \valid}
\side{x \in \V_K \setminus \V_K(\Gamma)}
\end{array}\]
\caption{Rules for context validity}
\label{fig:contextValidityRules}
\end{figure}

The map $\ok_K : \D_K \rightarrow \Ss$, for each $K \in \K$, 
associates the statement of being meaningful, \(\ok_{K} D\), to each \(D\). 
%%%For type properties:
   For types: 
\[\begin{array}{r@@{\,}l}
\ok_\TY (\hole{}) &= \valid \\
\ok_\TY (\defn{\tau}) &= \tau \type
\end{array}\]
%%%Now we can define the context validity statement
%%%$\valid$ as shown in Figure~\ref{fig:contextValidityRules}.

Henceforth we %%%implicitly 
assume that all contexts treated are valid,
and ensure we only construct valid ones. We typically ignore 
%%%the issue of fresh names, 
   freshness issues, 
as our simple counter implementation suffices for most
purposes.

%%%DONE: don't do this. \TODO{Relate to traditional presentation - give intuition.}

\subsection{Rules for establishing statements}

Figure~\ref{fig:statementRules} gives rules for establishing statements other than
$\valid$.
We deduce that variables are types by looking up the context, but we need
a structural rule for the $\arrow$ type constructor.

%%%DONE: use \mathframe. \TODO{Fix rule box sizes.}

\begin{figure}[ht]
\[\begin{array}{c}
\mathframe{\tau \type}\qquad\mathframe{\tau \equiv \upsilon}\qquad\mathframe{S \wedge S'}
\smallskip\\
\Rule{\tau \type   \quad   \upsilon \type}
     {\tau \arrow \upsilon \type}
\qquad
\Rule{\tau \type}
     {\tau \equiv \tau}
\qquad
\Rule{\upsilon \equiv \tau}
     {\tau \equiv \upsilon}
\\
\Rule{\tau_0 \equiv \upsilon_0
      \quad
      \tau_1 \equiv \upsilon_1}
     {\tau_0 \arrow \tau_1 \equiv \upsilon_0 \arrow \upsilon_1}
\qquad
\Rule{\tau_0 \equiv \tau_1
      \quad
      \tau_1 \equiv \tau_2}
     {\tau_0 \equiv \tau_2}
\\
\Rule{S \quad S'} {S \wedge S'}
  \qquad
  \Rule{\entailsN S \wedge S'}
       {\entailsN S}
  \qquad
  \Rule{\entailsN S \wedge S'}
       {\entailsN S'}
\end{array}\]
\caption{Rules for types, equivalence and conjunction}
\label{fig:statementRules}
\end{figure}

Statement conjunction $S \wedge S'$ allows us to package multiple facts
about a single variable, with a normal introduction rule (pairing) and neutral
elimination rules (projections).
This is but one instance of a general pattern: we add \emph{normal} introduction
rules for composite forms, but supply
eliminators only for statements 
%%%which ultimately rest 
   ultimately resting 
on (composite) hypotheses,
obtained by \name{Lookup}. This forces
derivations to be cut-free, facilitating reasoning by induction on
derivations.
Adding the corresponding projections for \emph{normal} judgments 
would hamper us in obtaining a syntax-directed rule system. In any case, we shall
ensure that the corresponding elimination rules are admissible, as is clearly
the case for conjunction.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{An information order for contexts\label{sec:stab}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% \subsection{Information order}

The transition from $\hole{\alpha}$ to $\alpha \defn \tau$ intuitively cannot
falsify any existing equations.
More generally, if we rely on the context to tell us what we may
deduce about variables, then making contexts more informative must preserve
%%%deductions. 
   derivability of judgments. 

Let $\Gamma$ and $\Delta$ be contexts.
A \define{substitution from $\Gamma$ to $\Delta$} is a map \(\delta\) from
$\tyvars{\Gamma}$ to $\{ \tau ~||~ \Delta \entails \tau \type \}$.
We could also substitute for term variables, and give a more general
definition, but we omit this for simplicity.
Substitutions act on types and statements as usual. 
Composition of substitutions \(\theta, \delta\) is given by
$(\theta \compose \delta) (\alpha) = \theta (\delta \alpha)$.
   The identity substitution is written \(\iota\). 
%%%We write $\subst{\tau}{\alpha}{}$ for the substitution that maps 
   The substitution $\subst{\tau}{\alpha}{}$ maps 
$\alpha$ to $\tau$ and 
%%%other variables to themselves. 
   otherwise acts as \(\iota\). 
If $\delta : \Gamma, \Gamma' \lei \Theta$ we write $\restrict{\delta}{\Gamma}$
for the restriction of $\delta$ to the type variables in $\Gamma$.

Given $\delta$ from $\Gamma$ to $\Delta$, we 
write the \define{information increase} 
   relation 
$\delta : \Gamma \lei \Delta$ 
and 
say \define{$\Delta$ is more informative than $\Gamma$} 
if for all $\decl{x}{D} \in \Gamma$, we have 
$\Delta \entails \delta \sem{\decl{x}{D}}$. 
That is, $\Delta$ supports the statements arising from declarations
in $\Gamma$.
We write $\Gamma \lei \Delta$ if 
%%%$\iota : \Gamma \lei \Delta$, where  $\iota$ is the identity substitution. 
   $\iota : \Gamma \lei \Delta$.

We write $\delta \eqsubst \theta : \Gamma \lei \Delta$ if
$\delta : \Gamma \lei \Delta$, $\theta : \Gamma \lei \Delta$
and for all $\alpha \in \tyvars{\Gamma}$,
$\Delta \entails \delta\alpha \equiv \theta\alpha$.
We will sometimes just write $\delta \equiv \theta$ if the contexts involved
are obvious.
It is straightforward to verify that $\eqsubst$ is an equivalence relation
for fixed contexts $\Gamma$ and $\Delta$, and that if
$\delta \eqsubst \theta$ then
$\Delta \entails \delta\tau \equiv \theta\tau$ for any $\Gamma$-type $\tau$.

This partial order on contexts suffices to ensure stability, as described
%%%in the following section, 
   below, 
but in practice the algorithm works with a more structured
subrelation of $\lei$. We give up more freedom to achieve a more comprehensible
algorithm. For example, our algorithm always uses the identity substitution.



\subsection{Stable statements}

We say a statement $S$ is \define{stable} if it is preserved under information
increase, that is, if
$$\Gamma \entails S  \quad \mathrm{and}  \quad  \delta : \Gamma \lei \Delta
    \quad \Rightarrow \quad  \Delta \entails \delta S.$$
This says that we can extend a simultaneous substitution on syntax to a
simultaneous substitution on derivations.
Since we only consider valid contexts, the statement $\valid$ always holds,
and is invariant under substitution, so it is clearly stable.

We observe that neutral proofs always ensure stability:
\begin{lemma}\label{lem:neutrality}
If $\Gamma \entailsN S$ and $\delta : \Gamma \lei \Delta$ then
$\Delta \entails \delta S$.
\end{lemma}
\proofsux\begin{proof}
By structural induction on derivations. If the proof is by \name{Lookup}, then
the result holds by definition of information increase. Otherwise, the proof is
by a neutral elimination rule, so the result follows by induction and
admissibility of the corresponding normal elimination rule.
\end{proof}

We have a standard approach, effective by construction, 
to proving stability of most statements. 
In each case we proceed by induction on  
%%%the structure of 
derivations. Where the \name{Neutral} rule is applied, stability holds by 
Lemma~\ref{lem:neutrality}. Otherwise, we verify that non-recursive hypotheses
are stable and that recursive hypotheses occur in strictly positive positions,
hence are stable by induction. Applying this method shows that both 
$\tau \type$ and $\tau \equiv \upsilon$ are stable.

\begin{lemma}[Conjunction preserves stability]\label{lem:stab-pres-conj}
If $S$ and $S'$ are stable then $S \wedge S'$ is stable.
\end{lemma}
\proofsux\begin{proof}
Suppose $\delta : \Gamma \lei \Delta$, the statements $S$ and $S'$ are stable,
and $\Gamma \entails (S \wedge S')$. If the proof is by \name{Neutral}
then $\Delta \entails \delta (S \wedge S')$ by Lemma~\ref{lem:neutrality}.
Otherwise $\Gamma \entails S$ and $\Gamma \entails S'$,
so by stability, $\Delta \entails \delta S$ and $\Delta \entails \delta S'$, 
and hence $\Delta \entails \delta (S \wedge S')$.
\end{proof}

Thanks to stability, our information order is reasonable:
\begin{lemma}\label{lei:preorder}
If $\sem{\decl{x}{D}}$ is stable for every declaration $\decl{x}{D}$, then
the $\lei$ relation is a preorder, with reflexivity demonstrated by
the identity substitution
$\iota : \Gamma \lei \Gamma : v \mapsto v$, and transitivity by composition:
$$\delta : \Gamma \lei \Delta  ~~\text{and}~~  \theta : \Delta \lei \Theta
  \quad \Rightarrow \quad  \theta \compose \delta : \Gamma \lei \Theta.$$
\end{lemma}
\proofsux\begin{proof}
Reflexivity follows immediately by applying the \name{Lookup} and
\name{Neutral} rules.
For transitivity, suppose $\decl{x}{D} \in \Gamma$,
then $\Delta \entails \delta \sem{\decl{x}{D}}$ since
$\delta : \Gamma \lei \Delta$.
Now by stability applied to $\delta \sem{\decl{x}{D}}$ using $\theta$, we have
$\Theta \entails \theta\delta \sem{\decl{x}{D}}$ as required.
\end{proof}

%%\TODO{How do we use the following lemma?}
%%\begin{lemma}
%%\label{lem:composePreservesEquivSubst}
%%If $\delta_0 \eqsubst \delta_1 : \Gamma \lei \Delta$
%%and $\theta_0 \eqsubst \theta_1 : \Delta \lei \Theta$
%%then $\theta_0 \compose \delta_0  \eqsubst  \theta_1 \compose \delta_1 :
%%         \Gamma \lei \Theta$.
%%\end{lemma}
%%\proofsux\begin{proof}
%%Fix $\alpha \in \tyvars{\Gamma}$. By definition of $\eqsubst$,
%%$\Delta \entails \delta_0\alpha \equiv \delta_1\alpha$,
%%so by stability,
%%$\Theta \entails \theta_0\delta_0\alpha \equiv \theta_0\delta_1\alpha$.
%%Moreover
%%$\Theta \entails \theta_0\delta_1\alpha \equiv \theta_1\delta_1\alpha$,
%%and hence
%%$\Theta \entails \theta_0\delta_0\alpha \equiv \theta_1\delta_1\alpha$
%%by transitivity.
%%\end{proof}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Constraints: problems at ground mode\label{sec:constrs}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We define a \define{constraint problem} to be a pair of a context $\Gamma$ and a statement
$P$, where
the \sanity s on the parameters of $P$ hold in $\Gamma$, but $P$ itself
may not. A \define{solution} to such a problem is then an information increase 
$\delta : \Gamma \lei \Delta$ such that
$\Delta \entails \delta P$. 
   In this setting, the \define{unification} problem \((\Gamma, \tau \equiv \upsilon)\) 
%%%is given $\Gamma$, $\tau$ and $\upsilon$ such that
   stipulates that 
$\Gamma \entails \tau \type \wedge \upsilon \type$, and 
   a solution to the problem (a \define{unifier}) is given by 
%%%must find 
$\delta : \Gamma \lei \Delta$ such that
$\Delta \entails \delta \tau \equiv \delta \upsilon$.

We are interested in algorithms to solve problems, preferably in as
general a way as possible (that is, by making the smallest information increase
necessary to find a solution). 
   For the unification problem, this 
corresponds to finding a most general
unifier. The solution $\delta : \Gamma \lei \Delta$ is \define{minimal} if, for
any other solution $\theta: \Gamma \lei \Theta$, there exists a
substitution $\zeta : \Delta \lei \Theta$ such that
$\theta \eqsubst \zeta \compose \delta$ (we say $\theta$ \emph{factors through}
$\delta$ with \emph{cofactor} $\zeta$).
%%%
We write $\LEIStmt{\Gamma}{P}{\Delta}$ to mean that $(\Gamma, P)$ is a
problem with minimal solution $\iota : \Gamma \lei \Delta$.
In fact, we %%%will 
always find minimal solutions 
%%%that use the identity substitution. 
%%%in the form $\iota : \Gamma \lei \Delta$. 
   in this form. 

As one might expect, the following rule is admissible:  
$$\Rule{\leiStmt{\Gamma}{P}{\Delta}
       \quad  \leiStmt{\Delta}{Q}{\Theta}}
       {\leiStmt{\Gamma}{P \wedge Q}{\Theta}}$$
since stability ensures that if $\Delta$ solves $P$ then any more
informative context $\Theta$ also solves $P$. More surprisingly, this also
gives minimal solutions to composite problems, allowing a \scare{greedy} 
solution strategy.
%
% We can now state the following \scare{greedy} approach to finding minimal
% solutions to such composite problems: find a minimal solution of problem $P$,
% then extend it to (minimally) solve $Q$:
%
\begin{lemma}[The Optimist's lemma]
\label{lem:optimist}
The following is admissible:
$$\Rule{\LEIStmt{\Gamma}{P}{\Delta}
       \quad  \LEIStmt{\Delta}{Q}{\Theta}}
       {\LEIStmt{\Gamma}{P \wedge Q}{\Theta}}.$$
\end{lemma}

\proofsux\begin{proof}[Sketch]
Any solution $\phi : \Gamma \lei \Phi$ to $(\Gamma, P \wedge Q)$ must solve
$(\Gamma, P)$, and hence factor through $\iota : \Gamma \lei \Delta$. But its
cofactor solves $(\Delta, Q)$, and hence factors through
$\iota : \Delta \lei \Theta$. For the detailed proof of a
more general result, see Lemma~\ref{lem:optimistInference}.
\end{proof}

This sequential approach to problem solving is not the only decomposition
justified by stability. \citeauthor{mcadam_unification_1998}'s account of
unification \citeyearpar{mcadam_unification_1998} amounts to a concurrent,
transactional decomposition of problems. The same context is extended via
multiple different substitutions, which are then unified to produce a single
substitution.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The unification algorithm, formally\label{sec:unif-formal}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We now present the algorithm formally. The structural rule ensures that
rigid problems, with $\arrow$ on each side, decompose
into subproblems: by the Optimist's lemma, these we solve
sequentially. Otherwise, we have either two variables, or a variable
and a type. In each case, we ask how the rightmost type
variable in the context helps us, and either solve
the problem or continue leftward in the context with an updated constraint.
When solving a variable with a type, we must accumulate
the type's dependencies as we find them, performing the occurs check to
ensure a solution exists.

The rules in Figure~\ref{fig:unifyRules} define our unification algorithm. The
judgment $\algUnify{\Gamma}{\tau}{\upsilon}{\Delta}$ means that given inputs
$\Gamma$, $\tau$ and $\upsilon$, unification succeeds and produces output
context $\Delta$. This is subject to the input \sanity\ 
$\Gamma \entails \tau \type \wedge \upsilon \type$.

The judgment
$\algInstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$
means that given inputs $\Gamma$, $\Xi$, $\alpha$ and $\tau$,
solving $\alpha$ with $\tau$ succeeds,  
yielding output context $\Delta$. The idea is that the bar ($||$) represents
%%%progress through the context, 
   progress in examining context elements in order, 
%%%and $\Xi$ contains dependencies of $\tau$ (which
%%%must be placed before $\tau$ for it to be well-defined). 
   and $\Xi$ contains exactly those declarations on which $\tau$ depends.  
Formally, the inputs 
must satisfy:

\hspace*{0.1in}$\alpha \in \tyvars{\Gamma}$, ~
$\tau$ is not a variable, \\ {}
\hspace*{0.1in}$\Gamma, \Xi \entails \tau \type$, ~ 
$\Xi$ contains only type variable declarations \\ {}
\hspace*{0.1in}$\beta \in \tyvars{\Xi} \Rightarrow \beta \in \FTV{\tau, \Xi}$.

\TODO{Chat about this lemma. Perhaps it needs to come slightly later?}

\begin{lemma}[Soundness and generality of unification]
\label{lem:unifySound}
\begin{enumerate}[(a)]
\item Suppose $\algUnify{\Gamma}{\tau}{\upsilon}{\Delta}$. Then 
$\tyvars{\Gamma} = \tyvars{\Delta}$ \\ and
$\LEIStmt{\Gamma}{\tau \equiv \upsilon}{\Delta}$.
\item Suppose 
$\algInstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$. Then 
$\tyvars{\Gamma, \Xi} = \tyvars{\Delta}$ and
$\LEIStmt{\Gamma, \Xi}{\alpha \equiv \tau}{\Delta}$.
\end{enumerate}

\end{lemma}
\proofsux\begin{proof}
By induction on the structure of derivations.
For each rule, we verify that it preserves the set of type variables and
that $\Gamma \lei \Delta$.

For minimality, it suffices to take some
$\theta : \Gamma \lei \Theta$ such that
$\Theta \entails \theta\tau \equiv \theta\upsilon$, and show
$\theta : \Delta \lei \Theta$. As the type variables of $\Gamma$ are
the same as $\Delta$, we simply note that definitions in $\Delta$ hold as
equations in $\Theta$ for each rule that rewrites or solves the problem.

The only rule not in this form is \name{Decompose}, but solutions to
$\tau_0 \arrow \tau_1 \equiv \upsilon_0 \arrow \upsilon_1$ are exactly those
that solve $\tau_0 \equiv \upsilon_0 \wedge \tau_1 \equiv \upsilon_1$,
so it gives a minimal solution by the Optimist's lemma.
%%%
\TODO{Do we need to say more about part (b)? Should we comment somewhere about
keeping things right not being necessary for generality at the moment, but
arising later?}
\end{proof}


Some context entries have no bearing on the problem at hand.
We write $x \perp X$ ($x$ is orthogonal to set $X$ of type variables)
if $x$ is not a type variable or not in $X$.

The rules \name{Define} and \name{Expand} have
symmetric counterparts, identical apart from interchanging the equated
terms in the conclusion. Usually we will ignore these without loss of generality.

\begin{figure}[ht]
\[\begin{array}{c}
\mathframe{\algUnify{\Gamma}{\tau}{\upsilon}{\Delta}}

\smallskip\\
\namer{Decompose}
\Rule{\algUnify{\Gamma}{\tau_0}{\upsilon_0}{\Delta_0}
      \quad
      \algUnify{\Delta_0}{\tau_1}{\upsilon_1}{\Delta}}
    {\algUnify{\Gamma}{\tau_0 \arrow \tau_1}{\upsilon_0 \arrow \upsilon_1}{\Delta}}

\smallskip\\

\namer{Idle}
% \Rule{\Gamma \entails \alpha \type}
\Axiom{\algUnify{\Gamma_0, \alpha D}{\alpha}{\alpha}{\Gamma_0, \alpha D}}

\smallskip\\ 

\namer{Define}
%\Rule{\Gamma_0 \entails \beta \type}
\Axiom{\algUnify{\Gamma_0, \hole{\alpha}}{\alpha}{\beta}{\Gamma_0, \alpha \defn \beta}}
\side{\alpha \neq \beta}

\smallskip\\ 

\namer{Ignore}
\Rule{\algUnify{\Gamma_0}{\alpha}{\beta}{\Delta_0}}
     {\algUnify{\Gamma_0, \decl{x}{D}}{\alpha}{\beta}{\Delta_0, \decl{x}{D}}}
\side{x \perp \{\alpha, \beta\} }

\smallskip\\ 

\namer{Expand}
\Rule{\algUnify{\Gamma_0}{\tau}{\beta}{\Delta_0}}
     {\algUnify{\Gamma_0, \alpha \defn \tau}{\alpha}{\beta}{\Delta_0, \alpha \defn \tau}}
\side{\alpha \neq \beta}

\smallskip\\ 

\namer{Solve}
\Rule{\algInstantiate{\Gamma}{\alpha}{\tau}{\emptycontext}{\Delta}}
     {\algUnify{\Gamma}{\alpha}{\tau}{\Delta}}
%% \side{\tau \neq \alpha}
\side{\tau \mathrm{~not~variable}}

\bigskip\\

\mathframe{\algInstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}}

\smallskip\\
\namer{DefineS}
% \Rule{\Gamma_0, \Xi \entails \tau \type}
\Axiom{\algInstantiate{\Gamma_0, \hole{\alpha}}{\alpha}{\tau}{\Xi}
                   {\Gamma_0, \Xi, \alpha \defn \tau}}
\side{\alpha \notin \FTV{\tau, \Xi}}

\smallskip\\ 

\namer{IgnoreS}
\Rule{\algInstantiate{\Gamma_0}{\alpha}{\tau}{\Xi}{\Delta_0}}
     {\algInstantiate{\Gamma_0, \decl{x}{D}}{\alpha}{\tau}{\Xi}{\Delta_0, \decl{x}{D}}}
\side{x \perp \FTV{\alpha, \tau, \Xi}}

\smallskip\\

\namer{ExpandS}
\Rule{\algUnify{\Gamma_0, \Xi}{\upsilon}{\tau}{\Delta_0}}
     {\algInstantiate{\Gamma_0, \alpha \defn \upsilon}{\alpha}{\tau}{\Xi}
                   {\Delta_0, \alpha \defn \upsilon}}
\side{\alpha \notin \FTV{\tau, \Xi}}

\smallskip\\

\namer{DependS}
\Rule{\algInstantiate{\Gamma_0}{\alpha}{\tau}{\beta D, \Xi}{\Delta}}
     {\algInstantiate{\Gamma_0, \beta D}{\alpha}{\tau}{\Xi}{\Delta}}
\side{\alpha \neq \beta, \beta \in \FTV{\tau, \Xi}}

\end{array}\]
\caption{Algorithmic rules for unification}
\label{fig:unifyRules}
\end{figure}

Observe that we have no rule in the situation where 
$$\algInstantiate{\Gamma_0, \alpha D}{\alpha}{\tau}{\Xi}{\Delta}
\mathrm{~with~} \alpha \in \FTV{\tau, \Xi}$$
so the algorithm fails in this case. 
This is an occurs check failure: $\alpha$ and $\tau$ cannot unify 
if $\alpha$ occurs in
$\tau$ or in an entry that $\tau$ depends on, and $\tau$ is not a variable.
Given the single type constructor symbol (the function arrow $\arrow$),
there are no failures due to rigid-rigid mismatch. 
To add these would not significantly complicate matters.

The idea of assertions producing a resulting context goes back at least to
\citet{pollack_implicit_1990}. \citet{Nipkow-Prehofer-JFP95} use (unordered)
input and output contexts to pass information about \scare{sorts} for Haskell
typeclass inference, alongside a conventional substitution-based presentation
of unification.

By exposing the contextual structure underlying unification we make
termination of the algorithm evident. Each recursive appeal to
unification (directly or via the solving process) either shortens the context
left of the $~||~$, shortens the overall
context, or preserves the context and decomposes
types~\citep{mcbride:unification}. We are correspondingly entitled to
reason about the total correctness of unification by induction on the
algorithmic rules.



\subsection{Completeness}

\begin{lemma}[Occurs check]
\label{lem:occursCheck}
Let $\alpha$ be a variable and $\tau$ a non-variable type such that
$\alpha \in \FTV{\tau}$. There is no context $\Theta$ and substitution
$\theta$ such that $\Theta \entails \theta\alpha \equiv \theta\tau$ or
$\Theta \entails \theta\tau \equiv \theta\alpha$.
\end{lemma}
\proofsux\begin{proof}
Suppose otherwise. Moreover, let $\Theta$ contain no definitions
(by extending $\theta$ to substitute them out). Now,
$\theta\alpha\equiv\theta\tau$ ensures $\theta\alpha=\theta\tau$,
but as $\alpha \in \FTV{\tau}$ and $\tau$ is not $\alpha$, $\theta\tau$
must be a proper subterm of itself, which is impossible.
\end{proof}

\begin{lemma}[Completeness of unification]
\label{lem:unifyComplete}
\begin{enumerate}[(a)]
\item If $\theta : \Gamma \lei \Theta$,
$\Gamma \entails \upsilon \type \wedge \tau \type$ and
$\Theta \entails \theta\upsilon \equiv \theta\tau$, then
there is some context $\Delta$ such that
$\algUnify{\Gamma}{\upsilon}{\tau}{\Delta}$.

% with
% $\theta : \Delta \lei \Theta$. That is, if a unifier for $\tau$ and $\upsilon$
% exists, then the algorithm succeeds and delivers a most general unifier.

\item Moreover, if $\theta : \Gamma, \Xi \lei \Theta$ is such that
$\Theta \entails \theta\alpha \equiv \theta\tau$ and
the input conditions are satisfied,
then there is some context $\Delta$ such that
$\algInstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$.
\end{enumerate}
\end{lemma}

\proofsux\begin{proof} It suffices to show that the algorithm succeeds
for every well-formed input in which a solution can exist. As the
algorithm terminates, we proceed by induction on its call graph. Each
step preserves solutions: if the equation in a conclusion can be
solved, so can those in its hypothesis.

The only case the rules omit is the case where an illegal occurrence
of a type variable is rejected. In this case, we are seeking to solve the
problem $\alpha \equiv \tau$ in the context
$\Gamma_0, \decl{\alpha}{D} ~||~ \Xi$ and we have $\alpha \in \FTV{\tau, \Xi}$.
Substituting out the definitions in $\Xi$ from $\tau$, we obtain a type
$\upsilon$ such that $\alpha \in \FTV{\upsilon}$, $\upsilon$ is not a variable
and $\Gamma_0, \decl{\alpha}{D}, \Xi \entails \upsilon \equiv \tau$.
Now the problem $\alpha \equiv \upsilon$ has the same solutions as
$\alpha \equiv \tau$, but by Lemma~\ref{lem:occursCheck}, there are none.
\end{proof}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Specifying type inference\label{sec:spec-tyinf}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We aim to implement type inference for the \hindleymilner\ system, so we need to
introduce type schemes and the term language. We extend the grammar of statements
to express additions to the context (binding statements), well-formed schemes,
type assignment and scheme assignment. The final grammar will be:
\[\begin{array}{r@@{\,}l}
S ::=~ \valid
    &~||~ \tau \type
    ~||~ \tau \equiv \upsilon
    ~||~ S \wedge S \\
    &~||~ \Sbind{\decl{x}{D}}{S}
    ~||~ \sigma \scheme
    ~||~ t : \tau
    ~||~ s \hasscheme \sigma
\end{array}\]

\subsection{Binding statements}

To account for schemes and type assignment, we need a controlled way
to extend the context.
If $S$ is a statement and $\decl{x}{D}$ is a declaration, then we define the
binding statement $\Sbind{\decl{x}{D}}{S}$. We give a generic introduction rule,
but, we make use of neutral elimination only for type variables.
\TODO{Explain that while we ought to mess about with the freshness renaming in
this rule, in practice we will ignore it because it isn't important.}
\[\begin{array}{c}
\Rule{\Gamma \entails \ok_K D    \quad    \Gamma, \decl{y}{D} \entails \subst{y}{x} S}
     {\Gamma \entails \Sbind{\decl{x}{D}}{S}}
\side{y \in \V_K \setminus \V_K(\Gamma)}.
\smallskip\\
\Rule{\entailsN \Sbind{\alpha D}{S}
      \quad
      \entails \subst{\tau}{\alpha}{\sem{\decl{\alpha}{D}}}}
     {\entailsN \subst{\tau}{\alpha}{S}}
\side{D \in \D_\TY}
\end{array}\]
%\TODO{Explain why we only have this for $\TY$: because we have only defined
%substitution for type variables. We could do it in general but we don't need to.}
The corresponding normal rule is admissible. If
$\Gamma \entails \Sbind{\decl{\alpha}{D}}{S}$ by the introduction rule, then
$\Gamma, \decl{\beta}{D} \entails \subst{\beta}{\alpha} S$ where $\beta$ is fresh.
But $\Gamma \entails \subst{\tau}{\alpha}{\sem{\decl{\alpha}{D}}}$ implies
$\Gamma \entails \subst{\tau}{\beta}{\sem{\decl{\beta}{D}}}$ and hence
we can obtain a proof of $\Gamma \entails \subst{\tau}{\alpha} S$ by replacing
every appeal to \name{Lookup} $\beta$ in the proof of 
$\Gamma, \decl{\beta}{D} \entails \subst{\beta}{\alpha} S$
with the proof of
$\Gamma \entails \subst{\tau}{\beta}{\sem{\decl{\beta}{D}}}$.
As a consequence, Lemma~\ref{lem:neutrality} still holds.

\begin{lemma}[Binding preserves stability]\label{lem:stab-pres-bind}
If $\decl{x}{D}$ is a declaration and both $\ok_K D$ and $S$ are stable, then
$\Sbind{\decl{x}{D}}{S}$ is stable.
\end{lemma}
\proofsux\begin{proof}
Suppose $\delta : \Gamma \lei \Delta$, the statement $S$ is stable and
$\Gamma \entails \Sbind{\decl{x}{D}}{S}$.  If the proof is by \name{Neutral}
then the result follows by Lemma~\ref{lem:neutrality}.
Otherwise, $\Gamma \entails \ok_K D$ and
$\Gamma, \decl{y}{D} \entails S$ for fresh $y$.
By stability (structural induction), $\Delta \entails \delta (\ok_K D)$.
% Let $\delta' = \subst{x}{x}{\delta}$, then
Now $\delta : \Gamma, \decl{y}{D} \lei \Delta, \decl{y}{(\delta D)}$
(with $y$ mapped to itself)
so by stability of $S$ we have $\Delta, \decl{y}{(\delta D)} \entails \delta S$.
Hence $\Delta \entails \Sbind{\decl{x}{(\delta D)}}{\delta S}$
and so $\Delta \entails \delta (\Sbind{\decl{x}{D}}{S})$.
\end{proof}

We write $\Sbind{\Xi}{S}$ where $\Xi$ is a list of declarations, defining
$\Sbind{\emptycontext}{S} = S$ and
$\Sbind{(\Xi, \decl{x}{D})}{S} = \Sbind{\Xi}{(\Sbind{\decl{x}{D}}{S})}$.

\TODO{\Sanity s for binding statements?}

\subsection{Type schemes}

To handle let-polymorphism, the context must assign type schemes to term
variables, rather than monomorphic types.
A \define{type scheme} $\sigma$ is a type wrapped in one or more $\forall$
quantifiers or $\letS{\cdot}{\cdot}{\cdot}$ bindings, with the syntax
$$\sigma ::= \gendot{\tau} ~||~ \forall\alpha~\sigma ~||~ \letS{\alpha}{\tau}{\sigma}.$$
We use explicit definitions in type schemes to avoid the need for substitution
in the type inference algorithm. 

Schemes arise by discharging a context suffix (a list of type variable
declarations) over a type, and any scheme can be viewed in this way. We write
$\gen{\Xi}{\tau}$ for the generalisation of the type $\tau$ over the suffix of
type variable declarations $\Xi$, defined by
%\begin{align*}
%\emptycontext         &\genarrow \tau = \gendot{\tau}  \\
%\hole{\alpha}, \Xi    &\genarrow \tau = \forall\alpha~\gen{\Xi}{\tau}  \\
%\alpha \defn \upsilon, \Xi &\genarrow \tau = \letS{\alpha}{\upsilon}{\gen{\Xi}{\tau}}
%\end{align*}
\[
\begin{array}{r@@{\,}l}
\emptycontext         &\genarrow \tau = \gendot{\tau}  \\
\hole{\alpha}, \Xi    &\genarrow \tau = \forall\alpha~\gen{\Xi}{\tau}  \\
\alpha \defn \upsilon, \Xi &\genarrow \tau = \letS{\alpha}{\upsilon}{\gen{\Xi}{\tau}}
\end{array}
\]

The statement $\sigma \scheme$ is then defined by
$$\gen{\Xi}{\tau} \scheme = \Sbind{\Xi}{\tau \type}.$$
The \sanity\  is just $\valid$, as for $\tau \type$.

\subsection{Terms and type assignment}

Now we are in a position to reuse the framework already
introduced, defining a new sort $\TM$, with 
$\V_\TM$ a set of term variables and $x$ ranging over $\V_\TM$.
Term variable declarations $\D_\TM$ are scheme assignments of the form
$\asc \sigma$, with
$\ok_\TM (\asc \sigma) = \sigma \scheme$.

%%%The set of terms has syntax
   Let $s$, $t$, $w$ range over the set of terms with syntax 
$$t ::= x ~||~ t~t ~||~ \lambda x . t ~||~ \letIn{x}{t}{t}$$
%%%and $s$, $t$, $w$ range over terms.

The type assignment statement $t : \tau$ is established by the declarative
rules in Figure~\ref{fig:typeAssignmentRules}. It has two parameters $t$ and
$\tau$ with \sanity s $\valid$ and $\tau \type$ respectively.
We define
$$t \hasscheme \gen{\Xi}{\tau} = \Sbind{\Xi}{t : \tau}$$
and observe this gives the parameters $t$ and $\sigma$ \sanity s
$\valid$ and $\sigma \scheme$ as one might expect.
We can interpret term variable declarations as scheme assignment statements:
$$\sem{x \asc \sigma}_\TM = x \hasscheme \sigma.$$

\begin{figure}[ht]
\[\begin{array}{c}
\mathframe{t : \tau}

\smallskip\\
\Rule{\Sbind{x \asc \gendot{\upsilon}}{t : \tau}}
     {\lambda x.t : \upsilon \arrow \tau}
\qquad
\Rule{f : \upsilon \arrow \tau
      \quad
      a : \upsilon}
     {f a : \tau}

\smallskip\\

\Rule{
      s \hasscheme \sigma
      \quad
      \Sbind{x \asc \sigma}{w : \tau}
     }
     {\letIn{x}{s}{w} : \tau}
\qquad
\Rule{t : \tau
      \quad
      \tau \equiv \upsilon}
     {t : \upsilon}
\end{array}\]
\caption{Declarative rules for type assignment}
\label{fig:typeAssignmentRules}
\end{figure}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Generalising \emph{local} type variables\label{sec:genloc}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%\subsection{Preserving order in the context}

We have previously observed, but not yet exploited, the importance of
declaration order in the context, and that we move declarations left as
little as possible. Thus rightmost entries are those most local to the problem
we are solving. This will be useful when we come to implement type inference
for the |Let| construct, as we want to generalise over \scare{local} type
variables but not \scare{global} variables.

In order to keep track of locality in the context, we need another kind of
context entry: the $\fatsemi$ separator. We add a new validity rule 
$$
\Rule{\Gamma \entails \valid}
     {\Gamma \fatsemi \entails \valid}.
$$

We also refine the $\lei$ relation.
Let $\semidrop$ be the partial function from contexts $\Gamma$ and natural numbers $n$ which truncates $\Gamma$ after $n$
$\fatsemi$ separators, provided $\Gamma$ contains at least $n$ such: 
\[\begin{array}{r@@{\,}l}
\Xi \semidrop 0 &= \Xi  \\
\Xi \fatsemi \Gamma \semidrop 0 &= \Xi  \\
\Xi \fatsemi \Gamma \semidrop n+1 &= \Xi \fatsemi (\Gamma \semidrop n)  \\
\Xi \semidrop n+1 &~\mathrm{undefined}
\end{array}\]

We write $\delta : \Gamma \lei \Delta$ if $\delta$ is a
substitution from $\Gamma$ to $\Delta$ such that, for all 
$\decl{x}{D} \in \Gamma \!\semidrop\! n$, we have that
$\Delta \!\semidrop\! n$ is defined and 
$\Delta \!\semidrop\! n \entails \delta \sem{\decl{x}{D}}$.

This definition of $\Gamma \lei \Delta$ is stronger than the previous one, 
because it requires the $\fatsemi$-separated sections of $\Gamma$ and $\Delta$ 
to correspond in such a way that 
declarations in the first $n$ sections of
$\Gamma$ can be interpreted over the first $n$ sections of $\Delta$.
However, it is fairly straightforward to verify that the previous results 
hold for the new definition.


\subsection{Amending the unification algorithm}

Modifying $\lei$ makes extra work only in the
unification algorithm, because the latter acts structurally on contexts, which may
now contain $\fatsemi$ separators. We extend the algorithmic rules:
\[\begin{array}{c}
\namer{Skip}
\Rule{\algUnify{\Gamma_0}{\alpha}{\beta}{\Delta_0}}
     {\algUnify{\Gamma_0 \fatsemi}{\alpha}{\beta}{\Delta_0 \fatsemi}}
\smallskip\\
\namer{Repossess}
\Rule{\algInstantiate{\Gamma_0}{\alpha}{\tau}{\Xi}{\Delta_0}}
     {\algInstantiate{\Gamma_0 \fatsemi}{\alpha}{\tau}{\Xi}{\Delta_0 \fatsemi}}
\end{array}\]

We must correspondingly update the induction in Lemma~\ref{lem:unifySound} to
show that adding the new rules preserves soundness and generality. For the
\name{Skip} rule, correctness follows immediately from this lemma:

\begin{lemma}
If $\LEIStmt{\Gamma}{S}{\Delta}$ then $\LEIStmt{\Gamma \fatsemi}{S}{\Delta \fatsemi}$.
\end{lemma}
\proofsux\begin{proof}
If $\Gamma \lei \Delta$ then $\Gamma \fatsemi \lei \Delta \fatsemi$ by
definition. If $\Delta \entails S$ then $\Delta \fatsemi \entails S$ since the
\name{Lookup} rule is the only one that extracts information from the context,
and it ignores the $\fatsemi$.

Now let $\theta : \Gamma \fatsemi \lei \Theta \fatsemi \Xi$ be such that
$\Theta \fatsemi \Xi \entails S$. By definition of $\lei$, we must have
$\theta : \Gamma \lei \Theta$, so by minimality there exists
$\zeta : \Delta \lei \Theta$ with $\theta \eqsubst \zeta \compose \iota$.
Then $\zeta : \Delta \fatsemi \lei \Theta \fatsemi \Xi$ and we are done.
\end{proof}

The \name{Repossess} rule is so named because it moves
declarations in $\Xi$ to the left of the $\fatsemi$ separator,
thereby \scare{repossessing} them. Despite such complications, 
unification still yields a most general solution:

\begin{lemma}[Soundness and generality of the \name{Repossess} rule]
Suppose $\algInstantiate{\Gamma \fatsemi}{\alpha}{\tau}{\Xi}{\Delta \fatsemi}$. 
Then $\tyvars{\Gamma \fatsemi \Xi} = \tyvars{\Delta \fatsemi}$ and
$\LEIUnify{\Gamma \fatsemi \Xi}{\alpha}{\tau}{\Delta \fatsemi}$.
\end{lemma}
\proofsux\begin{proof}
We extend the structural induction in lemma~\ref{lem:unifySound} with an extra
case. The only proof of
$\algInstantiate{\Gamma \fatsemi}{\alpha}{\tau}{\Xi}{\Delta \fatsemi}$,
is by \name{Repossess}, so inversion gives
$\algInstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$.
By induction, $\tyvars{\Gamma, \Xi} = \tyvars{\Delta}$ and
$\LEIUnify{\Gamma, \Xi}{\alpha}{\tau}{\Delta}$.

We immediately observe that
$$\tyvars{\Gamma \fatsemi \Xi} = \tyvars{\Gamma, \Xi} = \tyvars{\Delta}
    = \tyvars{\Delta \fatsemi}.$$
Moreover, we have $\Gamma, \Xi \lei \Delta$ so
$\Gamma \fatsemi \Xi \lei \Delta \fatsemi$,
and $\Delta \entails \alpha \equiv \tau$ so
$\Delta \fatsemi \entails \alpha \equiv \tau$.

For minimality, suppose
$\theta : \Gamma \fatsemi \Xi \lei \Theta \fatsemi \Phi$
and $\Theta \fatsemi \Phi \entails \theta\alpha \equiv \theta\tau$.
Observe that  $\alpha \in \tyvars{\Gamma}$ and
$\beta \in \tyvars{\Xi}  \Rightarrow  \beta \in \FTV{\tau, \Xi}$
by the conditions for the algorithmic judgment.
Now $\theta\alpha$ is a $\Theta$-type and $\theta\tau$ is equal to it,
so the only declarations in $\Phi$ that $\theta\tau$ (hereditarily) depends on
must be definitions over $\Theta$. But all the variables declared in $\Xi$ are
used in $\tau$, so there is a substitution
$\psi : \Gamma \fatsemi \Xi \lei \Theta \fatsemi$
that agrees with $\theta$ on $\Gamma$ and maps variables in $\Xi$ to their
definitions in $\Theta$.
Note that $\psi \eqsubst \theta : \Gamma \fatsemi \Xi \lei \Theta \fatsemi \Phi$.
\TODO{Check and improve this explanation.}

% Now we can filter $\Phi$ to give $\Psi$ consisting only of definitions
% such that $\Theta \fatsemi \Psi \entails \theta\alpha \equiv \theta\tau$.
% Let $\psi = \lfloor \Psi \rfloor \compose \theta$, then
% $\psi : \Gamma \fatsemi \Xi \lei \Theta \fatsemi$
% and $\Theta \fatsemi \entails \psi\alpha \equiv \psi\tau$.

Hence $\psi : \Gamma, \Xi \lei \Theta$ and
$\Theta \entails \psi\alpha \equiv \psi\tau$, so by hypothesis there exists
$\zeta : \Delta \lei \Theta$ such that
$\psi \eqsubst \zeta \compose \iota : \Gamma, \Xi \lei \Theta$.
Then $\zeta : \Delta \fatsemi \lei \Theta \fatsemi \Phi$
and
$\psi \eqsubst \zeta \compose \iota :
    \Gamma \fatsemi \Xi \lei \Theta \fatsemi \Phi$,
so
$\theta \eqsubst \zeta \compose \iota :
    \Gamma \fatsemi \Xi \lei \Theta \fatsemi \Phi$.
\end{proof}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Type inference problems and their solutions\label{sec:tyinf}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%\subsection{Inference problems: multiple-mode }

\TODO{Tidy up and improve motivation for definitions in this section.}

Type inference involves making the statement $t : \tau$ hold. However,
a key contrast with unification is that the type should
be an \emph{output} of problem-solving, along with the solution context. We need
a more liberal definition than that of constraint problems.

We associate a \define{mode} with each parameter in a statement: either
\scare{input} or \scare{output}. For simplicity, assume statements always have
one parameter of each mode (which may be trivial or composite).
% An
% \define{inference problem}
% is a triple $(\Gamma, S, Q)$ where $\Gamma$ is a context, $S$ is a statement
% \TODO{(?)} and
% $Q$ is a value for the input parameter that satisfies its \sanity\  in
% $\Gamma$.
% \TODO{Clarify notation for statements and parameter values. What is $Q A$?}
We must extend the apparatus of minimal solutions to problems with outputs.
Let $B$ be a set of values closed under substitution. For a fixed context
$\Gamma$, suppose we have a
preorder on $B$ written $\leParam{\Gamma}{\cdot}{\cdot}$. This induces a
preorder on context-value pairs, with $\delta : \leiParam{\Gamma}{a}{\Delta}{b}$ if
$\delta : \Gamma \lei \Delta$ and $\leParam{\Delta}{\delta a}{b}$.

An \define{$A$-indexed problem family $x.Q$ for $B$} is a family
of input parameters for a statement, indexed by elements of $A$, such that for
all $a, a' \in A$, contexts $\Gamma$ and output parameter values $b \in B$,
$$\leParam{\Gamma}{a}{a'} ~\wedge~ \Gamma \entails Q[a'] b
    \quad\Rightarrow\quad  \Gamma \entails Q[a] b,$$
where we write $Q[a] b$ for the statement with input at index $a$ and output
value $b$. Note that the input parameters for a single statement, and hence
constraint problems, can be regarded as a family indexed by the unit set with
the trivial preorder.

An \define{inference problem} consists of a context $\Gamma$, an $A$-indexed
problem $Q$ and an index $a \in A$ such that the \sanity\  of $Q[a]$
holds in $\Gamma$.

A \define{solution} of $(\Gamma, Q[a])$ consists of an information increase
$\delta : \Gamma \lei \Delta$ and a value for the output parameter $b \in B$
such that $(\delta (Q[a])) b$ and the \sanity\  on $b$ hold in $\Delta$.

If $A$ and $B$ are preordered for fixed $\Gamma$, we can define a preorder on
$A \times B$ given by $\leParam{\Gamma}{(a, b)}{(a', b')}$ if
$\leParam{\Gamma}{a}{a'}$ and $\leParam{\Gamma}{b}{b'}$.

We write $\LEIProb{\Gamma}{P}{\Delta}{a}$ if
$\Gamma \lei \Delta$, $\Delta \entails P a$,
and for all $\theta : \Gamma \lei \Theta$ and $b$ such that
$\Delta \entails (\theta P) b$, we have
$\zeta : \leiParam{\Delta}{a}{\Theta}{b}$ for some $\zeta$ such that
$\theta \eqsubst \zeta \compose \iota$.


\subsection{The Optimist's lemma}

Let $P$ be a problem for $A$ and let $Q$ be an $A$-indexed problem family for
$B$. Then the conjunction of problems
$$(\pconj{P}{x}{Q}) (a, b) = P a \wedge Q[a] b$$
is a problem for $A \times B$. This generalisation of $P \wedge Q$
and allows the output of $P$ to be used in the input of $Q$, so it resembles a
dependent sum type.

This allows us to state the general Optimist's lemma:

\begin{lemma}[The Optimist's lemma for inference problems]
\label{lem:optimistInference}
The following inference rule is admissible:
$$\Rule{\LEIProb{\Gamma}{P}{\Delta}{b}
       \quad  \LEIProb{\Delta}{Q[b]}{\Theta}{c}}
       {\LEIProb{\Gamma}{(\pconj{P}{x}{Q})}{\Theta}{(b, c)}}.$$
\end{lemma}
\proofsux\begin{proof}
We have $\Gamma \lei \Theta$ by Lemma~\ref{lei:preorder}.
Furthermore, $\Theta \entails (\pconj{P}{x}{Q}) (b, c)$ since
stability gives $\Theta \entails P b$, and
$\Theta \entails Q[b] c$ by assumption.

Now suppose there is some other solution
$(\phi : \Gamma \lei \Phi, (b', c'))$, so
$\Phi \entails (\phi P) b'$ and
$\Phi \entails (\phi Q)[b'] c'$.
Since $\LEIProb{\Gamma}{P}{\Delta}{b}$, there exists
$\zeta : \Delta \lei \Phi$
with $\leParam{\Phi}{\zeta b}{b'}$ and $\phi \eqsubst \zeta \compose \iota$.

By definition of an indexed problem family,
$\Phi \entails (\phi Q)[\zeta b] c'$
and hence $\Phi \entails (\zeta (Q[b])) c'$.
But $\LEIProb{\Delta}{Q[b]}{\Theta}{c}$, so there exists
$\xi : \Theta \lei \Phi$ such that $\leParam{\Phi}{\xi c}{c'}$
and $\zeta \eqsubst \xi \compose \iota$.

Hence $\xi : \Theta \lei \Phi$ and $\leParam{\Phi}{\xi (b, c)}{(b', c')}$
so $\xi : \leiParam{\Theta}{(b, c)}{\Phi}{(b', c')}$. Moreover
$\phi \eqsubst \zeta \compose \iota
      \eqsubst (\xi \compose \iota) \compose \iota
      \eqsubst \xi \compose \iota$
so we are done.
\end{proof}



\subsection{The Generalist's lemma}

We have considered problems with abstract inputs and outputs, but
which sets of concrete values do we actually use? Since we want to
solve type inference problems, we are interested in types and
type schemes.

For a fixed context $\Gamma$, we define the preorder on schemes by
$\leParam{\Gamma}{\gen{\Xi}{\tau}}{\gen{\Psi}{\upsilon}}$
if there is some $\psi : \Gamma \fatsemi \Xi \lei \Gamma \fatsemi \Psi$
such that $\Gamma \fatsemi \Psi \entails \psi \tau \equiv \upsilon$
and $\restrict{psi}{\Gamma} \eqsubst \iota$. That is,
$\leParam{\Gamma}{\sigma}{\sigma'}$
if $\sigma$ is a more general type scheme than $\sigma'$.

Since types are just schemes with no quantifiers, we instantiate the above
definition with $\Xi = \emptycontext = \Psi$, to get a preorder on types:
$\leParam{\Gamma}{\tau}{\upsilon}$
if $\Gamma \entails \tau \equiv \upsilon$.

Thus the type inference problem is given by a context $\Gamma$ and a term
parameter $t$ as input to the type assignment statement. Following the
definitions, a solution is an information increase
$\delta : \Gamma \lei \Delta$ and a type $\tau$ such that
$\Delta \entails \tau \type \wedge t : \tau$. A solution with output $\tau$ is
minimal if, given any other solution, we can find a substitution that unifies $\tau$
and the other type: that is, $\tau$ is a principal type.

Note that if $\delta : \Gamma \fatsemi \Gamma' \lei \Delta \fatsemi \Delta'$,
where $\Gamma$ and $\Delta$ contain the same number of $\fatsemi$ separators,
then $\restrict{\delta}{\Gamma} : \Gamma \lei \Delta$.
This allows us to prove the following:

\begin{lemma}[The Generalist's lemma]
\label{lem:generalist}
This rule is admissible:
$$
\Rule{\LEIInfer{\Gamma \fatsemi}{t}{\tau}{\Delta \fatsemi \Xi}}
     {\LEIInferScheme{\Gamma}{t}{\gen{\Xi}{\tau}}{\Delta}}
$$
\end{lemma}
\proofsux\begin{proof}
If $\Gamma \fatsemi \lei \Delta \fatsemi \Xi$ then $\Gamma \lei \Delta$ by
the revised definition of $\lei$. Furthermore,
$\Delta \entails t \hasscheme \gen{\Xi}{\tau}$ is defined to be
$\Delta, \Xi \entails t : \tau$, which holds if
$\Delta \fatsemi \Xi \entails t : \tau$.

For minimality, suppose $\theta : \Gamma \lei \Theta$ is an information increase
and $\gen{\Psi}{\upsilon}$ is a scheme such that
$\Theta \entails t \hasscheme \gen{\Psi}{\upsilon}$.
Then $\Theta, \Psi \entails t : \upsilon$. Now
$\theta : \Gamma \fatsemi \lei \Theta \fatsemi \Psi$
and $\Theta \fatsemi \Psi \entails t : \upsilon$,
so by minimality of the hypothesis there is a substitution
$\zeta : \Delta \fatsemi \Xi \lei \Theta \fatsemi \Psi$ such that
$\theta \equiv \zeta \compose \iota$ and
$\Theta \fatsemi \Psi \entails \zeta\tau \equiv \upsilon$.
Then $\restrict{\zeta}{\Delta} : \Delta \lei \Theta$,
$\theta \eqsubst \restrict{\zeta}{\Delta} \compose \iota : \Gamma \lei \Delta$ and
$\leParam{\Theta}{\theta\gen{\Xi}{\tau}}{\gen{\Psi}{\upsilon}}$.
\end{proof}

\TODO{The proofs of this lemma and the following two are all somewhat dull.
Can we omit and summarise them?}


\subsection{The binding lemmas}

Just as we have a general notion of conjunction problems, so we can regard
binding statements as problems. However, there are two ways in which this makes
sense, depending on the mode of the bound property. Each has a minimality result
corresponding to the Optimist's lemma and Generalist's lemma.

First, if $Q$ is a problem for $A$, then $\Sbind{x \asc \sigma}{Q}$
is also a problem for $A$, with statement
$$(\Sbind{x \asc \sigma}{Q}) a = \Sbind{x \asc \sigma}{Q a}.$$
That is, we regard $\sigma$ as an input.

\begin{lemma}
\label{lem:bindVariableProblem}
If $\Xi$ contains only type variables, then this rule is admissible:
$$\Rule{\LEIProb{\Gamma, x \asc \sigma}{Q}{\Delta, x \asc \sigma, \Xi}{a}}
       {\LEIProb{\Gamma}{(\Sbind{x \asc \sigma}{Q})}{\Delta, \Xi}{a}}$$
\end{lemma}
\proofsux\begin{proof}
If $\Gamma, x \asc \sigma \lei \Delta, x \asc \sigma, \Xi$ then
$\Gamma \lei \Delta, \Xi$ since nothing can depend on $x$.
If $\Delta, x \asc \sigma, \Xi \entails Q a$ then
$\Delta, \Xi, x \asc \sigma \entails Q a$ (permuting the context) and hence
$\Delta, \Xi \entails \Sbind{x \asc \sigma}{Q a}$.

If $\theta : \Gamma \lei \Theta$ is such that
$\Theta \entails \Sbind{x \asc \theta\sigma}{(\theta Q) a'}$ then, by inversion,
$\Theta, x \asc \theta\sigma \entails (\theta Q) a'$.
By minimality of the hypothesis, there is
$\zeta : \Delta, x \asc \sigma, \Xi \lei \Theta, x \asc \theta\sigma$ such that
$\leParam{\Theta, x \asc \theta\sigma}{\theta a}{a'}$ and
$\theta \eqsubst \zeta \compose \iota$.
Now $\zeta : \Delta, \Xi \lei \Theta$ and
$\leParam{\Theta}{\theta a}{a'}$ so we are done.
%%%
\TODO{Should this go after $\leiR$ has been introduced, so we can mention it?
Also, we are relying on the fact that $\leParam{\cdot}{\cdot}{\cdot}$ is defined
without reference to term variables.}
\end{proof}


Alternatively, when binding type variables we can regard $D$ as an output, and
obtain the problem $\Qbind{\beta}{Q}$ with the output being a pair of a type and
a value in $A$. The corresponding statement is
$$(\Qbind{\alpha}{Q}) (\tau, a) = \Sbind{\alpha \defn \tau}{Q a}.$$

\TODO{This rule makes clear we need a new notation for problem inputs/outputs!}

\begin{lemma}
\label{lem:inventVariableProblem}
This rule is admissible:
$$\Rule{\LEIProb{\Gamma, \hole{\beta}}{Q}{\Delta}{a}}
       {\LEIProb{\Gamma}{(\Qbind{\alpha}{Q})}{\Delta}{(\beta, a)}}$$
\end{lemma}
\proofsux\begin{proof}
If $\Gamma, \hole{\beta} \lei \Delta$ then $\Gamma \lei \Delta$ immediately.
If $\Delta \entails Q a$ then clearly
$\Delta, \alpha \defn \beta \entails Q a$ and hence
$\Delta \entails \Sbind{\alpha \defn \beta}{Q a}$.

If $\theta : \Gamma \lei \Theta$ is such that
$\Theta \entails \Sbind{\alpha \defn \tau}{Q a'}$, then
$\Theta, \alpha \defn \tau \entails Q a'$.
By minimality of the hypothesis with the substitution
$\phi = \theta \compose \subst{\beta}{\alpha}
    : \Gamma, \hole{\beta} \lei \Theta, \alpha \defn \tau$,
there is some $\zeta : \Delta \lei \Theta, \alpha \defn \tau$ such that
$\leParam{\Theta, \alpha \defn \tau}{\phi a}{a'}$ and
$\phi \eqsubst \zeta \compose \iota$.
Now $\subst{\alpha}{\tau} \compose \zeta : \Delta \lei \Theta$...
\TODO{finish me!}
\end{proof}



\subsection{Transforming type assignment into type inference}

To transform a rule into an algorithmic form, we proceed clockwise starting from
the conclusion. For each hypothesis, we must ensure that the problem is fully
specified, inserting variables to stand for unknown problem inputs. Moreover, we
cannot pattern match on problem outputs, so we ensure there are schematic
variables in output positions, fixing things up with appeals to unification. 

Figure~\ref{fig:transformedRules} shows the transformed version of the
declarative rule system. The 
%%%rule for $\lambda$-abstractions 
   $\lambda$-rule 
now binds a fresh name for the argument type, which 
%%%we will replace 
   gets replaced 
with an unknown in the algorithm. The rule for application assigns
types to the function and argument separately, then inserts an
equation with a fresh name for the codomain type.

\begin{figure}[ht]
\[\begin{array}{c}
\mathframe{t : \tau}
\smallskip\\
\Rule{\Sbind{\beta \defn \upsilon, x \asc \gendot{\beta}}{\Pinf{t}{\tau}}}
       {\Pinf{\lambda x . t}{\upsilon \arrow \tau}}
\qquad
\Rule{\Pinf{f}{\chi}
        \quad
        \Pinf{a}{\upsilon}
        \quad
        \Sbind{\beta \defn \tau}{\Puni{\chi}{\upsilon \arrow \beta}}
       }
       {\Pinf{f a}{\tau}}

\smallskip\\

\Rule{
      s \hasscheme \sigma
      \quad
      \Sbind{x \asc \sigma}{\Pinf{w}{\tau}}
     }
     {\Pinf{\letIn{x}{s}{w}}{\tau}}
\qquad
\Rule{t : \tau
      \quad
      \tau \equiv \upsilon}
     {t : \upsilon}

\end{array}\]
\caption{Transformed rules for type assignment}
\label{fig:transformedRules}
\end{figure}

We must verify that the rule systems in Figures~\ref{fig:typeAssignmentRules}
and \ref{fig:transformedRules} are equivalent. This is mostly straightforward,
as 
%%%the fresh variable bindings 
   fresh name bindings 
can be substituted out.
The only difficulty is in the application rule, where an equation 
%%%has been
   is 
introduced. If an application has a type in the old system, it can be assigned
the same type in the new system with 
%%%the equation being reflexive. 
   using a reflexive equation. 
Conversely,
if an application has a type in the new system, then using the conversion
with the equation allows the same type to be assigned in the old system.
\TODO{Make this a lemma?}

\TODO{Segue...}

We define 
   the type inference assertion $\algInfer{\Gamma}{t}{\tau}{\Delta}$ 
and 
   the scheme inference assertion $\algInferScheme{\Gamma}{s}{\sigma}{\Delta}$ 
% (inferring the type of $t$ in $\Gamma_0$ yields $\tau$ in the more informative
% context $\Gamma_1$)
by the rules in Figure~\ref{fig:inferRules}.
As they are clearly structural on terms, they 
yield a terminating algorithm, 
%%%leading naturally to an implementation, given in
   and hence the implementation in 
subsection~\ref{sec:inferImplementation}.

%%%\TODO{Say something about freshness of $\Xi$ in \name{Var} rule.}
% We use Lemma~\ref{lem:specialise} to ensure in rule \name{Var} that
% we compute a suffix \(\Xi\) consisting of fresh names, such that the
% output \ensuremath{\Gamma, \Xi} is well-formed.

\begin{figure}[ht]
\[\begin{array}{c}
\mathframe{\algInferScheme{\Gamma}{s}{\sigma}{\Delta}}

\smallskip\\
\namer{Gen}
\Rule{\algInfer{\Gamma \fatsemi}{s}{\upsilon}{\Delta \fatsemi \Xi}}
     {\algInferScheme{\Gamma}{s}{\gen{\Xi}{\upsilon}}{\Delta}}
\bigskip\\ 

\mathframe{\algInfer{\Gamma}{t}{\tau}{\Delta}}

\smallskip\\
\namer{Var}
\Rule{x \asc \gen{\Xi}{\upsilon} \in \Gamma}
     {\algInfer{\Gamma}{x}{\upsilon}{\Gamma, \Xi}}

\smallskip\\

\namer{Abs}
\Rule{\algInfer{\Gamma, \hole{\alpha}, x \asc \gendot{\alpha}}{w}{\upsilon}
          {\Delta_0, x \asc \gendot{\alpha}, \Xi}}
     {\algInfer{\Gamma}{\lambda x.w}{\alpha \arrow \upsilon}{\Delta_0, \Xi}}
\side{\alpha \notin \tyvars{\Gamma}}

\smallskip\\

\namer{App}
\BigRule{\algInfer{\Gamma}{f}{\chi}{\Delta_0}
         \quad
         \algInfer{\Delta_0}{a}{\upsilon}{\Delta_1}}
        {\algUnify{\Delta_1, \hole{\beta}}{\chi}{\upsilon \arrow \beta}{\Delta}}
        {\algInfer{\Gamma}{f a}{\beta}{\Delta}}
\side{\beta \notin \tyvars{\Delta_1}}

\smallskip\\ 

\namer{Let}
\BigRule%%%{\algInfer{\Gamma \fatsemi}{s}{\upsilon}{\Delta_0 \fatsemi \Xi_0}}
        %%%{\algInfer{\Delta_0, x \asc \gen{\Xi_0}{\upsilon}}{w}{\chi}
        %%%       {\Delta_1, x \asc \gen{\Xi_0}{\upsilon}, \Xi_1}}
        %%%{\algInfer{\Gamma}{\letIn{x}{s}{w}}{\chi}{\Delta_1, \Xi_1}}
        {\algInferScheme{\Gamma}{s}{\sigma}{\Delta_0}}
        {\algInfer{\Delta_0, x \asc \sigma}{w}{\chi}
               {\Delta_1, x \asc \sigma, \Xi_1}}
        {\algInfer{\Gamma}{\letIn{x}{s}{w}}{\chi}{\Delta_1, \Xi_1}}

\end{array}\]
\caption{Algorithmic rules for type inference}
\label{fig:inferRules}
\end{figure}


\subsection{Soundness and completeness}

Recall that we defined $\sem{x \asc \sigma}_\TM = x \hasscheme \sigma$, so
$\Gamma \lei \Delta$ requires $\Delta$ to assign a term variable all the types
that $\Gamma$ assigns it, but allows $x$ to become more polymorphic
and acquire new types.  This notion certainly retains stability:
every variable lookup can be simulated in the more general context.
However, it allows arbitrary generalisation of the schemes assigned to term
variables which are incompatible with the known and intended value of
those variables.

As \citet{wells_principal_typings_2002} points out, \hindleymilnershort\ 
type inference is not in this respect compositional. He carefully
distinguishes principal \emph{typings}, given the right to demand more
polymorphism, from Milner's principal \emph{type schemes} and analyses
how the language of types must be extended to express principal
typings.

We, too, note this distinction. We cannot hope to find principal types
with respect to $\lei$, so we capture Milner's compromise by defining
a sub-relation $\leiR$, by $\delta : \Gamma \leiR \Delta$ if $\delta :
\Gamma \lei \Delta$ and $$x \asc \sigma \in \Gamma ~\Rightarrow~ x
\asc \delta\sigma \in \Delta.$$ Thus, if $\Gamma \leiR \Delta$, then
$\Delta$ assigns the \emph{same} type schemes to term variables as $\Gamma$
does (modulo substitution). Since the unification algorithm ignores term
variables, it is easy to see that all the previous results hold if we
replace $\lei$ with $\leiR$ throughout.

Corresponding to $\leiParam{\Gamma}{a}{\Delta}{b}$, we write
$\delta : \leiRParam{\Gamma}{a}{\Delta}{b}$
if $\delta : \Gamma \leiR \Delta$ and $\leParam{\Delta}{\delta a}{b}$.

Corresponding to $\LEIProb{\Gamma}{P}{\Delta}{a}$, we write
$\LEIRProb{\Gamma}{P}{\Delta}{a}$ if $\Gamma \leiR \Delta \entails P a$, and for any
$\theta : \Gamma \leiR \Theta$ such that $\Theta \entails (\theta P) b$ we have
$\zeta : \leiRParam{\Delta}{a}{\Theta}{b}$ for some $\zeta$ such that
$\theta \eqsubst \zeta \compose \iota$.

\TODO{Why do the Optimist's and Generalist's lemmas still hold?}

Since the algorithmic rules correspond directly to the transformed declarative
system in Figure~\ref{fig:transformedRules}, we can easily prove soundness,
completeness and generality of type inference with respect to this system.
Each proof is by induction on 
%%%the structure of 
derivations, observing that each
algorithmic rule maintains the appropriate properties.

\begin{lemma}[Soundness of type inference]
\label{lem:inferSound}
If $P$ is a type or scheme inference problem, and $\alg{\Gamma}{P}{\Delta}{a}$,
then $\Gamma \leiR\Delta$ and $\Delta \entails P a$.
\end{lemma}
\proofsux\begin{proof}
We maintain this property as an invariant in all the rules.
\end{proof}

\begin{lemma}[Generality of type inference]
\label{lem:inferGeneral}
If $P$ is a type or scheme inference problem, and $\alg{\Gamma}{P}{\Delta}{a}$,
then $\LEIRProb{\Gamma}{P}{\Delta}{a}$.
\end{lemma}
\proofsux\begin{proof}
Thanks to soundness (lemma~\ref{lem:inferSound}) it only remains to show that
each algorithmic rule becomes admissible if we replace $\transto$ with $\LEIR$.
\TODO{How to phrase this?}
All the work has been done in proving the previous lemmas.

The Generalist's lemma proves exactly the property required for the \name{Gen}
rule. 
The \name{Abs} rule is minimal by lemmas~\ref{lem:bindVariableProblem} and
\ref{lem:inventVariableProblem}.
The \name{App} rule is minimal by two uses of the Optimist's lemma,
lemma~\ref{lem:inventVariableProblem} and minimality of unification.
The \name{Let} rule is minimal by the Optimist's lemma and
lemma~\ref{lem:bindVariableProblem}.
\TODO{Do \name{Let} rule in detail?}

For the \name{Var} rule, suppose $\theta : \Gamma \leiR \Theta$ and
$\Theta \entails x : \tau$. By inversion, the proof must consist of
\name{Lookup} followed by eliminating
$\Theta \entailsN x \hasscheme \gen{\theta\Xi}{\theta\upsilon}$
with some $\Theta$-types. Hence it determines a map from the unbound type variables
of $\Xi$ to types over $\Theta$, i.e.\ a substitution
$\zeta : \Gamma, \Xi \leiR \Theta$ that agrees with $\theta$ on $\Gamma$ and
maps type variables in $\Xi$ to their definitions in $\Theta$.
\TODO{Better way of saying this?}
\end{proof}

\begin{lemma}[Completeness of type inference]
\label{lem:inferComplete}
If $P$ is a type or scheme inference problem, and
there exist $\theta : \Gamma \leiR \Theta$ and $a'$ such that
$\Theta \entails (\theta P) a'$, then $\alg{\Gamma}{P}{\Delta}{a}$
for some context $\Delta$ and output $a$.
\end{lemma}
\proofsux\begin{proof}
We proceed by induction on the derivation of $\Theta \entails (\theta P) a'$.
For each rule in the transformed declarative system (excluding conversion)
there is a corresponding algorithmic rule, and inversion ensures its
premises are satisfied. \TODO{More?}
\end{proof}


\subsection{Implementation of type inference}
\label{sec:inferImplementation}

\begin{figure*}[p]

\begin{minipage}[t]{0.5\linewidth}

\subfigure[][Type schemes]{\frame{\parbox{\textwidth}{\fixpars\medskip

> data Index a = Z | S a deriving (Functor, Foldable)

> data Schm a  =  Type (Ty a) 
>              |  All (Schm (Index a))
>              |  LetS (Ty a) (Schm (Index a))
>     deriving (Functor, Foldable)

> type Scheme  = Schm TyName

\label{subfig:schemeCode}
}}}

\subfigure[][Specialisation]{\frame{\parbox{\textwidth}{\fixpars\medskip

> specialise :: Scheme -> Contextual Type
> specialise (Type tau) = return tau
> specialise sigma = do
>     let (d, sigma') = unpack sigma
>     beta <- fresh d
>     specialise (fmap (fromS beta) sigma')
>   where
>     unpack :: Scheme -> (TyDecl, Schm (Index TyName))
>     unpack (All sigma')       = (Hole      , sigma')
>     unpack (LetS tau sigma')  = (Some tau  , sigma')
>
>     fromS :: TyName -> Index TyName -> TyName
>     fromS beta  Z             = beta
>     fromS beta  (S alpha)     = alpha

\label{subfig:specialiseCode}
}}}

\subfigure[][Generalisation]{\frame{\parbox{\textwidth}{\fixpars\medskip

> bind :: TyName -> Scheme -> Schm (Index TyName)
> bind alpha = fmap help
>   where
>     help :: TyName -> Index TyName
>     help beta  | alpha == beta  = Z
>                | otherwise      = S beta

> (>=>) :: Suffix -> Type -> Scheme
> F0                               >=> tau = Type tau
> (alpha := Hole          :> _Xi)  >=> tau = All (bind alpha (_Xi >=> tau))
> (alpha := Some upsilon  :> _Xi)  >=> tau = LetS upsilon (bind alpha (_Xi >=> tau))

> generaliseOver ::  Contextual Type -> Contextual Scheme
> generaliseOver mt = do
>     modifyContext (:< LetGoal)
>     tau <- mt
>     _Xi <- skimContext F0
>     return (_Xi >=> tau)
>   where
>     skimContext :: Suffix -> Contextual Suffix
>     skimContext _Xi = do
>         _Gamma :< vD <- getContext
>         putContext _Gamma
>         case vD of
>             LetGoal    -> return _Xi
>             TY alphaD  -> skimContext (alphaD :> _Xi)
>             TM _       -> error "Unexpected TM variable!"

\label{subfig:generaliseCode}
}}}

\end{minipage}
\hspace{\medskipamount}
\begin{minipage}[t]{0.5\linewidth}


\subfigure[][Terms and contexts]{\frame{\parbox{\textwidth}{\fixpars\medskip

> data Tm a  =  X a
>            |  Tm a :$ Tm a 
>            |  Lam a (Tm a)
>            |  Let a (Tm a) (Tm a)
>     deriving (Functor, Foldable)

> type TmName   = String
> type Term     = Tm TmName
>
> data TmEntry  = TmName ::: Scheme
> data Entry    = TY TyEntry | TM TmEntry | LetGoal

> find :: TmName -> Contextual Scheme
> find x = getContext >>= help
>   where
>     help :: Context -> Contextual Scheme
>     help (_Gamma :< TM (y ::: sigma)) | x == y  = return sigma
>     help (_Gamma :< _)                          = help _Gamma
>     help B0                                     = fail "Missing var!"

\label{subfig:termCode}
}}}

\subfigure[][Bringing term variables into scope]{\frame{\parbox{\textwidth}{\fixpars\medskip

> (>-) :: TmEntry -> Contextual a -> Contextual a
> x ::: sigma >- ma = do
>     modifyContext (:< TM (x ::: sigma))
>     a <- ma
>     modifyContext extract
>     return a 
>   where          
>     extract ::  Context -> Context
>     extract (_Gamma :< TM (y ::: _)) | x == y = _Gamma
>     extract (_Gamma :< TY xD) = (extract _Gamma) :< TY xD
>     extract (_Gamma :< _)  = error "Bad context entry!"
>     extract B0             = error "Missing TM variable!"

\label{subfig:termScopeCode}
}}}

\subfigure[][Type inference]{\frame{\parbox{\textwidth}{\fixpars\medskip

> infer :: Term -> Contextual Type
>
> infer (X x) = find x >>= specialise
>
> infer (Lam x w) = do
>     alpha    <- fresh Hole
>     upsilon  <- x ::: Type (V alpha) >- infer w
>     return (V alpha :-> upsilon)
>
> infer (f :$ a) = do
>     chi      <- infer f
>     upsilon  <- infer a
>     beta     <- fresh Hole
>     unify chi (upsilon :-> V beta)
>     return (V beta)
>
> infer (Let x s w) = do
>     sigma <- generaliseOver (infer s)
>     x ::: sigma >- infer w

\label{subfig:inferCode}
}}}

\end{minipage}

\caption{Haskell implementation of type inference}
\label{fig:inferCode}
\end{figure*}

Figure~\ref{fig:inferCode} shows the Haskell implementation of our
type inference algorithm. Note that the monadic |fail| is called if 
scope checking fails, whereas |error| signals violation of one of the
algorithmic invariants.

Figure~\ref{subfig:schemeCode} implements type schemes.
It is convenient to represent bound variables by de Bruijn indices and free
variables (i.e.\ those defined in the context) by names
\citep{mcbride_mckinna_not_number_2004}.
Moreover, we use
Haskell's type system to prevent some incorrect manipulations of indices by
defining the \scare{successor} type
\citep{bird_paterson_nested_1999, bellegarde_hook_substitution_1994} |Index|,
where the outermost bound variable is represented by |Z| and the other variables
are wrapped in the |S| constructor.

Figures~\ref{subfig:specialiseCode} and~\ref{subfig:generaliseCode} implement
specialisation and generalisation of type schemes. The former unpacks a %%%type
scheme with fresh names, while the latter \scare{skims} 
%%%type variables 
   entries 
off the top of the context as far as the |LetGoal| marker.

Figure~\ref{subfig:termCode} implements the data type of terms, and gives the
final definition of |Entry| including type and term variable declarations and
|LetGoal| markers. It implements the |find| function to look up a term variable
in the context and return its scheme.

Figure~\ref{subfig:termScopeCode} implements the |(>-)| operator to evaluate
|Contextual| code in the scope of a term variable, then remove it afterwards.
This is necessary for dealing with $\lambda$-abstractions and let-bindings 
during type inference.

Finally, Figure~\ref{subfig:inferCode} implements the type inference algorithm
itself. It proceeds structurally over the term, adding term variables to the
context and looking them up as appropriate, and calling |unify| when needed
to check applications.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Discussion\label{sec:conc}}  %%% Concussion?
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We have arrived at an implementation of \hindleymilner\ type inference
which involves all the same steps as \AlgorithmW, but not
necessarily in the same order. In particular, the dependency analysis
which \W\ performs all of a sudden in the let-rule is here pushed
down to a requirement that the underlying unification algorithm
maintain the well-foundedness of the context.

Our algorithm is presented as a system of problem transformation
locally preserving all possibile solutions, hence finding a most
general global solution if any at all. Accumulating solutions to
decomposed problems is justified simply by the stability of solutions
with respect to information increase. We have established a discipline
of problem solving which happens to be complete for Hindley-Milner
type inference but in any case maintains a coupling of soundness with
generality.

Maintain context validity, make definitions anywhere and only where
there is no choice, so the solutions you find will be general and
generalisable locally: this is a key design principle for
elaboration of high-level code in systems like Epigram and Agda; bugs
arise from its transgression. By giving a disciplined account of
\scare{current information} in terms of contexts and their information
ordering, we provide a means to investigate these problems and justify
the steps we take to repair them.

We are, however, missing yet more context. Our task was greatly
simplified by studying a structural type inference process for
\scare{finished} expressions in a setting where unification is
complete. Each subproblem is either solved or rejected on first
inspection---there is never a need for a \scare{later, perhaps} outcome. As
a result, the conventional control discipline of \scare{direct style} 
recursive programming is adequate to the task. If problems could get
stuck, how might we abandon them and return to them later? By storing
their \emph{context}, of course!

Here, we have combined the linguistic contexts for the various sorts
of variable involved in problems; our next acquisition is the
syntactic context of the target term, interspersing variable
declarations with components of its
\emph{zipper}~\citep{huet:zipper}. We thus become free to abandon
fixed recursion strategies and refocus wherever progress is to be
made. The tree-like proof states of McBride's thesis evolved into
exactly such \scare{zippers with binding} in the implementation of Epigram.

As we have seen, an information increase is nothing other than the
extension of a simultaneous substitution from variables and terms to
declarations and derivations. Our generic analysis of the role of
declarations in derivations shows that stability is endemic, amounting
to the action of hereditary substitution on \scare{cut-free} derivations.
And that is exactly what it should be. We have rationalised
Hindley-Milner type inference by adapting a discipline for
interactively constructing inhabitants of dependent types as the means
to manage unknowns when incrementally constructing solutions to
problems. The analysis can only become clearer, the technology
simpler, as we bring these two kinds of construction together,
mediating \emph{problems as types}.



\phantomsection
\addcontentsline{toc}{section}{References}
\bibliographystyle{plainnat}
\bibliography{lib-short}



%if showCode

\appendix

\subsection{Lists}

We define our own types of forward (|Fwd|) and backward (|Bwd|) lists,
which are foldable functors and monoids.

> data Fwd a = F0 | a :> Fwd a
>     deriving (Eq, Functor, Foldable, Show)

> data Bwd a = B0 | Bwd a :< a
>     deriving (Eq, Functor, Foldable, Show)

> infixr 8 :>
> infixl 8 :<

> instance Monoid (Fwd a) where
>     mempty = F0
>     F0         `mappend` ys = ys
>     (x :> xs)  `mappend` ys = x :> (xs `mappend` ys)

> (<+>) :: Monoid a => a -> a -> a
> (<+>) = mappend

The fish operator |(<><)| combines a backward and a forward list to
produce a backward list. Similarly, the |(<>>)| operator (chips?)
produces a forward list.

% > (<><) :: Context -> Suffix -> Context
% > infixl 8 <><
% > xs <>< F0 = xs
% > xs <>< (alpha := d :> ys) = (xs :< TY (alpha := d) ) <>< ys

> (<>>) :: Bwd a -> Fwd a -> Fwd a
> infixl 8 <>>
> B0 <>> ys         = ys
> (xs :< x) <>> ys  = xs <>> (x :> ys)


\section{Tests}

The |findType| function looks up a type variable in the context and returns its binding,
or |Nothing| if it is unbound or missing from the context.

> findType :: Context -> TyName -> Maybe Type
> findType B0              _                      = Nothing
> findType (_ :< TY (y := Some tau))  x | x == y  = Just tau
> findType (_ :< TY (y := Hole))      x | x == y  = Nothing
> findType (c :< _)        x                      = findType c x


The |normalise| function returns the normal form (i.e.\ with all type variables expanded as far
as possible) of the given type within the given context. Laziness means that every
variable in the context is normalised at most once and only if necessary.

> normalise :: Context -> Type -> Type
> normalise _Gamma tau = normalStep (normaliseContext B0 (_Gamma <>> F0)) tau
>     where
>         normalStep :: Context -> Type -> Type
>         normalStep c (s :-> t) = (normalStep c s) :-> (normalStep c t)
>         normalStep c (V x) = case findType c x of
>             Just t   -> t
>             Nothing  -> (V x)
>
>         normaliseContext :: Context -> Fwd Entry -> Context
>         normaliseContext c F0 = c
>         normaliseContext c (TY (x := Some t) :> es) = 
>             normaliseContext (c :< TY (x := Some (normalStep c t))) es
>         normaliseContext c (e :> es) = normaliseContext (c :< e) es


|inferType| is a convenience method for inferring the type of a term in the empty context.

> inferType :: Term -> Maybe (Type, (TyName, Context))
> inferType t = runStateT (infer t) (0, B0)


A collection of very simple unit tests follows. These allow the unifier and
type inference algorithm to be tested with

< main

Note that equality of types is syntactic (it does not perform renaming) so
changing the algorithm may sometimes cause spurious failures as the fresh
variable numbers may be different.

> main :: IO ()
> main = unifyTest unifyTests >> inferTest inferTests

> alpha *= d = TY (alpha := d)

> unifyTests :: [(Type, Type, Context, Maybe Context)]
> unifyTests = [
>     (V 0, V 1,
>         B0 :< 0 *= Hole :< 1 *= Hole,
>         Just (B0 :< 0 *= Hole :< 1 *= Some (V 0))),
>     (V 0, V 1 :-> V 2, 
>         B0 :< 0 *= Hole :< 1 *= Hole :< 2 *= Hole,
>         Just (B0 :< 1 *= Hole :< 2 *= Hole :< 0 *= Some (V 1 :-> V 2))),
>     (V 0, V 1 :-> V 2,
>         B0 :< 0 *= Hole :< 2 *= Some (V 0) :< 1 *= Some (V 0),
>         Nothing),
>     (V 0 :-> V 0, V 1 :-> V 1,
>         B0 :< 1 *= Hole :< 0 *= Hole,
>         Just (B0 :< 1 *= Hole :< 0 *= Some (V 1))),
>     (V 0, V 1 :-> V 2,
>        B0 :< 1 *= Hole :< 0 *= Some (V 1 :-> V 1) :< 2 *= Hole,
>        Just (B0 :< 1 *= Hole :< 2 *= Some (V 1) :< 0 *= Some (V 1 :-> V 1))),
>     (V 0 :-> V 1, V 1 :-> V 0,
>        B0 :< 0 *= Hole :< 1 *= Hole,
>        Just (B0 :< 0 *= Hole :< 1 *= Some (V 0))),
>     (V 0 :-> V 1 :-> V 2, V 1 :-> V 0 :-> V 0,
>        B0 :< 2 *= Hole :< 0 *= Hole :< 1 *= Hole,
>        Just (B0 :< 2 *= Hole :< 0 *= Some (V 2) :< 1 *= Some (V 0)))
>     ]

> unifyTest :: [(Type, Type, Context, Maybe Context)] -> IO ()
> unifyTest [] = return ()
> unifyTest ((sigma, tau, c0, mc):xs) =
>     do case runStateT (unify sigma tau) (0, c0) of
>          Just ((), (_, c1)) ->
>              if Just c1 == mc
>              then putStrLn "OKAY" -- ++ (show sigma) ++ " == " ++ (show tau) ++ " in " ++ (show c1))
>              else putStrLn ("\nFAIL: " ++ (show sigma) ++ " == " 
>                                 ++ (show tau) ++ " in " ++ (show c1))
>          Nothing -> 
>              if mc == Nothing
>              then putStrLn "OKAY" -- ++ show sigma ++ " /= " ++ show tau)
>              else putStrLn ("\nFAIL: " ++ show sigma ++ " /= " ++ show tau)
>        unifyTest xs


> inferTests :: [(Term, Maybe Type)]
> inferTests = [
>     (X "u", 
>          Nothing),
>     (Lam "x" (X "x"),
>          Just (V 0 :-> V 0)),
>     (Lam "x" (X "x" :$ X "x"),
>          Nothing),
>     (Lam "x" (Lam "y" (X "y")),
>          Just (V 0 :-> V 1 :-> V 1)),
>     (Lam "x" (Lam "y" (X "x")),
>          Just (V 0 :-> V 1 :-> V 0)),
>     (Lam "x" ((Lam "y" (X "y")) :$ X "x"),
>          Just (V 0 :-> V 0)),
>     (Lam "x" ((Lam "y" (X "x")) :$ X "x"),
>          Just (V 0 :-> V 0)),
>     (Let "m" (Lam "a" (X "a")) (X "m" :$ X "m"),
>          Just (V 2 :-> V 2)),
>     (Let "s" (Let "m" (Lam "a" (X "a")) (X "m" :$ X "m")) (X "s"), 
>          Just (V 4 :-> V 4)),
>     (Lam "x" (Lam "y" (X "x")),
>          Just (V 0 :-> (V 1 :-> V 0))),
>     (Lam "x" (Lam "y" (X "x" :$ X "y")),
>          Just ((V 1 :-> V 2) :-> (V 1 :-> V 2))),
>     (Let "I" (Lam "x" (X "x")) (X "I"),
>          Just (V 1 :-> V 1))
>   ]

> inferTest :: [(Term, Maybe Type)] -> IO ()
> inferTest [] = return ()
> inferTest ((t, expected):tes) =
>     do case inferType t of
>          Just (tau, (_, c)) ->
>              let tau' = normalise c tau
>              in
>                  if Just tau' == expected
>                  then putStrLn "OKAY" -- ++ (show t) ++ " : " ++ (show tau') ++ " in " ++ (show c))
>                  else putStrLn ("\nFAIL: " ++ (show t) ++ " : " 
>                                 ++ (show tau') ++ " /= " ++ (show expected)
>                                 ++ " in " ++ (show c))
>          Nothing -> 
>              if expected == Nothing
>              then putStrLn "OKAY" -- ++ (show t) ++ " does not type")
>              else putStrLn ("\nFAIL: " ++ (show t) ++ " should type to " ++ (show expected))
>        inferTest tes


We need some |Eq| and |Show| instances for testing purposes:

> deriving instance Eq a => Eq (Ty a)
> deriving instance Show a => Show (Ty a)
> deriving instance Eq Entry
> deriving instance Show Entry
> deriving instance Show Term
> deriving instance Eq a => Eq (Schm a)
> deriving instance Show a => Show (Schm a)
> deriving instance Eq a => Eq (Index a)
> deriving instance Show a => Show (Index a)

> deriving instance Eq TyDecl
> deriving instance Show TyDecl

> deriving instance Eq TyEntry
> deriving instance Show TyEntry
> deriving instance Eq TmEntry
> deriving instance Show TmEntry

%endif



\end{document}
