\documentclass[authoryear]{sigplanconf}

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
\newcommand{\NotForPublication}[1]{#1}

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

% Definitions
\newcommand{\defmap}{~\mapsto~}
\newcommand{\centcolon}{\mathrel{\mathop:}}
\newcommand{\defsyn}{\centcolon\centcolon=}

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
\newcommand{\defn}{\ensuremath{\!\centcolon=\!}}
\newcommand{\asc}{\ensuremath{\!::\!}}
\newcommand{\hole}[1]{\ensuremath{#1 \!\centcolon= ?}}
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
\newcommand{\letIn}[3]{\ensuremath{\mathrm{let}\; #1 \!\centcolon=\! #2 \;\mathrm{in}\; #3}}
\newcommand{\letS}[3]{\ensuremath{(!#1 \!\centcolon=\! #2 ~\mathrm{in}~ #3)}}
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

\newcommand{\iRel}[4]{#1 #3 #4 \entails #2}
\newcommand{\ioRel}[5]{#1 \circ #2 #3 #4 \bullet #5}

\newcommand{\leiStmt}[3]{\iRel{#1}{#2}{\lei}{#3}}
\newcommand{\leiRStmt}[3]{\iRel{#1}{#2}{\leiR}{#3}}
\newcommand{\LEIStmt}[3]{\iRel{#1}{#2}{\LEI}{#3}}
\newcommand{\LEIRStmt}[3]{\iRel{#1}{#2}{\LEIR}{#3}}
\newcommand{\leiRParam}[4]{(#1, #2) \leiR (#3, #4)}
\newcommand{\LEIProb}[4]{\ioRel{#1}{#2}{\LEI}{#3}{#4}}
\newcommand{\LEIRProb}[4]{\ioRel{#1}{#2}{\LEIR}{#3}{#4}}
\newcommand{\LEIUnify}[4]{\leiStmt{#1}{#2 \equiv #3}{#4}}
\newcommand{\LEIRUnify}[4]{\leiRStmt{#1}{#2 \equiv #3}{#4}}
\newcommand{\LEIInfer}[4]{\LEIProb{#1}{(#2 :)}{#4}{#3}}
\newcommand{\LEIRInfer}[4]{\LEIRProb{#1}{(#2 :)}{#4}{#3}}
\newcommand{\LEIInferScheme}[4]{\LEIProb{#1}{(#2 \hasscheme)}{#4}{#3}}
\newcommand{\LEIRInferScheme}[4]{\LEIRProb{#1}{(#2 \hasscheme)}{#4}{#3}}

\newcommand{\alg}[4]{\ioRel{#1}{#2}{\transto}{#3}{#4}}
\newcommand{\ialg}[3]{\iRel{#1}{#2}{\transto}{#3}}
\newcommand{\algUnify}[4]{\ialg{#1}{#2 \equiv #3}{#4}}
\newcommand{\algInstantiate}[5]{\ialg{#1 ~||~ #4}{#2 \equiv #3}{#5}}
\newcommand{\algInfer}[4]{\alg{#1}{(#2 :)}{#4}{#3}}
\newcommand{\algInferScheme}[4]{\alg{#1}{(#2 \hasscheme)}{#4}{#3}}

% Problem bits
\newcommand{\iprobcond}[2]{#1\! [#2]}
\newcommand{\iprobstmt}[3]{#1\! [#2]\, #3}
\newcommand{\iprobsubst}[4]{(#1 (#2\! [#3]))\, #4}
\newcommand{\probstmt}[2]{#1 #2}
\newcommand{\probsubst}[3]{(#1 #2) #3}

\newcommand{\leParam}[4]{#2 \entails #3 \subset_{#1} #4}
\newcommand{\pconj}[3]{\Sigma #1 #3}
\newcommand{\Qbind}[2]{#1 ~ \Yright #2}



\usepackage{amsthm}
\usepackage{amsmath}
\usepackage{enumerate}
\usepackage{eucal}
\usepackage{natbib}
\usepackage[T1]{fontenc}
\usepackage{subfigure}

\newcommand{\url}[1]{{\tt #1}}

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

\conferenceinfo{MSFP'10,} {September 26, 2010, Baltimore, Maryland, USA.}
\CopyrightYear{2010}
\copyrightdata{978-1-4503-0251-7/10/09}

\titlebanner{\NotForPublication{REVISED DRAFT}}

\title{Type Inference in Context}
\authorinfo{Adam Gundry\thanks{
                 Supported by the Microsoft Research PhD Scholarship Programme.} 
            \and Conor McBride}
           {University of Strathclyde, Glasgow}
           {\{adam.gundry,conor.mcbride\}@@cis.strath.ac.uk}
\authorinfo{James McKinna\thanks{
                  Supported by the NWO cluster `\textsc{Diamant}'. }}
           {Radboud University, Nijmegen}
           {james.mckinna@@cs.ru.nl}

\maketitle

\begin{abstract}

We consider the problems of first-order unification and type inference
from a general perspective on problem-solving, namely that of
information increase in the problem context.  This leads to a powerful
technique for implementing type inference algorithms.  We describe a
unification algorithm and illustrate the technique for the familiar
Hindley-Milner type system, but it can be applied to more advanced
type systems.  The algorithms depend on \emph{well-founded} contexts:
type variable bindings and type-schemes for terms may depend only on
earlier bindings.  We ensure that unification yields a most general
unifier, and that type inference yields principal types, by advancing
definitions earlier in the context only when necessary.

\end{abstract}

\category{F.3.3}{Logics and Meanings of Programs}{Studies of Program Constructs}[Type structure]

\terms
Algorithms, Theory

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction\label{sec:intro}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\AlgorithmW\ is a well-known type inference algorithm for the \hindleymilner\
(\hindleymilnershort)
system \citep{milner_theory_1978, damas_principal_1982}, based on
\citeauthor{robinson_machine-oriented_1965}'s Unification Algorithm
\citeyearpar{robinson_machine-oriented_1965}. The system consists of
simply-typed $\lambda$-calculus with \scare{let-expressions} for polymorphic
definitions.
For example,
$$\letIn{i}{\lambda x . x}{i\:i}$$
is well-typed: $i$ is given a polymorphic type, which is instantiated in two
different ways. The syntax of types is
$$\tau \defsyn \alpha ~||~ \tau \arrow \tau.$$
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
   As 
a first step towards a longer-term goal:
   explaining how to elaborate 
high-level \emph{dependently typed} programs into fully explicit calculi. 
Just as \W\ specialises polymorphic type schemes, 
elaboration involves inferring \emph{implicit arguments} by solving constraints, but
with fewer algorithmic guarantees. Pragmatically, 
   we need to account for
stepwise progress in problem solving from states of partial knowledge.
We 
   seek  
local correctness criteria for type inference 
   that guarantee 
global correctness.


In contrast to other presentations of unification and \hindleymilnershort\ type
inference, our algorithm is based on contexts carrying variable definitions as
well as declarations. This avoids the need to represent substitutions explicitly.
(We use them to reason about the system.)

This paper has been a long time brewing. 
   Its origins lie in a constraint
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
   Agda implementation~\citeyearpar{norell:agda}.
It is high time we began to explain how it works and perhaps to understand it.

We are grateful to an anonymous referee for pointing out the work of
\citet{dunfield_polymorphism_2009} on polymorphism in a bidirectional type system.
Dunfield uses well-founded contexts that contain existential type variables
(amongst other things). These variables can be solved, and there is an informal
notion of information increase between input and output contexts.
However, our concerns are different: whilst Dunfield elaborates a
particular approach to bidirectional polymorphic checking to a larger
class of type theories, here we pursue a methodological understanding
of the problem-solving strategy in \hindleymilner\ type inference.

This paper is literate Haskell, with full source code available at
\footnotesize\url{http://personal.cis.strath.ac.uk/{\(\sim\)}adam/type-inference/}\normalsize.

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
\end{cases}.
$$
The context \(A\) is an unordered set of type scheme 
   bindings, 
with \(A_x\) denoting 
   `\(A\) minus any \(x\) binding ': such 
contexts
   do not
reflect lexical scope, so shadowing requires deletion and reinsertion.

The `let' rule is the only real complexity in \AlgorithmW,
and as \citet{milner_theory_1978} wrote, ``the
reader may still feel that our rules are arbitrarily chosen and only partly
supported by intuition.'' The rules are well-chosen
indeed; perhaps we can recover the intuition.

In both cases, the occurs check is used to detect dependencies between variables.
Type variables are traditionally left floating in space and given meaning by
substitution, but by exposing structure we can manage definitions and
dependencies as we go. Recording type variables in the context is natural when
dealing with dependent types, as there is no distinction between type and term
variables, but it also works well in the simply-typed setting.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Unification over a context\label{sec:unif}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We begin
by revisiting unification for
type expressions containing free variables. Let us equip ourselves to
address the problem---solving equations---by explaining which types
are considered equal, raising the question of which things a given
context admits as types, and 
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
of type variables, each of which may be declared 
\define{unknown} (written $\hole{\alpha}$) or
\define{defined} (written $\alpha \defn \tau$). 
A context is \define{valid} if the type \(\tau\) in
every definition makes sense in its preceding context.
For example, the context
$\hole{\alpha}, \hole{\beta}, \gamma \defn \alpha \arrow \beta$
is valid, while 
$\alpha \defn \beta, \hole{\beta}$
is not, because $\beta$ is not in scope for the definition of $\alpha$.
This topological sorting of the dependency graph means that 
entries on the right are harder to depend on, and correspondingly easier to
generalise, just by discharging them as hypotheses in the usual way.

Definitions in the context induce a nontrivial equational theory on types,
starting with $\alpha \equiv \tau$ for every definition $\alpha \defn \tau$ in
the context, then taking the congruence closure.
Unification is the problem of making variable definitions (thus increasing
information) 
   in order to make an equation hold. 
The idea is to decompose constraints on the syntactic structure of types
until we reach variables, then move through the context and update it to solve
the equation. 

For example, we might start in context
$\hole{\alpha}, \hole{\beta}, \gamma \defn \alpha \arrow \beta$
aiming to solve the equation $\beta \arrow \alpha \equiv \gamma$.
It suffices to define $\beta \defn \alpha$, giving as final judgment
$\hole{\alpha}, \beta \defn \alpha, \gamma \defn \alpha \arrow \beta
    \entails \beta \arrow \alpha \equiv \gamma.$

A context represents a substitution in `triangular form'~\cite{DBLP:books/el/RV01/BaaderS01}, 
which can be applied on demand.
As we proceed with the development,
the context structure will evolve to hold a variety of information
about variables of all sorts and some control markers, managing the
generalisation process.

\subsection{Implementation of unification}

\begin{figure*}[p]

\begin{minipage}[b]{0.5\linewidth}

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

\subfigure[][Contexts and suffixes]{\frame{\parbox{\textwidth}{\fixpars\medskip

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

\vspace{6pt}
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
\begin{minipage}[b]{0.5\linewidth}

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
   \AlgorithmW\ has been formally verified 
in Isabelle/HOL by \citet{NaraschewskiN-JAR}, using a counter for fresh 
   name 
generation and a monad to propagate failure; 
we use similar techniques here.

Figure~\ref{subfig:typeCode} implements types as a functor
parameterised by a type of variable names;  
   for simplicity, we use integers.
We compute free type variables using the typeclass |FTV| with membership
function |(<?)|. 
The typeclass instances are derived
using |Foldable|, 
thanks to a language
extension in GHC 6.12 \citep{ghc_team_glorious_2009}. 

Figure~\ref{subfig:contextCode} defines context entries, contexts and suffixes.
The types |Bwd| and |Fwd|, whose definitions are omitted, are backwards and forwards lists
with |B0| for 
   the empty list 
and |:<| and |:>| for snoc and cons respectively.
Lists are monoids under concatenation |(<+>)|; the \scare{fish}
operator |(<><)| appends a suffix to a context. We
later extend |Entry| to
handle term variables, so this definition is incomplete.

Figure~\ref{subfig:monadCode} defines the |Contextual| monad of computations which mutate
the context or fail. The |TyName| component is the next fresh 
   name 
to use; it is an implementation detail not mentioned in the typing
rules. The |fresh| function generates a 
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
of variables, it examines the context, using 
   |onTop| 
to pick out
a variable declaration to consider. Depending on the variables, it 
then either succeeds, restoring the old entry or replacing it with a new one, 
or continues 
with an updated constraint.

The |solve| function is called 
   to unify a variable 
with a non-variable type. 
It works similarly to 
   |unify| on variables, 
but must accumulate a list of
the type's dependencies and push them left through the context. It also performs
the occurs check and 
   calls the monadic |fail| 
if an illegal occurrence
(leading to an infinite type) is detected.

As an example, consider the behaviour of the algorithm when |unify| is called
to solve $\alpha \arrow \beta \equiv \alpha' \arrow (\gamma \arrow \gamma)$:
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
     \grot{ \hole{\gamma} \mid \beta\equiv\gamma\arrow\gamma} &
     \alpha' \defn \beta \\
 &
  \hole{\alpha},&
     \grot{\hole{\gamma} \mid \alpha\equiv\gamma\arrow\gamma}, &
     \beta\defn\alpha,& \alpha' \defn \beta
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

   Given this 
implementation of unification, let us try to understand it.
We would like 
a general picture of \scare{statements-in-context} that
allows us to view unification and type inference in a uniform setting.
What is the common structure?

A \define{context} is a list of \define{declarations} assigning
\define{properties} to
   names (in particular, those of type variables). 
We let $\Gamma, \Delta, \Theta$ range over contexts.
The empty context is written $\emptycontext$. 
Let $\V_\TY$ be a set of type
variables and $\D_\TY$ the properties 
   assignable to them: 
the 
   \scare{unknown} 
property $\,\hole{}$ and 
   \scare{defined}
properties $\,\defn{\tau}$, one for each type $\tau$.

Later we 
introduce corresponding definitions for term variables. Where
needed we let $K \in \{ \TY, \TM \}$ represent an arbitrary sort of variable.
We write $\decl{x}{D}$ for an arbitrary property, with $x \in \V_K$ and
$D \in \D_K$. The set of variables of $\Gamma$ with sort $K$ is written
$\V_K(\Gamma)$.

We will build a set $\Ss$ of \define{statements}, assertions that can be judged
in contexts. For now, the grammar of statements will be
$$S \defsyn~ \valid
    ~||~ \tau \type
    ~||~ \tau \equiv \upsilon
    ~||~ S \wedge S,$$
meaning (respectively) that the context is valid, $\tau$ is a type, the types
$\tau$ and $\upsilon$ are equivalent, and both conjuncts hold.

A statement has zero or more
\define{parameters}, each of which has an associated \define{\sanity}, 
i.e.\ a statement whose truth is presupposed for the original statement to make sense.
The $\valid$ statement has no parameter and hence no \sanity s.
In $\tau \type$, the parameter $\tau$ has \sanity\  $\valid$.
The type equivalence statement $\tau \equiv \upsilon$ has two 
   parameters, with \sanity s 
$\tau \type$ and $\upsilon \type$ respectively.
Finally, $S \wedge S'$ has parameters (and \sanity s) taken from $S$ and
$S'$.

Each declaration in the context causes some statement to hold.
We maintain a map $\sem{\cdot}_K : \V_K \times \D_K \rightarrow \Ss$
from declarations to statements. (Typically we will omit the subscript $K$.)
The idea is that $\sem{\decl{x}{D}}$ is the statement that holds by virtue of the
declaration $\decl{x}{D}$ in the context. For type variables, we define
\[\begin{array}{r@@{\,}l}
\sem{\hole{\alpha}} &\defmap \alpha \type \\ 
\sem{\alpha \defn \tau} &\defmap \alpha \type \wedge \alpha \equiv \tau.
\end{array}\]

We can inspect the context in derivations using the inference rule
$$\namer{Lookup}
  \Rule{\decl{x}{D} \in \Gamma}
       {\Gamma \entailsN \sem{\decl{x}{D}}}.$$
Note the different turnstile 
in the conclusion of this rule.
We write the \define{normal judgment} $\Gamma \entails S$
to mean that the declarations in $\Gamma$ support the statement 
   \(S\). 
We write the \define{neutral judgment} $\Gamma \entailsN S$ to
mean that $S$ follows directly from 
a fact in $\Gamma$.
Neutral judgments capture exactly the valid appeals to declarations
in the context, just as \scare{neutral terms} in $\lambda$-calculus are
   applied variables, the \scare{atoms} of terms. 
   Such appeals to 
the context are the atoms of derivations.

The \name{Lookup} rule is our only means to extract information from the
context, so we omit contextual plumbing (almost) everywhere else.
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
   For types: 
\[\begin{array}{r@@{\,}l}
\ok_\TY (\,\hole{}) &\defmap \valid \\
\ok_\TY (\,\defn{\tau}) &\defmap \tau \type
\end{array}\]

Henceforth we
assume that all contexts treated are valid,
and ensure we only construct valid ones. We typically ignore 
   freshness issues, 
as our simple counter implementation suffices for most
purposes.

\subsection{Rules for establishing statements}

Figure~\ref{fig:statementRules} gives rules for establishing statements other than
$\valid$.
We deduce that variables are types by 
   lookup in 
the context, but we need
a structural rule for the $\arrow$ type constructor.

\begin{figure}[ht]
\[\begin{array}{c}
\mathframe{\tau \type}\qquad\mathframe{\tau \equiv \upsilon}\qquad\mathframe{S \wedge S'}
\smallskip\\
\Rule{\tau \type   \quad   \upsilon \type}
     {\tau \arrow \upsilon \type}
\qquad
\Rule{\tau \type}
     {\tau \equiv \tau}
\quad
\Rule{\upsilon \equiv \tau}
     {\tau \equiv \upsilon}
\quad
\Rule{\tau_0 \equiv \tau_1
      \quad
      \tau_1 \equiv \tau_2}
     {\tau_0 \equiv \tau_2}
\\
\Rule{\tau_0 \equiv \upsilon_0
      \quad
      \tau_1 \equiv \upsilon_1}
     {\tau_0 \arrow \tau_1 \equiv \upsilon_0 \arrow \upsilon_1}
\qquad
\Rule{S \quad S'} {S \wedge S'}
  \quad
  \Rule{\entailsN S \wedge S'}
       {\entailsN S}
  \quad
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

The transition from $\hole{\alpha}$ to $\alpha \defn \tau$ intuitively cannot
falsify any existing equations.
More generally, if we rely on the context to tell us what we may
deduce about variables, then making contexts more informative must preserve
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
   The substitution $\subst{\tau}{\alpha}{}$ maps 
$\alpha$ to $\tau$ and 
   otherwise acts as \(\iota\). 

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
   $\iota : \Gamma \lei \Delta$.
If $\delta : \Gamma, \Gamma' \lei \Theta$ we write $\restrict{\delta}{\Gamma}$
for the restriction of $\delta$ to 
   \(\V_\TY(\Gamma)\). 

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


\subsection{Stable statements}

A statement $S$ is \define{stable} if information
increase preserves it, i.e., if
$$\Gamma \entails S  \quad \mathrm{and}  \quad  \delta : \Gamma \lei \Delta
    \quad \Rightarrow \quad  \Delta \entails \delta S.$$
That is, we can extend a simultaneous substitution on syntax to 
   one on derivations.
Since we only consider valid contexts, the statement $\valid$ always holds,
is invariant under substitution, hence is stable.

We observe that neutral derivations always ensure stability:
\begin{lemma}\label{lem:neutrality}
If $\Gamma \entailsN S$ and $\delta : \Gamma \lei \Delta$ then
$\Delta \entails \delta S$.
\end{lemma}
\proofsux\begin{proof}
By 
   induction on derivations. In the case of \name{Lookup}, it 
holds by definition of information increase. Otherwise, the proof is
by a neutral elimination rule, so the result follows by induction, and
admissibility of the corresponding normal elimination rule.
\end{proof}

We have a standard way, effective by construction,  
to prove stability of most 
   statements: we proceed by induction on
   derivations. In the \name{Neutral} case, 
stability holds by 
Lemma~\ref{lem:neutrality}. Otherwise, we check the non-recursive hypotheses
are stable and that recursive hypotheses occur in strictly positive positions,
   so are stable by induction. In this way we see that 
$\tau \type$ and $\tau \equiv \upsilon$ are stable.

\begin{lemma}[Conjunction preserves stability]\label{lem:stab-pres-conj}
If $S$ and $S'$ are stable then $S \wedge S'$ is stable.
\end{lemma}
\proofsux\begin{proof}
Suppose $S, S'$ are stable,  $\Gamma \entails S \wedge S'$, 
and $\delta \!:\! \Gamma \lei \Delta$. In the \name{Neutral} case, 
$\Delta \entails \delta (S \wedge S')$ by Lemma~\ref{lem:neutrality}.
Otherwise $\Gamma \entails S$ and $\Gamma \entails S'$. 
By stability, $\Delta \entails \delta S$ and $\Delta \entails \delta S'$,   
so $\Delta \entails \delta (S \wedge S')$.
\end{proof}
We shall exploit the preorder structure of $\lei$, induced by stability.
\begin{lemma}\label{lei:preorder}
If $\sem{\decl{x}{D}}$ is stable for every declaration $\decl{x}{D}$, then
the $\lei$ relation is a preorder, with reflexivity witnessed by
the identity substitution $\iota : \Gamma \lei \Gamma$, and transitivity by
composition:
$$\delta : \Gamma \lei \Delta  ~~\text{and}~~  \theta : \Delta \lei \Theta
  \quad \Rightarrow \quad  \theta \compose \delta : \Gamma \lei \Theta.$$
\end{lemma}
\proofsux\begin{proof}
Reflexivity follows immediately by applying the \name{Lookup} and
\name{Neutral} rules.
For transitivity, suppose that $\decl{x}{D} \in \Gamma$,
then $\Delta \entails \delta \sem{\decl{x}{D}}$ since
$\delta : \Gamma \lei \Delta$.
Now by stability applied to $\delta \sem{\decl{x}{D}}$ using $\theta$, we have
$\Theta \entails \theta\delta \sem{\decl{x}{D}}$ as required.
\end{proof}


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
   stipulates that 
$\Gamma \entails \tau \type \wedge \upsilon \type$, and 
   a solution to the problem (a \define{unifier}) is given by 
$\delta : \Gamma \lei \Delta$ such that
$\Delta \entails \delta \tau \equiv \delta \upsilon$.

We are interested in algorithms to solve problems, preferably in as
general a way as possible (that is, by making the smallest information increase
necessary to find a solution). 
   For the unification problem, this 
corresponds to finding a most general
unifier. We say
the solution $\delta : \Gamma \lei \Delta$ is \define{minimal} if, for
any other solution $\theta: \Gamma \lei \Theta$, there exists a
substitution $\zeta : \Delta \lei \Theta$ such that
$\theta \eqsubst \zeta \compose \delta$ (we say $\theta$ \emph{factors through}
$\delta$ with \emph{cofactor} $\zeta$).

Variables can become more informative either by definition or by substitution.
Our algorithms exploit only the former, always choosing solutions of the form
$\iota : \Gamma \lei \Delta$, but we show these minimal with respect to
arbitrary information increase. Correspondingly,
we write $\LEIStmt{\Gamma}{P}{\Delta}$ to mean that $(\Gamma, P)$ is a
problem with minimal solution $\iota : \Gamma \lei \Delta$.

Unsurprisingly, stability permits \emph{sound} sequential problem solving:
$$\Rule{\iota:\leiStmt{\Gamma}{P}{\Delta}
       \quad  \iota:\leiStmt{\Delta}{Q}{\Theta}}
       {\iota:\leiStmt{\Gamma}{P \wedge Q}{\Theta}}.$$
If $\Delta$ solves $P$ then any more
informative context $\Theta$ also solves $P$. More surprisingly, composite
problems acquire \emph{minimal} solutions similarly,
allowing a \scare{greedy}  strategy.
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

The rules in Figure~\ref{fig:unifyRules} define our unification algorithm. 
The 
   \define{unify} 
judgment $\algUnify{\Gamma}{\tau}{\upsilon}{\Delta}$ means that given inputs
$\Gamma$, $\tau$ and $\upsilon$, 
   satisfying the input \sanity\ 
$\Gamma \entails \tau \type \wedge \upsilon \type$, 
unification succeeds, yielding output context $\Delta$. 

\newpage
The 
   \define{solve} 
judgment $\algInstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$
means that given inputs $\Gamma$, $\Xi$, $\alpha$ and $\tau$,
solving $\alpha$ with $\tau$ succeeds,  
yielding output context $\Delta$. The idea is that the bar $(||)$ represents
   progress in examining context elements in order, 
   and $\Xi$ contains exactly those declarations on which $\tau$ depends.  
Formally, the inputs 
must satisfy \((\dag)\):

\hspace*{0.1in}$\alpha \in \tyvars{\Gamma}$, ~
$\tau$ is not a variable, \\ {}
\hspace*{0.1in}$\Gamma, \Xi \entails \tau \type$, ~ 
$\Xi$ contains only type variable declarations \\ {}
\hspace*{0.1in}$\beta \in \tyvars{\Xi} \Rightarrow \beta \in \FTV{\tau, \Xi}$.

The set \(\FTV{\tau}\) records those variables occurring free in type \(\tau\); the notation extends to (sub-)contexts \(\FTV\Xi\) and composite objects \FTV{\tau, \Xi} in the obvious way. 
Some context entries have no bearing on the problem at hand.
We write $x \!\perp\! X$ ($x$ is orthogonal to set $X$ of type variables)
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
\Axiom{\algUnify{\Gamma, \alpha D}{\alpha}{\alpha}{\Gamma, \alpha D}}

\smallskip\\ 

\namer{Define}
\Axiom{\algUnify{\Gamma, \hole{\alpha}}{\alpha}{\beta}{\Gamma, \alpha \defn \beta}}
\side{\alpha \neq \beta}

\smallskip\\ 

\namer{Ignore}
\Rule{\algUnify{\Gamma}{\alpha}{\beta}{\Delta}}
     {\algUnify{\Gamma, \decl{x}{D}}{\alpha}{\beta}{\Delta, \decl{x}{D}}}
\side{x \perp \{\alpha, \beta\} }

\smallskip\\ 

\namer{Expand}
\Rule{\algUnify{\Gamma}{\tau}{\beta}{\Delta}}
     {\algUnify{\Gamma, \alpha \defn \tau}{\alpha}{\beta}{\Delta, \alpha \defn \tau}}
\side{\alpha \neq \beta}

\smallskip\\ 

\namer{Solve}
\Rule{\algInstantiate{\Gamma}{\alpha}{\tau}{\emptycontext}{\Delta}}
     {\algUnify{\Gamma}{\alpha}{\tau}{\Delta}}
\side{\tau \mathrm{~not~variable}}

\bigskip\\

\mathframe{\algInstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}}

\smallskip\\
\namer{DefineS}
\Axiom{\algInstantiate{\Gamma, \hole{\alpha}}{\alpha}{\tau}{\Xi}
                   {\Gamma, \Xi, \alpha \defn \tau}}
\side{\alpha \notin \FTV{\tau, \Xi}}

\smallskip\\ 

\namer{IgnoreS}
\Rule{\algInstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}}
     {\algInstantiate{\Gamma, \decl{x}{D}}{\alpha}{\tau}{\Xi}{\Delta, \decl{x}{D}}}
\side{x \perp \FTV{\alpha, \tau, \Xi}}

\smallskip\\

\namer{ExpandS}
\Rule{\algUnify{\Gamma, \Xi}{\upsilon}{\tau}{\Delta}}
     {\algInstantiate{\Gamma, \alpha \defn \upsilon}{\alpha}{\tau}{\Xi}
                   {\Delta, \alpha \defn \upsilon}}
\side{\alpha \notin \FTV{\tau, \Xi}}

\smallskip\\

\namer{DependS}
\Rule{\algInstantiate{\Gamma}{\alpha}{\tau}{\beta D, \Xi}{\Delta}}
     {\algInstantiate{\Gamma, \beta D}{\alpha}{\tau}{\Xi}{\Delta}}
\side{\alpha \neq \beta, \beta \in \FTV{\tau, \Xi}}

\end{array}\]
\caption{Algorithmic rules for unification}
\label{fig:unifyRules}
\end{figure}

Observe that no rule applies in the case \((\ddag)\) 
$$\algInstantiate{\Gamma, \alpha D}{\alpha}{\tau}{\Xi}{\Delta}
\mathrm{~with~} \alpha \in \FTV{\tau, \Xi},$$
   where the algorithm fails. 
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
left of the bar, shortens the overall
context, or preserves the context and decomposes
types~\citep{mcbride:unification}. We are correspondingly entitled to
reason about the total correctness of unification by induction on the
algorithmic rules.

\subsection{Soundness and completeness}

At present, order in the context is unimportant (providing dependencies are
respected) but we will see in Section~\ref{sec:genloc} that the algorithm does
keep entries as far right as possible, which will be necessary for generality
of type inference.

\begin{lemma}[Soundness and generality of unification]
\label{lem:unifySound} ~
\vspace*{-0.1in}\begin{enumerate}[(a)]
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
\end{proof}

We prove a straightforward lemma about the occurs check, and hence show
completeness of unification.

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
\item If 
$\theta : \Gamma \lei \Theta$, \\
$\Gamma \entails \upsilon \type \wedge \tau \type$  
and
$\Theta \entails \theta\upsilon \equiv \theta\tau$, then
there is some context $\Delta$ such that
$\algUnify{\Gamma}{\upsilon}{\tau}{\Delta}$.

\item Moreover, if $\theta : \Gamma, \Xi \lei \Theta$ is such that
$\Theta \entails \theta\alpha \equiv \theta\tau$ and
the input conditions \((\dag)\) are satisfied,
then there is some context $\Delta$ such that
$\algInstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$.
\end{enumerate}
\end{lemma}

\proofsux\begin{proof} It suffices to show that the algorithm succeeds
for every well-formed input in which a solution can exist. As the
algorithm terminates, we proceed by induction on its call graph. Each
step preserves solutions: if the equation in a conclusion can be
solved, so can those in its hypothesis.

The only case the rules omit is the case \((\ddag)\) where an illegal occurrence
of a type variable is rejected. In this case, we are seeking to solve the
problem $\alpha \equiv \tau$ in the context
$\Gamma, \decl{\alpha}{D} ~||~ \Xi$ and we have $\alpha \in \FTV{\tau, \Xi}$.
Substituting out the definitions in $\Xi$ from $\tau$, we obtain a type
$\upsilon$ such that $\alpha \in \FTV{\upsilon}$, $\upsilon$ is not a variable
and $\Gamma, \decl{\alpha}{D}, \Xi \entails \upsilon \equiv \tau$.
Now the problem $\alpha \equiv \upsilon$ has the same solutions as
$\alpha \equiv \tau$, but by Lemma~\ref{lem:occursCheck}, there are 
   no such. 
\end{proof}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Specifying type inference\label{sec:spec-tyinf}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We aim to implement type inference for the \hindleymilner\ system, so we need to
introduce type schemes and the term language. We extend the grammar of statements
to express additions to the context (binding statements), well-formed schemes,
type assignment and scheme assignment. The final grammar will be:
\[\begin{array}{r@@{\,}l}
S \defsyn~ \valid
    &~||~ \tau \type
    ~||~ \tau \equiv \upsilon
    ~||~ S \wedge S \\
    &~||~ \Sbind{\decl{x}{D}}{S}
    ~||~ \sigma \scheme
    ~||~ t : \tau
    ~||~ s \hasscheme \sigma.
\end{array}\]

\subsection{Binding statements}

To account for schemes and type assignment, we need a controlled way
to extend the context.
   Given statement $S$ and declaration $\decl{x}{D}$, then we define the
   statement $\Sbind{\decl{x}{D}}{S}$, binding \(x\) in \(S\), subject to \(D\). 

We give a generic introduction rule,
but we make use of neutral elimination only for type variables.
\[\begin{array}{c}
\Rule{\Gamma \entails \ok_K D    \quad    \Gamma, \decl{y}{D} \entails \subst{y}{x} S}
     {\Gamma \entails \Sbind{\decl{x}{D}}{S}}
\side{y \in \V_K \setminus \V_K(\Gamma)}
\smallskip\\
\Rule{\entailsN \Sbind{\alpha D}{S}
      \quad
      \entails \subst{\tau}{\alpha}{\sem{\decl{\alpha}{D}}}}
     {\entailsN \subst{\tau}{\alpha}{S}}
\side{D \in \D_\TY}
\end{array}\]
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

While the introduction rule allows renaming to ensure freshness, in practice we
will ignore this and assume that the bound variable name is always fresh for the
context.

\begin{lemma}[Binding preserves stability]\label{lem:stab-pres-bind}
If $\decl{x}{D}$ is a declaration and both $\ok_K D$ and $S$ are stable, then
$\Sbind{\decl{x}{D}}{S}$ is stable.
\end{lemma}
\proofsux\begin{proof}
Suppose $S$ is stable, $\delta : \Gamma \lei \Delta$, $x$ chosen
fresh for $\Gamma$ and $\Delta$, and 
$\Gamma \entails \Sbind{\decl{x}{D}}{S}$.  
   In the \name{Neutral} case,  
the result follows by Lemma~\ref{lem:neutrality}.
Otherwise, $\Gamma \entails \ok_K D$ and 
   $\Gamma, \decl{x}{D} \entails S$.
By stability and inductive hypothesis, $\Delta \entails \delta (\!\ok_K D)$.
Now we have $\delta : \Gamma, \decl{x}{D} \lei \Delta, \decl{x}{(\delta D)}$
so we also have $\Delta, \decl{x}{(\delta D)} \entails \delta S$ by stability of $S$.
Hence $\Delta \entails \Sbind{\decl{x}{(\delta D)}}{\delta S}$
and so $\Delta \entails \delta (\Sbind{\decl{x}{D}}{S})$.
\end{proof}

We 
   extend the binding notation to 
$\Sbind{\Xi}{S}$, where $\Xi$ is a list of declarations, 
   by:  
$\Sbind{\emptycontext}{S} \defmap S$ and
$\Sbind{(\Xi, \decl{x}{D})}{S} \defmap \Sbind{\Xi}{(\Sbind{\decl{x}{D}}{S})}$.

If $S$ is a statement and $C$ is a sanity condition for one of its parameters,
the statement $\Sbind{x D}{S}$ has sanity condition $\Sbind{x D}{C}$ for the
corresponding parameter.

\subsection{Type schemes}

To handle let-polymorphism, the context must assign type schemes to term
variables, rather than monomorphic types.
A \define{type scheme} $\sigma$ is a type wrapped in one or more $\forall$
quantifiers or $\letS{\cdot}{\cdot}{\cdot}$ bindings, with the syntax
$$\sigma \defsyn \gendot{\tau} ~||~ \forall\alpha~\sigma ~||~ \letS{\alpha}{\tau}{\sigma}.$$
We use explicit definitions in type schemes to avoid the need for substitution
in the type inference algorithm. 

Schemes arise by discharging a context suffix (a list of type variable
declarations) over a type, and any scheme can be viewed in this way. We write
$\gen{\Xi}{\tau}$ for the generalisation of the type $\tau$ over the suffix of
type variable declarations $\Xi$, defined by
\[
\begin{array}{r@@{\,}l}
\emptycontext         &\genarrow \tau \defmap \gendot{\tau}  \\
\hole{\alpha}, \Xi    &\genarrow \tau \defmap \forall\alpha~\gen{\Xi}{\tau}  \\
\alpha \defn \upsilon, \Xi &\genarrow \tau \defmap \letS{\alpha}{\upsilon}{\gen{\Xi}{\tau}}
\end{array}
\]

The statement $\sigma \scheme$ is then defined by
$$\gen{\Xi}{\tau} \scheme \defmap \Sbind{\Xi}{\tau \type}.$$
The \sanity\  is just $\valid$, as for $\tau \type$.

\subsection{Terms and type assignment}

Now we are in a position to reuse the framework already
introduced, defining the sort $\TM$, with 
$\V_\TM$ a set of term variables and $x$ ranging over $\V_\TM$.
Term variable properties $\D_\TM$ are scheme assignments of the form
$\,\asc \sigma$, with
$\ok_\TM (\,\asc \sigma) = \sigma \scheme$.

Let $s$, $t$, $w$ range over the set of terms with syntax 
$$t \defsyn x ~||~ t~t ~||~ \lambda x . t ~||~ \letIn{x}{t}{t}.$$

The type assignment statement $t : \tau$ is established by the
rules in Figure~\ref{fig:typeAssignmentRules}. It has two parameters $t$ and
$\tau$ with \sanity s $\valid$ and $\tau \type$ respectively.
We overload notation to define the scheme assignment statement
$t \hasscheme \sigma$ by
$$t \hasscheme \gen{\Xi}{\tau} \defmap \Sbind{\Xi}{t : \tau}.$$
Note this gives the parameters $t$ and $\sigma$ \sanity s
$\valid$ and $\sigma \scheme$ as one might expect.
This overloading is 
reasonable because the meaning of $\hasscheme$ is clear from
the context, and the interpretation of declarations embeds them in
statements:
$$\sem{x \asc \sigma}_\TM \defmap x \hasscheme \sigma.$$

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

The definition of
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
with respect to $\lei$, so we will define a subrelation $\leiR$ to capture
Milner's compromise, requiring that, for \(\delta : \Gamma \lei \Delta\), 
$$x \asc \sigma \in \Gamma ~\Rightarrow~ x \asc \delta\sigma \in \Delta.$$
If $\Gamma \leiR \Delta$, then
$\Delta$ assigns the \emph{same} type schemes to term variables as $\Gamma$
does (modulo substitution). Since the unification algorithm ignores term
variables, it must preserve this property.
This is not the full story, however; we need to extend the notion of
context to complete the definition of the $\leiR$ relation.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Generalising \emph{local} type variables\label{sec:genloc}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We have previously observed, but not yet exploited, the importance of
declaration order in the context, and that we move declarations left as
little as possible. Thus rightmost entries are those most local to the problem
we are solving. This will be useful when we come to implement type inference
for the `let' construct, as we want to generalise over \scare{local} type
variables but not \scare{global} variables.

In order to keep track of locality in the context, we need another kind of
context entry: the $\fatsemi$ separator. We add a new validity rule 
$$
\Rule{\Gamma \entails \valid}
     {\Gamma \fatsemi \entails \valid}.
$$

   We must then refine the $\leiR$ relation to respect these $\fatsemi$ divisions.
Let $\semidrop$ be the partial function from contexts $\Gamma$ and natural numbers $n$ which truncates $\Gamma$ after $n$
$\fatsemi$ separators, provided $\Gamma$ contains at least $n$ such: 
\[\begin{array}{r@@{\,}l}
\Xi \semidrop 0 &\defmap \Xi  \\
\Xi \fatsemi \Gamma \semidrop 0 &\defmap \Xi  \\
\Xi \fatsemi \Gamma \semidrop n+1 &\defmap \Xi \fatsemi (\Gamma \semidrop n)  \\
\Xi \semidrop n+1 &~\mathrm{undefined}
\end{array}\]
We write $\delta : \Gamma \leiR \Delta$ if $\delta$ is a substitution from
$\Gamma$ to $\Delta$ such that, for all
$\decl{x}{D} \in \Gamma \!\semidrop\! n$, we have that
$\Delta \!\semidrop\! n$ is defined,
$\Delta \!\semidrop\! n \entails \delta \sem{\decl{x}{D}}$ and
$$x \asc \sigma \in \Gamma ~\Rightarrow~ x \asc \delta\sigma \in \Delta.$$
We thus make the $\fatsemi$-separated sections of $\Gamma$ and
$\Delta$ correspond, so that declarations in the first $n$ sections of
$\Gamma$ can be interpreted over the first $n$ sections of $\Delta$. As
a consequence, \scare{moving left of \(\fatsemi\)} is an irrevocable
commitment. In particular, we note that
\[
\iota : \Gamma\fatsemi\hole{\alpha},\Delta
   \leiR \Gamma,\hole{\alpha}\fatsemi\Delta
\;\;\mbox{but}\;\;
\iota : \Gamma,\hole{\alpha}\fatsemi\Delta
   \not\leiR \Gamma\fatsemi\hole{\alpha},\Delta
\]

Note also that if $\delta : \Gamma \fatsemi \Gamma' \leiR \Delta \fatsemi \Delta'$,
where $\Gamma$ and $\Delta$ contain the same number of $\fatsemi$ separators,
then $\restrict{\delta}{\Gamma} : \Gamma \leiR \Delta$.

When the contexts contain only type variables, the two relations $\lei$ and
$\leiR$ coincide; the latter is a proper subrelation if the contexts also 
contain term variables.
Hence, most of the previous results hold if we replace $\lei$ with $\leiR$
throughout.


\subsection{Amending the unification algorithm}

Replacing $\lei$ with $\leiR$ makes extra work only in the unification
algorithm, because it acts structurally on contexts, which may now contain
$\fatsemi$ separators. We complete the algorithmic rules:
\[\begin{array}{c}
\namer{Skip}
\Rule{\algUnify{\Gamma}{\alpha}{\beta}{\Delta}}
     {\algUnify{\Gamma \fatsemi}{\alpha}{\beta}{\Delta \fatsemi}}
\smallskip\\
\namer{Repossess}
\Rule{\algInstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}}
     {\algInstantiate{\Gamma \fatsemi}{\alpha}{\tau}{\Xi}{\Delta \fatsemi}}
\end{array}\]

We must correspondingly update the induction in Lemma~\ref{lem:unifySound} to
show that adding the new rules preserves soundness and generality. For the
\name{Skip} rule, correctness follows immediately from this lemma:

\begin{lemma}
If $\LEIRStmt{\Gamma}{S}{\Delta}$ then $\LEIRStmt{\Gamma \! \fatsemi}{S}{\Delta \fatsemi}$.
\end{lemma}
\proofsux\begin{proof}
If $\Gamma \leiR \Delta$ then $\Gamma \fatsemi \leiR \Delta \fatsemi$ by
definition. If $\Delta \entails S$ then $\Delta \fatsemi \entails S$ since the
\name{Lookup} rule is the only one that extracts information from the context,
and it ignores the $\fatsemi$.

Now let $\theta : \Gamma \fatsemi \leiR \Theta \fatsemi \Xi$ be such that
$\Theta \fatsemi \Xi \entails S$. By definition of $\leiR$, we must have
$\theta : \Gamma \leiR \Theta$, so by minimality there exists
$\zeta : \Delta \leiR \Theta$ with $\theta \eqsubst \zeta \compose \iota$.
Then $\zeta : \Delta \fatsemi \leiR \Theta \fatsemi \Xi$ and we are done.
\end{proof}

The \name{Repossess} rule is so named because it moves
declarations in $\Xi$ to the left of the $\fatsemi$ separator,
thereby \scare{repossessing} them. To guarantee a solution
most general with respect to \(\leiR\),
we show that $\Xi$'s leftward journey is really necessary.

\begin{lemma}[Soundness and generality of the \name{Repossess} rule]
Suppose $\algInstantiate{\Gamma \fatsemi}{\alpha}{\tau}{\Xi}{\Delta \fatsemi}$. 
Then $\tyvars{\Gamma \fatsemi \Xi} = \tyvars{\Delta \fatsemi}$ and
$\LEIRUnify{\Gamma \fatsemi \Xi}{\alpha}{\tau}{\Delta \fatsemi}$.
\end{lemma}
\proofsux\begin{proof}
We extend the structural induction in Lemma~\ref{lem:unifySound} with an extra
case. The only proof of
$\algInstantiate{\Gamma \! \fatsemi}{\alpha}{\tau}{\Xi}{\Delta \fatsemi}$
is by \name{Repossess}, so inversion gives
$\algInstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$.
By induction, $\tyvars{\Gamma, \Xi} = \tyvars{\Delta}$ and
$\LEIRUnify{\Gamma, \Xi}{\alpha}{\tau}{\Delta}$.

We immediately observe that $\Gamma \fatsemi \Xi \leiR \Delta \fatsemi$,
\, 
$\Delta \fatsemi \entails \alpha \equiv \tau$ and
$$\tyvars{\Gamma \fatsemi \Xi} = \tyvars{\Gamma, \Xi} = \tyvars{\Delta}
    = \tyvars{\Delta \fatsemi}.$$

For minimality, suppose
$\theta : \Gamma \fatsemi \Xi \leiR \Theta \fatsemi \Phi$
and $\Theta \fatsemi \Phi \entails \theta\alpha \equiv \theta\tau$.
Observe that  $\alpha \in \tyvars{\Gamma}$ and
$\beta \in \tyvars{\Xi}  \Rightarrow  \beta \in \FTV{\tau, \Xi}$
by the conditions for the algorithmic judgment.
Now $\theta\alpha$ is a $\Theta$-type and $\theta\tau$ is equal to it,
so the only declarations in $\Phi$ that $\theta\tau$ (hereditarily) depends on
must be definitions over $\Theta$. But all the variables declared in $\Xi$ are
used in $\tau$, so there is a substitution
$\psi : \Gamma \fatsemi \Xi \leiR \Theta \fatsemi$
that agrees with $\theta$ on $\Gamma$ and maps variables in $\Xi$ to their
definitions in $\Theta$.

Hence $\psi : \Gamma, \Xi \leiR \Theta$ and
$\Theta \entails \psi\alpha \equiv \psi\tau$, so by hypothesis there exists
$\zeta : \Delta \leiR \Theta$ such that
$\psi \eqsubst \zeta \compose \iota : \Gamma, \Xi \leiR \Theta$.
Note that $\psi \eqsubst \theta : \Gamma \fatsemi \Xi \leiR \Theta \fatsemi \Phi$.
Then $\zeta : \Delta \fatsemi \leiR \Theta \fatsemi \Phi$
and
$\psi \eqsubst \zeta \compose \iota :
    \Gamma \fatsemi \Xi \leiR \Theta \fatsemi \Phi$,
so
$\theta \eqsubst \zeta \compose \iota :
    \Gamma \fatsemi \Xi \leiR \Theta \fatsemi \Phi$.
\end{proof}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Type inference problems and their solutions\label{sec:tyinf}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Type inference involves making the statement $t : \tau$ hold, but
unlike unification, the type should
be an \emph{output} of problem-solving along with the solution context. We need
a more liberal definition than that of constraint problems.
We associate a \define{mode} with each parameter in a statement: either
\scare{input} or \scare{output}. For simplicity, assume statements always have
one parameter of each mode (which may be trivial or composite).
We now extend the apparatus of minimal solutions to problems with outputs.

What can outputs be, and how can we compare them?
An \define{output set} is a set $B$ closed under
substitution, such that every context $\Gamma$ induces a preorder
$\leParam{}{\Gamma}{\cdot}{\cdot}$ on $B$ which is congruent
with respect to the definitional equality, i.e.\ if
$\Gamma \entails \alpha \equiv \tau \wedge \beta \equiv \upsilon$, then
$\leParam{}{\Gamma}{b}{c}$ if and only if 
$\leParam{}{\Gamma}{\subst{\tau}{\alpha} b}{\subst{\upsilon}{\beta} c}$.
This is easily verified for each preorder we use.

We need subsequent problems to depend on the results of earlier problems,
threading the output from one into the input of the next. Thus we must index
problems to determine the input parameters. 

Let $A$ be an output set.
An \define{$A$-indexed problem family $Q$ for $B$} is an output set $B$ and a
family of input parameters for a statement, indexed by elements of $A$, such
that the \define{simplicity condition} holds:
for all $a, a' \in A$, contexts $\Gamma$ and output parameter values $b \in B$,
$$\leParam{}{\Gamma}{a}{a'} ~\wedge~ \Gamma \entails \iprobstmt{Q}{a'}{b}
    \quad\Rightarrow\quad  \Gamma \entails \iprobstmt{Q}{a}{b}.$$
We write $\iprobstmt{Q}{a}{b}$ for the statement with input at index $a$ and
output value $b$, and $\iprobcond{Q}{a}$ for the \sanity s on the input
parameters at index $a$.
We use $\leParam{Q}{\Gamma}{\cdot}{\cdot}$ for the preorder on the output set.
The idea behind this contravariant condition is that the preorder
represents specialisation of solutions, so if a problem can be solved with an
input $a'$ then it can be solved with the more general $a$.

Now we can generalise the notion of constraint problem and its solution.
An \define{inference problem} consists of a context $\Gamma$, an $A$-indexed
problem family $Q$ and an index $a \in A$ such that
$\Gamma \entails \iprobcond{Q}{a}$.
A \define{solution} of it consists of an information increase
$\delta : \Gamma \leiR \Delta$ and a value for the output parameter $b \in B$
such that $\Delta \entails \iprobsubst{\delta}{Q}{a}{b}$.

The preorder on outputs induces a
preorder on context-output pairs, with $\delta : \leiRParam{\Gamma}{a}{\Delta}{b}$ if
$\delta : \Gamma \leiR \Delta$ and $\leParam{}{\Delta}{\delta a}{b}$.
We will look for minimal solutions with respect to this preorder,
and write $\LEIRProb{\Gamma}{Q[a]}{\Delta}{b}$ if
$(\iota : \Gamma \leiR \Delta, b)$ is a solution (i.e.\ $\Delta \entails \iprobstmt{Q}{a}{b}$)
and for all solutions $(\theta : \Gamma \leiR \Theta, c)$ we have
$\zeta : \leiRParam{\Delta}{b}{\Theta}{c}$ for some $\zeta$ such that
$\theta \eqsubst \zeta \compose \iota$.
As with unification, we only use the identity substitution
but are minimal with respect to any solution.

A \define{problem $P$ for $B$} is a problem family indexed by the 
unit set with the trivial preorder. We simply omit the index in this case.

\subsection{The Optimist's lemma}

Let $P$ be a problem for $A$ and let $Q$ be an $A$-indexed family for $B$.
Then the conjunction $\pconj{P}{x}{Q}$ is a problem for $A \times B$
with statement
$$\probstmt{(\pconj{P}{x}{Q})}{(a, b)} \defmap \probstmt{P}{a} \wedge \iprobstmt{Q}{a}{b}$$
and the preorder defined pointwise.
This \scare{dependent} generalisation of $P \wedge Q$
allows the output of $P$ to be threaded into $Q$.
The Optimist's lemma correspondingly generalises:

\begin{lemma}[The Optimist's lemma for inference problems]
\label{lem:optimistInference}
$$\Rule{\LEIRProb{\Gamma}{P}{\Delta}{b}
       \quad  \LEIRProb{\Delta}{Q[b]}{\Theta}{c}}
       {\LEIRProb{\Gamma}{(\pconj{P}{x}{Q})}{\Theta}{(b, c)}}.$$
\end{lemma}
\proofsux\begin{proof}
Since $\Gamma \leiR \Delta$ and $\Delta \leiR \Theta$,
we have $\Gamma \leiR \Theta$ by (updating) Lemma~\ref{lei:preorder}.
Furthermore, $\Theta \entails \probstmt{(\pconj{P}{x}{Q})}{(b, c)}$ since
$\Theta \entails \iprobstmt{Q}{b}{c}$ by assumption
and $\Delta \entails \probstmt{P}{b}$ so
stability gives $\Theta \entails \probstmt{P}{b}$.

For minimality, suppose there is a solution
$(\phi : \Gamma \leiR \Phi, (b', c'))$, so
$\Phi \entails \probsubst{\phi}{P}{b'}$ and
$\Phi \entails \iprobstmt{(\phi Q)}{b'}{c'}$.
Since $\LEIRProb{\Gamma}{P}{\Delta}{b}$, there exists
$\zeta : \Delta \leiR \Phi$
with $\leParam{}{\Phi}{\zeta b}{b'}$ and $\phi \eqsubst \zeta \compose \iota$.
By the simplicity condition,
$\Phi \entails \iprobstmt{(\phi Q)}{\zeta b}{c'}$
and hence $\Phi \entails \iprobsubst{\zeta}{Q}{b}{c'}$.
But $\LEIRProb{\Delta}{Q[b]}{\Theta}{c}$, so there exists
$\xi : \Theta \leiR \Phi$ such that $\leParam{}{\Phi}{\xi c}{c'}$
and $\zeta \eqsubst \xi \compose \iota$.
Hence $\leParam{}{\Phi}{\xi (b, c)}{(b', c')}$
so $\xi : \leiRParam{\Theta}{(b, c)}{\Phi}{(b', c')}$, and
$\phi \eqsubst \zeta \compose \iota
      \eqsubst (\xi \compose \iota) \compose \iota
      \eqsubst \xi \compose \iota$.
\end{proof}



\subsection{The Generalist's lemma}

We have considered problems with abstract inputs and outputs, but
which 
concrete values do we actually use? We want to
solve type inference problems, so we are interested in types and
type schemes.

The statement $t \hasscheme \sigma$ defines 
a problem for the set of schemes with preorder given by
$\leParam{\hasscheme}{\Gamma}{\gen{\Xi}{\tau}}{\gen{\Psi}{\upsilon}}$
if there is some $\psi : \Gamma \fatsemi \Xi \leiR \Gamma \fatsemi \Psi$
such that $\Gamma \fatsemi \Psi \entails \psi \tau \equiv \upsilon$
and $\restrict{\psi}{\Gamma} \eqsubst \iota$. That is,
$\leParam{\hasscheme}{\Gamma}{\sigma}{\sigma'}$
if $\sigma$ is a more general type scheme than $\sigma'$.

Since types are just schemes with no quantifiers, we instantiate the above
definition with $\Xi = \emptycontext = \Psi$, to get a preorder on types:
$\leParam{:}{\Gamma}{\tau}{\upsilon}$
if $\Gamma \entails \tau \equiv \upsilon$.

Thus the type inference problem is given by a context $\Gamma$ and a term
parameter $t$ as input to the type assignment statement. Following the
definitions, a solution is an information increase
$\delta : \Gamma \leiR \Delta$ and a type $\tau$ such that
$\Delta \entails \tau \type \wedge t : \tau$. A solution with output $\tau$ is
minimal if, given any other solution, we can find a substitution that unifies $\tau$
and the other type: that is, $\tau$ is a principal type.

In the type inference algorithm, we will use $\fatsemi$ to determine what can be
generalised, based on the following lemma.

\begin{lemma}[The Generalist's lemma]
\label{lem:generalist}
This rule is admissible:
$$
\Rule{\LEIRInfer{(\Gamma \fatsemi)}{t}{\tau}{(\Delta \fatsemi \Xi)}}
     {\LEIRInferScheme{\Gamma}{t}{\gen{\Xi}{\tau}}{\Delta}}.
$$
\end{lemma}
\proofsux\begin{proof}
If $\Gamma \fatsemi \leiR \Delta \!\fatsemi\! \Xi$ then $\Gamma \leiR \Delta$ by
definition. Furthermore,
$\Delta \entails t \hasscheme \gen{\Xi}{\tau}$ is defined to be
$\Delta \entails \Sbind{\Xi}{t : \tau}$, which holds iff
$\Delta \fatsemi \Xi \entails t : \tau$.

For minimality, suppose $\theta : \Gamma \leiR \Theta$ is an information
increase and $\gen{\Psi}{\upsilon}$ is a scheme such that
$\Theta \entails t \hasscheme \gen{\Psi}{\upsilon}$.
Then $\Theta, \Psi \entails t~:~\upsilon$. Now
$\theta : \Gamma \fatsemi \leiR \Theta \fatsemi \Psi$
and $\Theta \fatsemi \Psi \entails t : \upsilon$,
so by minimality of the hypothesis there is a substitution
$\zeta : \Delta \fatsemi \Xi \leiR \Theta \fatsemi \Psi$ such that
$\theta \equiv \zeta \compose \iota$ and
$\Theta \fatsemi \Psi \entails \zeta\tau \equiv \upsilon$.
Then by definition
$\restrict{\zeta}{\Delta} : \leiRParam{\Delta}{\gen{\Xi}{\tau}}{\Theta}{\gen{\Psi}{\upsilon}}$
and
$\theta \eqsubst \restrict{\zeta}{\Delta} \compose \iota : \Gamma \leiR \Theta$.
\end{proof}


\subsection{The binding lemmas}

Just as we have a general notion of conjunction problems, so we can regard
binding statements as problems. There are two ways to do so, depending on the
mode of the bound property. Each has a corresponding minimality result.

First, if $Q$ is a problem for $A$, then $\Sbind{x \asc \sigma}{Q}$
is also a problem for $A$ where we regard $\sigma$ as an input. It has statement
$$(\Sbind{x \asc \sigma}{Q}) a \defmap \Sbind{x \asc \sigma}{Q a}$$
and preorder given by $\leParam{(\Sbind{x \asc \sigma}{Q})}{\Gamma}{a}{b}$ if
$\leParam{Q}{\Gamma, x \asc \sigma}{a}{b}$.
Minimal solutions are found by bringing $x$ into scope temporarily.

\begin{lemma}
\label{lem:bindVariableProblem}
If $\Xi$ does not contain any $\fatsemi$ separators, then we have:
$$\Rule{\LEIRProb{(\Gamma, x \asc \sigma)}{Q}{(\Delta, x \asc \sigma, \Xi)}{a}}
       {\LEIRProb{\Gamma}{(\Sbind{x \asc \sigma}{Q})}{(\Delta, \Xi)}{a}}.$$
\end{lemma}
\proofsux\begin{proof}
If $\Gamma, x \asc \sigma \leiR \Delta, x \asc \sigma, \Xi$ then
$\Gamma \leiR \Delta, \Xi$ since nothing in $\Xi$ can depend on $x$.
If $\Delta, x \asc \sigma, \Xi \entails Q a$ then
$\Delta, \Xi, x \asc \sigma \entails Q a$ (permuting the context) and hence
$\Delta, \Xi \entails \Sbind{x \asc \sigma}{Q a}$.

If $\theta : \Gamma \leiR \Theta$ is such that
$\Theta \entails \Sbind{x \asc \theta\sigma}{(\theta Q) a'}$, then by inversion,
$\Theta, x \asc \theta\sigma \entails (\theta Q) a'$.
By minimality of the hypothesis, there is
$\zeta : \Delta, x \asc \sigma, \Xi \leiR \Theta, x \asc \theta\sigma$ such that
$\leParam{Q}{\Theta, x \asc \theta\sigma}{\theta a}{a'}$ and
$\theta \eqsubst \zeta \compose \iota$.
Hence $\zeta : \Delta, \Xi \leiR \Theta$ and
$\leParam{(\Sbind{x \asc \sigma}{Q})}{\Theta}{\theta a}{a'}$.
\end{proof}


Alternatively, we can regard a type variable binding as being
initially unknown, and obtain the problem $\Qbind{\alpha}{Q}$ whose output is
a pair of a type and a value in $A$. The corresponding statement is
$$(\Qbind{\alpha}{Q}) (\tau, b) \defmap \subst{\tau}{\alpha}(\probstmt{Q}{b})$$
and the output preorder is given by
$\leParam{(\Qbind{\alpha}{Q})}{\Gamma}{(\tau, a)}{(\upsilon, b)}$ if
$\Gamma \entails \tau \equiv \upsilon$ and
$\leParam{Q}{\Gamma}{\subst{\tau}{\alpha} a}{\subst{\upsilon}{\alpha} b}$.
Minimal solutions arise by adding an unknown to the context and returning it
as the output:

\begin{lemma}
\label{lem:inventVariableProblem}
\raisebox{-0.1in}{\qquad\qquad\(
\Rule{\LEIRProb{(\Gamma, \hole{\alpha})}{Q}{\Delta}{b}}
       {\LEIRProb{\Gamma}{(\Qbind{\alpha}{Q})}{\Delta}{(\alpha, b)}}
\)}
\end{lemma}
\proofsux\begin{proof}
By hypothesis, $\Delta \entails \probstmt{Q}{b}$ so clearly
$\Delta \entails \subst{\alpha}{\alpha}(\probstmt{Q}{b})$.
Moreover, $\Gamma, \hole{\alpha} \leiR \Delta$ so $\Gamma \leiR \Delta$.
If $\theta : \Gamma \leiR \Theta$ is such that
$\Theta \entails \subst{\upsilon}{\alpha}(\probsubst{\theta}{Q}{c})$, then
$\Theta \entails \probstmt{(\subst{\upsilon}{\alpha} \theta Q)}{(\subst{\upsilon}{\alpha} c)}$.
By minimality of the hypothesis
with the substitution
$\subst{\upsilon}{\alpha} \compose \theta : \Gamma, \hole{\alpha} \leiR \Theta$,
there is some $\zeta : \Delta \leiR \Theta$ such that
$\leParam{Q}{\Theta}{\zeta b}{(\subst{\upsilon}{\alpha} c)}$ and
$\subst{\upsilon}{\alpha} \compose \theta \eqsubst \zeta \compose \iota$.
Hence
$\zeta : \leiRParam{\Delta}{(\alpha, b)}{\Theta}{(\upsilon, c)}$.
\end{proof}



\subsection{Transforming type assignment into type inference}

To transform a rule into an algorithmic form, we proceed clockwise starting from
the conclusion. For each hypothesis, we must ensure that the problem is fully
specified, inserting variables to stand for unknown problem inputs. Moreover, we
cannot pattern match on problem outputs, so we ensure there are schematic
variables in output positions, fixing things up with appeals to unification. 

Figure~\ref{fig:transformedRules} shows the transformed version of the
declarative rule system. The 
   $\lambda$-rule 
now binds a fresh name for the argument type, which 
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
   fresh name bindings 
can be substituted out.
The only difficulty is in the application rule, where an equation 
   is 
introduced. If an application has a type in the old system, it can be assigned
the same type in the new system with 
   using a reflexive equation. 
Conversely,
if an application has a type in the new system, then using the conversion
with the equation allows the same type to be assigned in the old system.


Given the transformed rules, we construct the algorithm to match.
We establish the type inference assertion $\algInfer{\Gamma}{t}{\tau}{\Delta}$ 
and the scheme inference assertion $\algInferScheme{\Gamma}{s}{\sigma}{\Delta}$ 
by the rules in Figure~\ref{fig:inferRules}.
As they are structural on terms, they 
yield a terminating algorithm, 
and hence the implementation in 
Subsection~\ref{sec:inferImplementation}.
The Optimist's lemma
permits sequential solution of problems and the binding lemmas
let us interpret binding statements as problems.

\begin{figure}[ht]
\[\begin{array}{c}
\mathframe{\algInferScheme{\Gamma}{s}{\sigma}{\Delta}}

\smallskip\\
\namer{Gen}
\Rule{\algInfer{(\Gamma \fatsemi)}{s}{\upsilon}{(\Delta \fatsemi \Xi)}}
     {\algInferScheme{\Gamma}{s}{\gen{\Xi}{\upsilon}}{\Delta}}
\bigskip\\ 

\mathframe{\algInfer{\Gamma}{t}{\tau}{\Delta}}

\smallskip\\
\namer{Var}
\Rule{x \asc \gen{\Xi}{\upsilon} \in \Gamma}
     {\algInfer{\Gamma}{x}{\upsilon}{(\Gamma, \Xi)}}

\smallskip\\

\namer{Abs}
\Rule{\algInfer{(\Gamma, \hole{\alpha}, x \asc \gendot{\alpha})}{w}{\upsilon}
          {(\Delta, x \asc \gendot{\alpha}, \Xi)}}
     {\algInfer{\Gamma}{\lambda x.w}{(\alpha \arrow \upsilon)}{(\Delta, \Xi)}}
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
\BigRule{\algInferScheme{\Gamma}{s}{\sigma}{\Delta_0}}
        {\algInfer{(\Delta_0, x \asc \sigma)}{w}{\chi}
               {(\Delta, x \asc \sigma, \Xi)}}
        {\algInfer{\Gamma}{\letIn{x}{s}{w}}{\chi}{(\Delta, \Xi)}}

\end{array}\]
\caption{Algorithmic rules for type inference}
\label{fig:inferRules}
\end{figure}


\subsection{Soundness and completeness}

Since the algorithmic rules correspond directly to the transformed declarative
system in Figure~\ref{fig:transformedRules}, we can easily prove soundness,
completeness and generality of type inference with respect to this system.
Each proof is by induction on 
derivations, observing that each
algorithmic rule maintains the appropriate properties.

Recall that a type inference problem $(\Gamma, P)$ has statement
$t : \tau$ where $t$ is a term and $\tau$ is the output type.
A scheme inference problem has statement $t \hasscheme \sigma$
where $\sigma$ is the output scheme.

\begin{lemma}[Soundness of type inference]
\label{lem:inferSound}
If $(\Gamma, P)$ is a type or scheme inference problem, and $\alg{\Gamma}{P}{\Delta}{a}$,
then $\Gamma \leiR\Delta$ and $\Delta \entails P a$.
\end{lemma}
\proofsux\begin{proof}
We maintain this property as an invariant in all the rules.
\end{proof}

To prove generality, we use the admissible rules in the Optimist's, Generalist's
and binding lemmas. The algorithmic rules map to compositions of these,
with multiple hypotheses corresponding to conjunctions of problems.
To apply the Optimist's lemma, we must check that the problem on the right
satisfies the \scare{simplicity condition}. For \name{Let}, this means we need
$$\leParam{\hasscheme}{\Gamma}{\sigma}{\sigma'}
     ~\wedge~ \Gamma, x \asc \sigma' \entails w : \chi
     \quad\Rightarrow\quad \Gamma, x \asc \sigma \entails w : \chi,$$
which says that if a solution can be found with $x$ having a given type scheme
then one can be found with it having a more general scheme.
The \name{App} case is even more straightforward.

\begin{lemma}[Generality of type inference]
\label{lem:inferGeneral}
If $(\Gamma, P)$ is a type or scheme inference problem, and $\alg{\Gamma}{P}{\Delta}{a}$,
then $\LEIRProb{\Gamma}{P}{\Delta}{a}$.
\end{lemma}
\proofsux\begin{proof}
Given soundness (Lemma~\ref{lem:inferSound}), it remains to show 
generality, i.e.\ that each algorithmic rule becomes
admissible in the transformed declarative system if we replace
$\transto$ with $\LEIR$.

For the \name{Var} rule, suppose $\theta : \Gamma \leiR \Theta$ and
$\Theta \entails x : \tau$. By inversion, the proof must consist of
the \name{Lookup} rule followed by eliminating 
$\Theta \entailsN x \hasscheme \gen{\theta\,\Xi}{\theta\upsilon}$
with some $\Theta$-types. Hence it determines a map from the unbound type variables
of $\Xi$ to types over $\Theta$, i.e.\ a substitution
$\zeta : \Gamma, \Xi \leiR \Theta$ that agrees with $\theta$ on $\Gamma$ and
maps type variables in $\Xi$ to their definitions in $\Theta$.

All the remaining cases are covered by the previous lemmas.
The Generalist's lemma proves exactly the property required for the \name{Gen}
rule. 
The \name{Abs} rule is minimal by Lemmas~\ref{lem:bindVariableProblem} and
\ref{lem:inventVariableProblem}.
The \name{App} rule is minimal by two uses of the Optimist's lemma,
Lemma~\ref{lem:inventVariableProblem} and minimality of unification.
The \name{Let} rule is minimal by the Optimist's lemma and
Lemma~\ref{lem:bindVariableProblem}.
\end{proof}

\begin{lemma}[Completeness of type inference]
\label{lem:inferComplete}
If $(\Gamma, P)$ is a type or scheme inference problem, and
there exist $\theta : \Gamma \leiR \Theta$ and $a'$ such that
$\Theta \entails (\theta P) a'$, then $\alg{\Gamma}{P}{\Delta}{a}$
for some context $\Delta$ and output $a$.
\end{lemma}
\proofsux\begin{proof}
We proceed by induction on the derivation of $\Theta \entails (\theta P) a'$.
Every case in the transformed declarative system (excluding the conversion rule)
is covered by the algorithm, and it reduces the problem to an equivalent form,
thereby preserving solutions. Thus if a solution exists, then the algorithm
will succeed.
\end{proof}


\subsection{Implementation of type inference}
\label{sec:inferImplementation}

\begin{figure*}[p]

\begin{minipage}[b]{0.5\linewidth}

\subfigure[][Type schemes]{\frame{\parbox{\textwidth}{\fixpars\medskip

> data Index a = Z | S a deriving (Functor, Foldable)
>
> data Schm a  =  Type (Ty a) 
>              |  All (Schm (Index a))
>              |  LetS (Ty a) (Schm (Index a))
>     deriving (Functor, Foldable)
>
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
>     fromS beta  Z          = beta
>     fromS beta  (S alpha)  = alpha

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

\vspace{1pt}

\label{subfig:generaliseCode}
}}}

\end{minipage}
\hspace{\medskipamount}
\begin{minipage}[b]{0.5\linewidth}


\subfigure[][Terms and context entries]{\frame{\parbox{\textwidth}{\fixpars\medskip

> data Tm a  =  X a
>            |  Tm a :$ Tm a 
>            |  Lam a (Tm a)
>            |  Let a (Tm a) (Tm a)
>     deriving (Functor, Foldable)

> type TmName   = String
> type Term     = Tm TmName

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
scope checking fails, whereas |error| signals violation of an
algorithmic invariant.

Figure~\ref{subfig:schemeCode} implements type schemes.
It is convenient to represent bound variables by de Bruijn indices and free
variables (in the context) by names
\citep{mcbride_mckinna_not_number_2004}.
We use
Haskell's type system to prevent some incorrect manipulations of indices by
defining a \scare{successor} type |Index|,
where the outermost bound variable is represented by |Z| and other variables
are wrapped in the |S| constructor
\citep{bird_paterson_nested_1999, bellegarde_hook_substitution_1994}.

Figures~\ref{subfig:specialiseCode} and~\ref{subfig:generaliseCode} implement
specialisation and generalisation of type schemes. The former unpacks a
scheme with fresh names; the latter \scare{skims} 
   entries 
off the top of the context to the |LetGoal| marker.

Figure~\ref{subfig:termCode} implements the data type of terms, and gives the
final definition of |Entry| including type and term variable declarations and
|LetGoal| markers. It implements the |find| function to look up a term variable
in the context and return its scheme.

Figure~\ref{subfig:termScopeCode} implements the |(>-)| operator to evaluate
|Contextual| code in the scope of a term variable, then remove it afterwards.
This is necessary for dealing with $\lambda$-abstractions and let-bindings.

Finally, Figure~\ref{subfig:inferCode} implements the type inference algorithm
itself. It proceeds structurally over the term,
following the rules in Figure~\ref{fig:inferRules}
and using the monadic operations.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Discussion\label{sec:conc}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We have arrived at an implementation of \hindleymilner\ type inference
which involves all the same steps as \AlgorithmW, but not
necessarily in the same order. In particular, the dependency panic
which seizes \W\ in the let-rule here becomes
an invariant that the underlying unification algorithm
maintain a well-founded context.

Our algorithm is presented as a problem transformation system locally
preserving all possible solutions, hence finding a most general
global solution if any at all. Accumulating solutions to decomposed
problems is justified simply by stability of solutions on information
increase. We have established a discipline of problem solving, happily
complete for Hindley-Milner type inference, but in any case coupling
soundness with generality.

Maintain context validity, make definitions anywhere and only where
there is no choice, so the solutions you find will be general and
generalisable locally: this is a key design principle for
elaboration of high-level code in systems like Epigram and Agda; bugs
arise from its transgression. Our disciplined account of
\scare{current information} in terms of contexts and their information
ordering provides a principled means to investigate and repair
these troubles.

We are, however, missing yet more context. Our task was greatly
simplified by studying a structural type inference process for
\scare{finished} expressions in a setting where unification is
complete. Each subproblem is either solved or rejected on first
inspection---there is never a need for a \scare{later, perhaps} outcome. As
a result, \scare{direct style} 
recursive programming is adequate to the task. If problems could get
stuck, how might we abandon them and return to them later? By storing
their \emph{context}, of course!

Here, we have combined the \emph{linguistic} contexts for various sorts
of variable; our next acquisition is the
\emph{syntactic} context of the target term, interspersing variable
declarations with pieces of its
\emph{zipper}~\citep{huet:zipper}. We thus enable a flexible traversal
strategy, refocusing wherever progress can be
made. The tree-like proof states of McBride's thesis evolved into
exactly such \scare{zippers with binding} in the implementation of Epigram.

As we have seen, `information increase' is really the
elaboration of simultaneous substitution from variables-and-terms to
declarations-and-derivations. Our analysis of role
declaration plays in derivation shows that stability is endemic---an
action of hereditary substitution on \scare{cut-free} derivations.
And that is just what it should be. We have rationalised
Hindley-Milner type inference, adapting a discipline for
incremental term construction in dependent types
to manage unknowns for incremental problem solving.
The analysis can only become clearer, the technology
simpler, as we identify these two kinds of construction,
mediating \emph{problems as types}.

\addcontentsline{toc}{section}{References}
\bibliographystyle{plainnat}

\begin{thebibliography}{21}
\providecommand{\natexlab}[1]{#1}
\providecommand{\url}[1]{\texttt{#1}}
\expandafter\ifx\csname urlstyle\endcsname\relax
  \providecommand{\doi}[1]{doi: #1}\else
  \providecommand{\doi}{doi: \begingroup \urlstyle{rm}\Url}\fi

\bibitem[Baader and Snyder(2001)]{DBLP:books/el/RV01/BaaderS01}
F.~Baader and W.~Snyder.
\newblock Unification theory.
\newblock In J.~A. Robinson and A.~Voronkov, editors, \emph{Handbook of
  Automated Reasoning}, pages 445--532. Elsevier and MIT Press, 2001.

\bibitem[Bellegarde and Hook(1994)]{bellegarde_hook_substitution_1994}
F.~Bellegarde and J.~Hook.
\newblock Substitution: a formal methods case study using monads and
  transformations.
\newblock \emph{Sci. Comp. Programming}, 23\penalty0 (2-3):\penalty0 287--311,
  1994.

\bibitem[Bird and Paterson(1999)]{bird_paterson_nested_1999}
R.~Bird and R.~Paterson.
\newblock de {Bruijn} notation as a nested datatype.
\newblock \emph{J. Functional Programming}, 9\penalty0 (1):\penalty0 77--91,
  1999.

\bibitem[Cl\'{e}ment et~al.(1986)Cl\'{e}ment, Despeyroux, Kahn, and
  Despeyroux]{clment_simple_1986}
D.~Cl\'{e}ment, T.~Despeyroux, G.~Kahn, and J.~Despeyroux.
\newblock A simple applicative language: {mini-ML}.
\newblock In \emph{Proc. {LISP and Functional Programming}}, pages 13--27. ACM,
  1986.

\bibitem[Damas and Milner(1982)]{damas_principal_1982}
L.~Damas and R.~Milner.
\newblock Principal type-schemes for functional programs.
\newblock In \emph{Proc. POPL '82}, pages 207--212. ACM, 1982.

\bibitem[Dunfield(2009)]{dunfield_polymorphism_2009}
J.~Dunfield.
\newblock Greedy bidirectional polymorphism.
\newblock In \emph{Proc. ML '09}, pages 15--26. ACM, 2009.

\bibitem[{GHC Team}(2009)]{ghc_team_glorious_2009}
{GHC Team}.
\newblock The {GHC} user's guide, version 6.12.1.
\newblock Section 7.5. Extensions to the "deriving" mechanism, 2009.

\bibitem[Huet(1997)]{huet:zipper}
G.~Huet.
\newblock {T}he {Z}ipper.
\newblock \emph{J. Functional Programming}, 7\penalty0 (5):\penalty0 549--554,
  1997.

\bibitem[{McAdam}(1998)]{mcadam_unification_1998}
B.~J. {McAdam}.
\newblock On the unification of substitutions in type inference.
\newblock In \emph{Proc. IFL' 98}, pages 139--154. Springer, 1998.

\bibitem[McBride(1999)]{mcbride:thesis}
C.~McBride.
\newblock \emph{Dependently {T}yped {F}unctional {P}rograms and their
  {P}roofs}.
\newblock PhD thesis, University of Edinburgh, 1999.

\bibitem[McBride(2003)]{mcbride:unification}
C.~McBride.
\newblock {F}irst-{O}rder {U}nification by {S}tructural {R}ecursion.
\newblock \emph{J. Functional Programming}, 13\penalty0 (6), 2003.

\bibitem[{McBride} and
  {McKinna}(2004{\natexlab{a}})]{mcbride.mckinna:view-from-the-left}
C.~{McBride} and J.~{McKinna}.
\newblock The view from the left.
\newblock \emph{J. Functional Programming}, 14\penalty0 (1):\penalty0 69--111,
  2004{\natexlab{a}}.

\bibitem[{McBride} and
  {McKinna}(2004{\natexlab{b}})]{mcbride_mckinna_not_number_2004}
C.~{McBride} and J.~{McKinna}.
\newblock Functional pearl: {I} am not a number--{I} am a free variable.
\newblock In \emph{Proc. {Haskell} workshop}, pages 1--9. ACM,
  2004{\natexlab{b}}.

\bibitem[Miller(1992)]{miller:mixed}
D.~Miller.
\newblock Unification under a mixed prefix.
\newblock \emph{J. Symbolic Computation}, 14\penalty0 (4):\penalty0 321--358,
  1992.

\bibitem[Milner(1978)]{milner_theory_1978}
R.~Milner.
\newblock A theory of type polymorphism in programming.
\newblock \emph{J. Computer and System Sciences}, 17\penalty0 (3):\penalty0
  348--375, 1978.

\bibitem[Naraschewski and Nipkow(1999)]{NaraschewskiN-JAR}
W.~Naraschewski and T.~Nipkow.
\newblock Type inference verified: Algorithm {W} in {Isabelle/HOL}.
\newblock \emph{J. Automated Reasoning}, 23\penalty0 (3):\penalty0 299--318,
  1999.

\bibitem[Nipkow and Prehofer(1995)]{Nipkow-Prehofer-JFP95}
T.~Nipkow and C.~Prehofer.
\newblock Type reconstruction for type classes.
\newblock \emph{J. Functional Programming}, 5\penalty0 (2):\penalty0 201--224,
  1995.

\bibitem[Norell(2007)]{norell:agda}
U.~Norell.
\newblock \emph{Towards a practical programming language based on dependent
  type theory}.
\newblock PhD thesis, Chalmers University of Technology, 2007.

\bibitem[Pollack(1990)]{pollack_implicit_1990}
R.~Pollack.
\newblock Implicit syntax.
\newblock In \emph{Informal Proceedings of First Workshop on Logical
  Frameworks}, 1990.

\bibitem[Robinson(1965)]{robinson_machine-oriented_1965}
J.~A. Robinson.
\newblock A machine-oriented logic based on the resolution principle.
\newblock \emph{JACM}, 12\penalty0 (1):\penalty0 23--41, 1965.

\bibitem[Wells(2002)]{wells_principal_typings_2002}
J.~B. Wells.
\newblock The essence of principal typings.
\newblock In \emph{Proc. ICALP '02}, pages 913--925. Springer, 2002.

\end{thebibliography}



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
