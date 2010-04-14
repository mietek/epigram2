\documentclass[authoryear,preprint]{sigplanconf}

%options ghci

%include lhs2TeX.fmt
%include lhs2TeX.sty

%format <-  = "\leftarrow "
%format :-> = "\arrow "
%format <>< = "<\!>\!< "
%format <>> = "<\!>\!> "
%format <+> = "\oplus "
%format <*> = "\varoast "
%format <$> = "<\!\!\$\!\!> "
%format :$  = ":\!\!\$\ "
%format ::: = "\asc "
%format ::~ = "\asc "
%format >=> = "\genarrow "
%format ::= = ":= "
%format <?  = "\in "

%format F0  = "\emptycontext"
%format B0  = "\emptycontext"

%format Lam (x) (b) = "\lambda" x "." b
%format Let (x) (s) (t) = "\letIn{" x "}{" s "}{" t "} "
%format LetGoal = "\letGoal "
%format notTypeVar = "\notTypeVar "

%format Nothing = "? "
%format Just = "!\!"

%format alpha  = "\alpha"
%format alpha0
%format alpha1
%format beta   = "\beta"
%format beta0
%format beta1
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
%format upsilon = "\upsilon"
%format upsilon0
%format upsilon1
%format _Xi = "\Xi"
%format _Xi0
%format _Xi1

\usepackage{color}
\definecolor{red}{rgb}{1.0,0.0,0.0}
\newcommand{\TODO}[1]{\textcolor{red}{#1}}

\newcommand{\compose}{\cdot}
\newcommand{\extend}{\ensuremath{\wedge}}
\newcommand{\yields}{\ensuremath{\dashv}}
\newcommand{\entails}{\ensuremath{\vdash}}
\newcommand{\var}{\ensuremath{\defn \_}}
\newcommand{\fresh}{\ensuremath{~\mathbf{fresh}}}
\newcommand{\type}{\ensuremath{~\mathbf{type}}}
\newcommand{\scheme}{\ensuremath{~\mathbf{scheme}}}
\newcommand{\valid}{\ensuremath{\mathbf{valid}}}
\newcommand{\ok}{\ensuremath{~\mathbf{ok}}}
\newcommand{\emptycontext}{\ensuremath{\varepsilon}}
\newcommand{\notTypeVar}{\ensuremath{\ldots}}
\newcommand{\letGoal}{\ensuremath{\mathbf{let}}}
\newcommand{\letIn}[3]{\ensuremath{\mathrm{let}~ #1 \!:=\! #2 ~\mathrm{in}~ #3}}
\newcommand{\letS}[3]{\ensuremath{(!#1 \!:=\! #2 ~\mathrm{in}~ #3)}}
\newcommand{\boxrule}[1]{\begin{center}\framebox{\ensuremath{#1}}\end{center}}
\newcommand{\boxrules}[2]{\begin{center}\framebox{\ensuremath{#1}}\quad\framebox{\ensuremath{#2}}\end{center}}

\newcommand{\tmvars}[1]{\ensuremath{tmvars(#1)}}
\newcommand{\tyvars}[1]{\ensuremath{V_\TY(#1)}}
\newcommand{\types}[1]{\ensuremath{types(#1)}}
\newcommand{\FTV}[1]{\ensuremath{FTV(#1)}}

\newcommand{\lei}{\ensuremath{\sqsubseteq}}
\newcommand{\gei}{\ensuremath{\sqsupseteq}}
\newcommand{\LEI}{\ensuremath{~\hat\sqsubseteq~}}

\newcommand{\arrow}{\ensuremath{\triangleright}}
\newcommand{\defn}{\ensuremath{\!:=\!}}
\newcommand{\asc}{\ensuremath{:\sim}}
\newcommand{\hasc}{~\hat{::}~}
\newcommand{\hole}[1]{\ensuremath{#1 \!:= ?}}
\newcommand{\contains}{\ensuremath{\ni}}

\newcommand{\Judge}[3]{\ensuremath{#1 \preceq #3 \vdash #2}}
\newcommand{\Jmin}[3]{\ensuremath{#1 \LEI #3 \vdash #2}}
\newcommand{\Junify}[4]{\Judge{#1}{#2 \equiv #3}{#4}}
\newcommand{\Jinstantiate}[5]{\Judge{#1}{#2 \equiv #3 ~[#4]}{#5}}
\newcommand{\Jspec}[4]{\Judge{#1}{#2 \succ #3}{#4}}
\newcommand{\Jtype}[4]{\Judge{#1}{#2 : #3}{#4}}
\newcommand{\Jhast}[4]{\Judge{#1}{#2 ~\hat:~ #3}{#4}}

\newcommand{\Pinf}[1]{\mathrm{Inf}_{#1}}

\newcommand{\name}[1]{\ensuremath{\mathrm{\textsc{#1}} \;}}
\newcommand{\side}[1]{\ensuremath{\; #1}}

\newcommand{\br}[2]{\genfrac{}{}{0pt}{0}{#1}{#2}}
\newcommand{\BigRule}[3]{\ensuremath{\Rule{\br{#1}{#2}}{#3}}}

\newcommand{\sym}{\ensuremath{^\vee}}
\newcommand{\sem}[1]{\ensuremath{\llbracket #1 \rrbracket}}

\newcommand{\W}{\ensuremath{\mathcal{W}}}

\newcommand{\genarrow}{\ensuremath{\Uparrow}}
\newcommand{\gen}[2]{\ensuremath{(#1 \genarrow #2)}}
\newcommand{\forget}[1]{\ensuremath{\lfloor #1 \rfloor}}
\newcommand{\hasscheme}{\ensuremath{::}}
\newcommand{\subcontext}{\ensuremath{\subset}}
\newcommand{\semidrop}{\downharpoonright}
\newcommand{\Sbind}[2]{(#1 \Yright #2)}

\newcommand{\define}[1]{\emph{#1}}
\newcommand{\scare}[1]{`#1'}

\newcommand{\V}{\mathcal{V}}
\newcommand{\D}{\mathcal{D}}
\newcommand{\Ss}{\mathcal{S}}
\newcommand{\K}{\mathcal{K}}
\newcommand{\TY}{\mathrm{\textsc{TY}}}
\newcommand{\TM}{\mathrm{\textsc{TM}}}

\newcommand{\In}[1]{\ensuremath{\mathit{In}_{#1}}}
\newcommand{\Out}[1]{\ensuremath{\mathit{Out}_{#1}}}
\newcommand{\Pre}[1]{\ensuremath{\mathit{Pre}_{#1}}}
\newcommand{\Post}[1]{\ensuremath{\mathit{Post}_{#1}}}
\newcommand{\R}[1]{\ensuremath{\mathit{R}_{#1}}}

\usepackage{amsthm}
\usepackage{amsmath}
\usepackage{enumerate}
\usepackage{eucal}
\usepackage{natbib}
\usepackage[T1]{fontenc}
\usepackage[draft=false]{hyperref}

\setlength{\parskip}{5pt}
\setlength{\parindent}{0pt}

\newtheorem{lemma}{Lemma}

\include{macros}
\setlength{\rulevgap}{0.05in}

\hyphenpenalty=5000
\tolerance=1000

\begin{document}

\conferenceinfo{ICFP '10}{September 27--29, Baltimore, Maryland, USA.} 
\copyrightyear{2010} 
\copyrightdata{[to be supplied]} 

\titlebanner{DRAFT}

\title{Functional Pearl: Type inference in context}
\authorinfo{Adam Gundry \and Conor McBride}
           {University of Strathclyde, Glasgow}
           {\{adam.gundry,conor.mcbride\} at cis.strath.ac.uk}
\authorinfo{James McKinna}
           {Radboud University, Nijmegen}
           {james.mckinna at cs.ru.nl}

\maketitle

\begin{abstract}
\input{abstract.ltx}
\end{abstract}



\section{Introduction}

Algorithm \W%%%, also known as the Damas-Milner algorithm, 
    \ is a well-known type inference algorithm, 
    based on the Unification Algorithm of \citet{robinson_machine-oriented_1965}, 
for the Hindley-Milner type system due to \citet{milner_theory_1978}, 
and proved correct by \citet{damas_principal_1982}.
%%%It is 

Successive presentations and formalisations of Algorithm \W\ have treated the
underlying unification algorithm as a \scare{black box}, but by considering both
simultaneously we are able to give a more elegant type inference algorithm.
In particular, the generalisation step 
%%%(required when 
(for 
 inferring the type of a let-expression) becomes straightforward.

We present algorithms using systems of inference rules to define relationships
between judgments of the form $\Judge{\Gamma_0}{S}{\Gamma_1}$. Here $\Gamma_0$
is the input context (before applying the rule), $S$ is the statement being
established, and $\Gamma_1$ is the output context (in which $S$ holds).
This idea of judgments producing a resulting context goes back at least to
\citet{pollack_implicit_1990}. 
%%%, and hence perhaps to \citet{harper_type_1991} and \citet{milner_definition_1990}.
   An interesting point of comparison is with the work of Nipkow and 
   co-workers \citep{Nipkow-Prehofer-JFP95,NaraschewskiN-JAR}, 
   but substitutions and new contexts are there kept separate. 
%%%
We %%%will 
   define an ordering on contexts based on the information they contain,
and show that $\Gamma_1$ is minimal with respect to this ordering. If one
thinks of a context as a set of atomic facts, then $\Gamma_1$ is the least upper
bound of $\Gamma_0$ together with the facts required to make $S$ hold.

In each case, at most one rule matches the input context and condition, and we
specify a termination order so the rules define algorithms. \TODO{Do we?}
It is straightforward to implement these algorithms by translating the rule
systems into code. We illustrate this by providing a Haskell implementation.

Contexts here are not simply sets of assumptions, but lists containing
information about type and term variables. The unification problem thus
becomes finding a \scare{more informative} context in which two expressions are
equivalent up to definition. Order of entries in a context is important: they are
subject to well-foundedness conditions (any definition must be in terms of
definitions earlier in the context), and we obtain most general unifiers and
principal types by keeping entries as far to the right as possible, only moving
them left when necessary to satisfy a constraint. This idea of imposing order
restrictions on the entries of a context is similar to the
\emph{ordered hypotheses} of deduction systems for non-commutative logic
\citep{polakow_natural_1999}.

In contrast to other presentations of unification and Hindley-Milner type
inference, our algorithm uses explicit definitions to avoid the need for a 
substitution operation. It thus lends itself to efficient implementation.
(We do use substitution in our reasoning about the system.) Many implementations
of (variations on) the Robinson unification algorithm are incorrect because they
do not handle substitutions correctly \citep{norvig_correctingwidespread_1991}.


\section{Plan}
\TODO{Develop abstract contextual and problem-solving machinery with
running example of types and unification, then redeploy for terms and
type inference. Our mission is to understand why type inference problems have
various solutions (Heeren, Wells, Schilling, McAdam...).}


%if False

< {-# LANGUAGE DeriveFunctor, DeriveFoldable #-}

> {-# LANGUAGE FlexibleInstances, TypeSynonymInstances, TypeFamilies, StandaloneDeriving, TypeOperators #-}

First, let's get some imports out of the way.

> import Prelude hiding (any)
> import Control.Applicative (Applicative, (<$>), (<*>), pure)
> import Control.Monad (ap)
> import Control.Monad.State (StateT, get, gets, lift, put, runStateT)
> import Data.Foldable (any, Foldable, foldMap)
> import Data.Monoid (Monoid, mappend, mempty)

> import Data.Traversable (Traversable, traverse, fmapDefault, foldMapDefault)

%endif


\section{Types and type variables}
\TODO{Syntax in mathematics and Haskell}

%% To make things more concrete, we define the sort $\TY \in \K$.
The syntax of types is
$$\tau ::= \alpha ~||~ \tau \arrow \tau$$
where $\alpha$ ranges over some set of type variables $\V_\TY$.
%% Let $\D_0 \subset \D$ be the set of types.
In the sequel, $\alpha$ and $\beta$ are type variables and $\tau$ and $\upsilon$
types.
%% (All of these symbols may be primed or subscripted.)
%% We use $\Xi$ to denote a context suffix containing only type variable declarations.

The foldable functor |Ty| defines types in our object language parameterised by
the type of variable names, which will be useful later. Thanks to a language
extension in GHC 6.12 \citep{ghc_team_glorious_2009} we can simply
derive the required typeclass instances.
We define |Type| to use integers as names.

> data Ty a  =  V a |  Ty a :-> Ty a

<     deriving (Functor, Foldable)

%if False

> infixr 5 :->

%endif

> type Name  = Integer
> type Type  = Ty Name


\TODO{What makes sense of the variables?
Idea (ideology?): make sure variables are bound somewhere, introduce
a context for this purpose}

Let $\K$ a set of sorts, and for each $K \in \K$ let $\V_K$ be a set of
variables and $\D_K$ a set of objects. Our running example will be the sort
$\TY$, where $\V_\TY$ is some set of type variables and $\D_\TY$ initially
contains only the \scare{unbound variable} object $~\hole{}$.

A \define{context} $\Gamma$ is a list of declarations $v D$, where
$v \in \V_K$ and $D \in \D_K$.
%% and separators $(\fatsemi)$. 
We write $\emptycontext$ for the empty context, and the symbols
$\Gamma, \Delta$ and $\Theta$ range over contexts.
%% $\Xi$ is a context that contains no $\fatsemi$ separators.

\TODO{Contexts collect variable declarations (what there is to know about
a variable); only a := ? initially. Statements are judged in a context.}

Let $\Ss$ be a set of statements.
We write $\Gamma \entails S$ to mean that the definitions in $\Gamma$,
corresponding to atomic facts, support the statement $S \in \Ss$.

\TODO{Start keeping our own house in order.
When is a context valid?
When its declarations are valid extensions.
Ok is a function, not a statement.}

We assume we have a map $\ok_K : \D_K \rightarrow \Ss$ for every $K \in \K$.
Let $\V_K(\Gamma)$ be the set of $K$-variables in $\Gamma$.
We define the context validity statement $\valid$ as shown in
Figure~\ref{fig:contextValidityRules}.

In the example, $\ok_\TY (\hole{}) = \valid$.

\begin{figure}[ht]
\boxrule{\Gamma \entails \valid}
$$
\Axiom{\emptycontext \entails \valid}
\qquad
%% \Rule{\Gamma \entails \valid}
%%      {\Gamma \fatsemi \entails \valid}
%% $$
%% $$
\Rule{\Gamma \entails \valid    \quad    \Gamma \entails \ok_K D}
     {\Gamma, v D \entails \valid}
\side{v \in \V_K \setminus \V_K(\Gamma)}
$$
\caption{Rules for context validity}
\label{fig:contextValidityRules}
\end{figure}

\TODO{When is a type meaningful (syntax isn't enough)?
When its variables are in scope.
Introduce lookup rule.}

We suppose that there is a map
$\sem{\cdot}_K : \V_K \times \D_K \rightarrow \mathcal{P}(\Ss)$
for each $K \in \K$, from declarations to sets of statements.
% such that $$\Gamma \contains v D  \Rightarrow  \Gamma \entails \sem{v D}.$$
(We typically omit the subscript when the sort is irrelevant or can be inferred.)
The basic rule of our inference system is
$$\name{Lookup}
  \Rule{v D \in \Gamma    ~\wedge~   S  \in \sem{v D}}
       {\Gamma \entails S}.$$
Thus $\sem{v D}$ is the set of atomic statements that hold if the declaration
$v D$ is in the context.

We define the statement $\tau \type$ in Figure~\ref{fig:typeOkRules}.
Note that there is no base case for the definition because we will deduce
$\alpha \type$ for variables $\alpha$ using the \textsc{Lookup} rule.
In the example, $\sem{\hole{\alpha}} = \{ \alpha \type \}$.

\begin{figure}[ht]
\boxrule{\Gamma \entails \tau \type}
$$
% \Rule{\Gamma \entails \valid}
%      {\Gamma \entails \alpha \type}
% \side{\alpha \in \tyvars{\Gamma}}
% \qquad
\Rule{\tau \type   \quad   \upsilon \type}
     {\tau \arrow \upsilon \type}
$$
% \boxrule{\Gamma \entails D \ok_\TY}
% $$\Rule{\valid}
%       {\;\hole{} \ok_\TY}
% \qquad
% \Rule{\tau \type}
%      {\;\defn \tau \ok_\TY}
% $$
\caption{Rules for types and definitions}
\label{fig:typeOkRules}
\end{figure}

\TODO{Lookups are the "variables" of derivations}


\section{Declarations}

\TODO{Discovering the value of a variable does not render it meaningless
(quite the reverse).
As we're going to solve constraints and learn values of variables,
we had better extend declarations.
Add := tau declarations with associated ok.}

A type variable declaration is written |alpha := mt|, where $\alpha$ is a
variable that is either bound to a type $\tau$ (written |alpha := Just tau| or
$\alpha \defn \tau$), or left unbound (written |alpha := Nothing|).
Thus $\D_\TY$ contains the \scare{undefined} binding $\;\hole{}$ and bindings
$\;\defn \tau$ for each type $\tau$.

In the example, $\ok_\TY (\defn \tau) = \tau \type$.

We define the set of free type variables of a type or context suffix thus:
\begin{align*}
\FTV{\alpha}    &= \{ \alpha \} \\
\FTV{\tau \arrow \upsilon}  &= \FTV{\tau} \cup \FTV{\upsilon}  \\
\FTV{\Xi}       &= \bigcup \{ \FTV{\tau} ~||~ \alpha \defn \tau \in \Xi \}  \\
\FTV{\tau, \Xi} &= \FTV{\tau} \cup \FTV{\Xi}.
\end{align*}



\subsection{Implementation}

A context is an ordered (backwards) list of entries, subject to the
conditions that each variable is defined at most once, and all variables that
occur in a type variable binding must be defined earlier in the list.
(These conditions will be maintained by the algorithm but are not enforced by
the type system, though that would be possible in a language such as Agda.)
A context suffix is a (forwards) list containing only type variable definitions.

< data Entry = Name := Maybe Type | notTypeVar

%if False

> data a ::= b = a ::= b

%endif

> type Context     = Bwd Entry
> type Suffix      = Fwd (Name ::= Maybe Type)

The types |Bwd| and |Fwd| are backwards (snoc) and forwards (cons) lists,
respectively. We overload |B0| for the empty list in both cases, and write
|:<| and |:>| for the data constructors. Data types are cheap, so we might
as well make the code match our intution about the meaning of data. Lists
are monoids where |<+>| is the append operator, and the \scare{fish} operator
\eval{:t (<><)} appends a suffix to a context. 

Since |Type| and |Suffix| are built from |Foldable| functors containing names, we can define a typeclass implementation of \ensuremath{FTV}, with membership function |(<?)|: 

> class OccursIn a where
>     (<?) :: Name -> a -> Bool

> instance OccursIn Name where
>     (<?) = (==)

> instance Foldable ((::=) a) where
>     foldMap f (_ ::= x) = f x

> instance (Foldable t, OccursIn a) => OccursIn (t a) where
>     alpha <? t = any (alpha <?) t

We work in the |Contextual| monad (computations that can fail and mutate the
context).  

> type Contextual  = StateT (Name, Context) Maybe

The |Name| component is the next fresh type variable name to use;
it is an implementation detail that is not mentioned in the typing rules. 
Our choice of |Name| means that it is easy to choose a name fresh with respect to a |Context|: 

> fresh :: Name -> Context -> Name
> fresh alpha _Gamma = succ alpha

Working in this monad, we first define some useful functions for dealing with
the context. The |getContext|, |putContext| and |modifyContext| functions
respectively retrieve, replace and update the stored context. They correspond
to |get|, |put| and |modify| in the |State| monad, but ignore the first component
of the state.

> getContext :: Contextual Context
> getContext = gets snd
>
> putContext :: Context -> Contextual ()
> putContext _Gamma = do  beta <- gets fst
>                         put (beta, _Gamma)
>
> modifyContext :: (Context -> Context) -> Contextual ()
> modifyContext f = getContext >>= putContext . f

The |popEntry| function removes and returns the topmost entry from the context.
\TODO{Since |popEntry| is only used twice, perhaps we should remove it?}

> popEntry :: Contextual Entry
> popEntry = do  _Gamma :< e <- getContext
>                putContext _Gamma
>                return e



\section{Equality, Information Order, Stability}


\TODO{Declarations induce an equational theory.
Equality judgment, extended lookup, structural rule, equivalence
closure.}

If $\tau$ and $\upsilon$ are types, we define the equivalence statement
$\tau \equiv \upsilon$ by making declarations yield equations:
\begin{align*}
\sem{\hole{\alpha}}_\TY &= \{ \alpha \type \}  \\
\sem{\alpha \defn \tau}_\TY &= \{ \alpha \type, \alpha \equiv \tau \}
%%%
%%% \sem{\hole{\alpha}}_\TY &= \{ \alpha \type, \alpha \equiv \alpha \}  \\
%%% \sem{\alpha \defn \tau}_\TY &= \{ \alpha \type, \alpha \equiv \alpha,
%%%            \alpha \equiv \tau, \tau \equiv \alpha \}
\end{align*}
and taking structural and equivalence closure by the rules in
Figure~\ref{fig:equivRules}.

\begin{figure}[ht]
\boxrule{\Gamma \entails \tau \equiv \upsilon}
% \Rule{\alpha \defn \tau}
%      {\alpha \equiv \tau}
$$
\Rule{\tau \type}
     {\tau \equiv \tau}
\qquad
\Rule{\upsilon \equiv \tau}
     {\tau \equiv \upsilon}
$$
$$
\Rule{\tau_0 \equiv \upsilon_0
      \quad
      \tau_1 \equiv \upsilon_1}
     {\tau_0 \arrow \tau_1 \equiv \upsilon_0 \arrow \upsilon_1}
\qquad
\Rule{\tau_0 \equiv \tau_1
      \quad
      \tau_1 \equiv \tau_2}
     {\tau_0 \equiv \tau_2}
$$
\caption{Rules for type equivalence}
\label{fig:equivRules}
\end{figure}


\TODO{Intuitively, defining a variable certainly can't make equations
become untrue.
More generally, if we rely on the context to tell us what we may
deduce about variables, making contexts more informative must preserve
deductions.
Information order, stability (no fatsemi yet, just forward pointer).}

For contexts $\Gamma$, $\Delta$ and for each $K \in \K$, we will define a set of
\define{$K$-substitutions from $\Gamma$ to $\Delta$}
from variables in $\V_K(\Gamma)$ to some set, which will apply to statements.
We write $\delta : \Gamma \lei \Delta$ to mean that for each $K \in \K$,
$\delta_K$ is a $K$-substitution from $\Gamma$ to $\Delta$ such that
if $v D \in \Gamma$ and $S \in \sem{v D}$ then
%% $\Delta \semidrop n$ is defined and
$\Delta \entails \delta S$.
(We write $\delta S$ for the simultaneous application of every $\delta_K$ to
$S$.)

If $\Gamma$ is a valid context, let $\types{\Gamma}$ be 
the set of types $\tau$ such that $\Gamma \entails \tau \type$. 
A \define{$\TY$-substitution from $\Gamma$ to $\Delta$} is a substitution from
$\V_\TY(\Gamma)$ to $\types{\Delta}$ which applies to types and statements in
the obvious way.

\TODO{Idea of information order as substitution on derivations.}

We may omit $\delta$ and write $\Gamma \lei \Delta$ if we are only interested
in the existence of a suitable substitution. This relation between contexts
captures the notion of \define{information increase}: $\Delta$ supports all the
statements corresponding to definitions in $\Gamma$. 

%% Moreover, this will still hold if we truncate both $\Gamma$ and $\Delta$ after
%% any number of $\fatsemi$ separators.

%% Note that if $\delta : \Gamma \lei \Delta$ then
%% $\delta||_{\Gamma \semidrop n} : \Gamma \semidrop n \lei \Delta \semidrop n$. 

We say a statement $S$ is
\define{stable} if it is preserved under information increase, that is, if
$$\Gamma \entails S  ~\wedge~  \delta : \Gamma \lei \Delta
    \quad \Rightarrow \quad
    \Delta \entails \delta S.$$


\TODO{Stability of == just by strict positivity of recursive hypotheses
and stability of non-recursive hypotheses.
Construction ensures effectiveness of this proof strategy.}

A simple induction on derivations shows that the statement $\tau \type$ is stable.
An induction on derivations shows that $\tau \equiv \upsilon$ is stable, since
the only rule that accesses the context is \textsc{Lookup}.


\TODO{Where should composite statements go?
Postpone fatsemi to later.}

If $S$ and $S'$ are statements and $v D$ is a declaration, then
we define statements $S \wedge S'$, $\fatsemi S$ and $\Sbind{v D}{S}$ thus:
$$
\Rule{S \quad S'}{S \wedge S'}
\qquad
\Rule{\Gamma \fatsemi \entails S}
     {\Gamma \entails \fatsemi S}
$$
$$
\Rule{\Gamma \entails D \ok_K    \quad    \Gamma, v D \entails S}
     {\Gamma \entails \Sbind{v D}{S}}
\side{v \in \V_K \setminus \V_K(\Gamma)}.
$$
We do not add elimination rules to make proofs by induction on the structure
of derivations easier, but they will be admissible.
Note that we omit the context from rules if it is constant throughout.
The only inference rules to access the context will be the \textsc{Lookup} rule
and the rules for the $\fatsemi$ and $\Sbind{\cdot}{\cdot}$ statements given above.


\TODO{Composition preserves stability.}

\begin{lemma}[Stability]
Every statement in $\Ss$ is stable.
\end{lemma}
\begin{proof}
Suppose $S$ and $S'$ are stable, $\Gamma \entails (S \wedge S')$ and
$\delta : \Gamma \lei \Delta$. Then $\Gamma \entails S$ and $\Gamma \entails S'$,
so by stability, $\Delta \entails \delta S$ and $\Delta \entails \delta S'$.
Hence $\Delta \entails \delta (S \wedge S')$.

Suppose $S$ is stable, $\Gamma \entails \Sbind{v D}{S}$ and
$\delta : \Gamma \lei \Delta$. Then $\Gamma \entails D \ok_K$ and
$\Gamma, v D \entails S$, so by induction, $\Delta \entails \delta D \ok_K$.
Let $\delta' = \delta[v/v]$, then
$\delta' : \Gamma, v D \lei \Delta, v (\delta D)$
so by stability of $S$ we have $\Delta, v (\delta D) \entails \delta' S$.
Hence $\Delta \entails \Sbind{v (\delta D)}{\delta' S}$
and so $\Delta \entails \delta \Sbind{v D}{S}$.
\TODO{We should at least mention freshness here.}

Suppose $S$ is stable, $\Gamma \entails \fatsemi S$ and
$\delta : \Gamma \lei \Delta$. Then $\Gamma \fatsemi \entails S$.
Now $\delta : \Gamma \fatsemi \lei \Delta \fatsemi$
so by stability, $\Delta \fatsemi \entails \delta S$ and hence
$\Delta \entails \delta (\fatsemi S)$.

For other statements that we define later, the proof will proceed by induction
on the structure of derivations. Where the \textsc{Lookup} rule is applied,
the result holds by the definition of information increase. No other rules
may refer to the context, so it is straightforward to see that the statement
is stable.
\end{proof}


\TODO{We need $\sem{\cdot}$ to be a set of stable statements, then $\lei$
is a preorder.}

This allows us to prove the following:

\begin{lemma}\label{lei:preorder}
The $\lei$ relation is a preorder, with reflexivity demonstrated by
$\iota : \Gamma \lei \Gamma : v \mapsto v$, and transitivity by
$$\gamma_1 : \Gamma_0 \lei \Gamma_1  ~\wedge~  \gamma_2 : \Gamma_1 \lei \Gamma_2
  \quad \Rightarrow \quad  \gamma_2 \compose \gamma_1 : \Gamma_0 \lei \Gamma_2.$$
\end{lemma}

\begin{proof}
Reflexivity follows immediately from the \textsc{Lookup} rule.
For transitivity, suppose $v D \in \Gamma_0 \semidrop n$ and $S \in \sem{v D}$.
Then $\Gamma_1 \semidrop n \entails \gamma_1 S$ since
$\gamma_1 : \Gamma_0 \lei \Gamma_1$.
Now by stability applied to $\gamma_1 S$ using
$\gamma_2||_{\Gamma_1 \semidrop n} :
    \Gamma_1 \semidrop n \lei \Gamma_2 \semidrop n$, we have
$\Gamma_2 \semidrop n \entails \gamma_2\gamma_1\sem{v D}$ .
\end{proof}



\section{Unification Problems}

\TODO{What is a problem?
Statement you wish true, or more generally, statement for which
you wish a witness.
We want algorithms which find witnesses to statements, preferably
general ones.
Refine statements to problems.
Set of well-posed questions, category of answers.}

A \define{problem} $P$ consists of
\begin{itemize}
\item sets \In{P}\ and \Out{P}\ of input and output parameters,
\item a precondition map $\Pre{P} : \In{P} \rightarrow \Ss$,
\item a postcondition map $\Post{P} : \In{P} \rightarrow \Out{P} \rightarrow \Ss$ and
\item a relation map $\R{P} : \Out{P} \rightarrow \Out{P} \rightarrow \Ss$,
\end{itemize}
such that \In{P}\ and \Out{P}\ are closed under substitution and the maps
respect substitution, for example, $\Pre{P}(\theta r) = \theta \Pre{P}(r)$.
Moreover, for any context $\Gamma$, $a \in \In{P}$ and $b, c, d \in \Out{P}$
such that
\[\Gamma \entails \Pre{P} (a) \wedge \Post{P} (a)(b) \wedge \Post{P} (a)(c)
         \wedge \Post{P} (a)(d), \]
we must have 
\(\Gamma \entails \R{P} (b)(b)\) and
\[\Gamma \entails \R{P} (b)(c) \wedge \R{P} (c)(d)
    \Rightarrow \Gamma \entails \R{P} (b)(d). \]

The unification problem $U$ is given by
\begin{align*}
\In{U} &= Type \times Type  \\
\Out{U} &= 1  \\
\Pre{U}(\tau, \upsilon) &= \tau \type \wedge \upsilon \type  \\
\Post{U}(\tau, \upsilon) ~\_ &= \tau \equiv \upsilon  \\
\R{U} ~\_ ~\_ &= \valid
\end{align*}

A \define{$P$-instance for a context $\Gamma$} is $a \in \In{P}$ such that
$\Gamma \entails \Pre{P}(a)$. The problem instance $a$ has \define{solution}
$(b, \delta, \Delta)$ if $b \in \Out{P}$ and $\delta : \Gamma \lei \Delta$
such that $\Delta \entails \Post{P} (\delta a, b)$. (Observe that
$\Delta \entails \Pre{P} (\delta a)$ by stability.)

The solution $(b, \delta, \Delta)$ is \define{minimal} if for any solution
$(c, \theta, \Theta)$ there exists $\zeta : \Delta \lei \Theta$ such that
$\theta = \zeta \compose \delta$ and $\Theta \entails \R{P} (\zeta b, c)$.

We write $P_a(b)$ for $\Post{P}(a)(b)$ and
$\delta : \Jmin{\Gamma}{P_a(b)}{\Delta}$ to mean that
$(b, \delta, \Delta)$ is a minimal solution of the $P$-instance $a$.


\TODO{Closure under conjunction.}

If $P$ and $Q$ are problems, then $P \wedge Q$ is a problem with
\begin{align*}
\In{P \wedge Q}                 &= \In{P} \times \In{Q}  \\
\Out{P \wedge Q}                &= \Out{P} \times \Out{Q}  \\
\Pre{P \wedge Q} (a, b)         &= \Pre{P} (a) \wedge \Pre{Q} b  \\
\Post{P \wedge Q} (a, b) (c, d) &= \Post{P}(a)(c) \wedge \Post{Q}(b)(d)  \\
\R{P \wedge Q}(a, b)(c, d)      &= \R{P}(a)(c) \wedge \R{Q}(b)(d)  \\
\end{align*}


\TODO{Optimist's lemma justifying sequential solution.}

The point of all this machinery is to be able to state and prove the following 
lemma, stating that the minimal solution to a conjunction of problems can be
found by finding the minimal solution of the first problem, then (minimally)
extending it to solve the second. 

\begin{lemma}[The Optimist's Lemma]
The following inference rule is admissible:
$$\Rule{\gamma_1 : \Jmin{\Gamma_0}{P_a(r)}{\Gamma_1}
       \quad  \gamma_2 : \Jmin{\Gamma_1}{Q_b(s)}{\Gamma_2}}
       {\gamma_2 \compose \gamma_1 :
           \Jmin{\Gamma_0}{P \wedge Q_{(a, b)}(\gamma_2 r, s)}{\Gamma_2}}$$
\end{lemma}

\TODO{Make the proof prettier, perhaps using a diagram.}

\begin{proof}
We have that $\gamma_2 \compose \gamma_1 : \Gamma_0 \lei \Gamma_2$ by 
Lemma~\ref{lei:preorder}. 

To show $\Gamma_2 \entails P \wedge Q_{(a, b)} (\gamma_2 r, s)$, it
suffices to show $\Gamma_2 \entails P_a(\gamma_2 r)$ and
$\Gamma_2 \entails Q_b(s)$. The latter holds by assumption. For the
former, note that $\Gamma_1 \entails P_a(r)$ and hence
$\Gamma_2 \entails \gamma_2 P_a(r)$ by stability of $P_a(r)$.
But $\gamma_2 P_a(r) = P_a(\gamma_2 r)$ by definition, so we are done.

Finally, suppose there is some $\theta : \Gamma_0 \lei \Theta$ such that
$\Theta \entails P \wedge Q_{(a, b)}(r', s')$, so
$\Theta \entails P_a(r')$ and
$\Theta \entails Q_b(s')$.
Since $\gamma_1 : \Jmin{\Gamma_0}{P_a(r)}{\Gamma_1}$, there exists
$\zeta_1 : \Gamma_1 \lei \Theta$ such that $\theta = \zeta_1 \compose \gamma_1$
and $\Theta \entails \R{P}(\zeta_1 r)(r')$.
But then $\gamma_2 : \Jmin{\Gamma_1}{Q_b(s)}{\Gamma_2}$, so there exists
$\zeta_2 : \Gamma_2 \lei \Theta$ such that $\zeta_1 = \zeta_2 \compose \gamma_2$
and $\Theta \entails \R{Q}(\zeta_2 s)(s')$.
Hence 
$\theta = \zeta_2 \compose (\gamma_2 \compose \gamma_1)$
and
$\Theta \entails \R{P \wedge Q}(\zeta_2 (\gamma_2 r), \zeta_2 s)(r', s')$.
\end{proof}

\TODO{This is not the only decomposition justified by stability (cf.
McAdam) ; there is a transactional flavour.}


\section{Deriving a unification algorithm}

\TODO{Derive algorithmic rules from declarative specification.}


We wish to transform these rules into a unification algorithm.
Starting with only the structural rule, if we try to prove admissibility of
equivalence closure, we encounter the proof obligations shown.

\begin{figure}[ht]
$$
\Rule{\alpha \type}
     {\alpha \equiv \alpha}
\qquad
\Rule{\alpha \equiv \tau}
     {\tau \equiv \alpha}
\qquad
\Rule{\tau \equiv \alpha}
     {\alpha \equiv \tau}
$$
$$
\Rule{\alpha \equiv \tau    \quad    \tau \equiv \upsilon}
     {\alpha \equiv \upsilon}
\qquad
\Rule{\upsilon \equiv \tau    \quad    \tau \equiv \alpha}
     {\upsilon \equiv \alpha}
$$
\caption{Proof obligations to admit equivalence closure}
\label{fig:admitEquivClosure}
\end{figure}

Now we can see how to construct the algorithm. The structural rule says that
whenever we have rigid $\arrow$ symbols on each side, we decompose the problem
into two subproblems, and thanks to the Optimist's Lemma we can solve these
sequentially. Otherwise, we either have variables on both sides, or a variable
on one side and a type on the other. In each case, we look at the head of the
context to see what information it gives us, but when instantiating a variable
with a type we need to accumulate a list of the type's dependencies as we
encounter them.
% \begin{itemize}
% \item If $\alpha D$ is at the head of the context and we are trying to
% unify $\alpha \equiv \alpha$ then we are done.
% \item If $\hole{\alpha}$ is at the head and we seek $\alpha \equiv \tau$ or
% $\tau \equiv \alpha$ then we can replace the head with the list of dependencies
% followed by $\alpha \defn \tau$.
% \end{itemize}

\TODO{Relating the declarative rules for type equivalence to the unification
algorithm needs some thought. It would be nice if we could turn transitivity
into an admissible rule.}
The rules in Figure~\ref{fig:unifyRules} define our unification algorithm. The
sequent $\Junify{\Gamma_0}{\tau}{\upsilon}{\Gamma_1}$ means that given inputs
$\Gamma_0$, $\tau$ and $\upsilon$, unification of $\tau$ with $\upsilon$ 
succeeds, producing output context $\Gamma_1$.
The sequent
$\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\Xi}{\Gamma_1}$
means that given inputs $\Gamma_0$, $\tau$, $\upsilon$ and $\Xi$,
instantiation of $\alpha$ with $\tau$ succeeds with output context $\Gamma_1$.
(Here $\Xi$ is a (possibly empty) list of type variable declarations.)


We define the orthogonality relation $e \perp S$ (entry $e$ does not have any
effect on the statement $S$) for unification and instantiation statements
as follows:
\begin{align*}
\delta \defn \_ \perp \alpha \equiv \beta
    &\mathrm{~if~} \delta \neq \alpha \wedge \delta \neq \beta  \\
e \perp \alpha \equiv \tau
    &\mathrm{~if~} e \perp \alpha \equiv \tau [] \wedge \tau \mathrm{~not~variable}  \\
e \perp \tau \equiv \alpha
    &\mathrm{~if~} e \perp \alpha \equiv \tau [] \wedge \tau \mathrm{~not~variable}  \\
e \perp \tau_0 \arrow \tau_1 \equiv \upsilon_0 \arrow \upsilon_1
    &\mathrm{~if~} e \perp \tau_0 \equiv \upsilon_0 \wedge e \perp \tau_1 \equiv \upsilon_1  \\
\delta \defn \_ \perp \alpha \equiv \tau [\Xi]
    &\mathrm{~if~} \alpha \neq \delta \wedge \delta \notin \FTV{\tau, \Xi}
\end{align*}

The rules \textsc{Coalesce}, \textsc{Expand} and \textsc{Instantiate} have
symmetric counterparts that are identical apart from interchanging the equated
terms in the conclusion. Usually we will ignore these without loss of generality,
but where necessary we refer to them as \textsc{Coalesce}\sym,
\textsc{Expand}\sym and \textsc{Instantiate}\sym.


\begin{figure}[ht]
\boxrule{\Junify{\Gamma_0}{\tau}{\upsilon}{\Gamma_1}}

$$
\name{Id}
\Axiom{\Junify{\Gamma, \alpha D}{\alpha}{\alpha}{\Gamma, \alpha D}}
$$

$$
\name{Coalesce}
\Axiom{\Junify{\Gamma, \hole{\alpha}}{\alpha}{\beta}{\Gamma, \alpha \defn \beta}}
$$

$$
\name{Expand}
\Rule{\Junify{\Gamma_0}{\tau}{\beta}{\Gamma_1}}
     {\Junify{\Gamma_0, \alpha \defn \tau}{\alpha}{\beta}{\Gamma_1, \alpha \defn \tau}}
\side{\alpha \neq \beta}
$$

$$
\name{Orthogonal}
\Rule{\Junify{\Gamma_0}{\alpha}{\beta}{\Gamma_1}}
     {\Junify{\Gamma_0, e}{\alpha}{\beta}{\Gamma_1, e}}
\side{e \perp \alpha \equiv \beta}
$$

% \begin{prooftree}
% \AxiomC{ $\Gamma_0 \extend \alpha \equiv \beta \yields \Gamma_1$ }
% \LeftLabel{ \textsc{Skip$_1$} }
% \RightLabel{ $\alpha, \beta, \delta $ distinct}
% \UnaryInfC{ $\Gamma_0, \delta \defn mt \extend \alpha \equiv \beta \yields \Gamma_1, \delta \defn mt$ }
% \end{prooftree}

% \begin{prooftree}
% \AxiomC{ $\Gamma_0 \extend \alpha \equiv \beta \yields \Gamma_1$ }
% \LeftLabel{ \textsc{Skip$_2$} }
% \RightLabel{ $\alpha \neq \beta$}
% \UnaryInfC{ $\Gamma_0, \Diamond \extend \alpha \equiv \beta \yields \Gamma_1, \Diamond$ }
% \end{prooftree}

$$
\name{Arrow}
\Rule{\Junify{\Gamma_0}{\tau_0}{\upsilon_0}{\Gamma}
      \quad
      \Junify{\Gamma}{\tau_1}{\upsilon_1}{\Gamma_1}}
     {\Junify{\Gamma_0}{\tau_0 \arrow \tau_1}{\upsilon_0 \arrow \upsilon_1}{\Gamma_1}}
$$

$$
\name{Instantiate}
\Rule{\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\emptycontext}{\Gamma_1}}
     {\Junify{\Gamma_0}{\alpha}{\tau}{\Gamma_1}}
\side{\tau \mathrm{~not~variable}}
$$

\bigskip

\boxrule{\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\Xi}{\Gamma_1}}

$$
\name{InstCoalesce}
\Axiom{\Jinstantiate{\Gamma, \hole{\alpha}}{\alpha}{\tau}{\Xi}{\Gamma, \Xi, \alpha \defn \tau}}
\side{\alpha \notin \FTV{\tau, \Xi}}
$$

$$
\name{InstExpand}
\Rule{\Junify{\Gamma_0, \Xi}{\upsilon}{\tau}{\Gamma_1}}
     {\Jinstantiate{\Gamma_0, \alpha \defn \upsilon}{\alpha}{\tau}{\Xi}{\Gamma_1, \alpha \defn \nu}}
$$

$$
\name{InstPass}
\Rule{\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\beta D, \Xi}{\Gamma_1}}
     {\Jinstantiate{\Gamma_0, \beta D}{\alpha}{\tau}{\Xi}{\Gamma_1}}
\side{\alpha \neq \beta, \beta \in \FTV{\tau, \Xi}}
$$

$$
\name{InstOrthogonal}
\Rule{\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\Xi}{\Gamma_1}}
     {\Jinstantiate{\Gamma_0, e}{\alpha}{\tau}{\Xi}{\Gamma_1, e}}
\side{e \perp \alpha \equiv \tau [\Xi]}
$$

\caption{Algorithmic rules for unification}
\label{fig:unifyRules}
\end{figure}


Observe that we have no rule for the case $\alpha \equiv \tau ~[\Xi]$
with $\alpha \in \FTV{\tau, \Xi}$ and the context $\Gamma_0, \hole{\alpha}$;
hence the algorithm fails if this situation arises. This is essentially an occur
check failure: $\alpha$ and $\tau$ cannot be unified if $\alpha$ occurs in
$\tau$ or in an entry that $\tau$ depends on. (Note that the trivial exception
$\tau = \alpha$ is dealt with by the \textsc{Id} rule.) Since we only have one
type constructor symbol (the function arrow $\arrow$), there are no failures due
to rigid-rigid mismatch. Adding these would not significantly complicate matters,
however.

\begin{lemma}[Soundness of unification]
\label{lem:unifySound}
(a) If $\Junify{\Gamma_0}{\tau}{\upsilon}{\Gamma_1}$, then
$\Gamma_1 \entails \tau \equiv \upsilon$,
$\tyvars{\Gamma_0} = \tyvars{\Gamma_1}$ and
$\iota : \Gamma_0 \lei \Gamma_1$ where
$$\iota: \tyvars{\Gamma_0} \rightarrow \types{\Gamma_1} : \alpha \mapsto \alpha$$
is the inclusion substitution.

(b) Moreover, if
$\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\Xi}{\Gamma_1}$, then
$\Gamma_1 \entails \alpha \equiv \tau$,
$\tyvars{\Gamma_0, \Xi} = \tyvars{\Gamma_1}$
and $\iota : \Gamma_0, \Xi \lei \Gamma_1$.
\end{lemma}

\begin{proof}
By induction on the structure of derivations.
\end{proof}

\begin{lemma}[Completeness of unification]
\label{lem:unifyComplete}
(a) If $\theta : \Gamma_0 \lei \Delta$ and
$\Delta \entails \theta\tau \equiv \theta\upsilon$, then
$\Junify{\Gamma_0}{\tau}{\upsilon}{\Gamma_1}$ for some $\Gamma_1$ with
$\theta : \Gamma_1 \lei \Delta$. That is, if a unifier for $\tau$ and $\upsilon$
exists, then the algorithm succeeds and delivers a most general unifier.

(b) Moreover, if $\theta : \Gamma, \Xi \lei \Delta$ and
$\Delta \entails \theta\alpha \equiv \theta\upsilon$
where $\Xi$ contains only type variable declarations and $\upsilon$ is not a
variable, then $\Jinstantiate{\Gamma}{\alpha}{\upsilon}{\Xi}{\Gamma_1}$ for some
$\Gamma_1$ with $\theta : \Gamma_1 \lei \Delta$.
\end{lemma}

\begin{proof}
(a) Suppose $\theta : \Gamma_0 \lei \Delta$ and
$\Delta \entails \theta\tau \equiv \theta\upsilon$.
We examine the structure of $\tau$ and $\upsilon$, and proceed by induction on
the length of the context plus suffix, the length of the context alone,
and structurally on types.

If $\tau = \alpha = \upsilon$ are both the same variable,  then the \textsc{Id}
rule applies, $\Gamma_1 = \Gamma_0$ and the result is trivial.

Now suppose $\tau = \alpha$ and $\upsilon = \beta$ are distinct variables.
Let $\Gamma_0 = \Gamma_0', e$ and examine $e$:
\begin{itemize}
\item If $e = \hole{\alpha}$ then the
\textsc{Coalesce} rule applies and $\Gamma_1 = \Gamma_0', \alpha \defn \beta$. Now
$\theta : \Gamma_0 \lei \Delta$ preserves definitions in $\Gamma_0'$, and
$\Delta \entails \theta\alpha \equiv \theta\beta$ by hypothesis, so
$\theta : \Gamma_1 \lei \Delta$.
The case $e = \beta$ is similar.

\item If $e = \alpha \defn \upsilon$ then
$\Delta \entails \theta\alpha \equiv \theta \upsilon$, and
$\Delta \entails \theta\alpha \equiv \theta\beta$ by hypothesis,
hence $\Delta \entails \theta\beta \equiv \theta\upsilon$.
But then $\theta_\alpha : \Gamma_0' \lei \Delta$ and
$\Delta \entails \theta_\alpha\beta \equiv \theta_\alpha\upsilon$,
so by induction,
$\Junify{\Gamma_0'}{\beta}{\upsilon}{\Gamma_1'}$
for some $\Gamma_1'$ with $\theta_\alpha : \Gamma_1' \lei \Delta$.
Hence the \textsc{Expand} rule applies, $\Gamma_1 = \Gamma_1', \alpha \defn \upsilon$
and $\theta : \Gamma_1 \lei \Delta$.
The case $e = \beta \defn \upsilon$ is similar.

\item Otherwise, $e \perp \alpha \equiv \beta$ and the \textsc{Orthogonal} rule
applies by a similar argument.
\end{itemize}

Now suppose $\tau = \tau_0 \arrow \tau_1$ and $\upsilon = \upsilon_0 \arrow \upsilon_1$.
Then by induction, there are some contexts $\Gamma$ and $\Gamma_1$ such that
$\Junify{\Gamma_0}{\tau_0}{\upsilon_0}{\Gamma}$ and
$\Junify{\Gamma}{\tau_1}{\upsilon_1}{\Gamma_1}$, with
$\theta : \Gamma \lei \Delta$ and $\theta : \Gamma_1 \lei \Delta$. Hence
the \textsc{Arrow} rule applies.

Finally, suppose wlog that $\tau = \alpha$ is a variable and $\upsilon$ is not a variable.
By part (b), $\Jinstantiate{\Gamma_0}{\alpha}{\upsilon}{}{\Gamma_1}$ and
the \textsc{Instantiate} rule applies.

(b) Suppose $\theta : \Gamma, \Xi \lei \Delta$ and
$\Delta \entails \theta\alpha \equiv \theta\upsilon$
where $\Xi$ contains only type variable declarations and $\upsilon$ is not a variable.
Let $\Gamma = \Gamma_0, e$. We proceed by induction as before.

\TODO{We need to fill in some details here.}

\begin{itemize}
\item If $e = \hole{\alpha}$ and $\alpha \notin \FTV{\upsilon, \Xi}$, then the \textsc{Coalesce} rule
applies and $\Gamma_1 = \Gamma_0, \Xi, \alpha := \upsilon$. Now $\theta$ preserves 
definitions in $\Gamma_0, \Xi$ and $\Delta \entails \theta\alpha \equiv \theta\upsilon$
by hypothesis, so $\theta : \Gamma_1 \lei \Delta$.

\item If $e = \hole{\alpha}$ and $\alpha \in \FTV{\upsilon, \Xi}$...

\item If $e = \alpha \defn \tau$, then the \textsc{InstExpand} rule applies.

\item If $e = \beta \defn mt$ and $\beta \in \FTV{\upsilon, \Xi}$ then the \textsc{InstPass}
rule applies.

\item Otherwise $e \perp \alpha \equiv \tau [\Xi]$ and the \textsc{InstOrthogonal}
rule applies.
\qedhere
\end{itemize}
\end{proof}


\subsection{Implementation}

First, we define some helpful machinery.
The |onTop| operator applies its argument to the topmost type variable
definition in the context, skipping over any other kinds of entry. The argument
function may |restore| the previous entry by returning |Nothing|, or it may
return a context extension (that contains at least as much information as the
entry that has been removed) with which to |replace| it.

> onTop ::  (Name ::= Maybe Type -> Contextual (Maybe Suffix)) 
>             -> Contextual ()
> onTop f = do
>     e <- popEntry
>     case e of
>         delta := mt  -> do  m <- f (delta ::= mt)
>                             case m of
>                                 Just _Xi  -> modifyContext (<>< _Xi)
>                                 Nothing   -> modifyContext (:< e)
>         _            -> onTop f >> modifyContext (:< e)

> restore :: Contextual (Maybe Suffix)
> restore = return Nothing

> replace :: Suffix -> Contextual (Maybe Suffix)
> replace = return . Just


The |unify| function attempts to modify the context to produce a most general
unifier for the two given types; it will fail if the types cannot be
unified given the current state of the context.

> unify :: Type -> Type -> Contextual ()
> unify (V alpha) (V beta) = onTop $ \ (delta ::= mt) -> case
>           (delta == alpha,  delta == beta,  mt        ) of
>           (True,            True,           _         )  ->  restore                                 
>           (True,            False,          Nothing   )  ->  replace (alpha ::= Just (V beta) :> F0)  
>           (False,           True,           Nothing   )  ->  replace (beta ::= Just (V alpha) :> F0)  
>           (True,            False,          Just tau  )  ->  unify (V beta)   tau       >> restore   
>           (False,           True,           Just tau  )  ->  unify (V alpha)  tau       >> restore   
>           (False,           False,          _         )  ->  unify (V alpha)  (V beta)  >> restore   
> unify (V alpha)        tau                               =   instantiate alpha F0 tau
> unify tau              (V alpha)                         =   instantiate alpha F0 tau    
> unify (tau0 :-> tau1)  (upsilon0 :-> upsilon1)           =   unify tau0 upsilon0 >> unify tau1 upsilon1


The |instantiate| function attempts to unify a variable name with a
(non-variable) type, given a list of entries that the type depends on,
which must be placed into the context before it.

> instantiate :: Name -> Suffix -> Type -> Contextual ()
> instantiate alpha _Xi tau = onTop $ \ (delta ::= mt) -> 
>     let occurs = delta <? tau || delta <? _Xi in case
>     (delta == alpha,  occurs,  mt            ) of
>     (True,            True,    _             )  ->  fail "Occur check failed"
>     (True,            False,   Nothing       )  ->  replace (_Xi <+> (alpha ::= Just tau :> F0))
>     (True,            False,   Just upsilon  )  ->  modifyContext (<>< _Xi)
>                                                 >>  unify upsilon tau
>                                                 >>  restore
>     (False,           True,    _             )  ->  instantiate alpha (delta ::= mt :> _Xi) tau
>                                                 >>  replace F0   
>     (False,           False,   _             )  ->  instantiate alpha _Xi tau
>                                                 >>  restore


%%%The |(<?)| typeclass function tests if a name occurs in a type or context
%%%suffix, since these are both |Foldable| functors containing names.


\section{Type schemes}

A \define{type scheme} $\sigma$ is a type wrapped in one or more $\forall$
quantifiers or let bindings, with the syntax
$$\sigma ::= .\tau ~||~ \forall\alpha~\sigma ~||~ \letS{\alpha}{\tau}{\sigma}.$$
We use explicit definitions in type schemes to avoid the need for substitution
in the type inference algorithm. 

We define a new statement $\sigma \scheme$
% ($\sigma$ is a valid scheme in $\Gamma$)
by the rules in Figure~\ref{fig:schemeValidityRules}.
% We also observe the further sanity condition
% $\Gamma \entails \sigma \scheme$ implies $\Gamma \entails \valid$.

\begin{figure}[ht]
\boxrule{\Gamma \entails \sigma \scheme}

$$
\Rule{\tau \type}
     {.\tau \scheme}
\qquad
\Rule{\Sbind{\hole{\alpha}}{\sigma \scheme}}
     {\forall\alpha~\sigma \scheme}
$$

$$
\Rule{\upsilon \type   \quad  \Sbind{\alpha \defn \upsilon}{\sigma \scheme}}
     {\letS{\alpha}{\upsilon}{\sigma} \scheme}
$$

\caption{Rules for scheme validity}
\label{fig:schemeValidityRules}
\end{figure}


%if False

\TODO{Get rid of the specialisation judgment and specialise on lookup instead.}
The statement $\sigma \succ \tau$, defined in
Figure~\ref{fig:genericInstRules}, means that $\sigma$ has
generic instance $\tau$ obtained by substituting $\Delta$-types
for the generic variables of $\sigma$.

\begin{figure}[ht]
\boxrule{\Delta \entails \sigma \succ \tau}

$$
\Rule{\Delta \entails \tau \type}
     {\Delta \entails .\tau \succ \tau}
\qquad
\Rule{\Delta \entails \upsilon \type
      \quad
      \Delta \entails [\upsilon/\alpha]\sigma \succ \tau}
     {\Delta \entails \forall\alpha~\sigma \succ \tau}
$$

$$
\Rule{\Delta \entails [\upsilon/\alpha]\sigma \succ \tau}
     {\Delta \entails \letS{\alpha}{\upsilon}{\sigma} \succ \tau}
\qquad
\Rule{\Delta \entails \sigma \succ \tau
      \quad
      \Delta \entails \tau \equiv \upsilon}
     {\Delta \entails \sigma \succ \upsilon}
$$

\caption{Rules for generic instantiation}
\label{fig:genericInstRules}
\end{figure}

%endif


It is convenient to represent bound variables 
%%%using 
   by 
de Brujin indices and
free variables (i.e.\ those defined in the context) 
%%%using 
   by 
names. Moreover, we %%%can
use the Haskell type system to prevent some incorrect manipulations of 
%%%the 
indices by defining a natural number type

> data Index a = Z | S a

<     deriving (Functor, Foldable)

and representing schemes as

> data Schm a  =  Type (Ty a) 
>              |  All (Schm (Index a))
>              |  LetS (Ty a) (Schm (Index a))

<     deriving (Functor, Foldable)

> type Scheme = Schm Name

The outermost bound variable is represented by |Z| and the other variables
are wrapped in the |S| constructor. For example, the type scheme
$\forall\alpha\forall\beta.\beta \arrow 2$ is represented as

< All (All (Type (V (S Z) :-> V (S (S 2)))))

Note that the code forces us to distinguish a type $\tau$ and its corresponding
type scheme (written $.\tau$), as the latter will be represented by
|Type tau :: Scheme|.


\section{Making contexts more informative}

Now we can define another sort, $\TM \in \K$, with $\V_\TM$ some set of term
variables and $\D_\TM$ containing scheme assignments of the form $\asc \sigma$.
The statement $D \ok_\TM$ is easy to define:
$$\Rule{\sigma \scheme}
       {\asc \sigma \ok_\TM}.$$
Let $x$ range over term variables. 
We define the jugment $x \hasc \sigma$ by the rules in
Figure~\ref{fig:termVarSchemeRules}, and define
$\sem{x \asc \sigma}_\TM = \{ x \hasc \sigma \}$.
Thus a term variable has a scheme $\sigma'$ if it is given scheme $\sigma$ in
the context and $\sigma$ specialises to $\sigma'$.
\TODO{Do we need to permute quantifiers when specialising schemes?
For example, consider $\forall \alpha \forall \beta. \alpha \arrow \beta.$} 

\begin{figure}[ht]
\boxrule{\Gamma \entails x \hasc \sigma}
$$
\Rule{\upsilon \type   ~\wedge~   x \hasc \forall \alpha \sigma}
     {x \hasc \sigma[\upsilon/\alpha]}
\qquad
\Rule{x \hasc \letS{\alpha}{\upsilon}{\sigma}}
     {x \hasc \sigma[\upsilon/\alpha]}
$$
\caption{Rules for scheme assignment to term variables}
\label{fig:termVarSchemeRules}
\end{figure}


% Now we can give the full definition of context entries that we postponed earlier.
% As before, |alpha := mt| declares a type variable with name $\alpha$; this is the only
%%%kind of 
%    entry used in unification. A scheme assmignment |x ::: sigma| 
%%%defines 
%    declares 
% a term variable $x$ with type scheme $\sigma$. A |LetGoal| marker is used when
% inferring the type of let bindings, to make it easy to determine which variables
% can be generalised over.
% The term variable definitions and |LetGoal| markers will record information about
% progress through the structure of a term when inferring its type.

% Since the additional context entries are not used in unification, it is
% straightforward to extend the orthogonality statements: if $e = \letGoal$ or
% $e = x \asc \sigma$ we have $e \perp S$ for any $S$.
% We also extend the context validity statement with additional rules, as given in
% Figure~\ref{fig:additionalContextValidityRules}.

% \begin{figure}[ht]
% \boxrule{\Gamma \entails \valid}
% $$
% \Rule{\Gamma \entails \sigma \scheme}
%      {\Gamma, x \asc \sigma \entails \valid}
% \qquad
% \Rule{\Gamma \entails \valid}
%      {\Gamma, \letGoal \entails \valid}
% $$
% \caption{Additional rules for context validity}
% \label{fig:additionalContextValidityRules}
% \end{figure}

% Note that term variable names are not necessarily unique, so the most recent
% definition of a name will shadow previous occurences. Thus we define
% $\Gamma \entails x \asc \sigma$ to mean that $x \asc \sigma \in \Gamma$ and
% moreover that this is the rightmost (i.e.\ most local) occurrence of $x$.

The full data type of context entries is thus:

> data Entry  =  Name := Maybe Type
>             |  TermName ::: Scheme
>             |  LetGoal


\section{Type scheme operations}

\subsection{Specialisation}

The judgment $\Jspec{\Gamma}{\sigma}{\tau}{\Gamma, \Xi}$ means
that, starting with the context $\Gamma$, the scheme $\sigma$ specialises
to the type $\tau$ when the context is extended with some type variable
definitions $\Xi$. This judgment
is defined as shown in Figure~\ref{fig:specialiseAlgorithm}.

\begin{figure}[ht]
\boxrule{\Jspec{\Gamma}{\sigma}{\tau}{\Gamma, \Xi}}

$$
\name{T}
\Rule{\Gamma \entails \tau \type}
     {\Jspec{\Gamma}{.\tau}{\tau}{\Gamma}}
$$

$$
\name{All}
\Rule{\Jspec{\Gamma, \hole{\alpha}}{\sigma}{\tau}{\Gamma, \hole{\alpha}, \Xi}}
     {\Jspec{\Gamma}{\forall\alpha~\sigma}{\tau}{\Gamma, \hole{\alpha}, \Xi}}
\side{\alpha \fresh}
$$

$$
\name{LetS}
\Rule{\Jspec{\Gamma, \alpha \defn \upsilon}{\sigma}{\tau}
            {\Gamma, \alpha \defn \upsilon, \Xi}}
     {\Jspec{\Gamma}{\letS{\alpha}{\upsilon}{\sigma}}{\tau}
            {\Gamma, \alpha \defn \upsilon, \Xi}}
\side{\alpha \fresh}
$$

\caption{Algorithmic rules for specialisation}
\label{fig:specialiseAlgorithm}
\end{figure}


We define $\Jhast{\Gamma_0}{x}{\tau}{\Gamma_1}$ to mean
$\Gamma_0 \entails x \hasc \sigma$ and
$\Jspec{\Gamma_0}{\sigma}{\tau}{\Gamma_1}$.


\begin{lemma}[Soundness of specialisation]
\label{lem:specialiseSound}
If $\Jhast{\Gamma_0}{x}{\tau}{\Gamma_1}$, then
$\Gamma_1 \entails x \hasc .\tau$,
$\tyvars{\Gamma_0} \subseteq \tyvars{\Gamma_1}$ and
$\iota : \Gamma_0 \lei \Gamma_1$.
\end{lemma}

\begin{proof}
By structural induction on $\sigma$.
\end{proof}

\begin{lemma}[Completeness of specialisation]
\label{lem:specialiseComplete}
If $\Gamma \entails x \hasc \sigma$ then
$\Jhast{\Gamma}{x}{\tau}{\Gamma, \Xi}$
for some type $\tau$ and list of type variable declarations $\Xi$.

% $$\forall \upsilon \forall \phi : \Gamma \lei \Phi . (
%     \Phi \entails \phi\sigma \succ \upsilon
%        \Leftrightarrow  \Phi \entails \phi\gen{\Xi}{\tau} \succ \upsilon).$$

% If $\theta_0 : \Gamma_0 \lei \Delta$, $\Gamma_0 \entails \sigma \scheme$ and
% $\Delta \entails \theta_0\sigma \succ \tau$,
% then $\Gamma_0 \extend \sigma \succ \upsilon \yields \Gamma_1$ for some type
% $\upsilon$ and context $\Gamma_1$ with $\theta_1 : \Gamma_1 \lei \Delta$,
% \Delta \entails \tau \equiv \theta_1\upsilon$ and
% $\forall \alpha \in \tyvars{\Gamma_0} .
%    \Delta \entails \theta_0 \alpha \equiv \theta_1 \alpha$.
\end{lemma}

\begin{proof}

\end{proof}

\begin{lemma}[Minimality of specialisation]
\label{lem:specialiseMinimal}
Define the problem $P_x(\tau) = x \hasc .\tau$.
If $\Jhast{\Gamma}{x}{\tau}{\Gamma, \Xi}$ then
$\Jmin{\Gamma}{P(x)(\tau)}{\Gamma, \Xi}$.
\end{lemma}

\begin{proof}
Suppose $\theta : \Gamma \lei \Theta \entails P(x)(\upsilon)$.
By stability, $\Theta \entails x \hasc \sigma$.
Examining the rules in Figure~\ref{fig:termVarSchemeRules}, the proof of
$\Theta \entails x \hasc .\tau$ must specialise $\sigma$ with types
$\Psi$ for its generic variables. Let $\theta' = \theta[\Psi/\Xi]$, then
$\theta' : \Gamma, \Xi \lei \Theta$ and $\theta = \theta' \compose \iota$.
\end{proof}


The |freshVar| function generates a fresh name for a type variable and defines it as unbound,
and the |freshDef| function generates a fresh name and binds it to the given type.

> freshen :: Maybe Type -> Contextual Name
> freshen mt = do  (beta, _Gamma) <- get
>                  put (fresh beta _Gamma, _Gamma :< beta := mt)
>                  return beta

> freshVar :: Contextual Name
> freshVar = freshen Nothing

> freshDef :: Type -> Contextual Name
> freshDef = freshen . Just

The |specialise| function will specialise a type scheme with fresh variables
to produce a type. That is, given a scheme $\sigma$ it computes a most general
type $\tau$ such that $\sigma \succ \tau$.

> specialise :: Scheme -> Contextual Type

If a $\forall$ quantifier is outermost, it is removed and an unbound fresh type variable
is substituted in its place (applying the \textsc{All} rule).

> specialise (All sigma) = do
>     alpha <- freshVar
>     specialise (schemeUnbind alpha sigma)

If a let binding is outermost, it is removed and added to the context with a fresh
variable name (applying the \textsc{LetS} rule).

> specialise (LetS tau sigma) = do
>     alpha <- freshDef tau
>     specialise (schemeUnbind alpha sigma)

This continues until a scheme with no quantifiers is reached, which can simply be
converted into a type (applying the \textsc{T} rule).

> specialise (Type tau) = return tau


The |schemeUnbind alpha sigma| function converts the body $\sigma$ of the scheme
$\forall\beta.\sigma$ or $\letS{\beta}{\tau}{\sigma}$ into $\sigma[\alpha/\beta]$.

> schemeUnbind :: Name -> Schm (Index Name) -> Scheme
> schemeUnbind alpha = fmap fromS
>   where
>     fromS :: Index Name -> Name
>     fromS Z          = alpha
>     fromS (S delta)  = delta


\subsection{Generalisation}

We write $\gen{\Xi}{\sigma}$ for the generalisation of the type scheme $\sigma$
over the list of type variable declarations $\Xi$. This is defined as follows:
\begin{align*}
\emptycontext         &\genarrow \sigma = \sigma  \\
\Xi, \hole{\alpha}    &\genarrow \sigma = \Xi \genarrow \forall\alpha~\sigma  \\
\Xi, \alpha \defn \nu &\genarrow \sigma = \Xi \genarrow \letS{\alpha}{\nu}{\sigma}
\end{align*}

\begin{lemma}
\label{lem:generalise}
If $\Gamma, \Xi \entails \sigma \scheme$ where $\Xi$ contains only type variable
definitions, then $\Gamma \entails \gen{\Xi}{\sigma} \scheme$.
\end{lemma}
\begin{proof}
By induction on the length of $\Xi$.
\end{proof}


Implementing the generalisation function is straightforward:

> (>=>) :: Bwd (Name ::= Maybe Type) -> Scheme -> Scheme
> B0                      >=> sigma = sigma
> (_Xi :< alpha ::=  mt)  >=> sigma = case mt of
>                    Nothing  -> _Xi >=> All sigma'
>                    Just nu  -> _Xi >=> LetS nu sigma'
>   where 
>     sigma' = fmap bind sigma
>     bind beta  | alpha == beta  = Z
>                | otherwise      = S beta


The |generaliseOver| operator appends a |LetGoal| marker to the context,
evalutes its argument, then generalises over the type variables
to the right of the |LetGoal| marker.

> generaliseOver ::  Contextual Type -> Contextual Scheme
> generaliseOver f = do
>     modifyContext (:< LetGoal)
>     tau <- f
>     _Xi <- skimContext
>     return (_Xi >=> Type tau)
>   where
>     skimContext :: Contextual (Bwd (Name ::= Maybe Type))
>     skimContext = do
>         e <- popEntry
>         case e of
>             LetGoal      -> return B0
>             alpha := mt  -> (:< alpha ::= mt) <$> skimContext
>             _ ::: _      -> undefined


\section{Type inference}

The syntax of terms is
$$t ::= x ~||~ t~t ~||~ \lambda x . t ~||~ \letIn{x}{t}{t}.$$
% where $x$ ranges over some set of term variables.

We define the type assignability statement $t : \tau$ by the rules in
Figure~\ref{fig:typeAssignmentRules}, and the scheme assignability statement
$t \hasscheme \sigma$ for arbitrary terms $t$ thus:
\begin{align*}
t \hasscheme .\tau   &\mapsto    t : \tau  \\
t \hasscheme \forall \alpha \sigma  &\mapsto 
    \Sbind{\hole{\alpha}}{t \hasscheme \sigma}   \\
t \hasscheme \letS{\alpha}{\tau}{\sigma}  &\mapsto
    \Sbind{\alpha \defn \tau}{t \hasscheme \sigma}
\end{align*}

\begin{figure}[ht]
\boxrule{\Delta \entails t : \tau}

$$
\Rule{t : \tau
      \quad
      \tau \equiv \upsilon}
     {t : \upsilon}
\qquad
\Rule{x \hasc .\tau}
     {x : \tau}
$$

$$
\Rule{\Sbind{x \asc .\upsilon}{t : \tau}}
     {\lambda x.t : \upsilon \arrow \tau}
\qquad
\Rule{f : \upsilon \arrow \tau
      \quad
      a : \upsilon}
     {f a : \tau}
$$

%      \forall \upsilon . (\Gamma \entails \sigma \succ \upsilon
%              \Rightarrow \Gamma \entails s : \upsilon)

$$
\Rule{
      s \hasscheme \sigma
      \quad
      \Sbind{x \asc \sigma}{t : \tau}
     }
     {\letIn{x}{s}{t} : \tau}
$$

\caption{Declarative rules for type assignment}
\label{fig:typeAssignmentRules}
\end{figure}


%if False

Now we can extend the $\lei$ relation to ensure that more informative contexts
preserve term information. First, let $\forget{\cdot}$ be the forgetful map from
contexts to lists of term names and |LetGoal| markers that discards type and
scheme information:
\begin{align*}
\forget{\emptycontext}         &= \emptycontext  \\
\forget{\Gamma, \alpha := \_}  &= \forget{\Gamma}  \\
\forget{\Gamma, x \asc \sigma} &= \forget{\Gamma} , x  \\
\forget{\Gamma, \letGoal}      &= \forget{\Gamma} , \letGoal
\end{align*}

We write $\theta : \Gamma \lei \Delta$ if
\begin{enumerate}[(a)]
\item $\Gamma \entails \alpha \defn \tau   \Rightarrow
           \Delta \entails \theta\alpha \equiv \theta\tau$,
\item $\Gamma \entails x \asc \sigma  \Rightarrow
           \forall \tau. (\Delta \entails \theta\sigma \succ \tau 
               \Rightarrow  \Delta \entails x : \tau)$ and
\item $\forget{\Gamma}$ is a prefix of $\forget{\Delta}$.
\end{enumerate}

We write $\theta : \Gamma \LEI \Delta$ if $\theta : \Gamma \lei \Delta$ and
$$\Gamma \entails x \asc \sigma  \Rightarrow
           \forall \tau. (\Delta \entails x : \tau
               \Rightarrow   \Delta \entails \theta\sigma \succ \tau).$$

It is straightforward to verify that the previous results go through using the
extended definition of the $\lei$ relation, since the unification algorithm
ignores term variables and $\letGoal$ markers completely.

As we have previously observed, condition (a) means that type equations are
preserved by information increase, as
$$\theta : \Gamma \lei \Delta  \wedge  \Gamma \entails \tau \equiv \upsilon
    \Rightarrow  \Delta \entails \theta\tau \equiv \theta\upsilon.$$
The new conditions ensure that type assignment is preserved:

\begin{lemma}
\label{lem:typeAssignmentPreserved}
If $\theta : \Gamma \lei \Delta$ and $\Gamma \entails t : \tau$ then
$\Delta \entails t : \theta\tau$.
\end{lemma}

A term $t$ \define{can be assigned type scheme} $\sigma$ in context $\Gamma$,
written $\Gamma \entails t \hasscheme \sigma$, if
$$\forall \tau . \forall \theta : \Gamma \lei \Delta . (
    \Delta \entails \theta\sigma \succ \tau
        \Rightarrow \Delta \entails t : \tau )$$ 
and $\sigma$ is \define{principal} if, additionally,
$$\forall \tau . \forall \theta : \Gamma \LEI \Delta . (
    \Delta \entails t : \tau
        \Rightarrow  \Delta \entails \theta\sigma \succ \tau).$$


\begin{lemma}
\label{lem:suffixSchemeEquivalence}
Let $\Gamma$ be a context and $\Xi$ a list of type variable declarations such
that $\Gamma, \Xi$ is a valid context. For any term $t$ and type $\tau$,
$$\Gamma, \Xi \entails t : \tau
    \Leftrightarrow    \Gamma \entails t \hasscheme \gen{\Xi}{\tau}.$$
\end{lemma}

\begin{proof}

\end{proof}

%endif


As with unification, we wish to translate these declarative rules into an
algorithm for type inference. 
% For each term $t$, we define the problem
% $\Pinf{t}$ on types with equivalence by $\Pinf{t}(\tau) = t : \tau$,
% and we seek an algorithm to find a minimal solution of $\Pinf{t}$.
We define the type inference problem $\Pinf{}$ by
\begin{align*}
\In{\Pinf{}} &= Term  \\
\Out{\Pinf{}} &= Type  \\
\Pre{\Pinf{}}(t) &= \valid  \\
\Post{\Pinf{}}(t)(\tau) &= t : \tau  \\
\R{\Pinf{}}(\tau)(\upsilon) &= \tau \equiv \upsilon
\end{align*}

To transform a rule into an algorithmic form, we proceed clockwise starting from
the conclusion. For each hypothesis, we must ensure that the problem is fully
specified, inserting variables to stand for unknown problem inputs. Moreover, we
cannot pattern match on problem outputs, so we ensure there are schematic variables
in output positions, fixing things up with appeals to unification. 

Consider the rule for application, written to highlight problem inputs and outputs
as
$$\Rule{\Pinf{f}(\upsilon \arrow \tau)    \quad \Pinf{a}(\upsilon)}
       {\Pinf{f a}(\tau)}.$$
We change this to the equivalent form
$$\Rule{\Pinf{f}(\chi)
        \quad
        \Pinf{a}(\upsilon)
        \quad
        \Sbind{\beta \defn \tau}{\chi \equiv \upsilon \arrow \beta}
       }
       {\Sbind{\beta \defn \tau}{\Pinf{f a}(\beta)}}$$
assuming $\beta$ is a fresh variable. Now the algorithmic version uses input and
output contexts, with $\beta$ initially unknown:
$$
\Rule{\Jtype{\Gamma_0}{f}{\chi}{\Gamma_1}
         \quad
         \Jtype{\Gamma_1}{a}{\upsilon}{\Gamma_2}
         \quad
         \Junify{\Gamma_2, \hole{\beta}}{\chi}{\upsilon \arrow \beta}{\Gamma_3}}
        {\Jtype{\Gamma_0}{f a}{\beta}{\Gamma_3}}
$$

The rule for abstraction is
$$\Rule{\Sbind{x \asc .\upsilon}{\Pinf{t}(\tau)}}
       {\Pinf{\lambda x . t}(\upsilon \arrow \tau)}$$
which is transformed to
$$\Rule{\Sbind{\beta \defn \upsilon}{\Sbind{x \asc .\beta}{\Pinf{t}(\tau)}}}
       {\Sbind{\beta \defn \upsilon}{\Pinf{\lambda x . t}(\beta \arrow \tau)}}$$
and hence
$$
\Rule{\Jtype{\Gamma_0, \hole{\beta}, x \asc .\beta}{t}{\tau}
          {\Gamma_1, x \asc .\beta, \Xi}}
     {\Jtype{\Gamma_0}{\lambda x.t}{\beta \arrow \tau}{\Gamma_1, \Xi}}
$$

The variable rule is
$$\Rule{x \hasc .\tau}
       {\Pinf{x}(\tau)}$$

The let rule is
$$
\Rule{
      s \hasscheme \sigma
      \quad
      \Sbind{x \asc \sigma}{t : \tau}
     }
     {\Pinf{\letIn{x}{s}{t}}(\tau)}
$$
which we transform to
$$
\Rule{
      \fatsemi (s : \upsilon)
      \quad
      x \asc \upsilon \Yup t : \tau
     }
     {\Pinf{\letIn{x}{s}{t}}(\tau)}
$$
where $\Yup$ is defined via
$$
\Rule{\Gamma \entails \Sbind{x \asc \gen{\Xi}{\sigma}}{S}}
     {\Gamma \fatsemi \Xi \entails x \asc \upsilon \Yup S}
$$

Now we define the type inference judgment $\Jtype{\Gamma_0}{t}{\tau}{\Gamma_1}$
% (inferring the type of $t$ in $\Gamma_0$ yields $\tau$ in the more informative
% context $\Gamma_1$)
by the rules in Figure~\ref{fig:inferRules}.

\begin{figure}[ht]
\boxrule{\Jtype{\Gamma_0}{t}{\tau}{\Gamma_1}}

$$
\name{Var}
\Rule{\Jhast{\Gamma_0}{x}{\tau}{\Gamma_1}}
     {\Jtype{\Gamma_0}{x}{\tau}{\Gamma_1}}
$$

$$
\name{Abs}
\Rule{\Jtype{\Gamma_0, \hole{\alpha}, x \asc .\alpha}{t}{\tau}
          {\Gamma_1, x \asc .\alpha, \Xi}}
     {\Jtype{\Gamma_0}{\lambda x.t}{\alpha \arrow \tau}{\Gamma_1, \Xi}}
\side{\alpha \fresh}
$$

$$
\name{App}
\BigRule{\Jtype{\Gamma_0}{f}{\chi}{\Gamma_1}
         \quad
         \Jtype{\Gamma_1}{a}{\upsilon}{\Gamma_2}}
        {\Junify{\Gamma_2, \hole{\beta}}{\chi}{\upsilon \arrow \beta}{\Gamma_3}}
        {\Jtype{\Gamma_0}{f a}{\beta}{\Gamma_3}}
\side{\beta \fresh}
$$

$$
\name{Let}
\BigRule{\Jtype{\Gamma_0 \fatsemi}{s}{\tau_0}{\Gamma \fatsemi \Xi_0}}
        {\Jtype{\Gamma, x \asc \gen{\Xi_0}{.\tau_0}}{t}{\tau_1}
               {\Gamma_1, x \asc \gen{\Xi_0}{.\tau_0}, \Xi_1}}
        {\Jtype{\Gamma_0}{\letIn{x}{s}{t}}{\tau_1}{\Gamma_1, \Xi_1}}
$$

\caption{Algorithmic rules for type inference}
\label{fig:inferRules}
\end{figure}


We say $\Theta$ is a \define{subcontext} of $\Gamma$, written
$\Theta \subcontext \Gamma$, if $\Gamma = \Theta; \Gamma'$ for some context
extension $\Gamma'$.


\begin{lemma}[Soundness of type inference]
\label{lem:inferSound}
If $\Jtype{\Gamma_0}{t}{\tau}{\Gamma_1}$, then
\begin{enumerate}[(a)]
\item $\Gamma_1 \entails t : \tau$;
\item $\tyvars{\Gamma_0} \subseteq \tyvars{\Gamma_1}$; and
% \item $\forget{\Gamma_0} = \forget{\Gamma_1}$;
\item $\iota : \Gamma_0 \lei \Gamma_1$, where $\iota$ is the inclusion
      substitution.
% \item if $\Theta_0 \subcontext \Gamma_0$ and $\Theta_1 \subcontext \Gamma_1$
% are such that
%    $\forget{\Theta_0} = \forget{\Theta_1}$, then
%    $\tyvars{\Theta_0} \subseteq \tyvars{\Theta_1}$ and
%    $\iota : \Theta_0 \lei \Theta_1$.
\end{enumerate}
\end{lemma}

\begin{proof}
By induction on the structure of derivations.
\end{proof}

%if False

\begin{lemma}[Completeness of type inference]
\label{lem:inferComplete}
If $\theta_0 : \Gamma_0 \lei \Delta$,
   $\Delta \entails t : \tau$ and
   $\tmvars{\Gamma_0} = \tmvars{\Delta}$
then there exists a type $\upsilon$ and a pair $(\Gamma_1, \theta_1)$ such that
$\Gamma_0 \extend t:\upsilon \yields \Gamma_1$,
$\theta_1 : \Gamma_1 \lei \Delta$,
$\Delta \entails \theta_1 \upsilon \equiv \tau$ and
$\forall \alpha \in \tyvars{\Gamma_0} . \Delta \entails \theta_0 \alpha \equiv \theta_1 \alpha$.
\end{lemma}

\begin{proof}
Suppose $\theta_0 : \Gamma_0 \lei \Delta$ and $\Delta \entails t : \tau$.
We proceed by induction on the structure of $t$:

\begin{itemize}
\item If $t = x$ is a variable, then since $\Delta \entails t : \tau$
we must have $x \asc \sigma \in \Delta$, $\Delta \entails \sigma \succ \tau'$ and
$\Delta \entails \tau \equiv \tau'$ for some type $\tau'$.
Now $\Gamma_0 \entails x \asc \sigma'$ for some $\sigma'$ with
$\Delta \entails \theta_0\sigma' \succ \tau$, so
by completeness of specialisation (lemma~\ref{lem:specialiseComplete}),
$\Gamma_0 \extend \sigma' \succ \upsilon \yields \Gamma_1$
for some $\upsilon$, $\Gamma_1$ and $\theta_1$
with $\Delta \entails \theta_1\upsilon \equiv \tau$.
Hence the \textsc{Var} rule applies.


\item If $t = \lambda x . w$ is an abstraction, then $\Delta \entails \tau \equiv \tau_0 \arrow \tau_1$
where $\tau_0$ and $\tau_1$ are some $\Delta$-types, and
$\Delta, x \asc .\tau_0 \entails w : \tau_1$.
Taking $\theta_1 = [\tau_0/\alpha]\theta_0$, we have that
$\theta_1 : \Gamma_0, \hole{\alpha}, x \asc .\alpha  \lei  \Delta, x \asc .\tau_0$
and hence
$\Gamma_0, \hole{\alpha}, x \asc .\alpha \extend w : \upsilon \yields \Gamma_1, x \asc .\alpha, \Xi$
for some $\upsilon, \Gamma_1, \Xi$ with $\Delta \entails \theta_1\upsilon \equiv \tau_1$ by induction.
Thus the \textsc{Abs} rule applies, so
$\Gamma_0 \extend \lambda x . w : \alpha \arrow \upsilon \yields \Gamma_1, \Xi$.
Moreover
$\Delta \entails \theta_1(\alpha \arrow \upsilon)
                      \equiv \theta_1\alpha \arrow \theta_1\upsilon
                      \equiv \tau_0 \arrow \tau_1
                      \equiv \tau$.


\item If $t = f a$ is an application, then
$\Delta \entails f : \tau_0 \arrow \tau$
so by induction
$\Gamma_0 \extend f : \upsilon \yields \Gamma$
where $\theta : \Gamma \lei \Delta$ and $\Delta \entails \theta\upsilon \equiv \tau_0 \arrow \tau$.
Now $\Delta \entails a : \tau_0$ so by induction
$\Gamma \extend a : \upsilon_0 \yields \Gamma_1$
where $\theta' : \Gamma_1 \lei \Delta$ and $\Delta \entails \theta'\upsilon_0 \equiv \tau_0$.

Let $\theta_1 = [\tau_1/\beta]\theta'$, then $\theta_1 : \Gamma_1, \hole{\beta} \lei \Delta$,
and since $\Delta \entails \theta_1\upsilon \equiv \tau_0 \arrow \tau \equiv \theta_1(\upsilon_0 \arrow \beta)$
we have $\Gamma_1, \hole{\beta} \extend \upsilon \equiv \upsilon \arrow \beta \yields \Gamma_2$
by completeness of unification.

Hence the \textsc{App} rule applies, so
$\Gamma_0 \extend f a : \beta \yields \Gamma_2$;
moreover $\Delta \entails \theta_1\beta \equiv \tau$ by definition.


\item If $t = \letIn{x}{s}{w}$ is a let binding, then there is some $\Delta$-scheme $\sigma$
such that $\Delta, x \asc \sigma \entails w : \tau$. Extend the context $\Delta, \letGoal$
with fresh type variables to produce a context $\Phi$ and generic instance $\upsilon$ of
$\sigma$. Then $\iota : \Gamma \lei \Phi$ and $\Phi \entails \sigma \succ \upsilon$ so
$\Phi \entails s : \upsilon$.

By induction, $\Gamma_0, \letGoal \extend s : \tau_0 \yields \Gamma_1, \letGoal, \Xi$.
Now $\Gamma_1 \entails \gen{\Xi}{\tau_0} \scheme$ by lemma~\ref{lem:generalise}.
Moreover $\Gamma_1, x \asc \gen{\Xi}{\tau_0} \lei \Delta, x \asc \sigma$ since ???.
By induction,
$\Gamma_1, x \asc \gen{\Xi}{\tau_0} \extend w : \tau_1 \yields \Gamma_2, x \asc \_, \Delta$.
\end{itemize}
\end{proof}


\begin{lemma}[Completeness of type inference 2]
If $\theta_0 : \Gamma_0; \Xi_0 \lei \Delta_0$ and $\Delta_0 \entails t : \tau_0$, then
\begin{enumerate}
\item $\Gamma_0; \Xi_0 \extend t : \upsilon \yields \Gamma_1; \Xi_1$
\item $\theta_1 : \Gamma_1; \Xi_1 \lei \Delta_0$
\item $\forall \tau . \forall \theta : \Gamma_1 \lei \Delta .
          (\Delta \entails t : \tau  \Leftrightarrow
               \Delta \entails \theta \gen{\Xi_1}{\upsilon} \succ \tau)$
\end{enumerate}
\end{lemma}

\begin{proof}
We proceed by induction on the structure of $t$.

\begin{itemize}
\item If $t = x$ is a variable, then by inversion
$\Delta_0 \entails x \asc \sigma_0$ and $\Delta_0 \entails \sigma_0 \succ \tau_0$.
Then $\Gamma_0 \entails x \asc \sigma$ by definition of $\lei$ and the fact
that $\Xi_0$ contains only type variables. By completeness of specialisation, we have
$\Gamma_0; \Xi_0 \extend \sigma \succ \upsilon \yields \Gamma_0; \Xi_0, \Xi_1$
and
$$\forall \tau . \forall \theta : \Gamma_0 \lei \Delta .
              (\Delta \entails \theta\sigma \succ \tau  \Leftrightarrow
                  \Delta \entails \theta \gen{\Xi_0, \Xi_1}{\upsilon} \succ \tau).$$
Now the \textsc{Var} rule applies so
$\Gamma_0; \Xi_0 \extend x : \upsilon \yields \Gamma_0; \Xi_0, \Xi_1$
and by definition of $\lei$,
$\Delta \entails \theta\sigma \succ \tau  \Leftrightarrow
     \Delta \entails x : \tau$.

\item If $t = \lambda x . w$ is a $\lambda$-abstraction, then by inversion
$\Delta_0 \entails \tau \equiv \tau_0 \arrow \tau_1$ and
$\Delta_0, x \asc .\tau_0 \entails w : \tau_1$ where $\tau_0$ and $\tau_1$ are
some $\Delta_0$-types.
Taking $\theta_1 = [\tau_0/\alpha]\theta_0$, we have that
$$\theta_1 : \Gamma_0; \Xi_0, \hole{\alpha}, x \asc .\alpha;  \lei  \Delta_0, x \asc .\tau_0$$
and hence, by induction,
$$\Gamma_0; \Xi_0, \hole{\alpha}, x \asc .\alpha; \extend w : \upsilon \yields \Gamma_1; \Xi, x \asc .\alpha; \Xi_1$$
for some $\upsilon, \Gamma_1, \Xi_1$ with
$$\forall \tau . \forall \theta : \Gamma_1; \Xi, x \asc .\alpha \lei \Delta .
          (\Delta \entails w : \tau  \Leftrightarrow
               \Delta \entails \theta \gen{\Xi_1}{\upsilon} \succ \tau).$$

Now the \textsc{Abs} rule applies so
$$\Gamma_0; \Xi_0 \extend \lambda x . w : \alpha \arrow \upsilon \entails \Gamma_1; \Xi, \Xi_1$$
and we need to prove
$$\forall \tau . \forall \theta : \Gamma_1 \lei \Delta .
          (\Delta \entails \lambda x . w : \tau  \Leftrightarrow
               \Delta \entails \theta \gen{\Xi, \Xi_1}{\alpha \arrow \upsilon} \succ \tau).$$

Fix $\tau$ and $\theta : \Gamma_1 \lei \Delta$ such that
$\Delta \entails \tau \equiv \tau_0 \arrow \tau_1$. First suppose that
$\Delta \entails \theta \gen{\Xi, \Xi_1}{\alpha \arrow \upsilon} \succ \tau_0 \arrow \tau_1$. By a lemma (to prove), there is some
$\psi : \Gamma_1, \Xi \lei \Delta$ with
$\Delta \entails \psi \gen{\Xi_1}{.\alpha \arrow \upsilon} \succ \tau_0 \arrow \tau_1$.
Now $\alpha \defn \_ \notin \Xi_1$ so $\Delta \entails \alpha \equiv \tau_0$,
so $\psi : \Gamma_1, \Xi, x \asc .\alpha \lei \Delta, x \asc .\tau_0$.
Moreover $\Delta, x \asc .\tau_0 \entails \psi \gen{\Xi_1}{\upsilon} \succ \tau_1$ so
$\Delta, x \asc .\tau_0 \entails w : \tau_1$.
Hence $\Delta \entails \lambda x . w : \tau_0 \arrow \tau_1$.

Conversely, suppose $\Delta \entails \lambda x . w : \tau$. Then
$\Delta \entails \tau \equiv \tau_0 \arrow \tau_1$ and
$\Delta, x \asc .\tau_0 \entails w : \tau_1$.

\item If $t = \letIn{x}{u}{w}$ is a let-binding, then by inversion there is some
$\Delta$-scheme $\sigma$ such that
$$\forall \upsilon \Phi . (\theta : \Delta \lei \Phi
          \wedge \Phi \entails \theta\sigma \succ \upsilon
              \Rightarrow \Phi \entails u : \upsilon)$$
and
$\Delta, x \asc \sigma \entails w : \tau$. 
\end{itemize}
\end{proof}

\begin{lemma}
If $\theta : \Gamma \lei \Delta$, $\Gamma; \Xi, \Xi' \entails \tau \type$
and $\Delta \entails \theta \gen{\Xi, \Xi'}{.\tau} \succ \upsilon$, then
there exists $\psi : \Gamma; \Xi \lei \Delta$ such that
$\Delta \entails \psi \gen{\Xi'}{.\tau} \succ \upsilon$.
\end{lemma}


\begin{lemma}[Completeness of specialisation]
If $\Gamma \entails \sigma \scheme$ then
\begin{enumerate}[(a)]
\item $\Gamma; \extend \sigma \succ \upsilon \yields \Gamma; \Xi$
\item $\forall \tau' . \forall \phi : \Gamma; \lei \Phi . (
    \Phi \entails \phi \gen{\Xi}{\upsilon} \succ \tau'
        \Leftrightarrow \Phi \entails \sigma \succ \tau' )$
\end{enumerate}
\end{lemma}

\begin{lemma}[Completeness of type inference]
If $\theta_0 : \Gamma_0; \lei \Delta;$ and $\Delta; \Lambda \entails t : \tau$
then
\begin{enumerate}[(a)]
\item $\Gamma_0; \extend t : \upsilon \yields \Gamma_1; \Xi$
\item $\theta_1 : \Gamma_1; \lei \Delta;$
\item $\forall \tau' . \forall \phi : \Gamma_1; \lei \Phi . (
          \Phi \entails \phi \gen{\Xi}{\upsilon} \succ \tau'
          \Leftrightarrow \Phi \entails t : \tau' )$
\end{enumerate}
\end{lemma}

\begin{proof}
If $t = x$ is a variable, then by inversion $\Delta \entails x \asc \sigma$ and
$\Delta; \Lambda \entails \sigma \succ \tau$. Now by definition of $\lei$,
$\Gamma_0 \entails x \asc \sigma'$ for some $\sigma'$ with
$$\forall \upsilon . \Delta; \Lambda \entails \theta_0\sigma' \succ \upsilon
    \Leftrightarrow  \Delta; \Lambda \entails x : \upsilon
    \Leftrightarrow  \Delta; \Lambda \entails \sigma \succ \upsilon.$$
By completeness of specialisation,
$\Gamma_0; \extend \sigma' \succ \upsilon \yields \Gamma_0; \Xi$
and hence the \textsc{Var} rule applies giving
$\Gamma_0; \extend x : \upsilon \yields \Gamma_0; \Xi$.
Moreover, (b) holds trivially with $\theta_1 = \theta_0$ and
(c) holds by completeness of specialisation.

If $t = (\letIn{x}{t}{w})$, then by inversion there is some scheme
$\sigma$ such that $\Delta; \Lambda, x \asc \sigma; \entails w : \tau$.
Let $\Psi$ be a list of fresh type variables so that
$\Delta; \Lambda, \letGoal; \Psi \entails \sigma \succ (\Psi \Downarrow \sigma)$
and hence
$\Delta; \Lambda, \letGoal; \Psi \entails t : (\Psi \Downarrow \sigma)$.
Moreover $\theta_0 : \Gamma_0; \letGoal; \lei \Delta; \Lambda, \letGoal;$ so
by induction
\begin{enumerate}[(a)]
\item $\Gamma_0; \letGoal; \extend t : \upsilon_t \yields \Gamma_1; \letGoal; \Xi_1$
\item $\theta_1 : \Gamma_1; \letGoal; \lei \Delta; \Lambda, \letGoal;$
\item $\forall \tau' . \forall \phi : \Gamma_1; \letGoal; \lei \Phi . (
    \Phi \entails \phi \gen{\Xi_1}{\upsilon_t} \succ \tau'
        \Leftrightarrow  \Phi \entails t : \tau'$
\end{enumerate}

Now in particular, for any type $\tau'$, we have
$$\Delta; \Lambda, \letGoal; \entails \theta_1\gen{\Xi_1}{\upsilon_t} \succ \tau'
    \Leftrightarrow \Delta; \Lambda, \letGoal; \entails \sigma \succ \tau'$$
so
$$\Delta; \Lambda \entails \theta_1\gen{\Xi_1}{\upsilon_t} \succ \tau'
    \Leftrightarrow \Delta; \Lambda \entails \sigma \succ \tau'$$
and hence
$$\theta_1 : \Gamma_1; x \asc \gen{\Xi_1}{\upsilon_t}; \lei \Delta; \Lambda, x \asc \sigma;$$
So by induction
\begin{enumerate}[(a)]
\item $\Gamma_1; x \asc \gen{\Xi_1}{\upsilon_t}; \extend w : \upsilon_w \yields \Gamma_2; x \asc \_; \Xi_2$
\item $\theta_2 : \Gamma_2; x \asc \gen{\Xi_1}{\upsilon_t}; \lei \Delta; \Lambda, x \asc \sigma;$
\item ...
\end{enumerate}
and the \textsc{Let} rule applies to give
\begin{enumerate}[(a)]
\item $\Gamma_0 \extend \letIn{x}{t}{w} : \upsilon_w \yields \Gamma_2; \Xi_2$
\item $\theta_2 : \Gamma_2; \lei \Delta;$
\item ...
\end{enumerate}
\end{proof}

%endif


\begin{lemma}
\label{lem:letSchemePrincipal}
If $\Delta \entails s \hasscheme \sigma$ principal and
$\Delta, x \asc \sigma; \entails w \hasscheme \sigma'$ principal then
$\Delta \entails \letIn{x}{s}{w} \hasscheme \sigma'$ principal.
\end{lemma}

\begin{lemma}[Completeness of type inference]
If $\theta_0 : \Gamma_0; \lei \Delta$ and $\Delta \entails t : \tau$ then
\begin{enumerate}[(a)]
\item $\Jtype{\Gamma_0;}{t}{\upsilon}{\Gamma_1; \Xi}$,
\item $\theta_1 : \Gamma_1; \lei \Delta$ with 
$\theta_0\alpha = \theta_1\alpha$ for any $\alpha \in \tyvars{\Gamma_0}$, and
\item $\Gamma_1; \entails t :: \gen{\Xi}{\upsilon}$ principal.
\end{enumerate}
\end{lemma}

\begin{proof}
If $t = x$ is a variable, then by inversion $\Delta \entails x \asc \sigma$ and
$\Delta \entails \sigma \succ \tau$. Now by definition of $\lei$,
$\Gamma_0; \entails x \asc \sigma'$ for some $\sigma'$ with
$$\forall \upsilon. \Delta \entails \theta_0\sigma' \succ \upsilon
    \Leftrightarrow \Delta \entails x : \upsilon.$$

By completeness of specialisation,
$\Jspec{\Gamma_0;}{\sigma'}{\upsilon}{\Gamma_0; \Xi}$
and
$$\forall\tau \forall \phi: \Gamma_0 \lei \Phi . (
    \Phi \entails \phi\sigma' \succ \tau
        \Leftrightarrow  \Phi \entails \phi\gen{\Xi}{\upsilon} \succ \tau.$$
Hence the \textsc{Var} rule applies giving
$\Jtype{\Gamma_0;}{x}{\upsilon}{\Gamma_0; \Xi}$,
(b) holds trivially with $\theta_1 = \theta_0$, and
$\Gamma_0 \entails x \hasscheme \gen{\Xi}{\upsilon}$ principal.


If $t = (\letIn{x}{s}{w})$, then by inversion there is some scheme
$\sigma$ such that $\Delta \entails s \hasscheme \sigma$ and
$\Delta, x \asc \sigma \entails w : \tau$. Specialise $\sigma$ with fresh type
variables $\Psi$ so that
$\Delta, \letGoal; \Psi \entails \sigma \succ \tau_s$
and hence
$\Delta, \letGoal; \Psi \entails s : \tau_s$.
Moreover $\theta_0 : \Gamma_0; \letGoal; \lei \Delta, \letGoal;$ so
by induction
\begin{enumerate}[(a)]
\item $\Jtype{\Gamma_0; \letGoal;}{s}{\upsilon}{\Gamma_1; \letGoal; \Xi_1}$
\item $\theta_1 : \Gamma_1; \letGoal; \lei \Delta, \letGoal; \Psi$
\item $\Gamma_1; \letGoal; \entails s \hasscheme \gen{\Xi_1}{\upsilon}$ principal.
\end{enumerate}

Now 
$$\theta_1 : \Gamma_1; x \asc \gen{\Xi_1}{\upsilon};
                            \lei \Delta, x \asc \gen{\Xi_1}{\upsilon}; \Psi$$
but
$$\iota : \Delta, x \asc \sigma; \lei \Delta, x \asc \gen{\Xi_1}{\upsilon};$$
by principality, and hence
$$\Delta, x \asc \gen{\Xi_1}{\upsilon}; \Psi \entails w : \tau$$
by stability.

Thus, by induction,
\begin{enumerate}[(a)]
\item $\Jtype{\Gamma_1, x \asc \gen{\Xi_1}{\upsilon};}{w}{\chi}{\Gamma_2; x \asc \gen{\Xi_1}{\upsilon}; \Xi_2}$
\item $\theta_2 : \Gamma_2; x \asc \gen{\Xi_1}{\upsilon}; \lei \Delta, x \asc \gen{\Xi_1}{\upsilon}; \Psi$
\item $\Gamma_2; x \asc \gen{\Xi_1}{\upsilon}; \entails w \hasscheme \gen{\Xi_2}{\chi}$ principal
\end{enumerate}
and the \textsc{Let} rule applies to give
\begin{enumerate}[(a)]
\item $\Jtype{\Gamma_0;}{\letIn{x}{s}{w}}{\chi}{\Gamma_2; \Xi_2}$
\item $\theta_2 : \Gamma_2; \lei \Delta;$ \TODO{Why?}
\item $\Gamma_2; \entails \letIn{x}{s}{w} \hasscheme \gen{\Xi_2}{\chi}$ principal by
lemma \ref{lem:letSchemePrincipal}.
\end{enumerate}


If $t = \lambda x . w$ is an abstraction, then by inversion
$\Delta \entails \tau \equiv \tau_0 \arrow \tau_1$
where $\tau_0$ and $\tau_1$ are some $\Delta$-types, and
$\Delta, x \asc .\tau_0; \entails w : \tau_1$.
Taking $\theta = [\tau_0/\alpha]\theta_0$, we have that
$$\theta : \Gamma_0; \hole{\alpha}, x \asc .\alpha;
             \lei  \Delta, x \asc .\tau_0;$$
and hence, by induction,
\begin{enumerate}[(a)]
\item $\Jtype{\Gamma_0; \hole{\alpha}, x \asc .\alpha;}{w}{\upsilon}
             {\Gamma_1; \Phi, x \asc .\alpha; \Xi}$
\item $\theta_1 : \Gamma_1; \Phi, x \asc .\alpha; \lei \Delta, x \asc .\tau_0;$
\item $\Gamma_1; \Phi, x \asc .\alpha; \entails w \hasscheme \gen{\Xi}{\upsilon}$
          principal.
\end{enumerate}

Thus the \textsc{Abs} rule applies, so we have
\begin{enumerate}[(a)]
\item $\Jtype{\Gamma_0;}{\lambda x . w}{\alpha \arrow \upsilon}
             {\Gamma_1; \Phi, \Xi}$
\item $\theta_1 : \Gamma_1; \lei \Delta$
\item $\Gamma_1; \entails \lambda x . w \hasscheme \gen{\Phi, \Xi}{\upsilon}$
          principal. \TODO{Why?}
\end{enumerate}


If $t = f a$ is an application, then
$\Delta \entails f : \tau_0 \arrow \tau$,
so by induction
\begin{enumerate}[(a)]
\item $\Jtype{\Gamma_0;}{f}{\upsilon}{\Gamma; \Xi}$
\item $\theta : \Gamma; \lei \Delta$ 
\item $\Gamma; \entails f \hasscheme \gen{\Xi}{\upsilon}$ principal.
\end{enumerate}

Now $\Delta \entails a : \tau_0$, so by induction
\begin{enumerate}[(a)]
\item $\Jtype{\Gamma;}{a}{\upsilon_0}{\Gamma_1; \Xi_1}$
\item $\theta' : \Gamma_1; \lei \Delta$ 
\item $\Gamma_1; \entails a \hasscheme \gen{\Xi_1}{\upsilon_0}$ principal.
\end{enumerate}

Let $\theta_1 = [\tau/\beta]\theta'$, then
$\theta_1 : \Gamma_1; \Xi_1, \Xi, \hole{\beta} \lei \Delta$,
and since
$$\Delta \entails \theta_1\upsilon \equiv \tau_0 \arrow \tau
    \equiv \theta_1(\upsilon_0 \arrow \beta)$$
we have
$\Junify{\Gamma_1; \hole{\beta}}{\upsilon}{\upsilon_0 \arrow \beta}{\Gamma_2}$
by completeness of unification.

Hence the \textsc{App} rule applies, so
\begin{enumerate}[(a)]
\item $\Jtype{\Gamma_0}{f a}{\beta}{\Gamma_2}$
\item $\theta_1 : \Gamma_2; \lei \Delta$ \TODO{Why?}
\item $\Gamma_2; \entails f a \hasscheme \gen{???}{\beta}$ principal. \TODO{Why?}
\end{enumerate}


\end{proof}


\subsection{Implementation}

A term $t$ may be a variable |(X)|, an application |(:$)|, an abstraction |(Lam)|
or a let binding |(Let)|. As with 
%%%type variables, 
   |Ty|, 
we parameterise over the type
of term variable names, so |Tm| is a foldable functor.

> data Tm a  =  X a
>            |  Tm a :$ Tm a 
>            |  Lam a (Tm a)
>            |  Let a (Tm a) (Tm a)

<     deriving (Functor, Foldable)

> type Term      = Tm TermName
> type TermName  = String

The |infer| function attempts to infer the type of the given term,
updating the context with the minimum necessary information.

> infer :: Term -> Contextual Type

To infer the type of a variable, we look up its type scheme in the context,
and specialise this scheme with fresh variables.

> infer (X x) = getContext >>= find >>= specialise
>   where
>     find :: Context -> Contextual Scheme
>     find B0                                 = fail "Missing variable"
>     find (_Gamma :< y ::: sigma)  | x == y  = return sigma
>     find (_Gamma :< _)                      = find _Gamma


To infer the type of a $\lambda$-abstraction, we recursively infer the type of its body
$t$ with its variable $x$ assigned type-scheme $.\alpha$, 
%%%where $\alpha$ is 
   with $\alpha$ 
a fresh type variable. The type is then $\alpha \arrow \tau$ in the context with
the $x$ binding removed.

> infer (Lam x t) = do
>     alpha  <- freshVar
>     tau    <- withDefinition (x ::~ Type (V alpha)) (infer t)
>     return (V alpha :-> tau)


To infer the type of an application, we infer the type $\tau$ of the function
$f$, then the type $\tau'$ of the argument. Unifying $\tau$ with
$\tau' \arrow \beta$, where $\beta$ is a fresh variable, produces the
result.

> infer (f :$ a) = do
>     tau   <- infer f
>     tau'  <- infer a
>     beta  <- freshVar
>     unify tau (tau' :-> V beta)
>     return (V beta)


Finally, to infer the type of a let construct we need a new kind of entry,
the goal marker $\letGoal$.
First we infer the type of the value $s$ being assigned, with a marker at the end of the
original context, to determine that $s : \tau_0$. We can then generalise $\tau_0$
to the scheme $\sigma$ by universally quantifying all variables in $\tau_0$ that
were introduced after the marker (i.e.\ during the type inference of $s$). This allows
us to infer the type of $t$ in the context where $x \asc \sigma$, producing a result type $\tau_1$
and a context from which the $x$ binding can be extracted.

> infer (Let x s t) = do
>     sigma <- generaliseOver (infer s)
>     withDefinition (x ::~ sigma) (infer t)



The |withDefinition| operator appends a term variable definition to the context,
evaluates its second argument, then removes the term variable definition.

%if False

> data a ::~ b = a ::~ b

%endif

> withDefinition ::  TermName ::~ Scheme -> Contextual a
>                      -> Contextual a
> withDefinition (x ::~ sigma) f = do
>     modifyContext (:< x ::: sigma)
>     result <- f
>     modifyContext extract
>     return result
>   where          
>     extract ::  Context -> Context
>     extract (_Gamma :< y ::: _)  | x == y  = _Gamma
>     extract (_Gamma :< alpha := mt)        = extract _Gamma :< alpha := mt
>     extract (_Gamma :< _)                  = undefined

%if False

>     extract B0 = error "extract reached empty context"

%endif



\section{Conclusion}

\TODO{Write a conclusion.}


%if False

\subsection{Lists}

We define our own types of forward (|Fwd|) and backward (|Bwd|) lists,
which are foldable functors and monoids.

> data Fwd a = F0 | a :> Fwd a
>     deriving (Eq, Show)

<     deriving (Eq, Functor, Foldable, Show)

> infixr 8 :>

> data Bwd a = B0 | Bwd a :< a
>     deriving (Eq, Show)

<     deriving (Eq, Functor, Foldable, Show)

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

> (<><) :: Context -> Suffix -> Context
> infixl 8 <><
> xs <>< F0 = xs
> xs <>< (alpha ::= mt :> ys) = (xs :< alpha := mt) <>< ys

> (<>>) :: Bwd a -> Fwd a -> Fwd a
> infixl 8 <>>
> B0 <>> ys         = ys
> (xs :< x) <>> ys  = xs <>> (x :> ys)


\section{Judgment typeclass}

> class Judgment j where
>     type Output j
>     fiat :: j -> Contextual (Output j)
>     orthogonal :: Entry -> j -> Bool

> instance Judgment () where
>     type Output () = ()
>     fiat () = return ()
>     orthogonal _ _ = True

> instance (Judgment j, Judgment k) => Judgment (j, k) where
>     type Output (j, k) = (Output j, Output k)
>     fiat (j, k) = do
>         a  <- fiat j
>         b  <- fiat k
>         return (a, b)
>     orthogonal e (a, b) = orthogonal e a && orthogonal e b

> instance Applicative Contextual where
>     pure = return
>     (<*>) = ap

> instance (Judgment j, Judgment k) => Judgment (Either j k) where
>     type Output (Either j k) = Either (Output j) (Output k)
>     fiat (Left j) = pure Left <*> fiat j
>     fiat (Right k) = pure Right <*> fiat k
>     orthogonal e = either (orthogonal e) (orthogonal e)

> data Unify = Type :==: Type
> infix 1 :==:

> data Instantiate = Name :===: (Type, Suffix)
> infix 1 :===:

> instance Judgment Unify where
>     type Output Unify = ()
>     fiat (tau    :==:   upsilon) = unify tau upsilon
>     orthogonal (delta := _) (V alpha :==: V beta) =
>         alpha /= delta && beta /= delta
>     orthogonal e (tau0 :-> tau1 :==: upsilon0 :-> upsilon1) =
>         orthogonal e (tau0 :==: upsilon0) && orthogonal e (tau1 :==: upsilon1)
>     orthogonal e (V alpha :==: tau) = orthogonal e (alpha :===: (tau, F0))
>     orthogonal e (tau :==: V alpha) = orthogonal e (alpha :===: (tau, F0))

> instance Judgment Instantiate where
>     type Output Instantiate = ()
>     fiat (alpha  :===:  (upsilon, _Xi)) = instantiate alpha _Xi upsilon
>     orthogonal (delta := _) (alpha :===: (tau, _Xi)) = not (alpha == delta) &&
>         not (delta <? tau) && not (delta <? _Xi)
>     orthogonal _ (_ :===: _) = True

> data Specialise = Specialise Scheme

> instance Judgment Specialise where
>     type Output Specialise = Type
>     fiat (Specialise sigma) = specialise sigma
>     orthogonal _ _ = False

> data Infer = Infer Term

> instance Judgment Infer where
>     type Output Infer = Type
>     fiat (Infer t) = infer t
>     orthogonal _ _ = False



> class Judgment j => Topmost j where
>     topmost :: Entry -> j -> Contextual (Output j, Maybe Suffix)
>     topset :: Entry -> j -> Contextual (Maybe Suffix)
>     topset e j = snd <$> topmost e j

> instance Topmost Instantiate where
>   topmost e j = (\_Xi -> ((),_Xi)) <$> topset e j
>   topset (delta := mt) (alpha :===: (tau, _Xi)) =
>    let occurs = delta <? tau || delta <? _Xi in case
>     (delta == alpha,  occurs,  mt            ) of
>     (True,            True,    _             )  ->  lift Nothing
>     (True,            False,   Nothing       )  ->  replace (_Xi <+> (alpha ::= Just tau :> F0))
>     (True,            False,   Just upsilon  )  ->  modifyContext (<>< _Xi)
>                                                 >>  unify upsilon tau
>                                                 >>  restore
>     (False,           True,    _             )  ->  instantiate alpha (delta ::= mt :> _Xi) tau
>                                                 >>  replace F0
>     (False,           False,   _             )  ->  undefined
>   topset _ _ = undefined


> onTop' :: Topmost j => j -> Contextual (Output j)
> onTop' j = do
>     e <- popEntry
>     if orthogonal e j
>         then do
>             x <- onTop' j
>             modifyContext (:< e)
>             return x
>         else do
>             (x, m) <- topmost e j
>             case m of
>                 Just _Xi  -> modifyContext (<>< _Xi)
>                 Nothing   -> modifyContext (:< e)
>             return x


\section{Tests}

The |findType| function looks up a type variable in the context and returns its binding,
or |Nothing| if it is unbound or missing from the context.

> findType :: Context -> Name -> Maybe Type
> findType B0              _           = Nothing
> findType (_ :< y := mt)  x | x == y  = mt
> findType (c :< _)        x           = findType c x


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
>         normaliseContext c (x := Just t :> es) = 
>             normaliseContext (c :< x := Just (normalStep c t)) es
>         normaliseContext c (e :> es) = normaliseContext (c :< e) es


|inferType| is a convenience method for inferring the type of a term in the empty context.

> inferType :: Term -> Maybe (Type, (Name, Context))
> inferType t = runStateT (infer t) (0, B0)


A collection of very simple unit tests follows. These allow the unifier and
type inference algorithm to be tested with

< main

Note that equality of types is syntactic (it does not perform renaming) so
changing the algorithm may sometimes cause spurious failures as the fresh
variable numbers may be different.

> main :: IO ()
> main = unifyTest unifyTests >> inferTest inferTests

> unifyTests :: [(Type, Type, Context, Maybe Context)]
> unifyTests = [
>     (V 0, V 1,
>         B0 :< 0 := Nothing :< 1 := Nothing,
>         Just (B0 :< 0 := Nothing :< 1 := Just (V 0))),
>     (V 0, V 1 :-> V 2, 
>         B0 :< 0 := Nothing :< 1 := Nothing :< 2 := Nothing,
>         Just (B0 :< 1 := Nothing :< 2 := Nothing :< 0 := Just (V 1 :-> V 2))),
>     (V 0, V 1 :-> V 2,
>         B0 :< 0 := Nothing :< 2 := Just (V 0) :< 1 := Just (V 0),
>         Nothing),
>     (V 0 :-> V 0, V 1 :-> V 1,
>         B0 :< 1 := Nothing :< 0 := Nothing,
>         Just (B0 :< 1 := Nothing :< 0 := Just (V 1))),
>     (V 0, V 1 :-> V 2,
>        B0 :< 1 := Nothing :< 0 := Just (V 1 :-> V 1) :< 2 := Nothing,
>        Just (B0 :< 1 := Nothing :< 2 := Just (V 1) :< 0 := Just (V 1 :-> V 1))),
>     (V 0 :-> V 1, V 1 :-> V 0,
>        B0 :< 0 := Nothing :< 1 := Nothing,
>        Just (B0 :< 0 := Nothing :< 1 := Just (V 0))),
>     (V 0 :-> V 1 :-> V 2, V 1 :-> V 0 :-> V 0,
>        B0 :< 2 := Nothing :< 0 := Nothing :< 1 := Nothing,
>        Just (B0 :< 2 := Nothing :< 0 := Just (V 2) :< 1 := Just (V 0)))
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


> deriving instance Eq a => Eq (Ty a)
> deriving instance Show a => Show (Ty a)
> deriving instance Eq Entry
> deriving instance Show Entry
> deriving instance Show Term
> deriving instance Eq a => Eq (Schm a)
> deriving instance Show a => Show (Schm a)
> deriving instance Eq a => Eq (Index a)
> deriving instance Show a => Show (Index a)


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

%endif

\perform{main}


\phantomsection
\addcontentsline{toc}{section}{References}
\bibliographystyle{plainnat}
\bibliography{lib}

\end{document}
