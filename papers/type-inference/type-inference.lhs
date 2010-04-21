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
%format >=> = "\genarrow "
%format <?  = "\in "
%format ... = "\ldots "
%format >-  = "\Yright "
%format .   = "\,\circ\, "

%format F0  = "\emptycontext"
%format B0  = "\emptycontext"

%format Lam (x) (b) = "\lambda" x "." b
%format Let (x) (s) (t) = "\letIn{" x "}{" s "}{" t "} "
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

\newcommand{\eqsubst}{\equiv}
\newcommand{\compose}{\cdot}
\newcommand{\subst}[3]{[#1/#2]#3}

\newcommand{\extend}{\ensuremath{\wedge}}
\newcommand{\yields}{\ensuremath{\dashv}}
\newcommand{\entails}{\ensuremath{\vdash}}
\newcommand{\var}{\ensuremath{\defn \_}}
\newcommand{\type}{\ensuremath{~\mathbf{type}}}
\newcommand{\scheme}{\ensuremath{~\mathbf{scheme}}}
\newcommand{\valid}{\ensuremath{\mathbf{valid}}}
\newcommand{\ok}{\ensuremath{~\mathbf{ok}}}
\newcommand{\emptycontext}{\ensuremath{\varepsilon}}
\newcommand{\letGoal}{\ensuremath{\fatsemi}}
\newcommand{\letIn}[3]{\ensuremath{\mathrm{let}~ #1 \!:=\! #2 ~\mathrm{in}~ #3}}
\newcommand{\letS}[3]{\ensuremath{(!#1 \!:=\! #2 ~\mathrm{in}~ #3)}}
\newcommand{\boxrule}[1]{\begin{center}\framebox{\ensuremath{#1}}\end{center}}
\newcommand{\boxrules}[2]{\begin{center}\framebox{\ensuremath{#1}}\quad\framebox{\ensuremath{#2}}\end{center}}

\newcommand{\tmvars}[1]{\ensuremath{tmvars(#1)}}
\newcommand{\tyvars}[1]{\ensuremath{\V_\TY(#1)}}
\newcommand{\types}[1]{\ensuremath{\T_\TY(#1)}}
\newcommand{\FTV}[1]{\ensuremath{\mathit{FTV}(#1)}}
\newcommand{\Type}{\ensuremath{\mathit{Type}}}
\newcommand{\Term}{\ensuremath{\mathit{Term}}}

\newcommand{\lei}{\ensuremath{\sqsubseteq}}
\newcommand{\gei}{\ensuremath{\sqsupseteq}}
\newcommand{\LEI}{\ensuremath{~\hat\sqsubseteq~}}

\newcommand{\arrow}{\ensuremath{\triangleright}}
\newcommand{\defn}{\ensuremath{\!:=\!}}
\newcommand{\asc}{\ensuremath{\hasc}}
\newcommand{\hasc}{\ensuremath{~\hat{::}~}}
\newcommand{\hole}[1]{\ensuremath{#1 \!:= ?}}
\newcommand{\contains}{\ensuremath{\ni}}

\newcommand{\Judge}[3]{\ensuremath{#1 \preceq #3 \vdash #2}}
\newcommand{\Jmin}[3]{\ensuremath{#1 \LEI #3 \vdash #2}}
\newcommand{\Junify}[4]{\Judge{#1}{#2 \equiv #3}{#4}}
\newcommand{\Jinstantiate}[5]{\Judge{#1 ~||~ #4}{#2 \equiv #3}{#5}}
\newcommand{\Jspec}[4]{\Judge{#1}{#2 \succ #3}{#4}}
\newcommand{\Jtype}[4]{\Judge{#1}{#2 : #3}{#4}}
\newcommand{\Jhast}[5]{\Judge{#1}{#2 ~\hat:_{#3}~ #4}{#5}}

\newcommand{\Prob}[3]{\ensuremath{#2 \,?_{#1}\, #3}}
\newcommand{\Pinf}[2]{\Prob{I}{#1}{#2}}
\newcommand{\Puni}[2]{\Prob{U}{#1 \equiv #2}{}}

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
\newcommand{\T}{\mathcal{T}}
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

\conferenceinfo{MSFP '10}{September 25, Baltimore, Maryland, USA.} 
\copyrightyear{2010} 
\copyrightdata{[to be supplied]} 

\titlebanner{DRAFT}

\title{Type inference in context}
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
between assertions of the form $\Judge{\Gamma}{S}{\Delta}$. Here $\Gamma$
is the input context (before applying the rule), $S$ is the statement being
established, and $\Delta$ is the output context (in which $S$ holds).
This idea of assertions producing a resulting context goes back at least to
\citet{pollack_implicit_1990}. 
%%%, and hence perhaps to \citet{harper_type_1991} and \citet{milner_definition_1990}.
   An interesting point of comparison is with the work of Nipkow and 
   co-workers \citep{Nipkow-Prehofer-JFP95,NaraschewskiN-JAR}, 
   but substitutions and new contexts are there kept separate. 
%%%
We %%%will 
   define an ordering on contexts based on the information they contain,
and show that $\Delta$ is minimal with respect to this ordering. If one
thinks of a context as a set of atomic facts, then $\Delta$ is the least upper
bound of $\Gamma$ together with the facts required to make $S$ hold.

In each case, at most one rule matches the input context and condition, and we
specify a termination order so the rules define algorithms.
\TODO{Do we? We need to say more about termination.}
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


\TODO{The plan: to develop abstract contextual and problem-solving machinery with
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

\subsection{Syntax}

The syntax of Hindley-Milner types is
$$\tau ::= \alpha ~||~ \tau \arrow \tau$$
where $\alpha$ ranges over some set of type variables $\V_\TY$.
For simplicity, we only consider one type constructor.
In the sequel, $\alpha$ and $\beta$ are type variables and $\tau$ and $\upsilon$
are types.
We write $\Type$ for the set of types.
%% (All of these symbols may be primed or subscripted.)
%% We use $\Xi$ to denote a context suffix containing only type variable declarations.

We write $\FTV{\tau}$ for the free type variables of $\tau$, defined as follows.
This will later be extended to other syntactic objects.
\begin{align*}
\FTV{\alpha}                &= \{ \alpha \} \\
\FTV{\tau \arrow \upsilon}  &= \FTV{\tau} \cup \FTV{\upsilon}
\end{align*}

The foldable functor |Ty| defines types in our object language parameterised by
the type of variable names, which will be useful later. Thanks to a language
extension in GHC 6.12 \citep{ghc_team_glorious_2009} we can simply
derive the required typeclass instances.
For simplicity, we use integers as names in the implementation.

> data Ty a  =  V a |  Ty a :-> Ty a

<     deriving (Functor, Foldable)

%if False

> infixr 5 :->

%endif

> type TyName  = Integer
> type Type    = Ty TyName


\subsection{Introducing contexts}

Types contain variables, but we need some way of interpreting what the variables
mean. Our ideology is that such information belongs in the context. We give an
abstract description of contexts, which may contain type variables and other
information.

Let $\K$ be a set of sorts, and for each $K \in \K$ let $\V_K$ be a set of
variables and $\D_K$ a set of objects. Our running example will be the sort
$\TY$, where $\V_\TY$ is some set of type variables and $\D_\TY$ initially
contains only the \scare{unbound variable} object $~\hole{}$.

A \define{context} $\Gamma$ is a list of declarations $v D$, where
$v \in \V_K$ and $D \in \D_K$.
%% and separators $(\fatsemi)$. 
We write $\emptycontext$ for the empty context, and the symbols
$\Gamma, \Delta$ and $\Theta$ range over contexts.
%% $\Xi$ is a context that contains no $\fatsemi$ separators.

We will gradually construct a set $\Ss$ of statements, which can be
judged in a context. We write the \define{judgment} $\Gamma \entails S$ to mean
that the declarations in $\Gamma$ support the statement $S \in \Ss$.

It is not enough for contexts to be lists of declarations: they must be
well-founded, that is, the declarations need to make sense.
A context is valid if it declares each variable at most
once, and each declaration is a valid extension of the preceding context.
We assume we have a map $\ok_K : \D_K \rightarrow \Ss$ for every $K \in \K$.
Let $\V_K(\Gamma)$ be the set of $K$-variables in $\Gamma$.
We define the context validity statement $\valid$ as shown in
Figure~\ref{fig:contextValidityRules}.

\TODO{Formally introduce statements and sanity conditions in a theorem-like
environment?}

\begin{figure}[ht]
\boxrule{\Gamma \entails \valid}
$$
\Axiom{\emptycontext \entails \valid}
\qquad
\Rule{\Gamma \entails \valid    \quad    \Gamma \entails \ok_K D}
     {\Gamma, v D \entails \valid}
\side{v \in \V_K \setminus \V_K(\Gamma)}
$$
\caption{Rules for context validity}
\label{fig:contextValidityRules}
\end{figure}

From now on, we will only be interested in valid contexts. All future definitions
implicitly assume the context is valid, and it is straightforward to verify that
our algorithms preserve context validity.

In the example of type declarations, we let $\ok_\TY (\hole{}) = \valid$.
That is, declaring a type variable to be unknown always makes sense.


\subsection{Making types meaningful}

Now we can ask whether a type is meaningful with respect to a context.
This requires us to determine whether the type variables are in scope.
More generally, each context entry makes some statements hold.

We suppose that there is a map
$\sem{\cdot}_K : \V_K \times \D_K \rightarrow \mathcal{P}(\Ss)$
for each $K \in \K$, from declarations to sets of statements.
% such that $$\Gamma \contains v D  \Rightarrow  \Gamma \entails \sem{v D}.$$
(We typically omit the subscript when the sort is irrelevant or can be inferred.)
The idea is that $\sem{v D}$ is the set of atomic statements that hold if the
declaration $v D$ is in the context.
The basic rule of our inference system is
$$\name{Lookup}
  \Rule{\Gamma \entails \valid   \quad  v D \in \Gamma  \quad  S  \in \sem{v D}}
       {\Gamma \entails S}.$$

Applications of the \textsc{Lookup} rule are the \scare{variables} of
derivations. 
Just as variable names are the atoms out of which compound expressions get built,
instances of \textsc{Lookup} are the axiom leaves out of which complex
derivations of judgments are built. 

We define the statement $\tau \type$ by taking
$\sem{\hole{\alpha}} = \{ \alpha \type \}$
together with the structural rule
$$
\Rule{\tau \type   \quad   \upsilon \type}
     {\tau \arrow \upsilon \type}.
$$
Note that we omit the context from rules if it is constant throughout.
We observe the sanity condition
$\Gamma \entails \tau \type  \Rightarrow  \Gamma \entails \valid$.


\subsection{Type variable declarations}

At the moment, variables are rather useless, because they can do nothing more
than exist. During unification we will solve constraints to discover the values
of variables, so we could then substitute them out. However, finding a value for
a variable does not render it meaningless, in fact the reverse is true. We will
therefore extend declarations instead, allowing variables to retain their values
and hence their meaning.
We extend $\D_\TY$ with bindings $\;\defn \tau$ for every type $\tau$, and
let $\ok_\TY (\defn \tau) = \tau \type$.

If $\Xi$ is a list of type variable declarations, we define its set of free
type variables $\FTV{\Xi}$ by
$$\FTV{\Xi} = \bigcup \{ \FTV{\tau} ~||~ \alpha \defn \tau \in \Xi \}.$$
If $X_0, \ldots, X_n$ are types or lists of type variable declarations then
$$\FTV{X_0, \ldots, X_n} = \FTV{X_0} \cup \ldots \cup \FTV{X_n}.$$


\subsection{Type equations}

Previously we could only consider the syntactic equality of types, but
type variable declarations now induce a more interesting equational theory. 
If $\tau$ and $\upsilon$ are types, we define the equivalence statement
$\tau \equiv \upsilon$ by making declarations yield equations:
\begin{align*}
%% \sem{\hole{\alpha}}_\TY &= \{ \alpha \type \}  \\
\sem{\alpha \defn \tau}_\TY &= \{ \alpha \type, \alpha \equiv \tau \}
%%%
%%% \sem{\hole{\alpha}}_\TY &= \{ \alpha \type, \alpha \equiv \alpha \}  \\
%%% \sem{\alpha \defn \tau}_\TY &= \{ \alpha \type, \alpha \equiv \alpha,
%%%            \alpha \equiv \tau, \tau \equiv \alpha \}
\end{align*}
and taking structural and equivalence closure by the rules in
Figure~\ref{fig:equivRules}. We observe the sanity condition
$$\Gamma \entails \tau \equiv \upsilon
    \Rightarrow  \Gamma \entails \tau \type \wedge \upsilon \type.$$

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




\subsection{Implementing types and contexts}

A type variable declaration is represented as a |TyEntry|, in which a variable
is either bound to a type (written |Some tau|) or left unbound (written |Hole|).

> data TyDecl   =  Some Type | {-"\;"-} Hole
> data TyEntry  =  TyName := TyDecl

A context is a (backwards) list of entries. At the moment we only have one
kind of entry, but later we will add others, so this definition is incomplete.
% subject to the
% conditions that each variable is defined at most once, and all variables that
% occur in a type variable binding must be defined earlier in the list.
The context validity conditions will be maintained by the algorithm but are not
enforced by the type system; this is possible in a language such as Agda.
A context suffix is a (forwards) list containing only type variable declarations.

< data Entry = TY TyEntry | ...

> type Context     = Bwd Entry
> type Suffix      = Fwd TyEntry

The types |Bwd| and |Fwd| are backwards (snoc) and forwards (cons) lists,
respectively. We overload |B0| for the empty list in both cases, and write
|:<| and |:>| for the data constructors. Data types are cheap, so we might
as well make the code match our intution about the meaning of data. Lists
are monoids where |<+>| is the append operator, and the \scare{fish} operator
\eval{:t (<><)} appends a suffix to a context. 

Since |Type| and |Suffix| are built from |Foldable| functors containing names, we can define a typeclass implementation of \ensuremath{FTV}, with membership function |(<?)|: 

> class OccursIn a where
>     (<?) :: TyName -> a -> Bool

> instance OccursIn TyName where
>     (<?) = (==)

> instance OccursIn TyEntry where
>    alpha <? (_ := Some tau)  = alpha <? tau
>    alpha <? (_ := Hole)      = False

> instance  (Foldable t, OccursIn a)
>               => OccursIn (t a) where
>     alpha <? t = any (alpha <?) t

We work in the |Contextual| monad (computations that can fail and mutate the
context), defined as follows:   

> type Contextual  = StateT (TyName, Context) Maybe

\TODO{Is it right to say $\alpha$ is fresh wrt $\Gamma$ here?}
The |TyName| component is the next fresh type variable name to use;
it is an implementation detail that is not mentioned in the typing rules. 
Our choice of |TyName| means that it is easy to choose a name fresh with respect
to a |Context|.

> freshen :: TyName -> Context -> TyName
> freshen alpha _Gamma = succ alpha

The |fresh| function generates a fresh variable name and appends a declaration
to the context.

> fresh :: TyDecl -> Contextual TyName
> fresh mt = do  (beta, _Gamma) <- get
>                put (freshen beta _Gamma, _Gamma :< TY (beta := mt))
>                return beta

The |getContext|, |putContext| and |modifyContext| functions
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



\section{Information and stable statements}

\subsection{Information order}

Intuitively, defining a variable cannot make equations cease to hold.
More generally, if we rely on the context to tell us what we may
deduce about variables, then making contexts more informative must preserve
deductions. 

Let $\Gamma$ and $\Delta$ be contexts.
A \define{substitution from $\Gamma$ to $\Delta$} is a map from
$\tyvars{\Gamma}$ to $\{ \tau ~||~ \Delta \entails \tau \type \}$.
Substitutions apply to types and statements in the obvious way.

We write $\delta : \Gamma \lei \Delta$ and say
\define{$\Delta$ is more informative than $\Gamma$} if $\delta$ is a
substitution from $\Gamma$ to $\Delta$ such that,
for every $v D \in \Gamma$ and $S \in \sem{v D}$, we have that
$\Delta \entails \delta S$.

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


%if False

Suppose we have a set $\T_K(\Delta)$ for each $K \in \K$ and context $\Delta$.
A \define{$K$-substitution from $\Gamma$ to $\Delta$} is map from
$\V_K(\Gamma)$ to $\T_K(\Delta)$.
Suppose further that substitutions can be applied to statements.
We write $\delta : \Gamma \lei \Delta$ and say
\define{$\Delta$ is more informative than $\Gamma$} if,
for each $K \in \K$, there is a 
$K$-substitution $\delta_K$ from $\Gamma$ to $\Delta$ such that
if $v D \in \Gamma$ and $S \in \sem{v D}$ then
$\Delta \entails \delta S$.
(We write $\delta S$ for the simultaneous application of every $\delta_K$ to
$S$.)
\TODO{Can we simplify this without making it too concrete?}


If $\delta : \Gamma \lei \Delta$ and $\theta : \Gamma \lei \Delta$, then we
write $\delta \eqsubst \theta$ if, for every statement $S$,
$\Delta \entails \delta S  \Leftrightarrow  \Delta \entails \theta S$.
It is easy to see that $\eqsubst$ is an equivalence relation that is preserved
under composition.
\TODO{What other properties of $\eqsubst$ do we need?}

% For each $K \in \K$ and context $\Delta$, suppose
% $\equiv_K : \T_K(\Delta) \rightarrow \T_K(\Delta) \rightarrow \Ss$.
% If $\delta : \Gamma \lei \Delta$ and $\theta : \Gamma \lei \Delta$, then we
% write $\delta \eqsubst \theta$ if, for every $K \in \K$ and
% $v \in \V_K(\Gamma)$,
% $\Delta \entails \delta v \equiv_K \theta v$.
% It is easy to see that $\eqsubst$ is an equivalence relation that is preserved
% under composition.

%endif


We may omit $\delta$ and write $\Gamma \lei \Delta$ if we are only interested
in the existence of a suitable substitution. This relation between contexts
captures the notion of \define{information increase}: $\Delta$ supports all the
statements corresponding to declarations in $\Gamma$. 

%% Moreover, this will still hold if we truncate both $\Gamma$ and $\Delta$ after
%% any number of $\fatsemi$ separators.

This definition of information increase is not quite complete, because it does
not place any constraints on the order of context entries, other than the
dependency order of variables in declarations. We will later see how to extend
$\lei$ to capture the order of entries at an appropriate level of precision. 

% For our running example, the sort $\TY$ of type variables, substitution is
% defined as one would expect.
% Let $\types{\Delta}$ be the set of types $\tau$ such that
% $\Delta \entails \tau \type$. 
% A $\TY$-substitution then maps type variables to types, so it can be applied
% to types and statements in the usual way.


\subsection{Stability}

We say a statement $S$ is
\define{stable} if it is preserved under information increase, that is, if
$$\Gamma \entails S  \quad \mathrm{and}  \quad  \delta : \Gamma \lei \Delta
    \quad \Rightarrow \quad  \Delta \entails \delta S.$$
This says that we can extend a simultaneous substitution on syntax to a
simultaneous substitution on derivations.
\TODO{Expand on this.}

Since we are only interested in valid contexts, the statement $\valid$ always
holds, and it is invariant under substitution, so it is clearly stable.

We have a standard strategy for proving stability of most statements, which is
effective by construction. In each case we proceed by induction on the structure
of derivations. Where the \textsc{Lookup} rule is applied, stability holds by
the definition of information increase. Otherwise, for rules that do not refer
to the context, we can verify that non-recursive hypotheses are stable and that
recursive hypotheses occur in strictly positive positions, so they are stable
by induction. Applying this strategy shows that the statements $\tau \type$
and $\tau \equiv \upsilon$ are stable.


\begin{lemma}\label{lei:preorder}
If every statement $S \in \sem{v D}$ is stable for every declaration $v D$, then
the $\lei$ relation is a preorder, with reflexivity demonstrated by
$\iota : \Gamma \lei \Gamma : v \mapsto v$, and transitivity by
$$\gamma_1 : \Gamma_0 \lei \Gamma_1  ~\wedge~  \gamma_2 : \Gamma_1 \lei \Gamma_2
  \quad \Rightarrow \quad  \gamma_2 \compose \gamma_1 : \Gamma_0 \lei \Gamma_2.$$
\end{lemma}

\begin{proof}
Reflexivity follows immediately from the \textsc{Lookup} rule.
For transitivity, suppose $v D \in \Gamma_0$ and $S \in \sem{v D}$.
Then $\Gamma_1 \entails \gamma_1 S$ since $\gamma_1 : \Gamma_0 \lei \Gamma_1$.
Now by stability applied to $\gamma_1 S$ using $\gamma_2$, we have
$\Gamma_2 \entails \gamma_2\gamma_1 S$ as required.
\end{proof}


\begin{lemma}
\label{lem:composePreservesEquivSubst}
If $\delta_0 \eqsubst \delta_1 : \Gamma \lei \Delta$
and $\theta_0 \eqsubst \theta_1 : \Delta \lei \Theta$
then $\theta_0 \compose \delta_0  \eqsubst  \theta_1 \compose \delta_1 :
         \Gamma \lei \Theta$.
\end{lemma}

\begin{proof}
Fix $\alpha \in \tyvars{\Gamma}$. By definition of $\eqsubst$,
$\Delta \entails \delta_0\alpha \equiv \delta_1\alpha$,
so by stability,
$\Theta \entails \theta_0\delta_0\alpha \equiv \theta_0\delta_1\alpha$.
Moreover
$\Theta \entails \theta_0\delta_1\alpha \equiv \theta_1\delta_1\alpha$,
and hence
$\Theta \entails \theta_0\delta_0\alpha \equiv \theta_1\delta_1\alpha$
by transitivity.
\end{proof}


\subsection{Composite statements}

If $S$ and $S'$ are statements and $v D$ is a declaration, then we define the
\define{composite} statements $S \wedge S'$ and $\Sbind{v D}{S}$ thus:
$$
\Rule{S \quad S'}{S \wedge S'}
\qquad
\Rule{\Gamma \entails \ok_K D    \quad    \Gamma, v D \entails S}
     {\Gamma \entails \Sbind{v D}{S}}
\side{v \in \V_K \setminus \V_K(\Gamma)}.
$$
We add general introduction forms for composite statements, but supply
eliminators only for composite hypotheses, in effect forcing derivations to be
cut-free. This facilitates reasoning by induction on derivations. The general
eliminators are in any case admissible rules.

\begin{lemma}[Composition preserves stability]
If $S$ and $S'$ are stable then $S \wedge S'$ is stable.
If $v D$ is a declaration and both $\ok_K D$ and $S$ are stable, then
$\Sbind{v D}{S}$ is stable.
\end{lemma}
\begin{proof}
Suppose $S$ and $S'$ are stable, $\Gamma \entails (S \wedge S')$ and
$\delta : \Gamma \lei \Delta$. Then $\Gamma \entails S$ and $\Gamma \entails S'$,
so by stability, $\Delta \entails \delta S$ and $\Delta \entails \delta S'$.
Hence $\Delta \entails \delta (S \wedge S')$.

Suppose $S$ is stable, $\Gamma \entails \Sbind{v D}{S}$ and
$\delta : \Gamma \lei \Delta$. Then $\Gamma \entails \ok_K D$ and
$\Gamma, v D \entails S$, so by stability, $\Delta \entails \delta \ok_K D$.
Let $\delta' = \subst{v}{v}{\delta}$, then
$\delta' : \Gamma, v D \lei \Delta, v (\delta D)$
so by stability of $S$ we have $\Delta, v (\delta D) \entails \delta' S$.
Hence $\Delta \entails \Sbind{v (\delta D)}{\delta' S}$
and so $\Delta \entails \delta \Sbind{v D}{S}$.
\TODO{We should at least mention freshness here.}
\end{proof}

Thanks to this lemma and the preceding results, every statement we have
introduced so far is stable. We will ensure that all statements in $\Ss$ are
stable, so we can make use of stability without qualification in the sequel.



\section{Problems}

\subsection{What is a problem?}

A problem represents a statement we wish to make hold by increasing information
in the context. More generally, it is a statement with distinguished output
positions for which we wish to find a witness in a more informative context.
Unification is an example of the first kind of problem and type inference an
example of the second.

We are interested in creating algorithms to solve problems, preferably in as
general a way as possible (that is, by making the smallest information increase
necessary to find a solution). This corresponds to finding a most general
unifier, in the case of unification, or a principal type in the case of type
inference.

\TODO{Set of well-posed questions, category of answers.
Make the categorical structure clearer.}
Formally, a \define{problem} $P$ consists of
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
\In{U} &= \Type \times \Type  \\
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
$\theta \eqsubst \zeta \compose \delta$ and $\Theta \entails \R{P} (\zeta b, c)$.

\TODO{One possible notation for problems: $?_P$ as an infix operator
with the input parameters before it and the output parameters after it.
Any other suggestions?}

We write $\Prob{P}{a}{b}$ for $\Post{P}(a)(b)$ and
$\delta : \Jmin{\Gamma}{\Prob{P}{a}{b}}{\Delta}$ to mean that
$(b, \delta, \Delta)$ is a minimal solution of the $P$-instance $a$.

\TODO{Define what it means for a rule system to be algorithmic.}


\subsection{The Optimist's Lemma}

If $P$ and $Q$ are problems, then $P \wedge Q$ is a problem with
\begin{align*}
\In{P \wedge Q}                 &= \In{P} \times \In{Q}  \\
\Out{P \wedge Q}                &= \Out{P} \times \Out{Q}  \\
\Pre{P \wedge Q} (a, b)         &= \Pre{P} (a) \wedge \Pre{Q} b  \\
\Post{P \wedge Q} (a, b) (c, d) &= \Post{P}(a)(c) \wedge \Post{Q}(b)(d)  \\
\R{P \wedge Q}(a, b)(c, d)      &= \R{P}(a)(c) \wedge \R{Q}(b)(d)  \\
\end{align*}

The point of all this machinery is to be able to state and prove the following 
lemma, stating that the minimal solution to a conjunction of problems can be
found by finding the minimal solution of the first problem, then (minimally)
extending it to solve the second. 

\begin{lemma}[The Optimist's Lemma]
The following inference rule is admissible:
$$\Rule{\gamma_1 : \Jmin{\Gamma_0}{\Prob{P}{a}{r}}{\Gamma_1}
       \quad  \gamma_2 : \Jmin{\Gamma_1}{\Prob{Q}{b}{s}}{\Gamma_2}}
       {\gamma_2 \compose \gamma_1 :
         \Jmin{\Gamma_0}{\Prob{P \wedge Q}{(a, b)}{(\gamma_2 r, s)}}{\Gamma_2}}$$
\end{lemma}

\TODO{Make the proof prettier, perhaps using a diagram.}

\begin{proof}
We have that $\gamma_2 \compose \gamma_1 : \Gamma_0 \lei \Gamma_2$ by 
Lemma~\ref{lei:preorder}. 

To show $\Gamma_2 \entails \Prob{P \wedge Q}{(a, b)}{(\gamma_2 r, s)}$, it
suffices to show $\Gamma_2 \entails \Prob{P}{a}{\gamma_2 r}$ and
$\Gamma_2 \entails \Prob{Q}{b}{s}$. The latter holds by assumption. For the
former, note that $\Gamma_1 \entails \Prob{P}{a}{r}$ and hence
$\Gamma_2 \entails \gamma_2 (\Prob{P}{a}{r})$ by stability of $\Prob{P}{a}{r}$.
But $\gamma_2 (\Prob{P}{a}{r}) = \Prob{P}{a}{\gamma_2 r}$ by definition, so we are done.

Finally, suppose there is some $\theta : \Gamma_0 \lei \Theta$ such that
$\Theta \entails \Prob{P \wedge Q}{(a, b)}{(r', s')}$, so
$\Theta \entails \Prob{P}{a}{r'}$ and
$\Theta \entails \Prob{Q}{b}{s'}$.
Since $\gamma_1 : \Jmin{\Gamma_0}{\Prob{P}{a}{r}}{\Gamma_1}$, there exists
$\zeta_1 : \Gamma_1 \lei \Theta$ such that
$\theta \eqsubst \zeta_1 \compose \gamma_1$
and $\Theta \entails \R{P}(\zeta_1 r)(r')$.
But then $\gamma_2 : \Jmin{\Gamma_1}{\Prob{Q}{b}{s}}{\Gamma_2}$, so there exists
$\zeta_2 : \Gamma_2 \lei \Theta$ such that
$\zeta_1 \eqsubst \zeta_2 \compose \gamma_2$
and $\Theta \entails \R{Q}(\zeta_2 s)(s')$.
Hence $\theta \eqsubst \zeta_2 \compose (\gamma_2 \compose \gamma_1)$
and $\Theta \entails \R{P \wedge Q}(\zeta_2 (\gamma_2 r), \zeta_2 s)(r', s')$.
\end{proof}

This sequential approach to problem solving is not the only decomposition
justified by stability. The account of unification given by
\citet{mcadam_unification_1998} amounts to a concurrent, transactional
decomposition of problems. The same context is extended via multiple different
substitutions, then these are unified to produce a single substitution.


\section{Deriving a unification algorithm}

\subsection{Transforming the rule system for equivalence}

We wish to transform these rules into a unification algorithm.
Starting with the rules in Figure~\ref{fig:equivRules}, consider what happens if
we remove each equivalence closure rule in turn and attempt to prove its
admissibility. This will fail, but the proof obligations left over give us a more
specific but equivalent system of algorithmic-looking rules for equivalence.
\TODO{Reference unfold/fold transformations.}

First, the reflexivity rule for types can be derived from the reflexivity
rule for variables given by
$$\Rule{\alpha \type}
       {\alpha \equiv \alpha}$$
by applying the structural rule until variables occur.

Next, transitivity can be derived from
$$
\Rule{\alpha \equiv \tau    \quad    \tau \equiv \upsilon}
     {\alpha \equiv \upsilon}
\side{\alpha \neq \tau, \alpha \neq \upsilon}
%% \qquad
%% \Rule{\upsilon \equiv \tau    \quad    \tau \equiv \alpha}
%%     {\upsilon \equiv \alpha}
$$
as follows. Suppose $\chi \equiv \tau$ and $\tau \equiv \upsilon$ and seek to
prove $\chi \equiv \upsilon$.
\begin{itemize}
\item If $\chi = \alpha$ is a variable distinct from $\tau$ and $\upsilon$
      then we can use the restricted transitivity rule.
\item If $\chi = \alpha = \upsilon$ then we can use reflexivity.
\item If $\chi = \alpha = \tau$ then the result holds by hypothesis.
\item If $\chi$ is not a variable but $\upsilon$ is then we can apply symmetry
      and one of the previous cases.
\item If $\chi$ and $\upsilon$ are both not variables then we can apply
      the structural rule.
\end{itemize}

Finally, symmetry becomes admissible (but not derivable) if replaced by
$$
\Rule{\alpha \equiv \tau}
     {\tau \equiv \alpha}.
%% \qquad
%% \Rule{\tau \equiv \alpha}
%%      {\alpha \equiv \tau}
$$
Note that the restricted symmetry rule covers the case we needed
for deriving transitivity. Suppose $\upsilon \equiv \tau$ and seek to prove
$\tau \equiv \upsilon$.
\begin{itemize}
\item If $\upsilon = \alpha$ is a variable then the rule applies.
\item If $\upsilon$ is not a variable but $\tau = \beta$ is, then
      the proof of $\upsilon \equiv \beta$ must be by restricted symmetry,
      in which case its hypothesis says that $\beta \equiv \upsilon$.
\item If $\tau$ and $\upsilon$ are both not variables then we can apply the
      structural rule.
\end{itemize} 


\subsection{Constructing a unification algorithm}

Now we can see how to construct the algorithm. The structural rule says that
whenever we have rigid $\arrow$ symbols on each side, we decompose the problem
into two subproblems, and thanks to the Optimist's Lemma we can solve these
sequentially. Otherwise, we either have variables on both sides, or a variable
on one side and a type on the other. In each case, we look at the head of the
context to see what information it gives us, and use the transformed rules to
see how to proceed. When solving a variable with a type, we need to accumulate
the type's dependencies as we encounter them, performing the occur check to
ensure a solution exists.

% \begin{itemize}
% \item If $\alpha D$ is at the head of the context and we are trying to
% unify $\alpha \equiv \alpha$ then we are done.
% \item If $\hole{\alpha}$ is at the head and we seek $\alpha \equiv \tau$ or
% $\tau \equiv \alpha$ then we can replace the head with the list of dependencies
% followed by $\alpha \defn \tau$.
% \end{itemize}

It is possible that a context entry may have no bearing on the unification
problem being solved, and hence can be ignored.
We define the orthogonality relation $v D \perp X$ (the set of type variables $X$
does not depend on the declaration $v D$) thus:
\begin{align*}
\delta \defn \_ \perp X
    &\mathrm{~if~} \delta \notin X  \\
v D \perp X
    &\mathrm{~if~} v \in \V_K, D \in \D_K \mathrm{~for~} K \neq \TY
\end{align*}

The rules in Figure~\ref{fig:unifyRules} define our unification algorithm. The
assertion $\Junify{\Gamma}{\tau}{\upsilon}{\Delta}$ means that given inputs
$\Gamma$, $\tau$ and $\upsilon$, where
$\Gamma \entails \tau \type \wedge \upsilon \type$,
unification of $\tau$ with $\upsilon$ 
succeeds, producing output context $\Delta$.

The assertion
$\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$
means that given inputs $\Gamma$, $\Xi$, $\alpha$ and $\tau$,
solving $\alpha$ with $\tau$ succeeds and produces output context $\Delta$,
subject to the conditions
\begin{itemize}
\item $\alpha \in \tyvars{\Gamma}$,
\item $\Gamma, \Xi \entails \tau \type$,
\item $\tau$ is not a variable,
\item $\Xi$ contains only type variable declarations and
\item $\beta \in \tyvars{\Xi} \Rightarrow \beta \in \FTV{\tau, \Xi}$.
\end{itemize}


The rules \textsc{Define}, \textsc{Expand} and \textsc{Ignore} have
symmetric counterparts that are identical apart from interchanging the equated
terms in the conclusion. Usually we will ignore these without loss of generality,
but where necessary we refer to them as \textsc{Define}\sym,
\textsc{Expand}\sym and \textsc{Ignore}\sym.

        
\begin{figure}[ht]
\boxrule{\Junify{\Gamma}{\tau}{\upsilon}{\Delta}}

$$
\name{Idle}
\Rule{\Gamma \entails \alpha \type}
     {\Junify{\Gamma}{\alpha}{\alpha}{\Gamma}}
$$

$$
\name{Decompose}
\Rule{\Junify{\Gamma}{\tau_0}{\upsilon_0}{\Delta_0}
      \quad
      \Junify{\Delta_0}{\tau_1}{\upsilon_1}{\Delta}}
    {\Junify{\Gamma}{\tau_0 \arrow \tau_1}{\upsilon_0 \arrow \upsilon_1}{\Delta}}
$$

$$
\name{Solve}
\Rule{\Jinstantiate{\Gamma}{\alpha}{\tau}{\emptycontext}{\Delta}}
     {\Junify{\Gamma}{\alpha}{\tau}{\Delta}}
%% \side{\tau \neq \alpha}
\side{\tau \mathrm{~not~variable}}
$$

$$
\name{Define}
\Rule{\Gamma_0 \entails \beta \type}
     {\Junify{\Gamma_0, \hole{\alpha}}{\alpha}{\beta}{\Gamma_0, \alpha \defn \beta}}
$$

$$
\name{Expand}
\Rule{\Junify{\Gamma_0}{\tau}{\beta}{\Delta_0}}
     {\Junify{\Gamma_0, \alpha \defn \tau}{\alpha}{\beta}{\Delta_0, \alpha \defn \tau}}
\side{\alpha \neq \beta}
$$

$$
\name{Ignore}
\Rule{\Junify{\Gamma_0}{\alpha}{\beta}{\Delta_0}}
     {\Junify{\Gamma_0, v D}{\alpha}{\beta}{\Delta_0, v D}}
\side{v D \perp \{\alpha, \beta\} }
$$

\bigskip

\boxrule{\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}}

$$
\name{DefineS}
\Rule{\Gamma_0 \entails \Sbind{\Xi}{\tau \type}}
     {\Jinstantiate{\Gamma_0, \hole{\alpha}}{\alpha}{\tau}{\Xi}
                   {\Gamma_0, \Xi, \alpha \defn \tau}}
\side{\alpha \notin \FTV{\tau, \Xi}}
$$

$$
\name{ExpandS}
\Rule{\Junify{\Gamma_0, \Xi}{\upsilon}{\tau}{\Delta_0}}
     {\Jinstantiate{\Gamma_0, \alpha \defn \upsilon}{\alpha}{\tau}{\Xi}
                   {\Delta_0, \alpha \defn \upsilon}}
\side{\alpha \notin \FTV{\tau, \Xi}}
$$

$$
\name{DependS}
\Rule{\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\beta D, \Xi}{\Delta}}
     {\Jinstantiate{\Gamma_0, \beta D}{\alpha}{\tau}{\Xi}{\Delta}}
\side{\alpha \neq \beta, \beta \in \FTV{\tau, \Xi}}
$$

$$
\name{IgnoreS}
\Rule{\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\Xi}{\Delta_0}}
     {\Jinstantiate{\Gamma_0, v D}{\alpha}{\tau}{\Xi}{\Delta_0, v D}}
\side{v D \perp \FTV{\alpha, \tau, \Xi}}
$$

\caption{Algorithmic rules for unification}
\label{fig:unifyRules}
\end{figure}


Observe that we have no rule for the case
$$\Jinstantiate{\Gamma_0, \alpha \defn \_}{\alpha}{\tau}{\Xi}{\Delta}
\mathrm{~with~} \alpha \in \FTV{\tau, \Xi}$$
so the algorithm fails if this situation arises. This is essentially an occur
check failure: $\alpha$ and $\tau$ cannot be unified if $\alpha$ occurs in
$\tau$ or in an entry that $\tau$ depends on, and $\tau$ is not a variable.
Since we only have one type constructor symbol (the function arrow $\arrow$),
there are no failures due to rigid-rigid mismatch. Adding these would not
significantly complicate matters, however.

At first there appears to be some redundancy in the system, with similar-looking
rules for flex-flex and flex-rigid problems
(\textsc{Define} versus \textsc{DefineS}, for example).
Unfortunately, it is not easy to remove the flex-flex versions, because they
permit the exception to the occur check when only variables are involved.


\subsection{Soundness and completeness}

\begin{lemma}[Soundness and generality of unification]
\label{lem:unifySound}
\begin{enumerate}[(a)]
\item First, if $\Junify{\Gamma}{\tau}{\upsilon}{\Delta}$, then
$\tyvars{\Gamma} = \tyvars{\Delta}$ and we have
$\iota : \Jmin{\Gamma}{\Puni{\tau}{\upsilon}}{\Delta}$,
%% $\Gamma_1 \entails \tau \equiv \upsilon$,
%% $\iota : \Gamma_0 \lei \Gamma_1$
where $\iota$
% $$\iota: \tyvars{\Gamma} \rightarrow \types{\Delta} : \alpha \mapsto \alpha$$
is the inclusion substitution.

\item Moreover, if
$\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$, then
% $\Gamma_1 \entails \alpha \equiv \tau$,
$\tyvars{\Gamma, \Xi} = \tyvars{\Delta}$
and $\iota : \Jmin{\Gamma, \Xi}{\Puni{\alpha}{\tau}}{\Delta}$.
\end{enumerate}
\end{lemma}

\begin{proof}
By induction on the structure of derivations. \TODO{Need a bit more here.}
\end{proof}


\begin{lemma}[Occur check]
\label{lem:occurCheck}
Let $\alpha$ be a variable and $\tau$ a non-variable type such that
$\alpha \in \FTV{\tau}$. For every context $\Gamma$ and substitution
$\theta$, $\Gamma \nvdash \theta\alpha \equiv \theta\tau$ and
$\Gamma \nvdash \theta\tau \equiv \theta\alpha$.
\end{lemma}

\begin{proof}
It suffices to prove $\Gamma \nvdash \alpha \equiv \tau$ and
$\Gamma \nvdash \tau \equiv \alpha$, because
$\theta\alpha$ must contain a variable $\beta \in \FTV{\theta\tau}$ 
and $\theta\tau$ is not a variable.

Since $\alpha$ is a variable but $\tau$ is not, neither reflexivity nor the
structural rule apply. Symmetry and transitivity do not apply because their
hypotheses cannot be satisifed.

By the well-formedness conditions for contexts, if
$\alpha \defn \upsilon \in \Gamma$ then $\alpha \notin \FTV{\upsilon}$, so
the \textsc{Lookup} rule does not apply.
\end{proof}


\begin{lemma}[Completeness of unification]
\label{lem:unifyComplete}
\begin{enumerate}[(a)]
\item If $\theta : \Gamma \lei \Theta$,
$\Gamma \entails \upsilon \type$, $\Gamma \entails \tau \type$ and
$\Theta \entails \theta\upsilon \equiv \theta\tau$, then
$\Junify{\Gamma}{\upsilon}{\tau}{\Delta}$ for some context $\Delta$.
% with
% $\theta : \Delta \lei \Theta$. That is, if a unifier for $\tau$ and $\upsilon$
% exists, then the algorithm succeeds and delivers a most general unifier.

\item Moreover, if $\theta : \Gamma, \Xi \lei \Theta$,
$\alpha \in \tyvars{\Gamma}$, $\Gamma, \Xi \entails \tau \type$,
$\tau$ is not a variable, $\Xi$ contains only type variable declarations,
$\beta \in \tyvars{\Xi}  \Rightarrow  \beta \in \FTV{\tau, \Xi}$
and $\Theta \entails \theta\alpha \equiv \theta\tau$,
then $\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$ for some context
$\Delta$.
\end{enumerate}
\end{lemma}

\begin{proof}
% We examine the structure of $\upsilon$ (or $\alpha$) and $\tau$, and 
We proceed by induction on the total length of the context, the length of the
context before the bar, and structurally on types. \TODO{Make this clearer.}

(a) Suppose $\theta : \Gamma \lei \Theta$ and
$\Theta \entails \theta\upsilon \equiv \theta\tau$.

If $\tau = \alpha = \upsilon$ are both the same variable,  then the \textsc{Idle}
rule applies, $\Delta = \Gamma$ and the result is trivial.

Now suppose $\upsilon = \alpha$ and $\tau = \beta$ are distinct variables.
Let $\Gamma = \Gamma_0, v D$ and examine $v D$:
\begin{itemize}
\item If $v D = \hole{\alpha}$ then the
\textsc{Define} rule applies and $\Delta = \Gamma_0, \alpha \defn \beta$.
% Now $\theta : \Gamma_0 \lei \Delta$ preserves definitions in $\Gamma_0'$, and
% $\Delta \entails \theta\alpha \equiv \theta\beta$ by hypothesis, so
% $\theta : \Gamma_1 \lei \Delta$.
The case $v D = \hole{\beta}$ is similar.

\item If $v D = \alpha \defn \chi$ then
$\Theta \entails \theta\alpha \equiv \theta\chi$ by definition of $\lei$,
and $\Theta \entails \theta\alpha \equiv \theta\beta$ by hypothesis,
so $\Theta \entails \theta\beta \equiv \theta\chi$ by transitivity and symmetry.
But then $\theta_\alpha : \Gamma_0 \lei \Theta$ and
$\Theta \entails \theta_\alpha\beta \equiv \theta_\alpha\chi$,
so by induction,
$\Junify{\Gamma_0}{\beta}{\chi}{\Delta_0}$
for some $\Delta_0$.
% with $\theta_\alpha : \Gamma_1' \lei \Delta$.
Hence the \textsc{Expand} rule applies and
$\Delta = \Delta_0, \alpha \defn \upsilon$.
%and $\theta : \Gamma_1 \lei \Delta$.
The case $v D = \beta \defn \upsilon$ is similar.
\TODO{Define $\theta_\alpha$ and possibly prove the relevant lemma.}

\item Otherwise, $v D \perp \{ \alpha, \beta \}$ and the \textsc{Ignore} rule
applies by a similar argument.
\end{itemize}

Now suppose $\tau = \tau_0 \arrow \tau_1$ and
$\upsilon = \upsilon_0 \arrow \upsilon_1$.
Then $\Theta \entails \theta\tau_0 \equiv \theta\upsilon_0$ and
$\Theta \entails \theta\tau_1 \equiv \theta\upsilon_1$,
so by induction there exist contexts
$\Delta'$ and $\Delta$ such that
$\Junify{\Gamma}{\tau_0}{\upsilon_0}{\Delta'}$ and
$\Junify{\Delta'}{\tau_1}{\upsilon_1}{\Delta}$.
%, with $\theta : \Gamma \lei \Delta$ and $\theta : \Gamma_1 \lei \Delta$.
Hence the \textsc{Decompose} rule applies.

Finally, suppose wlog that $\upsilon = \alpha$ is a variable and $\tau$ is not a
variable. By part (b),
$\Jinstantiate{\Gamma}{\alpha}{\tau}{\emptycontext}{\Delta}$
and the \textsc{Solve} rule applies.


(b) Suppose $\theta : \Gamma, \Xi \lei \Theta$ and
$\Theta \entails \theta\alpha \equiv \theta\tau$.
% where $\Xi$ contains only type variable declarations and $\upsilon$ is not a
% variable.
Let $\Gamma = \Gamma_0, v D$.
\begin{itemize}
\item If $v D = \hole{\alpha}$ and $\alpha \notin \FTV{\tau, \Xi}$, then the
\textsc{DefineS} rule applies and $\Delta = \Gamma_0, \Xi, \alpha := \tau$.
% Now $\theta$ preserves  definitions in $\Gamma_0, \Xi$ and
% $\Delta \entails \theta\alpha \equiv \theta\upsilon$
% by hypothesis, so $\theta : \Gamma_1 \lei \Delta$.

\item If $v D = \alpha \defn \chi$ and $\alpha \notin \FTV{\tau, \Xi}$, then
$\Theta \entails \theta\alpha \equiv \theta\chi$,
so $\Theta \entails \theta\chi \equiv \theta\tau$ by symmetry and transitivity. 
Moreover, $\Gamma_0, \Xi \entails \valid$ and $\Gamma_0, \Xi \entails \tau \type$
since $\alpha \notin \FTV{\tau, \Xi}$, and
$\theta_\alpha : \Gamma_0, \Xi \lei \Theta$
so by induction
$\Junify{\Gamma_0, \Xi}{\chi}{\tau}{\Delta_0}$
for some $\Delta_0$, and the \textsc{ExpandS} rule applies with
$\Delta = \Delta_0, \alpha \defn \chi$.

\item If $v = \alpha$ and $\alpha \in \FTV{\tau, \Xi}$, then there is some
non-variable type $\tau'$ such that
$\Theta \entails \theta\alpha \equiv \theta\tau'$
and $\alpha \in \FTV{\tau'}$. But this cannot occur, by
lemma~\ref{lem:occurCheck}.

% \item If $v = \alpha$ and $\alpha \in \FTV{\Xi}$ then $\alpha \in \FTV{\chi}$
% for some $\chi$ with $\Xi = \Xi_0, \beta \defn \chi, \Xi_1$ and
% $\beta \in \FTV{\tau, \Xi_1}$.
% \TODO{Prove this is contradictory.}

\item If $v = \beta$ for $\alpha \neq \beta$ and
$\beta \in \FTV{\upsilon, \Xi}$ then
$\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\beta D, \Xi}{\Delta}$
is well-posed, so it has a solution by induction and
the \textsc{DependS} rule applies. \TODO{Reword this.}

\item Otherwise $v D \perp \FTV{\alpha, \tau, \Xi}$ and
$\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\Xi}{\Delta_0}$
is well-posed, so it has a solution by induction and
the \textsc{IgnoreS} rule applies with $\Delta = \Delta_0, v D$.
\qedhere
\end{itemize}
\end{proof}


\subsection{Implementing unification}

First, we define some helpful machinery.
The |onTop| operator applies its argument to the topmost type variable
declaration in the context, skipping over any other kinds of entry. The argument
function may |restore| the previous entry by returning |Nothing|, or it may
return a context extension (that contains at least as much information as the
entry that has been removed) with which to |replace| it.

> onTop ::  (TyEntry -> Contextual (Maybe Suffix)) 
>             -> Contextual ()
> onTop f = do
>     _Gamma :< vD <- getContext
>     putContext _Gamma
>     case vD of
>         TY alphaD    -> do  m <- f alphaD
>                             case m of
>                                 Just _Xi  -> modifyContext (<>< _Xi)
>                                 Nothing   -> modifyContext (:< vD)
>         _            -> onTop f >> modifyContext (:< vD)

> restore :: Contextual (Maybe Suffix)
> restore = return Nothing

> replace :: Suffix -> Contextual (Maybe Suffix)
> replace = return . Just


The |unify| function attempts to modify the context to produce a most general
unifier for the two given types; it will fail if the types cannot be
unified given the current state of the context.

> unify :: Type -> Type -> Contextual ()
> unify (V alpha) (V beta) = onTop $ \ (delta := mt) -> case
>           (delta == alpha,  delta == beta,  mt        ) of
>           (True,            True,           _         )  ->  restore                                 
>           (True,            False,          Hole      )  ->  replace (alpha := Some (V beta) :> F0)  
>           (False,           True,           Hole      )  ->  replace (beta := Some (V alpha) :> F0)  
>           (True,            False,          Some tau  )  ->  unify (V beta)   tau       >> restore   
>           (False,           True,           Some tau  )  ->  unify (V alpha)  tau       >> restore   
>           (False,           False,          _         )  ->  unify (V alpha)  (V beta)  >> restore   
> unify (V alpha)        tau                               =   solve alpha F0 tau
> unify tau              (V alpha)                         =   solve alpha F0 tau    
> unify (tau0 :-> tau1)  (upsilon0 :-> upsilon1)           =   unify tau0 upsilon0 >> unify tau1 upsilon1


The |solve| function attempts to unify a variable name with a
(non-variable) type, given a list of entries that the type depends on,
which must be placed into the context before it.

> solve :: TyName -> Suffix -> Type -> Contextual ()
> solve alpha _Xi tau = onTop $ \ (delta := mt) -> 
>     let occurs = delta <? tau || delta <? _Xi in case
>     (delta == alpha,  occurs,  mt            ) of
>     (True,            True,    _             )  ->  fail "Occur check failed"
>     (True,            False,   Hole          )  ->  replace (_Xi <+> (alpha := Some tau :> F0))
>     (True,            False,   Some upsilon  )  ->  modifyContext (<>< _Xi)
>                                                 >>  unify upsilon tau
>                                                 >>  restore
>     (False,           True,    _             )  ->  solve alpha (delta := mt :> _Xi) tau
>                                                 >>  replace F0   
>     (False,           False,   _             )  ->  solve alpha _Xi tau
>                                                 >>  restore


%%%The |(<?)| typeclass function tests if a name occurs in a type or context
%%%suffix, since these are both |Foldable| functors containing names.


\section{The type inference problem}

\subsection{Introducing type schemes}

Having implemented unification, we now turn to the problem of type inference
for terms. We will reuse the abstract framework already introduced, defining
a new sort $\TM$ for term variables. To handle polymorphism, these need to
be associated with type schemes rather than monomorphic types.

A \define{type scheme} $\sigma$ is a type wrapped in one or more $\forall$
quantifiers or let bindings, with the syntax
$$\sigma ::= .\tau ~||~ \forall\alpha~\sigma ~||~ \letS{\alpha}{\tau}{\sigma}.$$
We use explicit definitions in type schemes to avoid the need for substitution
in the type inference algorithm. 

We define a new statement $\sigma \scheme$
% ($\sigma$ is a valid scheme in $\Gamma$)
by the rules in Figure~\ref{fig:schemeValidityRules}.
We observe the sanity condition
$\Gamma \entails \sigma \scheme  \Rightarrow  \Gamma \entails \valid$.

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


The structure of these rules strongly suggests that schemes arise by discharging
a list of type variable declarations over a type. In fact, any scheme can be
viewed in this way. We write $\gen{\Xi}{\sigma}$ for the generalisation of
the type scheme $\sigma$ over the list of type variable declarations $\Xi$,
defined by
\begin{align*}
\emptycontext         &\genarrow \sigma = \sigma  \\
\Xi, \hole{\alpha}    &\genarrow \sigma = \Xi \genarrow \forall\alpha~\sigma  \\
\Xi, \alpha \defn \nu &\genarrow \sigma = \Xi \genarrow \letS{\alpha}{\nu}{\sigma}
\end{align*}
We will usually be interested in the case $\sigma = .\tau$      for some type $\tau$.

\begin{lemma}
\label{lem:generalise}
If $\Gamma, \Xi \entails \sigma \scheme$ where $\Xi$ contains only type variable
declarations, then $\Gamma \entails \gen{\Xi}{\sigma} \scheme$.
\end{lemma}
\begin{proof}
By induction on the length of $\Xi$.
\end{proof}


\subsection{Implementing type schemes}

It is convenient to represent bound variables by de Brujin indices and free
variables (i.e.\ those defined in the context) by names
\citep{mcbride_mckinna_not_number_2004}.
Moreover, we use the
Haskell type system to prevent some incorrect manipulations of indices by
defining a \scare{successor} type
\citep{bird_paterson_nested_1999, bellegarde_hook_substitution_1994}

> data Index a = Z | S a

<     deriving (Functor, Foldable)

We can then represent schemes as

> data Schm a  =  Type (Ty a) 
>              |  All (Schm (Index a))
>              |  LetS (Ty a) (Schm (Index a))

<     deriving (Functor, Foldable)

> type Scheme = Schm TyName

The outermost bound variable is represented by |Z| and the other variables
are wrapped in the |S| constructor. For example, the type scheme
$\forall\alpha\forall\beta.\beta \arrow 2$ is represented as

< All (All (Type (V (S Z) :-> V (S (S 2)))))

Note that the code forces us to distinguish a type $\tau$ and its corresponding
type scheme (written $.\tau$), as the latter will be represented by
|Type tau :: Scheme|.


Implementing the generalisation function is straightforward:

> (>=>) :: Bwd TyEntry -> Scheme -> Scheme
> B0                      >=> sigma = sigma
> (_Xi :< alpha :=   mt)  >=> sigma = case mt of
>                    Hole     -> _Xi >=> All sigma'
>                    Some nu  -> _Xi >=> LetS nu sigma'
>   where 
>     sigma' = fmap bind sigma
>     bind beta  | alpha == beta  = Z
>                | otherwise      = S beta


\subsection{Term variables}

Let $\V_\TM$ be some set of term variables and let $x$ range over $\V_\TM$.
Term variable declarations $\D_\TM$ are scheme assignments of the form
$\asc \sigma$, with
$\ok_\TM (\asc \sigma) = \sigma \scheme$.

We define the statement $x \hasc \sigma$ by the rules in
Figure~\ref{fig:termVarSchemeRules}, and let
$\sem{x \asc \sigma}_\TM = \{ x \hasc \sigma \}$.
Thus a term variable has a scheme $\sigma'$ if it is given scheme $\sigma$ in
the context and $\sigma$ specialises to $\sigma'$.
We observe the sanity condition
$\Gamma \entails x \hasc \sigma  \Rightarrow  \Gamma \entails \sigma \scheme$.

\begin{figure}[ht]
\boxrule{\Gamma \entails x \hasc \sigma}
$$
\Rule{\upsilon \type   ~\wedge~   x \hasc \forall \alpha \sigma}
     {x \hasc \subst{\upsilon}{\alpha}{\sigma}}
\qquad
\Rule{x \hasc \letS{\alpha}{\upsilon}{\sigma}}
     {x \hasc \subst{\upsilon}{\alpha}{\sigma}}
$$
\caption{Rules for scheme assignment to term variables}
\label{fig:termVarSchemeRules}
\end{figure}

It may appear that this definition of scheme assignment is overly restrictive,
because it offers no way to permute quantifiers or specialise inner variables
without specialising outer ones first. However, this will not be a problem for
type inference, because we always work with fully specialised schemes.
Indeed, the changes to type schemes that can occur on information increase are
deliberately limited, to ensure terms have principal types.
\TODO{Characterise and prove result needed for let completeness.}

% We are not going to substitute for term variables, so we let $\T_\TM = \V_\TM$
% and assume that $\TM$-substitutions are always the identity map.
% \TODO{Comment on what would happen if we did allow term substitutions.}


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


In the implementation, we extend the definition of |Entry|:

> type TmName   = String
> data TmEntry  = TmName ::: Scheme

< data Entry    = TY TyEntry | TM TmEntry | ...




\subsection{Type assignment system}

The syntax of terms is
$$t ::= x ~||~ t~t ~||~ \lambda x . t ~||~ \letIn{x}{t}{t}.$$
% where $x$ ranges over some set of term variables.

We define the type assignability statement $t : \tau$ by the rules in
Figure~\ref{fig:typeAssignmentRules}, and the scheme assignability statement
$t \hasscheme \sigma$ for arbitrary terms $t$ and schemes $\sigma$ thus:
\begin{align*}
t \hasscheme .\tau   &\mapsto    t : \tau  \\
t \hasscheme \forall \alpha \sigma  &\mapsto 
    \Sbind{\hole{\alpha}}{t \hasscheme \sigma}   \\
t \hasscheme \letS{\alpha}{\tau}{\sigma}  &\mapsto
    \Sbind{\alpha \defn \tau}{t \hasscheme \sigma}
\end{align*}

We observe the sanity condition
$\Gamma \entails x : \tau  \Rightarrow  \Gamma \entails \tau \type$.

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



As with unification, we wish to translate these declarative rules into an
algorithm for type inference. We define the type inference problem $I$ by
\begin{align*}
\In{I} &= \Term  \\
\Out{I} &= \Type  \\
\Pre{I}(t) &= \valid  \\
\Post{I}(t)(\tau) &= \tau \type \wedge t : \tau  \\
\R{I}(\tau)(\upsilon) &= \tau \equiv \upsilon
\end{align*}



\section{Local contexts for local problems}

\subsection{Preserving order in the context}

We have previously observed \TODO{(have we?)}, but not yet made use of, the
property that order in the context is important and we move declarations left as
little as possible. Thus the rightmost entries are the most local to the problem
we are solving. This will be useful when we come to implement type inference
for the |Let| construct, as we want to generalise over \scare{local} type
variables but not \scare{global} variables.

In order to keep track of locality in the context, we need another kind of
context extension: the $\fatsemi$ separator. We add the context validity rule
$$
\Rule{\Gamma \entails \valid}
     {\Gamma \fatsemi \entails \valid}
$$
so the (finally) complete data type of context entries is:

> data Entry = TY TyEntry | TM TmEntry | LetGoal

We also need to refine the $\lei$ relation.
Let $\semidrop$ be the partial function from contexts and natural numbers to
contexts that takes $\Gamma \semidrop n$ to $\Gamma$ truncated after $n$
$\fatsemi$ separators, provided $\Gamma$ contains at least $n$ of them. It is
defined by
\begin{align*}
\Xi \semidrop 0 &= \Xi  \\
\Xi \fatsemi \Gamma \semidrop 0 &= \Xi  \\
\Xi \fatsemi \Gamma \semidrop n+1 &= \Xi \fatsemi (\Gamma \semidrop n)  \\
\Xi \semidrop n+1 &~\mathrm{undefined}
\end{align*}

We write $\delta : \Gamma \lei \Delta$ if $\delta$ is a
substitution from $\Gamma$ to $\Delta$ such that, for every
$v D \in \Gamma \semidrop n$ and $S \in \sem{v D}$, we have that
$\Delta \semidrop n$ is defined and
$\Delta \entails \delta S$.

This definition of $\Gamma \lei \Delta$ is stronger than the previous definition,
because it requires a correspondence between the $\fatsemi$-separated sections of
$\Gamma$ and $\Delta$, such that declarations in the first $n$ sections of
$\Gamma$ can be interpreted over the first $n$ sections of $\Delta$.
However, it is mostly straightforward to verify that the previous results go
through with the new definition.

%% Note that if $\delta : \Gamma \lei \Delta$ then
%% $\delta||_{\Gamma \semidrop n} : \Gamma \semidrop n \lei \Delta \semidrop n$. 


\subsection{Fixing the unification algorithm}

The only place where the change is nontrivial is in the unification algorithm,
because it acts structurally over the context, so we need to specify what happens
when it finds a $\fatsemi$ separator. It turns out that these can simply be
ignored, so we add the following algorithmic rules:
$$
\name{Skip}
\Rule{\Junify{\Gamma_0}{\alpha}{\beta}{\Delta_0}}
     {\Junify{\Gamma_0 \fatsemi}{\alpha}{\beta}{\Delta_0 \fatsemi}}
$$
$$
\name{Repossess}
\Rule{\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\Xi}{\Delta_0}}
     {\Jinstantiate{\Gamma_0 \fatsemi}{\alpha}{\tau}{\Xi}{\Delta_0 \fatsemi}}
$$
Proving correctness of the \textsc{Skip} rule is relatively straightforward,
thanks to the following lemma.

\begin{lemma}
If $\delta : \Jmin{\Gamma}{\Prob{P}{a}{b}}{\Delta}$ then
$\delta : \Jmin{\Gamma \fatsemi}{\Prob{P}{a}{b}}{\Delta \fatsemi}$.
\end{lemma}

The \textsc{Repossess} rule is more complicated. It is so named because it moves
the variable declarations in $\Xi$ to the left of the $\fatsemi$ separator,
thereby \scare{repossessing} them. Despite this, unification does still
produce a most general solution:

\begin{lemma}[Soundness and generality of \textsc{Repossess} rule]
If $\Jinstantiate{\Gamma \fatsemi}{\alpha}{\tau}{\Xi}{\Delta \fatsemi}$
then $\tyvars{\Gamma \fatsemi \Xi} = \tyvars{\Delta \fatsemi}$ and
$\iota : \Jmin{\Gamma \fatsemi \Xi}{\Puni{\alpha}{\tau}}{\Delta \fatsemi}$.
\end{lemma}
\begin{proof}
Suppose $\Jinstantiate{\Gamma \fatsemi}{\alpha}{\tau}{\Xi}{\Delta \fatsemi}$,
so $\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$ as only the
\textsc{Repossess} rule applies.
By induction and lemma~\ref{lem:unifySound},
$\tyvars{\Gamma, \Xi} = \tyvars{\Delta}$ and
$\iota : \Jmin{\Gamma, \Xi}{\Puni{\alpha}{\tau}}{\Delta}$.

For the first part, we have
$$\tyvars{\Gamma \fatsemi \Xi} = \tyvars{\Gamma, \Xi} = \tyvars{\Delta}
    = \tyvars{\Delta \fatsemi}.$$

For the second part, since $\iota : \Gamma, \Xi \lei \Delta$ we have
$\iota : \Gamma \fatsemi \Xi \lei \Delta \fatsemi$,
and $\Delta \entails \alpha \equiv \tau$ so
$\Delta \fatsemi \entails \alpha \equiv \tau$.

For minimality, suppose
$\theta : \Gamma \fatsemi \Xi \lei \Theta \fatsemi \Phi$
and $\Theta \fatsemi \Phi \entails \theta\alpha \equiv \theta\tau$.
Observe that  $\alpha \in \tyvars{\Gamma}$ and
$\beta \in \tyvars{\Xi}  \Rightarrow  \beta \in \FTV{\tau, \Xi}$
by the sanity conditions.
Now $\theta\alpha$ is a $\Theta$-type and $\theta\tau$ is equal to it,
so the only declarations in $\Phi$ that $\theta\tau$ (hereditarily) depends on
must be definitions over $\Theta$. But all the variables declared in $\Xi$ are
used in $\tau$, so there is a substitution
$\psi : \Gamma \fatsemi \Xi \lei \Theta \fatsemi$
that agrees with $\theta$ on $\Gamma$ and maps variables in $\Xi$ to their
definitions in $\Theta$.
Note that $\psi \eqsubst \theta : \Gamma \fatsemi \Xi \lei \Theta \fatsemi \Phi$.

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


% \subsection{A new composite statement}
% 
% \TODO{Do we actually use this anywhere? Perhaps it is redundant.}
% 
% If $S$ is a statement then $\fatsemi S$ is a composite statement given by
% $$
% \Rule{\Gamma \fatsemi \entails S}
%      {\Gamma \entails \fatsemi S}.
% $$
% If $S$ is stable then $\fatsemi S$ is stable, which we can see as follows.
% Suppose $\Gamma \entails \fatsemi S$ and $\delta : \Gamma \lei \Delta$. Then
% $\Gamma \fatsemi \entails S$, and
% $\delta : \Gamma \fatsemi \lei \Delta \fatsemi$
% by the new definition of the $\lei$ relation. Hence
% $\Delta \fatsemi \entails \delta S$ by stability and so
% $\Delta \entails \delta (\fatsemi S)$.




\section{A type inference algorithm}

\subsection{Introducing specialisation}

Consider the variable rule for type assignment, which is
$$\Rule{x \hasc .\tau}
       {\Pinf{x}{\tau}}.$$
We need an algorithm that, given a term variable as input, finds a type that
can be assigned to it (by specialising its scheme).

Let $S$ be the problem given by
\begin{align*}
\In{S}                 &= \V_\TM  \\
\Out{S}                &= \Type  \\
\Pre{S} (x)            &= \valid  \\
\Post{S} (x, \tau)     &= \tau \type \wedge x \hasc .\tau  \\
\R{S} (\tau, \upsilon) &= \tau \equiv \upsilon
\end{align*}

The assertion $\Jspec{\Gamma}{\sigma}{\tau}{\Gamma, \Xi}$ means
that, starting with the context $\Gamma$, the scheme $\sigma$ specialises
to the type $\tau$ when the context is extended with some type variable
declarations $\Xi$. It is defined in Figure~\ref{fig:specialiseAlgorithm}.
We define $\Jhast{\Gamma}{x}{\sigma}{\tau}{\Gamma, \Xi}$ to mean
$\Gamma \entails x \hasc \sigma$ and
$\Jspec{\Gamma}{\sigma}{\tau}{\Gamma, \Xi}$.


\begin{figure}[ht]
\boxrule{\Jspec{\Gamma}{\sigma}{\tau}{\Gamma, \Xi}}

$$
\name{T}
\Rule{\Gamma \entails \tau \type}
     {\Jspec{\Gamma}{.\tau}{\tau}{\Gamma}}
$$

$$
\name{All}
\Rule{\Jspec{\Gamma, \hole{\beta}}{\subst{\beta}{\alpha}{\sigma}}{\tau}
            {\Gamma, \hole{\beta}, \Xi}}
     {\Jspec{\Gamma}{\forall\alpha~\sigma}{\tau}{\Gamma, \hole{\beta}, \Xi}}
\side{\beta \notin \tyvars{\Gamma}}
$$

$$
\name{LetS}
\Rule{\Jspec{\Gamma, \beta \defn \upsilon}{\subst{\beta}{\alpha}{\sigma}}{\tau}
            {\Gamma, \beta \defn \upsilon, \Xi}}
     {\Jspec{\Gamma}{\letS{\alpha}{\upsilon}{\sigma}}{\tau}
            {\Gamma, \beta \defn \upsilon, \Xi}}
\side{\beta \notin \tyvars{\Gamma}}
$$

\caption{Algorithmic rules for specialisation}
\label{fig:specialiseAlgorithm}
\end{figure}



\begin{lemma}[Soundness and minimality of specialisation]
\label{lem:specialiseSound}
If $\Jhast{\Gamma}{x}{\sigma}{\tau}{\Gamma, \Xi}$, then
$\iota : \Jmin{\Gamma}{\Prob{S}{x}{\tau}}{\Gamma, \Xi}$.
\end{lemma}

\begin{proof}
Clearly $\iota : \Gamma \lei \Gamma, \Xi$.
By structural induction on $\sigma$,
$$\Gamma, \Xi \entails \tau \type \wedge x \hasc .\tau.$$

For minimality, suppose
$\theta : \Gamma \lei \Theta \entails \Prob{S}{x}{\upsilon}$.
By stability, $\Theta \entails x \hasc \sigma$.
Examining the rules in Figure~\ref{fig:termVarSchemeRules}, the proof of
$\Theta \entails x \hasc .\tau$ must specialise $\sigma$ with types
$\Psi$ for its generic variables. Let $\theta' = \subst{\Psi}{\Xi}{\theta}$, then
$\theta' : \Gamma, \Xi \lei \Theta$ and $\theta = \theta' \compose \iota$.

\end{proof}

\begin{lemma}[Completeness of specialisation]
\label{lem:specialiseComplete}
If $\Gamma \entails x \hasc \gen{\Xi}{\tau}$ then
$\Jhast{\Gamma}{x}{\sigma}{\tau}{\Gamma, \Xi}$.

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
By structural induction on $\Xi$.
\end{proof}


\subsection{Implementing specialisation}

The |specialise| function will specialise a type scheme with fresh variables
to produce a type. That is, given a scheme $\sigma$ it computes a most general
type $\tau$ such that $\sigma \succ \tau$.

> specialise :: Scheme -> Contextual Type

If a $\forall$ quantifier is outermost, it is removed and an unbound fresh type
variable is substituted in its place (applying the \textsc{All} rule).

> specialise (All sigma) = do
>     beta <- fresh Hole
>     specialise (schemeUnbind beta sigma)

If a let binding is outermost, it is removed and added to the context with a
fresh variable name (applying the \textsc{LetS} rule).

> specialise (LetS tau sigma) = do
>     beta <- fresh (Some tau)
>     specialise (schemeUnbind beta sigma)

This continues until a scheme with no quantifiers is reached, which can simply be
converted into a type (applying the \textsc{T} rule).

> specialise (Type tau) = return tau


The |schemeUnbind| function converts the body $\sigma$ of the scheme
$\forall\alpha.\sigma$ or $\letS{\alpha}{\tau}{\sigma}$ into
$\subst{\beta}{\alpha}{\sigma}$. Since we use different syntactic
representations for free and bound variables, this is easy to implement.

> schemeUnbind
>   :: TyName -> Schm (Index TyName) -> Scheme
> schemeUnbind beta = fmap fromS
>   where
>     fromS :: Index TyName -> TyName
>     fromS Z           = beta
>     fromS (S alpha')  = alpha'



\subsection{Transforming the rule system}

To transform a rule into an algorithmic form, we proceed clockwise starting from
the conclusion. For each hypothesis, we must ensure that the problem is fully
specified, inserting variables to stand for unknown problem inputs. Moreover, we
cannot pattern match on problem outputs, so we ensure there are schematic
variables in output positions, fixing things up with appeals to unification. 

Consider the rule for application, written to highlight problem inputs and
outputs as
$$\Rule{\Pinf{f}{(\upsilon \arrow \tau)}  \quad  \Pinf{a}{\upsilon}}
       {\Pinf{f a}{\tau}}.$$
Since we cannot pattern match on the output of the first subproblem, we use a
metavariable instead and add a unification constraint, giving
$$\Rule{\Pinf{f}{\chi}  \quad \Pinf{a}{\upsilon}
            \quad  \Puni{\chi}{\upsilon \arrow \tau}}
       {\Pinf{f a}{\tau}}.$$
Furthermore, $\tau$ is an input to the unification problem, but it is not
determined by the previous inputs or outputs, so we have to bind a fresh variable
$\beta$ instead to give the algorithmic version
$$\Rule{\Pinf{f}{\chi}
        \quad
        \Pinf{a}{\upsilon}
        \quad
        \Sbind{\beta \defn \tau}{\Puni{\chi}{\upsilon \arrow \beta}}
       }
       {\Sbind{\beta \defn \tau}{\Pinf{f a}{\beta}}}.$$


%if False
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
%endif


The rule for abstraction is
$$\Rule{\Sbind{x \asc .\upsilon}{\Pinf{t}{\tau}}}
       {\Pinf{\lambda x . t}{\upsilon \arrow \tau}}$$
which has $\upsilon$ as an unknown input, so we bind a fresh variable $\beta$
to give
$$\Rule{\Sbind{\beta \defn \upsilon}{\Sbind{x \asc .\beta}{\Pinf{t}{\tau}}}}
       {\Sbind{\beta \defn \upsilon}{\Pinf{\lambda x . t}{\beta \arrow \tau}}}.$$

% and hence
% $$
% \Rule{\Jtype{\Gamma_0, \hole{\beta}, x \asc .\beta}{t}{\tau}
%           {\Gamma_1, x \asc .\beta, \Xi}}
%      {\Jtype{\Gamma_0}{\lambda x.t}{\beta \arrow \tau}{\Gamma_1, \Xi}}
% $$


The let rule is
$$
\Rule{
      s \hasscheme \sigma
      \quad
      \Sbind{x \asc \sigma}{t : \tau}
     }
     {\Pinf{\letIn{x}{s}{t}}{\tau}}.
$$
Writing $\sigma = \gen{\Xi}{\upsilon}$ and expanding the definition of
$\hasscheme$, we obtain
$$
\Rule{
      \Sbind{\Xi}{s : \upsilon}
      \quad
      \Sbind{x \asc \gen{\Xi}{\upsilon}}{t : \tau}
     }
     {\Pinf{\letIn{x}{s}{t}}{\tau}}.
$$
where we let $\Sbind{\emptycontext}{S} = S$ and
$\Sbind{\Xi, v D}{S} = \Sbind{\Xi}{\Sbind{v D}{S}}$.


But how can we find $\Xi$?
This is where the $\fatsemi$ context separator becomes necessary. Instead of an
unknown list of type variables, we simply add a $\fatsemi$ to the context, 
infer the type of $s$, then generalise its type by \scare{skimming off} the type
variables from the top of the context until the $\fatsemi$ is reached.


% which we transform to \TODO{what?}
% $$
% \Rule{
%       \fatsemi (s : \upsilon)
%       \quad
%       x \asc \upsilon \Yup t : \tau
%      }
%      {\Pinf{\letIn{x}{s}{t}}{\tau}}
% $$
% where $\Yup$ is defined via
% $$
% \Rule{\Gamma \entails \Sbind{x \asc \gen{\Xi}{\sigma}}{S}}
%      {\Gamma \fatsemi \Xi \entails x \asc \upsilon \Yup S}
% $$


We define the type inference assertion $\Jtype{\Gamma}{t}{\tau}{\Delta}$
% (inferring the type of $t$ in $\Gamma_0$ yields $\tau$ in the more informative
% context $\Gamma_1$)
by the rules in Figure~\ref{fig:inferRules}.
These rules are clearly structural on terms, so they give a terminating
algorithm, and they lead naturally to an implementation, given in
subsection~\ref{sec:inferImplementation}.

\begin{figure}[ht]
\boxrule{\Jtype{\Gamma}{t}{\tau}{\Delta}}

$$
\name{Var}
\Rule{\Jhast{\Gamma}{x}{\sigma}{\tau}{\Gamma, \Xi}}
     {\Jtype{\Gamma}{x}{\tau}{\Gamma, \Xi}}
$$

$$
\name{Abs}
\Rule{\Jtype{\Gamma, \hole{\alpha}, x \asc .\alpha}{w}{\upsilon}
          {\Delta_0, x \asc .\alpha, \Xi}}
     {\Jtype{\Gamma}{\lambda x.w}{\alpha \arrow \upsilon}{\Delta_0, \Xi}}
\side{\alpha \notin \tyvars{\Gamma}}
$$

$$
\name{App}
\BigRule{\Jtype{\Gamma}{f}{\chi}{\Delta_0}
         \quad
         \Jtype{\Delta_0}{a}{\upsilon}{\Delta_1}}
        {\Junify{\Delta_1, \hole{\beta}}{\chi}{\upsilon \arrow \beta}{\Delta}}
        {\Jtype{\Gamma}{f a}{\beta}{\Delta}}
\side{\beta \notin \tyvars{\Delta_1}}
$$

$$
\name{Let}
\BigRule{\Jtype{\Gamma \fatsemi}{s}{\upsilon}{\Delta_0 \fatsemi \Xi_0}}
        {\Jtype{\Delta_0, x \asc \gen{\Xi_0}{.\upsilon}}{t}{\chi}
               {\Delta_1, x \asc \gen{\Xi_0}{.\upsilon}, \Xi_1}}
        {\Jtype{\Gamma}{\letIn{x}{s}{t}}{\chi}{\Delta_1, \Xi_1}}
$$

\caption{Algorithmic rules for type inference}
\label{fig:inferRules}
\end{figure}


\subsection{Soundness and completeness}

% We say $\Theta$ is a \define{subcontext} of $\Gamma$, written
% $\Theta \subcontext \Gamma$, if $\Gamma = \Theta; \Gamma'$ for some context
% extension $\Gamma'$.


\begin{lemma}[Soundness and generality of type inference]
\label{lem:inferSound}
If $\Jtype{\Gamma}{t}{\tau}{\Delta}$, then
$\iota : \Jmin{\Gamma}{\Pinf{t}{\tau}}{\Delta}$.
% \begin{enumerate}[(a)]
% \item $\Gamma_1 \entails t : \tau$;
% \item $\tyvars{\Gamma_0} \subseteq \tyvars{\Gamma_1}$; and
% % \item $\forget{\Gamma_0} = \forget{\Gamma_1}$;
% \item $\iota : \Gamma_0 \lei \Gamma_1$, where $\iota$ is the inclusion
%       substitution.
%% \item if $\Theta_0 \subcontext \Gamma_0$ and $\Theta_1 \subcontext \Gamma_1$
%% are such that
%%    $\forget{\Theta_0} = \forget{\Theta_1}$, then
%%    $\tyvars{\Theta_0} \subseteq \tyvars{\Theta_1}$ and
%%    $\iota : \Theta_0 \lei \Theta_1$.
% \end{enumerate}
\end{lemma}

\begin{proof}
By induction on the structure of derivations.
\TODO{Need a bit more here.}
\end{proof}


\begin{lemma}[Completeness of type inference]
If $\theta : \Gamma \lei \Theta$ and $\Theta \entails t : \tau$ then
$\Jtype{\Gamma}{t}{\upsilon}{\Delta}$
for some type $\upsilon$ and context $\Delta$.

% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0;}{t}{\upsilon}{\Gamma_1; \Xi}$,
% \item $\theta_1 : \Gamma_1; \lei \Delta$ with 
% $\theta_0\alpha = \theta_1\alpha$ for any $\alpha \in \tyvars{\Gamma_0}$, and
% \item $\Gamma_1; \entails t :: \gen{\Xi}{\upsilon}$ principal.
% \end{enumerate}
\end{lemma}

\begin{proof}
If $t = x$ is a variable, then by inversion $\Theta \entails x \hasc .\tau$
Now by definition of $\lei$,
$\Gamma \entails x \asc \sigma$ for some $\sigma$,
% with
% $$\forall \upsilon. \Theta \entails \theta\sigma' \succ \upsilon
%     \Leftrightarrow \Theta \entails x : \upsilon.$$
so by completeness of specialisation (lemma~\ref{lem:specialiseComplete}),
$\Jhast{\Gamma}{x}{\sigma}{\upsilon}{\Gamma, \Xi}$
% and
% $$\forall\tau \forall \phi: \Gamma_0 \lei \Phi . (
%     \Phi \entails \phi\sigma' \succ \tau
%         \Leftrightarrow  \Phi \entails \phi\gen{\Xi}{\upsilon} \succ \tau.$$
Hence the \textsc{Var} rule applies giving
$\Jtype{\Gamma}{x}{\upsilon}{\Gamma, \Xi}$.
% (b) holds trivially with $\theta_1 = \theta_0$, and
% $\Gamma_0 \entails x \hasscheme \gen{\Xi}{\upsilon}$ principal.


If $t = (\letIn{x}{s}{w})$, then by inversion there is some scheme
$\sigma$ such that $\Theta \entails s \hasscheme \sigma$ and
$\Theta, x \asc \sigma \entails w : \tau$.
Let $\sigma = \gen{\Psi}{.\tau_s}$,
then $\Theta \fatsemi \entails s \hasscheme \gen{\Psi}{.\tau_s}$ so
$\Theta \fatsemi \Psi \entails s : \tau_s$.

Moreover $\theta : \Gamma \fatsemi \lei \Theta \fatsemi \Psi$, so
by induction
$\Jtype{\Gamma \fatsemi}{s}{\upsilon}{\Delta_0 \fatsemi \Xi_0}$
and by minimality there exists
$\theta_0 : \Delta_0 \fatsemi \Xi_0 \lei \Theta \fatsemi \Psi$
such that $\Theta \entails \theta_0 \upsilon \equiv \tau_s$.

% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0; \letGoal;}{s}{\upsilon}{\Gamma_1; \letGoal; \Xi_1}$
% \item $\theta_1 : \Gamma_1; \letGoal; \lei \Delta, \letGoal; \Psi$
% \item $\Gamma_1; \letGoal; \entails s \hasscheme \gen{\Xi_1}{.\upsilon}$ principal.
% \end{enumerate}

Now 
$\theta_0 ||_{\Delta_0} : \Delta_0 \lei \Theta$, so
$$\theta_0 ||_{\Delta_0} : \Delta_0, x \asc \gen{\Xi_0}{.\upsilon}
    \lei \Theta, x \asc \theta_0\gen{\Xi_0}{.\upsilon}$$
% but
% $$\iota : \Theta, x \asc \sigma \lei \Theta, x \asc \gen{\Xi_0}{.\upsilon}$$
% \TODO{by principality?}, and hence
and
$\Theta, x \asc \theta_0\gen{\Xi_0}{.\upsilon} \entails w : \tau$
since if $\Theta, x \asc \sigma \entails x \hasc .\tau_x$ then
$\Theta, x \asc \theta_0\gen{\Xi_0}{.\upsilon} \entails x \hasc .\tau_x$.
\TODO{Prove this as a lemma.}

Hence, by induction,
$$\Jtype{\Delta_0, x \asc \gen{\Xi_0}{.\upsilon}}{w}{\chi}
        {\Delta_1, x \asc \gen{\Xi_0}{.\upsilon}, \Xi_2}$$
% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_1, x \asc \gen{\Xi_1}{.\upsilon};}{w}{\chi}
% {\Gamma_2; x \asc \gen{\Xi_1}{.\upsilon}; \Xi_2}$
% \item $\theta_2 : \Gamma_2; x \asc \gen{\Xi_1}{.\upsilon};
%   \lei \Delta, x \asc \gen{\Xi_1}{.\upsilon}; \Psi$
% \item $\Gamma_2; x \asc \gen{\Xi_1}{.\upsilon};
%   \entails w \hasscheme \gen{\Xi_2}{.\chi}$ principal
% \end{enumerate}
and the \textsc{Let} rule applies to give
$\Jtype{\Gamma}{\letIn{x}{s}{w}}{\chi}{\Delta_1, \Xi_1}$.
% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0;}{\letIn{x}{s}{w}}{\chi}{\Gamma_2; \Xi_2}$
% \item $\theta_2 : \Gamma_2; \lei \Delta;$ \TODO{Why?}
% \item $\Gamma_2; \entails \letIn{x}{s}{w} \hasscheme \gen{\Xi_2}{.\chi}$
% principal by
% lemma \ref{lem:letSchemePrincipal}.
% \end{enumerate}


If $t = \lambda x . w$ is an abstraction, then by inversion
$\Theta \entails \tau \equiv \tau_0 \arrow \tau_1$
for some types $\tau_0$ and $\tau_1$, and
$\Theta, x \asc .\tau_0 \entails w : \tau_1$.
Taking $\theta' = \subst{\tau_0}{\alpha}{\theta}$, we have that
$$\theta' : \Gamma, \hole{\alpha}, x \asc .\alpha
             \lei  \Theta, x \asc .\tau_0$$
and hence, by induction,
$$\Jtype{\Gamma, \hole{\alpha}, x \asc .\alpha}{w}{\upsilon}
              {\Delta_0, x \asc .\alpha, \Xi}.$$

% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0; \hole{\alpha}, x \asc .\alpha;}{w}{\upsilon}
%              {\Gamma_1; \Phi, x \asc .\alpha; \Xi}$
% \item $\theta_1 : \Gamma_1; \Phi, x \asc .\alpha; \lei \Delta, x \asc .\tau_0;$
% \item $\Gamma_1; \Phi, x \asc .\alpha;
%   \entails w \hasscheme \gen{\Xi}{\upsilon}$
%          principal.
% \end{enumerate}

Thus the \textsc{Abs} rule applies, so we have
$$\Jtype{\Gamma}{\lambda x . w}{\alpha \arrow \upsilon}
              {\Delta_0, \Xi}.$$

% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0;}{\lambda x . w}{\alpha \arrow \upsilon}
%              {\Gamma_1; \Phi, \Xi}$
% \item $\theta_1 : \Gamma_1; \lei \Delta$
% \item $\Gamma_1; \entails \lambda x . w \hasscheme \gen{\Phi, \Xi}{\upsilon}$
%           principal. \TODO{Why?}
% \end{enumerate}


If $t = f a$ is an application, then
$\Theta \entails f : \tau_0 \arrow \tau$,
so by induction
$\Jtype{\Gamma}{f}{\chi}{\Delta_0}$
and by minimality there exists
$\theta_0 : \Delta_0 \lei \Theta$
such that $\Theta \entails \theta_0\chi \equiv \tau_0 \arrow \tau$.
% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0;}{f}{\upsilon}{\Gamma; \Xi}$
% \item $\theta : \Gamma; \lei \Delta$ 
% \item $\Gamma; \entails f \hasscheme \gen{\Xi}{\upsilon}$ principal.
% \end{enumerate}
Now $\Theta \entails a : \tau_0$, so by induction
$\Jtype{\Delta_0}{a}{\upsilon}{\Delta_1}$
and by minimality there exists
$\theta_1 : \Delta_1 \lei \Theta$
such that $\Theta \entails \theta_1\upsilon \equiv \tau_0$ and
$\theta_0 \eqsubst \theta_1 \compose \iota$.

% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma;}{a}{\upsilon_0}{\Gamma_1; \Xi_1}$
% \item $\theta' : \Gamma_1; \lei \Delta$ 
% \item $\Gamma_1; \entails a \hasscheme \gen{\Xi_1}{\upsilon_0}$ principal.
% \end{enumerate}

Let $\theta_2 = \subst{\tau}{\beta}{\theta_1}$, then
$\theta_2 : \Delta_1, \hole{\beta} \lei \Theta$,
and since \TODO{(explain why)}
$$\Theta \entails \theta_2\chi \equiv \tau_0 \arrow \tau
    ~\wedge~
    \tau_0 \arrow \tau \equiv \theta_2(\upsilon \arrow \beta)$$
we have
$\Junify{\Delta_1, \hole{\beta}}{\chi}{\upsilon \arrow \beta}{\Delta}$
by completeness of unification.
Hence the \textsc{App} rule applies, so
$\Jtype{\Gamma}{f a}{\beta}{\Delta}$.

% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0}{f a}{\beta}{\Gamma_2}$
% \item $\theta_1 : \Gamma_2; \lei \Delta$
% \item $\Gamma_2; \entails f a \hasscheme \gen{???}{\beta}$ principal.
% \end{enumerate}


\end{proof}


\subsection{Implementing type inference}
\label{sec:inferImplementation}

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

> type Term      = Tm TmName


The |infer| function attempts to infer the type of the given term,
updating the context with the minimum necessary information.

> infer :: Term -> Contextual Type

To infer the type of a variable, we look up its type scheme in the context,
and specialise this scheme with fresh variables.

> infer (X x) = getContext >>= find >>= specialise
>   where
>     find :: Context -> Contextual Scheme
>     find (_Gamma :< TM (y ::: sigma))
>         | x == y                        = return sigma
>     find (_Gamma :< _)                  = find _Gamma
>     find B0                             = fail "Missing variable"

To infer the type of a $\lambda$-abstraction, we recursively infer the type of its body
$t$ with its variable $x$ assigned type-scheme $.\alpha$, 
%%%where $\alpha$ is 
   with $\alpha$ 
a fresh type variable. The type is then $\alpha \arrow \tau$ in the context with
the $x$ binding removed.

> infer (Lam x t) = do
>     alpha  <- fresh Hole
>     tau    <- x ::: Type (V alpha) >- infer t
>     return (V alpha :-> tau)


To infer the type of an application, we infer the type $\tau$ of the function
$f$, then the type $\tau'$ of the argument. Unifying $\tau$ with
$\tau' \arrow \beta$, where $\beta$ is a fresh variable, produces the
result.

> infer (f :$ a) = do
>     tau   <- infer f
>     tau'  <- infer a
>     beta  <- fresh Hole
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
>     x ::: sigma >- infer t


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
>     skimContext :: Contextual (Bwd TyEntry)
>     skimContext = do
>         _Gamma :< vD <- getContext
>         putContext _Gamma
>         case vD of
>             LetGoal    -> return B0
>             TY alphaD  -> (:< alphaD) <$> skimContext
>             TM _       -> undefined


The |(>-)| operator appends a term variable declaration to the context,
evaluates its second argument, then removes the declaration.

> (>-) :: TmEntry -> Contextual a -> Contextual a
> x ::: sigma >- f = do
>     modifyContext (:< TM (x ::: sigma))
>     tau <- f
>     modifyContext extract
>     return tau
>   where          
>     extract ::  Context -> Context
>     extract (_Gamma :< TM (y ::: _))
>         | x == y               = _Gamma
>     extract (_Gamma :< TY te)  = (extract _Gamma) :< TY te
>     extract (_Gamma :< _)      = undefined

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
> xs <>< (alpha := mt :> ys) = (xs :< TY (alpha := mt) ) <>< ys

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

> alpha *= mt = TY (alpha := mt)

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
