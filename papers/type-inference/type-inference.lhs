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

\usepackage{color}
\definecolor{red}{rgb}{1.0,0.0,0.0}
\newcommand{\TODO}[1]{\NotForPublication{\textcolor{red}{#1}}}
\newcommand{\NotForPublication}[1]{#1}

\newcommand{\eqsubst}{\equiv}
\newcommand{\compose}{\cdot}
\newcommand{\subst}[3]{[#1/#2]#3}

\newcommand{\extend}{\ensuremath{\wedge}}
\newcommand{\yields}{\ensuremath{\dashv}}
\newcommand{\entails}{\ensuremath{\vdash}}
\newcommand{\entailsN}{\ensuremath{\Vdash}}
% \newcommand{\var}{\ensuremath{\defn \_}}
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
% \newcommand{\Scheme}{\ensuremath{\mathit{Scheme}}}

\newcommand{\lei}{\ensuremath{\preceq}}
\newcommand{\LEI}{\ensuremath{~\hat\lei~}}
\newcommand{\leiR}{\ensuremath{\sqsubseteq}}
\newcommand{\LEIR}{\ensuremath{~\hat\sqsubseteq~}}

\newcommand{\arrow}{\ensuremath{\triangleright}}
\newcommand{\defn}{\ensuremath{\!:=\!}}
\newcommand{\asc}{\ensuremath{\hasc}}
\newcommand{\hasc}{\ensuremath{~\hat{::}~}}
\newcommand{\hole}[1]{\ensuremath{#1 \!:= ?}}
\newcommand{\contains}{\ensuremath{\ni}}

\newcommand{\Judge}[3]{\ensuremath{#1 \lei #3 \vdash #2}}
\newcommand{\JudgeR}[3]{\ensuremath{#1 \leiR #3 \vdash #2}}
\newcommand{\Jmin}[3]{\ensuremath{#1 \LEI #3 \vdash #2}}
\newcommand{\Junify}[4]{\Judge{#1}{\Puni{#2}{#3}}{#4}}
\newcommand{\JunifyR}[4]{\JudgeR{#1}{\Puni{#2}{#3}}{#4}}
\newcommand{\Jinstantiate}[5]{\Judge{#1 ~||~ #4}{\Puni{#2}{#3}}{#5}}
\newcommand{\JinstantiateMin}[5]{\Jmin{#1 ~||~ #4}{\Puni{#2}{#3}}{#5}}
\newcommand{\Jspec}[4]{\Judge{#1}{#2 \succ #3}{#4}}
\newcommand{\Jtype}[4]{\JudgeR{#1}{\Pinf{#2}{#3}}{#4}}
\newcommand{\Jhast}[5]{\Judge{#1}{#2 ~\hat:_{#3}~ #4}{#5}}

\newcommand{\JminR}[3]{\ensuremath{#1 \LEIR #3 \vdash #2}}

\newcommand{\InParam}[1]{(#1)}
\newcommand{\OutParam}[1]{\langle #1 \rangle}
\newcommand{\Prob}[3]{#1 \InParam{#2} \OutParam{#3}}
\newcommand{\Pinf}[2]{#1 : \OutParam{#2}}
\newcommand{\Puni}[2]{#1 \equiv #2}
\newcommand{\Pspec}[2]{\Prob{S}{#1}{#2}}

\newcommand{\name}[1]{\ensuremath{\mathrm{\textsc{#1}} \;}}
\newcommand{\side}[1]{\ensuremath{\; #1}}

\newcommand{\br}[2]{\genfrac{}{}{0pt}{0}{#1}{#2}}
\newcommand{\BigRule}[3]{\ensuremath{\Rule{\br{#1}{#2}}{#3}}}

% \newcommand{\sym}{\ensuremath{^\vee}}
\newcommand{\sem}[1]{\ensuremath{\llbracket #1 \rrbracket}}

\newcommand{\W}{\ensuremath{\mathcal{W}}}
\newcommand{\AlgorithmW}{Algorithm~\W}

\newcommand{\genarrow}{\ensuremath{\Uparrow}}
\newcommand{\gen}[2]{\ensuremath{(#1 \genarrow #2)}}
\newcommand{\forget}[1]{\ensuremath{\lfloor #1 \rfloor}}
\newcommand{\hasscheme}{\ensuremath{::}}
\newcommand{\subcontext}{\ensuremath{\subset}}
\newcommand{\semidrop}{\downharpoonright}
\newcommand{\Sbind}[2]{(#1 \Yright #2)}
\newcommand{\spec}{\ensuremath{\succ}}

\newcommand{\define}[1]{\emph{#1}}
\newcommand{\scare}[1]{`#1'}

\newcommand{\V}{\mathcal{V}}
\newcommand{\D}{\mathcal{D}}
\newcommand{\Ss}{\mathcal{S}}
\newcommand{\K}{\mathcal{K}}
\newcommand{\T}{\mathcal{T}}
\newcommand{\TY}{\mathrm{\textsc{TY}}}
\newcommand{\TM}{\mathrm{\textsc{TM}}}

\newcommand{\decl}[2]{#1 #2}

\newcommand{\In}[1]{\ensuremath{\mathit{In}_{#1}}}
\newcommand{\Out}[1]{\ensuremath{\mathit{Out}_{#1}}}
\newcommand{\Pre}[2]{\ensuremath{\mathit{Pre}_{#1} \InParam{#2}}}
\newcommand{\Post}[3]{#1 \InParam{#2} \OutParam{#3}}
\newcommand{\R}[3]{\ensuremath{\mathit{R}_{#1} \OutParam{#2} \OutParam{#3}}}

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

\titlebanner{\NotForPublication{DRAFT}}

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

\AlgorithmW\ is a well-known type inference algorithm, 
based on \citeauthor{robinson_machine-oriented_1965}'s 
Unification Algorithm \citeyearpar{robinson_machine-oriented_1965} 
for the Hindley-Milner type system \citep{milner_theory_1978}, 
verified by \citet{damas_principal_1982}.

Successive presentations and formalisations of \AlgorithmW\ have treated the
underlying unification algorithm as a \scare{black box}, but by considering both
simultaneously we are able to give a more elegant type inference algorithm.
In particular, the generalisation step (for inferring the type of a
let-expression) becomes straightforward.

This paper is literate Haskell, with full source code available at
\footnotesize\url{http://personal.cis.strath.ac.uk/~adam/type-inference/}.
\normalsize


\subsection{Motivating Context}

Why revisit \AlgorithmW? This is a first step towards a longer term
objective: explaining the elaboration of high-level \emph{dependently
typed} programs into fully explicit calculi. Elaboration involves
inferring \emph{implicit arguments} by solving constraints, just as
\W\ specialises polymorphic type schemes, but with fewer algorithmic
guarantees.  Dependently typed programs are often constructed
incrementally, with pieces arriving in an unpredictable
order. Unification problems involve computations as well as
constructors, and may evolve towards tractability even if not
apparently solvable at first. Type inference without annotation is out
of the question, but we may still exploit most general solutions to
constraints when they exist. Milner's insights still serve us well,
if not completely.

The existing literature on 
\scare{implicit syntax}~\citep{pollack_implicit_1990,norell:agda} 
neither fully nor clearly accounts for the behaviour of the systems in
use today, nor are any of these systems free from murky corners. We
feel the need to step back and gain perspective.  Pragmatically, we
need to account for stepwise progress in problem solving from states
of partial knowledge.

What are such states of partial knowledge?  In this
paper, we model them by \emph{contexts} occurring in
typing judgments, describing the known properties of all variables in
scope. We present algorithms via systems of inference rules 
defining relationships between asser-tions of the form
$\Judge{\Gamma}{S}{\Delta}$. Here $\Gamma$ is the input context
(before applying the rule), $S$ the statement to be established,
and $\Delta$ the output context (in which $S$ holds). We revisit
\AlgorithmW\ as a 
%%%necessary check 
%%%sanity check 
check
that our perspective is helpful, 
as a familiar example of problem solving presented anew, and because
our context discipline yields a clearer account of generalisation
in let-binding.

This idea of assertions producing a resulting context goes back at least to
\citet{pollack_implicit_1990}. 
%%%, and hence perhaps to \citet{harper_type_1991} and \citet{milner_definition_1990}.
   An interesting point of comparison is with the work of Nipkow and 
   co-workers \citep{Nipkow-Prehofer-JFP95,NaraschewskiN-JAR}, 
   but substitutions and new contexts are there kept separate. 
\TODO{Need to compare with Dunfield.}

We define an ordering on contexts based on their information content, 
and show that $\Delta$ is minimal with respect to this ordering. If one
thinks of a context as a set of atomic facts, then $\Delta$ is the least upper
bound of $\Gamma$ together with the facts required for $S$ to hold.
In each case, at most one rule matches the input context and condition, and we
specify a termination order so the rules define algorithms. These are
straightforward to implement by translating the rule systems into appropriately
monadic code. We illustrate this with our Haskell implementation.

Contexts here are not simply sets of assumptions, but lists containing
information about type and term variables. The unification problem
thus becomes finding a \scare{more informative} context in which two
expressions are equivalent up to definition. Order of entries in a
context is important. They are subject to well-foundedness conditions:
any definition or declaration must be in terms of variables earlier in
the context, as in dependent type theories. We obtain most general
unifiers and principal types \emph{just} by keeping entries as far to
the right as possible, moving them left only when necessary to satisfy
a constraint. 
Imposing order restrictions on context entries 
is similar to the \emph{ordered hypotheses} of deduction
systems for non-commutative logic \citep{polakow_natural_1999}.

In contrast to other presentations of unification and Hindley-Milner type
inference, our algorithm uses explicit definitions to avoid the need for a 
substitution operation.
(We do use substitution in reasoning about the system.) Many implementations
of (variations on) the Robinson unification algorithm are incorrect because they
do not handle substitutions correctly \citep{norvig_correctingwidespread_1991}.

This paper has been brewing for a long time. Its origins lie in a 
%%%long lost 
constraint engine cannibalised by McBride from 
%%%components of
an implementation of \citeauthor{miller:mixed}'s \scare{mixed prefix}
unification~\citeyearpar{miller:mixed}, mutating the quantifier prefix
into a context. \citeauthor{mcbride:thesis}'s
thesis~\citeyearpar{mcbride:thesis} gives an early account of 
   using
typing contexts 
%%%representing 
   to represent 
the state of an interactive construction system,
the \scare{holes} in programs and proofs 
%%%as 
   being 
specially designated
variables. Contexts 
%%%come equipped with 
   carry 
an information order: 
%%%
   increase of information  
preserves typing and equality judgments; proof tactics
are admissible context validity rules which increase information;
unification is specified as a tactic which increases information to
make an equation hold, but its imple-mentation is not discussed. This
view of construction underpinned the implementation of
Epigram~\citep{mcbride.mckinna:view-from-the-left} and informed
\citeauthor{norell:agda}'s implementation of
Agda~\citeyearpar{norell:agda}. It is high time we began to explain
how it works and perhaps to understand it.

\TODO{Explain organisation of paper?}


%if showCode

> {-# LANGUAGE DeriveFunctor, DeriveFoldable #-}

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
%%%We write $\Type$ for the set of types. 
   Let $\Type$ be the set of types.
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
>     deriving (Functor, Foldable)

%if showCode

> infixr 5 :->

%endif

> type TyName  = Integer
> type Type    = Ty TyName


We %%%can 
implement $\mathit{FTV}$ via a typeclass with membership function
|(<?)|. We get most of the required instances for free using |Foldable|.

> class FTV a where
>     (<?) :: TyName -> a -> Bool

> instance FTV TyName where
>     (<?) = (==)

> instance  (Foldable t, FTV a) => FTV (t a) where
>     alpha <? t = any (alpha <?) t


\subsection{Introducing contexts}

Types contain variables, but we need some way of interpreting what the variables
mean. Our ideology is that such information belongs in the context. We give an
abstract description of contexts, which may contain type variables and other
information.

Let $\K$ be a set of sorts, and for each $K \in \K$ let $\V_K$ be a
set of variables and $\D_K$ a set of
%%%\emph{declaration properties}.
    \emph{properties}.
Our running example will be the sort $\TY$, where
$\V_\TY$ is some set of type variables and $\D_\TY$ initially contains
only the \scare{unbound variable} property $~\hole{}$. Properties of
variables play the same atomic role in \emph{derivations} that variables
themselves play in terms.

A \define{context} is a list of declarations $\decl{x}{D}$, with
$x \in \V_K$ and $D \in \D_K$.
%% and separators $(\fatsemi)$. 
%%%We write $\emptycontext$ for the empty context, and 
   The empty context is written $\emptycontext$. 
%%%the symbols 
   We let 
$\Gamma, \Delta, \Theta$ range over contexts.
%% $\Xi$ is a context that contains no $\fatsemi$ separators.

We will gradually construct a set $\Ss$ of statements, which can be
judged in a context: these are the \scare{sorts}  of our syntax of
derivations. We write the \define{normal judgment} $\Gamma \entails S$
to mean that the declarations in $\Gamma$ support the statement $S \in
\Ss$.  We write the \define{neutral judgment} $\Gamma \entailsN S$ to
mean that $S$ follows directly from applying a fact in $\Gamma$.
Neutral judgments capture exactly the legitimate appeals to assumptions
in the context, just the way \scare{neutral terms}  in $\lambda$-calculus are
applied variables. We embed neutral into normal: 
$$\name{Neutral}
  \Rule{\Gamma \entailsN S}
       {\Gamma \entails S}$$

It is not enough for contexts to be lists of declarations: they must
be well-founded, that is, each declaration should make sense in
\emph{its} context.  A context is valid if it declares each variable
at most once, and each
%%%declaration
property is meaningful in the
preceding context.  We maintain a map $\ok_K : \D_K \rightarrow
\Ss$ for every $K \in \K$.  Let $\V_K(\Gamma)$ be the set of
$K$-variables in $\Gamma$.  We define the context validity statement
$\valid$ as shown in Figure~\ref{fig:contextValidityRules}.

\begin{figure}[ht]
\boxrule{\Gamma \entails \valid}
$$
\Axiom{\emptycontext \entails \valid}
\qquad
\Rule{\Gamma \entails \valid    \quad    \Gamma \entails \ok_K D}
     {\Gamma, \decl{x}{D} \entails \valid}
\side{x \in \V_K \setminus \V_K(\Gamma)}
$$
\caption{Rules for context validity}
\label{fig:contextValidityRules}
\end{figure}

From now on, we consider only valid contexts. All future definitions
implicitly assume the context is valid, and it is straightforward to verify that
our algorithms preserve context validity.

In the example of type declarations, we let $\ok_\TY (\hole{}) = \valid$.
That is, declaring our ignorance is always reasonable.


\subsection{Making types meaningful}

Now we can ask whether a type is meaningful with respect to a context.
This requires us to determine whether a type variable is in scope.
In general, each context entry forces some statement to hold.

We suppose that there is a map
$\sem{\cdot}_K : \V_K \times \D_K \rightarrow \Ss$
for each $K \in \K$, from declarations to statements.
(We typically omit the subscript when the sort is irrelevant or can be inferred.)
The idea is that $\sem{\decl{x}{D}}$ is the statement that holds by virtue of the
declaration $\decl{d}{D}$ in the context.
The basic rule of our inference system is
$$\name{Lookup}
  \Rule{\Gamma \entails \valid   \quad  \decl{x}{D} \in \Gamma}
       {\Gamma \entailsN \sem{\decl{x}{D}}}.$$

As promised, uses of \textsc{Lookup} act as \scare{variables} in
derivations.  Our $\sem{\cdot}_K$ associates to an \scare{expression atom} 
its \scare{derivation atom}. This is the only rule which interrogates
the context, hence we propose 
%%%the bold step of 
dropping the
shared context from the presentation of all other rules.

We define the statement $\tau \type$ by taking
$\sem{\hole{\alpha}} = \alpha \type$
together with the structural rule
$$
\Rule{\tau \type   \quad   \upsilon \type}
     {\tau \arrow \upsilon \type}.
$$
Note that we omit the context from rules if it is constant throughout.
We observe the \emph{sanity} condition
$\Gamma \entails \tau \type  \Rightarrow  \Gamma \entails \valid$.


\subsection{Conjunctions}

We shall sometimes need to package multiple facts about a single
variable, so we introduce the composite statement $S \wedge S'$ for
statements $S$ and $S'$, with normal introduction rule (pairing) and neutral
elimination rules (projections):
 $$\Rule{S \quad S'} {S \wedge S'}
\qquad
\Rule{\entailsN S \wedge S'}
       {\entailsN S}
  \qquad
  \Rule{\entailsN S \wedge S'}
       {\entailsN S'}$$
This is but one instance of a general pattern: we add normal introduction
forms for composite statements, but supply
eliminators only for composite \emph{hypotheses}, in effect forcing
derivations to be cut-free. This facilitates reasoning by induction on
derivations. We shall ensure that the corresponding elimination rules
for \emph{normal} judgments are in any case admissible.



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
% \sem{\alpha \defn \tau}_\TY &= \{ \alpha \type, \alpha \equiv \tau \}
\sem{\alpha \defn \tau}_\TY &= \alpha \type \wedge \alpha \equiv \tau
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

A type variable declaration is given by a |TyEntry|, where a variable
is either bound to a type (written |Some tau|) or left unbound (written |Hole|).

> data TyDecl   =  Some Type | {-"\;"-} Hole
> data TyEntry  =  TyName := TyDecl

We define |FTV| for |TyEntry|, and thanks to the relevant |Foldable| instances
it will automatically be defined for lists of type variable declarations.

> instance FTV TyEntry where
>    alpha <? (_ := Some tau)  = alpha <? tau
>    alpha <? (_ := Hole)      = False

A context is a (backwards) list of entries. At the moment we only have one
kind of entry, but later we will add others, so this definition is incomplete.
% subject to the
% conditions that each variable is defined at most once, and all variables that
% occur in a type variable binding must be defined earlier in the list.
% The context validity conditions will be maintained by the algorithm but are not
% enforced by the type system; this is possible in a language such as Agda.

< data Entry    = TY TyEntry | ...
< type Context  = Bwd Entry

%if False

> type Context  = Bwd Entry -- so we can line up the two previous lines

%endif

The type |Bwd| is a backwards (snoc) list, with empty list |B0| and data
constructor |:<|. Lists are monoids with the append operator |<+>|.

% The types |Bwd| and |Fwd| are backwards (snoc) and forwards (cons) lists,
% respectively. We overload |B0| for the empty list in each case, and write
% |:<| and |:>| for the backwards and forwards list data constructors.
%% Data types are cheap, so we might
%% as well make the code match our intution about the meaning of data.
% Lists are monoids with |<+>| the append operator, and the \scare{fish}
% operator |(<><) :: Context -> Suffix -> Context| appends a suffix to a context. 


We work in the |Contextual| monad (computations that can fail and mutate the
context), defined as follows:   

> type Contextual  = StateT (TyName, Context) Maybe

The |TyName| component is the next fresh type variable name to use;
it is an implementation detail not mentioned in the typing rules. 
The |fresh| function generates a fresh variable name and appends a declaration
to the context.
Our choice of |TyName| means that it is easy to choose a name fresh with respect
to a |Context|.

> fresh :: TyDecl -> Contextual TyName
> fresh d = do   (beta, _Gamma) <- get
>                put (succ beta, _Gamma :< TY (beta := d))
>                return beta

%  fresh :: TyDecl -> Contextual TyName
% > fresh d = do   (beta, _Gamma) <- get
% >                put (freshen beta _Gamma, _Gamma :< TY (beta := d))
% >                return beta
% >   where freshen alpha _Gamma = succ alpha
% > freshen :: TyName -> Context -> TyName
% > freshen alpha _Gamma = succ alpha

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
Composition of substitutions is given by
$(\theta \compose \delta) (\alpha) = \theta (\delta \alpha)$.
We write $\subst{\tau}{\alpha}{}$ for the substitution that maps
$\alpha$ to $\tau$ and other variables to themselves.

%%%We write $\delta : \Gamma \lei \Delta$ and say
%%%\define{$\Delta$ is more informative than $\Gamma$} if $\delta$ is a
%%%substitution from $\Gamma$ to $\Delta$ such that,
%%%%%%for every $\decl{x}{D} \in \Gamma$, we have that 
%%%   for all $\decl{x}{D} \in \Gamma$, we have 
%%%$\Delta \entails \delta \sem{\decl{x}{D}}$. 

Given a substitution $\delta$ from $\Gamma$ to $\Delta$, 
we write  $\delta : \Gamma \lei \Delta$ and say 
\define{$\Delta$ is more informative than $\Gamma$} if 
for all $\decl{x}{D} \in \Gamma$, we have 
$\Delta \entails \delta \sem{\decl{x}{D}}$. 

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

We may omit $\delta$ and write $\Gamma \lei \Delta$ if we are only interested
in the existence of a suitable substitution. This relation between contexts
captures the notion of \define{information increase}: $\Delta$ supports all the
statements corresponding to declarations in $\Gamma$. 

%% Moreover, this will still hold if we truncate both $\Gamma$ and $\Delta$ after
%% any number of $\fatsemi$ separators.

This 
%%%definition of information increase 
   partial order on information 
is not 
%%%quite complete, because it does not place any 
   yet sufficient, because it places no 
constraints on the order of context entries, 
%%%other than 
   beyond 
the
dependency order of variables in declarations. We 
%%%will later see 
   show later 
how to extend
$\lei$ to capture the order of entries at 
%%%an appropriate 
   a finer 
level of precision. 



\subsection{Stability}

We say a statement $S$ is
\define{stable} if it is preserved under information increase, that is, if
$$\Gamma \entails S  \quad \mathrm{and}  \quad  \delta : \Gamma \lei \Delta
    \quad \Rightarrow \quad  \Delta \entails \delta S.$$
This says that we can extend a simultaneous substitution on syntax to a
simultaneous substitution on derivations.
\TODO{Expand on this.}

Since we 
%%%are only interested in 
   only consider 
valid contexts, the statement $\valid$ always
holds, and is invariant under substitution, so 
   it 
is clearly stable.

We have a standard strategy for proving stability of most statements, which is
effective by construction. In each case we proceed by induction on the structure
of derivations. Where the \textsc{Lookup} rule is applied, stability holds by 
%%%the 
definition of information increase. Otherwise, for rules 
%%%that do not refer 
   not referring 
to the context, we 
%%%can 
verify that non-recursive hypotheses are stable and that
recursive hypotheses occur 
in strictly positive positions, so 
%%%they 
are stable
by induction. Applying this strategy shows that 
%%%the statements 
   both 
$\tau \type$
and $\tau \equiv \upsilon$ are stable.

\begin{lemma}\label{lei:preorder}
If $\sem{\decl{x}{D}}$ is stable for every declaration $\decl{x}{D}$, then
the $\lei$ relation is a preorder, with reflexivity demonstrated by
the identity substitution
$\iota : \Gamma \lei \Gamma : v \mapsto v$, and transitivity by composition:
$$\delta : \Gamma \lei \Delta  ~~\text{and}~~  \theta : \Delta \lei \Theta
  \quad \Rightarrow \quad  \theta \compose \delta : \Gamma \lei \Theta.$$
\end{lemma}

\begin{proof}
Reflexivity follows immediately from the \textsc{Lookup} rule.
For transitivity, suppose $\decl{x}{D} \in \Gamma$,
then $\Delta \entails \delta \sem{\decl{x}{D}}$ since
$\delta : \Gamma \lei \Delta$.
Now by stability applied to $\delta \sem{\decl{x}{D}}$ using $\theta$, we have
$\Theta \entails \theta\delta \sem{\decl{x}{D}}$ as required.
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


\subsection{Binding statements}

\TODO{We don't use these until section 6.1, so should we move them?
Should we split the lemma?}

If $S$ is a statement and $\decl{x}{D}$ is a declaration, then we define the
binding statement $\Sbind{\decl{x}{D}}{S}$ with the introduction rule
$$
\Rule{\Gamma \entails \ok_K D    \quad    \Gamma, \decl{x}{D} \entails S}
     {\Gamma \entails \Sbind{\decl{x}{D}}{S}}
\side{v \in \V_K \setminus \V_K(\Gamma)}.
$$
and neutral elimination rule
$$
\Rule{\Gamma \entailsN \Sbind{\alpha D}{S}
      \quad
      \Gamma \entails \subst{\tau}{\alpha}{\sem{\alpha D}}}
     {\Gamma \entailsN \subst{\tau}{\alpha}{S}}
\side{D \in \D_\TY}
$$

\begin{lemma}[Composition preserves stability]\label{lem:stab-pres}
If $S$ and $S'$ are stable then $S \wedge S'$ is stable.
If $\decl{x}{D}$ is a declaration and both $\ok_K D$ and $S$ are stable, then
$\Sbind{\decl{x}{D}}{S}$ is stable.
\end{lemma}
\begin{proof}
Suppose $\delta : \Gamma \lei \Delta$, the statements $S$ and $S'$ are stable
and $\Gamma \entails (S \wedge S')$. If the proof is by \textsc{Lookup}
then $\Delta \entails \delta (S \wedge S')$ by definition of information
increase. Otherwise $\Gamma \entails S$ and $\Gamma \entails S'$,
so by stability, $\Delta \entails \delta S$ and $\Delta \entails \delta S'$, so
$\Delta \entails \delta (S \wedge S')$.

Suppose $\delta : \Gamma \lei \Delta$, the statement $S$ is stable and
$\Gamma \entails \Sbind{\decl{x}{D}}{S}$.  If the proof is by \textsc{Lookup}
then $\Delta \entails \delta S$ by definition of information increase.
Otherwise, $\Gamma \entails \ok_K D$ and
$\Gamma, \decl{x}{D} \entails S$, so by stability, $\Delta \entails \delta (\ok_K D)$.
% Let $\delta' = \subst{x}{x}{\delta}$, then
Now $\delta : \Gamma, \decl{x}{D} \lei \Delta, \decl{x}{(\delta D)}$
so by stability of $S$ we have $\Delta, \decl{x}{(\delta D)} \entails \delta S$.
Hence $\Delta \entails \Sbind{\decl{x}{(\delta D)}}{\delta S}$
and so $\Delta \entails \delta \Sbind{\decl{x}{D}}{S}$.
\TODO{We should at least mention freshness here.}
\end{proof}

Thanks to Lemma~\ref{lem:stab-pres} and 
%%%preceding results, 
   the foregoing, 
every statement we have
introduced so far is stable. We will ensure stability for all statements in $\Ss$, so we can exploit it without qualification in the sequel.



\section{Problems}

\subsection{What is a problem?}

A problem represents a statement we wish to make hold by increasing information
in the context. More generally, it is a statement with distinguished output
positions for which we wish to find a witness in a more informative context.
%% Unification is an example of the first kind of problem and type inference 
%% the second.
Unification and type inference are examples of problems, with the latter
having a single output position (for the type being inferred).

We are interested in creating algorithms to solve problems, preferably in as
general a way as possible (that is, by making the smallest information increase
necessary to find a solution). This corresponds to finding a most general
unifier, in the case of unification, or a principal type in the case of type
inference.

\TODO{Make the structure of problems clearer.}

We distinguish output positions with angle brackets $\OutParam{\cdot}$ for clarity.
Formally, a \define{problem} $P$ consists of
%%   Distinguishing output positions with angle brackets $\OutParam{\cdot}$, 
%%   formally, a \define{problem} $P$ consists of 
\begin{itemize}
\item sets \In{P}\ and \Out{P}\ of input and output parameters,
\item a precondition map $\Pre{P}{\cdot} : \In{P} \rightarrow \Ss$,
\item a postcondition map $\Post{P}{\cdot}{\cdot} : \In{P} \rightarrow \Out{P} \rightarrow \Ss$ and
\item a relation map $\R{P}{\cdot}{\cdot} : \Out{P} \rightarrow \Out{P} \rightarrow \Ss$,
\end{itemize}
such that \In{P}\ and \Out{P}\ are closed under substitution and the maps
respect substitution, for example, $\Pre{P}{\theta a} = \theta \Pre{P}{a}$.
Moreover, for any $\Gamma$, $a \in \In{P}$ and $r, s, t \in \Out{P}$
such that
\[\Gamma \entails \Pre{P}{a} \wedge \Post{P}{a}{r} \wedge \Post{P}{a}{s}
         \wedge \Post{P}{a}{t}, \]
we must have 
\(\Gamma \entails \R{P}{r}{r}\) and
\[\Gamma \entails \R{P}{r}{s} \wedge \R{P}{s}{t}
    \Rightarrow \Gamma \entails \R{P}{r}{t}. \]

%%%We write angle brackets $\OutParam{\cdot}$ around the output parameters of a problem.

The unification problem $U$ is given by
\begin{align*}
\In{U}                        &= \Type \times \Type  \\
\Out{U}                       &= \{ 1 \}  \\
\Pre{U}{\tau, \upsilon}       &= \tau \type \wedge \upsilon \type  \\
\Post{U}{\tau, \upsilon}{\_}  &= \tau \equiv \upsilon  \\
\R{U}{\_}{\_}                 &= \valid
\end{align*}

A 
%%%\define{$P$-instance for a context $\Gamma$} 
   \define{$P$-instance for $\Gamma$}  
is $a \in \In{P}$ such that
$\Gamma \entails \Pre{P}{a}$. 
%%%The problem 
   Such an 
instance $a$ has \define{solution}
$(r, \delta, \Delta)$ if $r \in \Out{P}$ and $\delta : \Gamma \lei \Delta$
such that $\Delta \entails \Post{P}{\delta a}{r}$. (Observe that
$\Delta \entails \Pre{P}{\delta a}$ by stability.)

The solution $(r, \delta, \Delta)$ is \define{minimal} if for any solution
$(s, \theta, \Theta)$ there exists $\zeta : \Delta \lei \Theta$ such that
$\theta \eqsubst \zeta \compose \delta$ and $\Theta \entails \R{P}{\zeta r}{s}$.
 
We write $\delta : \Jmin{\Gamma}{\Prob{P}{a}{r}}{\Delta}$ to mean that
$(r, \delta, \Delta)$ is a minimal solution of the $P$-instance $a$.

\TODO{Define what it means for a rule system to be algorithmic.}


\subsection{The Optimist's Lemma}
%%%
If $P$ and $Q$ are problems, then $P \wedge Q$ is a problem with
\begin{align*}
\In{P \wedge Q}                 &= \In{P} \times \In{Q}  \\
\Out{P \wedge Q}                &= \Out{P} \times \Out{Q}  \\
\Pre{P \wedge Q}{a, b}          &= \Pre{P}{a} \wedge \Pre{Q}{b}  \\
\Post{(P \wedge Q)}{a, b}{r, s}   &= \Post{P}{a}{r} \wedge \Post{Q}{b}{s}  \\
\R{P \wedge Q}{r, s}{t, u}      &= \R{P}{r}{t} \wedge \R{Q}{s}{u}  \\
\end{align*}
%%%The point of all this machinery is to be able to state and prove the following 
%%%lemma, stating that the minimal solution to a conjunction of problems can be
%%%found by finding the minimal solution of the first problem, then (minimally)
%%%extending it to solve the second. 
We can now state the following \scare{greedy} approach to finding minimal solutions to such composite problems: find a minimal solution of problem \(P\), then extend it to (minimally) solve \(Q\):  
%%%
\begin{lemma}[The Optimist's lemma]
\label{lem:optimist}
The following inference rule is admissible:
$$\Rule{\delta : \Jmin{\Gamma}{\Prob{P}{a}{r}}{\Delta}
       \quad  \theta : \Jmin{\Delta}{\Prob{Q}{b}{s}}{\Theta}}
       {\theta \compose \delta :
         \Jmin{\Gamma}{\Prob{P}{a}{\theta r} \wedge \Prob{Q}{b}{s}}{\Theta}}.$$
\end{lemma}

%%%\begin{proof}[Sketch] The solutions of $P(a)$ arise exactly by
%%%extending $\delta$, so if we seek also to solve $Q(b)$, it is
%%%necessary and sufficient to search amongst the extensions of $\delta$.
%%%For details, see Appendix.  \end{proof}

\begin{proof}%%%[Proof of lemma~\ref{lem:optimist} (Optimist's Lemma)]
We have that $\theta \compose \delta : \Gamma \lei \Theta$ by 
Lemma~\ref{lei:preorder}. 

To show $\Theta \entails \Prob{P \wedge Q}{a, b}{\theta r, s}$, it
suffices to show $\Theta \entails \Prob{P}{a}{\theta r}$ and
$\Theta \entails \Prob{Q}{b}{s}$. The latter holds by assumption. For the
former, note that $\Delta \entails \Prob{P}{a}{r}$ and hence
$\Theta \entails \theta (\Prob{P}{a}{r})$ by stability of $\Prob{P}{a}{r}$.
But $\theta (\Prob{P}{a}{r}) = \Prob{P}{a}{\theta r}$ by definition. 

Finally, suppose there is some $\phi : \Gamma \lei \Phi$ 
and outputs $t, u$ such that
$\Phi \entails \Prob{P \wedge Q}{a, b}{t, u}$, so
$\Phi \entails \Prob{P}{a}{t}$ and
$\Phi \entails \Prob{Q}{b}{u}$.
Since $\delta : \Jmin{\Gamma}{\Prob{P}{a}{r}}{\Delta}$, there exists
$\zeta_1 : \Delta \lei \Phi$ such that
$\phi \eqsubst \zeta_1 \compose \delta$
and $\Phi \entails \R{P}{\zeta_1 r}{t}$.
But then $\theta : \Jmin{\Delta}{\Prob{Q}{b}{s}}{\Theta}$, so there exists
$\zeta_2 : \Theta \lei \Phi$ such that
$\zeta_1 \eqsubst \zeta_2 \compose \theta$
and $\Phi \entails \R{Q}{\zeta_2 s}{u}$.
Hence $\phi \eqsubst \zeta_2 \compose (\theta \compose \delta)$
and $\Phi \entails \R{P \wedge Q}{\zeta_2 (\theta r), \zeta_2 s}{t, u}$.
\end{proof}


This sequential approach to problem solving is not the only decomposition
justified by stability. \citeauthor{mcadam_unification_1998}'s account of unification 
\citeyearpar{mcadam_unification_1998} amounts to a concurrent, transactional
decomposition of problems. The same context is extended via multiple different
substitutions, then these are unified to produce a single substitution.


\section{Deriving a unification algorithm}

\subsection{Transforming the rule system for equivalence}

We wish to transform the equivalence rules in Figure~\ref{fig:equivRules} 
into a unification algorithm. Consider what happens if
we remove each of reflexivity, transitivity and symmetry in turn, and attempt to
prove their
admissibility. This will fail, but the proof obligations left over give us a more
specific but equivalent system of algorithmic-looking rules for equivalence.
\TODO{Reference unfold/fold transformations.}

First, 
%%%the reflexivity rule for types can be derived from 
%%%the reflexivity rule for variables given by
we reduce the reflexivity rule to the atomic case 
$$\name{Refl\(_\alpha\)}
  \Rule{\alpha \type}
       {\alpha \equiv \alpha}$$
by applying the structural rule until variables occur.

Next, transitivity can be derived from the restricted case 
$$\name{Trans\(_\alpha\)}
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
      then use \name{Trans\(_\alpha\)}\!.
\item If $\chi = \alpha = \upsilon$ then use \name{Refl\(_\alpha\)}\!.
\item If $\chi = \alpha = \tau$ then the result holds by hypothesis.
\item If $\chi$ is not a variable but $\upsilon$ is then apply symmetry
      and one of the previous cases.
\item If $\chi$ and $\upsilon$ are both not variables then apply
      the structural rule.
\end{itemize}

Finally, symmetry 
%%%becomes 
   is 
admissible (but not derivable) if replaced by
$$\name{Sym\(_\alpha\)}
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
      the proof of $\upsilon \equiv \beta$ must be by \name{Sym\(_\alpha\)}\!,
      in which case its hypothesis says that $\beta \equiv \upsilon$.
\item If $\tau$ and $\upsilon$ are both not variables then apply the
      structural rule.
\end{itemize} 


\subsection{Constructing a unification algorithm}

Now we can see how to construct the algorithm. The structural rule says that whenever we have rigid $\arrow$ symbols on each side, we decompose the problem into two subproblems, and thanks to the Optimist's Lemma we can solve these sequentially. Otherwise, we either have variables on both sides, or a variable on one side and a type on the other. In each case, we look at the head of the context to see what information it gives us, and use the transformed rules to see how to proceed. When solving a variable with a type, we need to accumulate the type's dependencies as we encounter them, performing the occur check to ensure a solution exists.

% \begin{itemize}
% \item If $\alpha D$ is at the head of the context and we are trying to
% unify $\alpha \equiv \alpha$ then we are done.
% \item If $\hole{\alpha}$ is at the head and we seek $\alpha \equiv \tau$ or
% $\tau \equiv \alpha$ then we can replace the head with the list of dependencies
% followed by $\alpha \defn \tau$.
% \end{itemize}

It is possible that a context entry may have no bearing on the unification
problem being solved, and hence can be ignored.
We define the orthogonality relation $\decl{x}{D} \perp X$ (the set of type variables $X$
does not depend on the declaration $\decl{x}{D}$) 
%%%thus:
   to capture this idea: 
\begin{align*}
\alpha D \perp X
    &\mathrm{~if~} \alpha \in \V_\TY \setminus X  \\
\decl{x}{D} \perp X
    &\mathrm{~if~} x \in \V_K, D \in \D_K \mathrm{~for~} K \neq \TY
\end{align*}

The rules in Figure~\ref{fig:unifyRules} define our unification algorithm. The
assertion $\Junify{\Gamma}{\tau}{\upsilon}{\Delta}$ means that 
unification of $\tau$ with $\upsilon$ 
succeeds, producing output context $\Delta$, 
given inputs
$\Gamma$, $\tau$ and $\upsilon$ satisfying 
$\Gamma \entails \tau \type \wedge \upsilon \type$. 

The assertion
$\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$
means that 
solving $\alpha$ with $\tau$ succeeds,  
%%%and produces 
   yielding output $\Delta$,
given inputs $\Gamma$, $\Xi$, $\alpha$ and $\tau$
%%%,subject to the conditions
   satisfying 
\begin{itemize}
\item $\alpha \in \tyvars{\Gamma}$,
\item $\Gamma, \Xi \entails \tau \type$,
\item $\tau$ is not a variable,
\item $\Xi$ contains only type variable declarations and
\item $\beta \in \tyvars{\Xi} \Rightarrow \beta \in \FTV{\tau, \Xi}$.
\end{itemize}

For clarity, we take a \scare{garbage-in, garbage-out} approach to the
algorithm: we omit the above sanity conditions from the rules, and
correspondingly do not check them in the implementation. 
\TODO{Reword this.}

The rules \textsc{Define}, \textsc{Expand} and \textsc{Ignore} have
symmetric counterparts, 
%%%that are 
identical apart from interchanging the equated
terms in the conclusion. Usually we will ignore these without loss of generality.
% but where necessary we refer to them as \textsc{Define}\sym,
% \textsc{Expand}\sym and \textsc{Ignore}\sym.

        
\begin{figure}[ht]
\boxrule{\Junify{\Gamma}{\tau}{\upsilon}{\Delta}}

$$
\name{Idle}
% \Rule{\Gamma \entails \alpha \type}
\Axiom{\Junify{\Gamma_0, \alpha D}{\alpha}{\alpha}{\Gamma_0, \alpha D}}
$$

$$
\name{Define}
%\Rule{\Gamma_0 \entails \beta \type}
\Axiom{\Junify{\Gamma_0, \hole{\alpha}}{\alpha}{\beta}{\Gamma_0, \alpha \defn \beta}}
\side{\alpha \neq \beta}
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
     {\Junify{\Gamma_0, \decl{x}{D}}{\alpha}{\beta}{\Delta_0, \decl{x}{D}}}
\side{\decl{x}{D} \perp \{\alpha, \beta\} }
$$

$$
\name{Solve}
\Rule{\Jinstantiate{\Gamma}{\alpha}{\tau}{\emptycontext}{\Delta}}
     {\Junify{\Gamma}{\alpha}{\tau}{\Delta}}
%% \side{\tau \neq \alpha}
\side{\tau \mathrm{~not~variable}}
$$

$$
\name{Decompose}
\Rule{\Junify{\Gamma}{\tau_0}{\upsilon_0}{\Delta_0}
      \quad
      \Junify{\Delta_0}{\tau_1}{\upsilon_1}{\Delta}}
    {\Junify{\Gamma}{\tau_0 \arrow \tau_1}{\upsilon_0 \arrow \upsilon_1}{\Delta}}
$$

\bigskip

\boxrule{\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}}

$$
\name{DefineS}
% \Rule{\Gamma_0, \Xi \entails \tau \type}
\Axiom{\Jinstantiate{\Gamma_0, \hole{\alpha}}{\alpha}{\tau}{\Xi}
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
     {\Jinstantiate{\Gamma_0, \decl{x}{D}}{\alpha}{\tau}{\Xi}{\Delta_0, \decl{x}{D}}}
\side{\decl{x}{D} \perp \FTV{\alpha, \tau, \Xi}}
$$

\caption{Algorithmic rules for unification}
\label{fig:unifyRules}
\end{figure}


Observe that we have no rule 
%%%for the case
   in the situation where 
$$\Jinstantiate{\Gamma_0, \alpha D}{\alpha}{\tau}{\Xi}{\Delta}
\mathrm{~with~} \alpha \in \FTV{\tau, \Xi}$$
so the algorithm fails 
%%%if this situation arises. 
   in this case. 
This is 
%%%essentially 
an occur check failure: $\alpha$ and $\tau$ cannot 
%%%be unified 
   unify 
if $\alpha$ occurs in
$\tau$ or in an entry that $\tau$ depends on, and $\tau$ is not a variable.
%%%Since we only have one 
   Given the single 
type constructor symbol (the function arrow $\arrow$),
there are no failures due to rigid-rigid mismatch. 
To add these would not
significantly complicate matters%%%, however
.

%At first there appears to be some redundancy in the system, with %similar-looking
%rules for flex-flex and flex-rigid problems
%(\textsc{Define} versus \textsc{DefineS}, for example).
%Unfortunately, it is not easy to remove the flex-flex versions, because %they
%permit the exception to the occur check when only variables are involved.

By exposing the contextual structure underlying unification we make
termination of the algorithm evident. Each recursive appeal to
unification (directly or via the solving process) either shortens the
context or preserves the context and decomposes
types~\citep{mcbride:unification}. We are correspondingly entitled to
reason about the total correctness of unification by induction on the
algorithmic rules.



\subsection{Soundness and completeness}

\begin{lemma}[Soundness of unification]
\label{lem:unifySound}
\begin{enumerate}[(a)]
\item If $\Junify{\Gamma}{\tau}{\upsilon}{\Delta}$, then
$\tyvars{\Gamma} = \tyvars{\Delta}$,
% and we have $\iota : \Jmin{\Gamma}{\Puni{\tau}{\upsilon}}{\Delta}$,
$\Delta \entails \tau \equiv \upsilon$ and
$\iota : \Gamma \lei \Delta$
where $\iota$
% $$\iota: \tyvars{\Gamma} \rightarrow \types{\Delta} : \alpha \mapsto \alpha$$
is the identity substitution.

\item If
$\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$, then
$\tyvars{\Gamma, \Xi} = \tyvars{\Delta}$,
$\Delta \entails \alpha \equiv \tau$ and
$\iota : \Gamma, \Xi \lei \Delta$.
% $\iota : \Jmin{\Gamma, \Xi}{\Puni{\alpha}{\tau}}{\Delta}$.
\end{enumerate}
\end{lemma}

\begin{proof}
By induction on the structure of derivations.
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


\begin{lemma}[Completeness and generality of unification]
\label{lem:unifyComplete}
\begin{enumerate}[(a)]
\item If $\theta : \Gamma \lei \Theta$,
$\Gamma \entails \upsilon \type \wedge \tau \type$ and
$\Theta \entails \theta\upsilon \equiv \theta\tau$, then
there is some context $\Delta$ such that
$\Jmin{\Gamma}{\Puni{\upsilon}{\tau}}{\Delta}$.

% with
% $\theta : \Delta \lei \Theta$. That is, if a unifier for $\tau$ and $\upsilon$
% exists, then the algorithm succeeds and delivers a most general unifier.

\item Moreover, if $\theta : \Gamma, \Xi \lei \Theta$ is such that
$\Theta \entails \theta\alpha \equiv \theta\tau$ and
\begin{itemize}
\item $\alpha \in \tyvars{\Gamma}$,
\item $\Gamma, \Xi \entails \tau \type$,
\item $\tau$ is not a variable,
\item $\Xi$ contains only type variable declarations and
\item $\beta \in \tyvars{\Xi}  \Rightarrow  \beta \in \FTV{\tau, \Xi}$,
\end{itemize}
then there is some context $\Delta$ such that
$\JinstantiateMin{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$.
\end{enumerate}
\end{lemma}

\begin{proof}[Sketch] Each step preserves all solutions. The
Optimist's Lemma justifies problem decomposition. The algorithm
terminates, and the only case not covered by the rules is the case
where the occur check fails, indicating no unifier exists.  For
details, see Appendix.  \end{proof}


\subsection{Implementing unification}

First, we define some helpful machinery. A context suffix is a (forwards) list
containing only type variable declarations. 

> type Suffix      = Fwd TyEntry

Like |Bwd|, the |Fwd| list type has empty list |B0| and data constructor |:>|,
and it is a monoid with |<+>| being append. The \scare{fish} operator appends a
suffix to a context.

> (<><) :: Context -> Suffix -> Context
> _Gamma <>< F0                   = _Gamma
> _Gamma <>< (alpha := d :> _Xi)  = _Gamma :< TY (alpha := d) <>< _Xi

%if False

> infixl 8 <><

%endif

The |onTop| operator applies its argument to the topmost type variable
declaration in the context, skipping over any other kinds of entry. The argument
function may |restore| the previous entry by returning |Nothing|, or it may
return a context extension (containing at least as much information as the
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
> unify (V alpha) (V beta) = onTop $
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
> unify (tau0 :-> tau1)  (upsilon0 :-> upsilon1)           =   unify tau0 upsilon0 >> unify tau1 upsilon1


The |solve| function attempts to unify a variable name with a
(non-variable) type, given a list of entries that the type depends on,
which must be placed into the context before it.

> solve :: TyName -> Suffix -> Type -> Contextual ()
> solve alpha _Xi tau = onTop $
>   \ (gamma := d) -> 
>     let occurs = gamma <? tau || gamma <? _Xi in case
>     (gamma == alpha,  occurs,  d             ) of
>     (True,            True,    _             )  ->  fail "Occur check failed"
>     (True,            False,   Hole          )  ->  replace (_Xi <+> (alpha := Some tau :> F0))
>     (True,            False,   Some upsilon  )  ->  modifyContext (<>< _Xi)
>                                                 >>  unify upsilon tau
>                                                 >>  restore
>     (False,           True,    _             )  ->  solve alpha (gamma := d :> _Xi) tau
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
the type scheme $\sigma$ over the prefix of type variable declarations $\Xi$,
defined by
\begin{align*}
\emptycontext         &\genarrow \sigma = \sigma  \\
\Xi, \hole{\alpha}    &\genarrow \sigma = \Xi \genarrow \forall\alpha~\sigma  \\
\Xi, \alpha \defn \nu &\genarrow \sigma = \Xi \genarrow \letS{\alpha}{\nu}{\sigma}
\end{align*}
We will usually be interested in the case $\sigma = .\tau$      for some type $\tau$.

When we infer the specialised type of a variable, we rely on the
ability to invert this operation, extending the contex with a
\emph{fresh} copy of a scheme's prefix. As shown above, we follow
\citet{NaraschewskiN-JAR} in achieving freshness with a simple
counter, built into the |Contextual| monad.

\begin{lemma}
\label{lem:specialise}
If $\Gamma \entails \sigma \scheme$ then $\sigma = \Xi\genarrow.\tau$
for some $\Xi$ and $\tau$ such that $\Gamma,\Xi\entails \tau \type$
\end{lemma}
\begin{proof}
By induction on the structure of $\sigma$, given that it is possible to choose
fresh variable names.
\end{proof}


\subsection{Implementing type schemes}

It is convenient to represent bound variables by de Bruijn indices and free
variables (i.e.\ those defined in the context) by names
\citep{mcbride_mckinna_not_number_2004}.
Moreover, we use
Haskell's type system to prevent some incorrect manipulations of indices by
defining a \scare{successor} type
\citep{bird_paterson_nested_1999, bellegarde_hook_substitution_1994}

> data Index a = Z | S a
>     deriving (Functor, Foldable)

We can then represent schemes as

> data Schm a  =  Type (Ty a) 
>              |  All (Schm (Index a))
>              |  LetS (Ty a) (Schm (Index a))
>     deriving (Functor, Foldable)

> type Scheme = Schm TyName

The outermost bound variable is represented by |Z| and the other variables
are wrapped in the |S| constructor. For example, the type scheme
$\forall\alpha\forall\beta.\beta \arrow \rho$ (with $\alpha$ unused and $\rho$ free) is represented as

< All (All (Type (V (S Z) :-> V (S (S rho)))))

Note that the code forces us to distinguish a type $\tau$ and its corresponding
type scheme (written $.\tau$), as the latter will be represented by
|Type tau :: Scheme|.


Implementing the generalisation function |(>=>)| is straightforward:

> type Prefix      = Bwd TyEntry 

> (>=>) :: Prefix -> Scheme -> Scheme
> B0                      >=> sigma = sigma
> (_Xi :< alpha :=   d)  >=> sigma = case d of
>                    Hole     -> _Xi >=> All sigma'
>                    Some nu  -> _Xi >=> LetS nu sigma'
>   where 
>     sigma' = fmap bind sigma
>     bind beta  | alpha == beta  = Z
>                | otherwise      = S beta

Conversely, we can |specialise| a type scheme by extending the context
with fresh variables to produce a type.

> specialise :: Scheme -> Contextual Type
> specialise (Type tau) = return tau
> specialise sigma = do
>     let (d, sigma') = unpack sigma
>     beta <- fresh d
>     specialise (fmap (fromS beta) sigma')
>   where
>     unpack (All sigma') = (Hole, sigma')
>     unpack (LetS tau sigma') = (Some tau, sigma')
>     fromS beta Z          = beta
>     fromS beta (S alpha)  = alpha


\subsection{Type assignment system}

Let $\V_\TM$ be some set of term variables and let $x$ range over $\V_\TM$.
Term variable declarations $\D_\TM$ are scheme assignments of the form
$\asc \sigma$, with
$\ok_\TM (\asc \sigma) = \sigma \scheme$.

%%%The syntax of terms is
   Let $\Term$ be the set of terms, with syntax 
$$t ::= x ~||~ t~t ~||~ \lambda x . t ~||~ \letIn{x}{t}{t}.$$
%%%Let $\Term$ be the set of terms.
% where $x$ ranges over some set of term variables.

We define the type assignability statement $t : \tau$ by the 
   declarative 
rules in
Figure~\ref{fig:typeAssignmentRules}.
We can then define scheme assignability
$t \hasscheme \sigma$ as a map from terms $t$ and schemes $\sigma$ to statements:
\begin{align*}
t \hasscheme .\tau   &\mapsto    t : \tau  \\
t \hasscheme \forall \alpha \sigma  &\mapsto 
    \Sbind{\hole{\alpha}}{t \hasscheme \sigma}   \\
t \hasscheme \letS{\alpha}{\tau}{\sigma}  &\mapsto
    \Sbind{\alpha \defn \tau}{t \hasscheme \sigma}
\end{align*}

We observe the sanity conditions
$\Gamma \entails x : \tau  \Rightarrow  \Gamma \entails \tau \type$
and
$\Gamma \entails x \hasscheme \sigma \Rightarrow \Gamma \entails \sigma \scheme$.

\begin{figure}[ht]
\boxrule{\Delta \entails t : \tau}

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
      \Sbind{x \asc \sigma}{w : \tau}
     }
     {\letIn{x}{s}{w} : \tau}
\qquad
\Rule{t : \tau
      \quad
      \tau \equiv \upsilon}
     {t : \upsilon}
$$

\caption{Declarative rules for type assignment}
\label{fig:typeAssignmentRules}
\end{figure}


We define $\sem{x \asc \sigma}_\TM = x \hasscheme \sigma$, so $\Gamma
\lei \Delta$ requires $\Delta$ to assign a term variable all the types
that $\Gamma$ assigns it, but allows $x$ to become more polymorphic
and acquire new types.  This notion certainly retains stability:
every variable lookup can be simulated in the more general context.
However, it allows arbitrary generalisation of the schemes assigned to term
variables which are incompatible with the known and intended value of
those variables.

As \citet{wells_principal_typings_2002} points out, Hindley-Milner
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
does (modulo substitution).

\TODO{Move the above to after section 7.1, where $\lei$ is modified?}

As with unification, we wish to 
%%%translate 
   turn 
these 
%%%declarative 
rules into an
algorithm for type inference. We define the type inference problem $I$ by
\begin{align*}
\In{I}                &= \Term  \\
\Out{I}               &= \Type  \\
\Pre{I}{t}            &= \valid  \\
\Post{I}{t}{\tau}     &= \Pinf{t}{\tau}  \\
\R{I}{\tau}{\upsilon} &= \OutParam{\tau} \equiv \OutParam{\upsilon}
\end{align*}


\subsection{Implementing terms}

We extend the |Entry| data type to include declarations of term variables.
It is still not quite complete, however.

> type TmName   = String
> data TmEntry  = TmName ::: Scheme

< data Entry    = TY TyEntry | TM TmEntry | ...


A term $t$ may be a variable |(X)|, an application |(:$)|, an abstraction |(Lam)|
or a let binding |(Let)|. As with |Ty|, we parameterise over the type
of term variable names, so |Tm| is a foldable functor.

> data Tm a  =  X a
>            |  Tm a :$ Tm a 
>            |  Lam a (Tm a)
>            |  Let a (Tm a) (Tm a)
>     deriving (Functor, Foldable)

> type Term      = Tm TmName


\section{Local contexts for local problems}

\subsection{Preserving order in the context}

We have previously 
%%%\TODO{(have we? Yes: Subsection "Motivating Context")} 
observed, but not yet 
%%%made use of, the property that order in the context is important and 
   exploited, the importance of declaration order in the context, and that 
we move declarations left as
little as possible. Thus rightmost entries are those most local to the problem
we are solving. This will be useful when we come to implement type inference
for the |Let| construct, as we want to generalise over \scare{local} type
variables but not \scare{global} variables.

In order to keep track of locality in the context, we need another kind of
context entry: the $\fatsemi$ separator. We add 
%%%the context validity rule
   a new validity rule 
$$
\Rule{\Gamma \entails \valid}
     {\Gamma \fatsemi \entails \valid}
$$
so the (finally) complete data type of context entries is:

> data Entry = TY TyEntry | TM TmEntry | LetGoal

We also 
%%%need to 
refine the $\lei$ relation.
Let $\semidrop$ be the partial function from contexts and natural numbers to
contexts taking $\Gamma \semidrop n$ to $\Gamma$ truncated after $n$
$\fatsemi$ separators, provided $\Gamma$ contains at least $n$ 
%%%of them. It is defined by
   such: 
\begin{align*}
\Xi \semidrop 0 &= \Xi  \\
\Xi \fatsemi \Gamma \semidrop 0 &= \Xi  \\
\Xi \fatsemi \Gamma \semidrop n+1 &= \Xi \fatsemi (\Gamma \semidrop n)  \\
\Xi \semidrop n+1 &~\mathrm{undefined}
\end{align*}

We write $\delta : \Gamma \lei \Delta$ if $\delta$ is a
substitution from $\Gamma$ to $\Delta$ such that, for all 
$\decl{x}{D} \in \Gamma \semidrop n$ and $S \in \sem{\decl{x}{D}}$, we have that
$\Delta \semidrop n$ is defined and 
%%%$\Delta \entails \delta S$. 
$\Delta \semidrop n \entails \delta S$. 

This definition of $\Gamma \lei \Delta$ is stronger than the previous one, 
because it requires 
%%%a correspondence between 
the $\fatsemi$-separated sections of $\Gamma$ and $\Delta$ 
   to correspond  
%%%such that 
   in such a way that 
declarations in the first $n$ sections of
$\Gamma$ can be interpreted over the first $n$ sections of $\Delta$.
However, it is mostly straightforward to verify that the previous results 
%%%go through with 
   hold for 
the new definition.

%% Note that if $\delta : \Gamma \lei \Delta$ then
%% $\delta||_{\Gamma \semidrop n} : \Gamma \semidrop n \lei \Delta \semidrop n$. 

We refine the $\leiR$ relation in a corresponding way, and further insist for
$\Gamma \leiR \Delta$ that $\Gamma$ and $\Delta$ have the same
\define{shape} (list of $\fatsemi$ separators and term variables).
Formally, we say that $\delta : \Gamma \leiR \Delta$ if
$\delta : \Gamma \lei \Delta$ and $\forget{\Gamma} = \delta\forget{\Delta}$,
where $\forget{\cdot}$ is the forgetful map from contexts to shapes that discards
type variables:
\begin{align*}
\forget{\emptycontext}         &= \emptycontext  \\
\forget{\Gamma, \alpha D}      &= \forget{\Gamma}  \\
\forget{\Gamma, x \asc \sigma} &= \forget{\Gamma} , x \asc \sigma  \\
\forget{\Gamma \, \letGoal}      &= \forget{\Gamma} \, \letGoal
\end{align*}
Substitution on shapes acts on type schemes only.

\subsection{Fixing the unification algorithm}

The only place where changing the $\lei$ relation requires extra work is in the
unification algorithm,
because it acts structurally over the context, so we need to specify what happens
when it finds a $\fatsemi$ separator. 
%%%It turns out that these can simply be ignored, so we 
   In fact it suffices to  
add the following algorithmic rules:
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

The \textsc{Repossess} rule is 
%%%more complicated. It is 
   so named because it moves
%%%the variable 
declarations in $\Xi$ to the left of the $\fatsemi$ separator,
thereby \scare{repossessing} them. Despite 
%%%this, 
   such complications, 
unification still
yields a most general solution:

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
\TODO{Explain the induction and use of Lemma~\ref{lem:unifyComplete} for minimality.}

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

Corresponding results hold for the more restrictive
$\leiR$ relation, because 
%%%the unification algorithm 
   unification 
does not change the shape of the input context. 


\section{A type inference algorithm}


\subsection{Transforming the rule system for type assignment}

To transform a rule into an algorithmic form, we proceed clockwise starting from
the conclusion. For each hypothesis, we must ensure that the problem is fully
specified, inserting variables to stand for unknown problem inputs. Moreover, we
cannot pattern match on problem outputs, so we ensure there are schematic
variables in output positions, fixing things up with appeals to unification. 

Consider the rule for application, written to highlight problem inputs and
outputs as
$$\Rule{\Pinf{f}{\upsilon \arrow \tau}  \quad  \Pinf{a}{\upsilon}}
       {\Pinf{f a}{\tau}}.$$
Since we cannot match on the output of the first subproblem, we use a
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
which has unknown input $\upsilon$, so we bind a fresh variable $\beta$
to give
$$\Rule{\Sbind{\beta \defn \upsilon}{\Sbind{x \asc .\beta}{\Pinf{t}{\tau}}}}
       {\Sbind{\beta \defn \upsilon}{\Pinf{\lambda x . t}{\beta \arrow \tau}}}.$$

% and hence
% $$
% \Rule{\Jtype{\Gamma_0, \hole{\beta}, x \asc .\beta}{t}{\tau}
%           {\Gamma_1, x \asc .\beta, \Xi}}
%      {\Jtype{\Gamma_0}{\lambda x.t}{\beta \arrow \tau}{\Gamma_1, \Xi}}
% $$


The let rule is \TODO{($\OutParam{\sigma}$ seems dubious)}
$$
\Rule{
      s \hasscheme \OutParam{\sigma}
      \quad
      \Sbind{x \asc \sigma}{\Pinf{w}{\tau}}
     }
     {\Pinf{\letIn{x}{s}{w}}{\tau}}.
$$
Writing $\sigma = \gen{\Xi}{.\upsilon}$ and expanding the definition of
$\hasscheme$, we obtain
$$
\Rule{
      \Sbind{\Xi}{\Pinf{s}{\upsilon}}
      \quad
      \Sbind{x \asc \gen{\Xi}{.\upsilon}}{\Pinf{w}{\tau}}
     }
     {\Pinf{\letIn{x}{s}{w}}{\tau}}.
$$
where we let $\Sbind{\emptycontext}{S} = S$ and
$\Sbind{(\Xi, \decl{x}{D})}{S} = \Sbind{\Xi}{\Sbind{\decl{x}{D}}{S}}$.


But how can we find $\Xi$?
This is where 
   we use 
the $\fatsemi$ separator.  
%%%becomes necessary. 
Instead of an
unknown list of type variables, we just add a $\fatsemi$ to the context, 
infer the type of $s$, then generalise its type 
by \scare{skimming off} type
variables from the top of the context until the $\fatsemi$ is reached.


We define the type inference assertion $\Jtype{\Gamma}{t}{\tau}{\Delta}$
% (inferring the type of $t$ in $\Gamma_0$ yields $\tau$ in the more informative
% context $\Gamma_1$)
by the rules in Figure~\ref{fig:inferRules}.
These rules are clearly structural on terms, so yield a terminating
algorithm, leading naturally to an implementation, given in
subsection~\ref{sec:inferImplementation}.

%%%\TODO{Say something about freshness of $\Xi$ in \textsc{Var} rule.}
We use Lemma~\ref{lem:specialise} to ensure in rule \textsc{Var} that
we compute a suffix \(\Xi\) consisting of fresh names, such that the
output \ensuremath{\Gamma, \Xi} is well-formed.

\begin{figure}[ht]
\boxrule{\Jtype{\Gamma}{t}{\tau}{\Delta}}

$$
\name{Var}
\Rule{x \asc \gen{\Xi}{.\upsilon} \in \Gamma}
     {\Jtype{\Gamma}{x}{\upsilon}{\Gamma, \Xi}}
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
        {\Jtype{\Delta_0, x \asc \gen{\Xi_0}{.\upsilon}}{w}{\chi}
               {\Delta_1, x \asc \gen{\Xi_0}{.\upsilon}, \Xi_1}}
        {\Jtype{\Gamma}{\letIn{x}{s}{w}}{\chi}{\Delta_1, \Xi_1}}
$$

\caption{Algorithmic rules for type inference}
\label{fig:inferRules}
\end{figure}


\subsection{Soundness and completeness}

% We say $\Theta$ is a \define{subcontext} of $\Gamma$, written
% $\Theta \subcontext \Gamma$, if $\Gamma = \Theta; \Gamma'$ for some context
% extension $\Gamma'$.


\begin{lemma}[Soundness of type inference]
\label{lem:inferSound}
If $\Jtype{\Gamma}{t}{\upsilon}{\Delta}$ then
$\iota : \Gamma \leiR \Delta$ and $\Delta \entails \Pinf{t}{\upsilon}$.
\end{lemma}

\begin{proof}
% Suppose $\Jtype{\Gamma}{t}{\upsilon}{\Delta}$.
By induction on the structure of derivations.
% It is straightforward to verify that $\iota : \Gamma \leiR \Delta$ and
% $\Delta \entails \upsilon \type \wedge t : \upsilon$.
\end{proof}


\begin{lemma}[Completeness and generality of type inference]
\label{lem:inferComplete}
If $\theta : \Gamma \leiR \Theta$ and $\Theta \entails t : \tau$ then
$\JminR{\Gamma}{\Pinf{t}{\upsilon}}{\Delta}$
for some type $\upsilon$ and context $\Delta$.
\end{lemma}


\begin{proof}[Sketch]
The algorithm is structurally recursive over terms, failing only when
unification fails. Each step locally preserves all possible solutions.
For let-expressions, observe that any type specialising any scheme
for $s$ must certainly specialise the type we infer for $s$, and
\emph{ipso facto}, the principal type scheme we assign to $x$.
For details, see Appendix.
\end{proof}


\subsection{Implementing type inference}
\label{sec:inferImplementation}


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

To infer the type of a $\lambda$-abstraction, we recursively infer the type of
its body $w$ with variable $x$ assigned type-scheme $.\alpha$, 
with $\alpha$ 
%%%a fresh type variable. 
   fresh. 
% The type is then $\alpha \arrow \upsilon$ in the context with
% the $x$ binding removed.

> infer (Lam x w) = do
>     alpha    <- fresh Hole
>     upsilon  <- x ::: Type (V alpha) >- infer w
>     return (V alpha :-> upsilon)


To infer the type of an application, we infer the type $\chi$ of the function
$f$, then the type $\upsilon$ of the argument. Unifying $\chi$ with
$\upsilon \arrow \beta$, where $\beta$ is a fresh variable, produces the
result.

> infer (f :$ a) = do
>     chi      <- infer f
>     upsilon  <- infer a
>     beta     <- fresh Hole
>     unify chi (upsilon :-> V beta)
>     return (V beta)


Finally, to infer the type of a let construct, 
we infer the type of the definiens $s$ and generalise  
%%%over type variables on top of the context 
   it 
to yield a scheme $\sigma$.
We then infer the type of the body $w$ in the context where $x \asc \sigma$.

> infer (Let x s w) = do
>     sigma <- generaliseOver (infer s)
>     x ::: sigma >- infer w


The |generaliseOver| operator adds a |LetGoal| to the context,
evaluates its argument, then generalises over type variables
to the right of the |LetGoal| marker.

> generaliseOver ::  Contextual Type -> Contextual Scheme
> generaliseOver mt = do
>     modifyContext (:< LetGoal)
>     tau <- mt
>     _Xi <- skimContext
>     return (_Xi >=> Type tau)
>   where
>     skimContext :: Contextual Prefix
>     skimContext = do
>         _Gamma :< vD <- getContext
>         putContext _Gamma
>         case vD of
>             LetGoal    -> return B0
>             TY alphaD  -> (:< alphaD) <$> skimContext
>             TM _       -> error "Unexpected TM variable!"


The |(>-)| operator appends a term variable declaration to the context,
evaluates its second argument, then removes the declaration.

> (>-) :: TmEntry -> Contextual a -> Contextual a
> x ::: sigma >- ma = do
>     modifyContext (:< TM (x ::: sigma))
>     a <- ma
>     modifyContext extract
>     return a 
>   where          
>     extract ::  Context -> Context
>     extract (_Gamma :< TM (y ::: _))
>         | x == y               = _Gamma
>     extract (_Gamma :< TY xD)  = (extract _Gamma) :< TY xD
>     extract (_Gamma :< _)  = error "Bad context entry!"
>     extract B0             = error "Missing TM variable!"



\section{Discussion}  %%% Concussion?

We have arrived at an implementation of Hindley-Milner type inference
which involves all the same steps as Algorithm \W{}, but not
necessarily in the same order. In particular, the dependency analysis
which \W{} performs all of a sudden in the let-rule is here pushed
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


%if showCode

\subsection{Lists}

We define our own types of forward (|Fwd|) and backward (|Bwd|) lists,
which are foldable functors and monoids.

> data Fwd a = F0 | a :> Fwd a

<     deriving (Eq, Show)

>     deriving (Eq, Functor, Foldable, Show)

> infixr 8 :>

> data Bwd a = B0 | Bwd a :< a

<     deriving (Eq, Show)

>     deriving (Eq, Functor, Foldable, Show)

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


\NotForPublication{\perform{main}}


\phantomsection
\addcontentsline{toc}{section}{References}
\bibliographystyle{plainnat}
\bibliography{lib}

\newpage
\appendix

\section{Appendix}



\begin{proof}[Proof of lemma~\ref{lem:unifyComplete}
(Completeness and generality of unification)]
It suffices to show that the algorithm succeeds and produces a solution that is
below $\Theta$.
% We examine the structure of $\upsilon$ (or $\alpha$) and $\tau$, and 
% We proceed by induction on the total length of the context, the length of the
% context before the bar, and structurally on types.
We proceed by induction on the call graph; since the algorithm terminates, this
is well-founded.

\begin{enumerate}[(a)]
\item 
\begin{enumerate}[(i)]
\item Suppose $\upsilon = \alpha$ and $\tau = \beta$ are variables.
Let $\Gamma = \Gamma_0, \decl{x}{D}$ and examine $\decl{x}{D}$:
\begin{itemize}
\item If $x = \alpha = \beta$ are all the same variable, then the
\textsc{Idle} rule applies, $\Delta = \Gamma$ and the result is trivial.

\item If $\decl{x}{D} = \hole{\alpha}$ then the \textsc{Define} rule applies,
$\Delta = \Gamma_0, \alpha \defn \beta$
and $\theta : \Delta \lei \Theta$.
The case $\decl{x}{D} = \hole{\beta}$ is similar.

\item If $\decl{x}{D} = \alpha \defn \chi$ then
$\Theta \entails \theta\alpha \equiv \theta\chi$ by definition of $\lei$,
and $\Theta \entails \theta\alpha \equiv \theta\beta$ by hypothesis,
so $\Theta \entails \theta\beta \equiv \theta\chi$ by transitivity and symmetry.
But then $\theta_\alpha : \Gamma_0 \lei \Theta$ where $\theta_\alpha$ is $\theta$
with the type assigned to $\alpha$ removed, and
$\Theta \entails \theta_\alpha\beta \equiv \theta_\alpha\chi$,
since $\beta$ and $\chi$ cannot depend on $\alpha$ by the sanity conditions.
Now, by induction,
$\Junify{\Gamma_0}{\beta}{\chi}{\Delta_0}$
for some $\Delta_0$.
with $\theta_\alpha : \Delta_0 \lei \Theta$.
Hence the \textsc{Expand} rule applies,
$\Delta = \Delta_0, \alpha \defn \upsilon$
and $\theta : \Delta \lei \Theta$.
The case $\decl{x}{D} = \beta \defn \upsilon$ is similar.

\item Otherwise, $\decl{x}{D} \perp \{ \alpha, \beta \}$ and the \textsc{Ignore} rule
applies by a similar argument. \TODO{Give this argument.}
\end{itemize}

\item Now suppose wlog that $\upsilon = \alpha$ is a variable and $\tau$ is
not a variable. The conditions for part (b) hold, so by induction,
$\Jinstantiate{\Gamma}{\alpha}{\tau}{\emptycontext}{\Delta}$
and the \textsc{Solve} rule applies.

\item Otherwise, we have $\tau = \tau_0 \arrow \tau_1$ and
$\upsilon = \upsilon_0 \arrow \upsilon_1$.
Then $\Theta \entails \theta\tau_0 \equiv \theta\upsilon_0$ and
$\Theta \entails \theta\tau_1 \equiv \theta\upsilon_1$,
so by induction there exist contexts
$\Delta_0, \Delta$ such that
$\Junify{\Gamma}{\tau_0}{\upsilon_0}{\Delta_0}$ and
$\Junify{\Delta_0}{\tau_1}{\upsilon_1}{\Delta}$.
%, with $\theta : \Gamma \lei \Delta$ and $\theta : \Gamma_1 \lei \Delta$.
Hence the \textsc{Decompose} rule applies, and
$\theta : \Delta \lei \Theta$ by the Optimist's lemma.


\end{enumerate}

\item  Let $\Gamma = \Gamma_0, \decl{x}{D}$.
\begin{enumerate}[(i)]
\item If $x = \alpha \in \FTV{\tau, \Xi}$, then there is some
non-variable type $\chi$ such that
$\Theta \entails \theta\alpha \equiv \theta\chi$
and $\alpha \in \FTV{\chi}$.
\TODO{Explain why this follows.}
But this cannot occur, by lemma~\ref{lem:occurCheck}.

\item If $\decl{x}{D} = \hole{\alpha}$ and $\alpha \notin \FTV{\tau, \Xi}$, then the
\textsc{DefineS} rule applies, $\Delta = \Gamma_0, \Xi, \alpha := \tau$ and
$\theta : \Delta \lei \Theta$.

\item If $\decl{x}{D} = \alpha \defn \chi$ and $\alpha \notin \FTV{\tau, \Xi}$, then
$\Theta \entails \theta\alpha \equiv \theta\chi$,
so $\Theta \entails \theta\chi \equiv \theta\tau$ by symmetry and transitivity. 
Moreover, $\Gamma_0, \Xi \entails \tau \type$
since $\alpha \notin \FTV{\tau, \Xi}$, and
$\theta_\alpha : \Gamma_0, \Xi \lei \Theta$
so by induction
$\Junify{\Gamma_0, \Xi}{\chi}{\tau}{\Delta_0}$
for some $\Delta_0$
with $\theta_\alpha : \Delta_0 \lei \Theta$.
Hence the \textsc{ExpandS} rule applies with
$\Delta = \Delta_0, \alpha \defn \chi$
and $\theta : \Delta \lei \Theta$.

\item If $x = \beta$ for $\alpha \neq \beta$ and
$\beta \in \FTV{\upsilon, \Xi}$ then
$\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\beta D, \Xi}{\Delta}$
is well-posed, so it has a solution by induction and
the \textsc{DependS} rule applies. \TODO{Explain this.}

\item Otherwise $\decl{x}{D} \perp \FTV{\alpha, \tau, \Xi}$ and
$\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\Xi}{\Delta_0}$
is well-posed, so it has a solution by induction and
the \textsc{IgnoreS} rule applies with $\Delta = \Delta_0, \decl{x}{D}$.
\TODO{Explain this.}
\qedhere
\end{enumerate}
\end{enumerate}
\end{proof}



\begin{proof}[Proof of lemma~\ref{lem:inferComplete}
(Completeness and generality of type inference)]
It suffices to show that the algorithm succeeds and delivers a result that is
below $(\tau, \theta, \Theta)$. We proceed by structural induction.

\paragraph{Variables.}
If $t = x$ is a variable, then by inversion
$x \asc \sigma \in \Theta$.
Now by definition of $\leiR$,
$x \asc \gen{\Xi}{\upsilon} \in \Gamma$
where $\sigma = \theta\gen{\Xi}{\upsilon}$.
Hence the \textsc{Var} rule applies giving
$\Jtype{\Gamma}{x}{\upsilon}{\Gamma, \Xi}$.

The proof of $\Theta \entails x : \tau$ must consist of applying
$\Theta \entailsN x \hasscheme \gen{\theta\Xi}{\theta\upsilon}$
to some $\Theta$-types, so it determines a map from the unbound type variables of
$\Xi$ to types over $\Theta$, and hence a substitution
$\zeta : \Gamma, \Xi \leiR \Theta$ that agrees with $\theta$ on $\Gamma$ and maps
type variables in $\Xi$ to their definitions in $\Theta$.
Thus $\theta \eqsubst \zeta \compose \iota : \Gamma \leiR \Theta$.



\paragraph{Let bindings.}
If $t = (\letIn{x}{s}{w})$, then by inversion there is some scheme
$\sigma = \gen{\Psi}{.\tau_s}$ such that $\Theta \entails s \hasscheme \sigma$
and $\Theta, x \asc \sigma \entails w : \tau$.
Then $\Theta \fatsemi \entails s \hasscheme \gen{\Psi}{.\tau_s}$ so
$\Theta \fatsemi \Psi \entails s : \tau_s$.

Moreover $\theta : \Gamma \fatsemi \lei \Theta \fatsemi \Psi$, so
by induction
$\Jtype{\Gamma \fatsemi}{s}{\upsilon}{\Delta_0 \fatsemi \Xi_0}$
and there exists
$\zeta_0 : \Delta_0 \fatsemi \Xi_0 \leiR \Theta \fatsemi \Psi$
such that
$\theta \eqsubst \zeta_0 \compose \iota$ and
$\Theta \fatsemi \Psi \entails \zeta_0 \upsilon \equiv \tau_s$.

Now $\zeta_0 ||_{\Delta_0} : \Delta_0 \leiR \Theta$, so
$$\zeta_0 ||_{\Delta_0} : \Delta_0, x \asc \gen{\Xi_0}{.\upsilon}
    \leiR \Theta, x \asc \zeta_0\gen{\Xi_0}{.\upsilon}.$$
and (note the $\lei$ relation since we are generalising the type scheme)
$$\iota : \Theta, x \asc \gen{\Psi}{.\tau_s}
    \lei  \Theta, x \asc \zeta_0\gen{\Xi_0}{.\upsilon}$$
so by stability of type assignment under the $\lei$ relation,
$$\Theta, x \asc \zeta_0\gen{\Xi_0}{.\upsilon} \entails w : \tau.$$

Hence, by induction,
$$\Jtype{\Delta_0, x \asc \gen{\Xi_0}{.\upsilon}}{w}{\chi}
        {\Delta_1, x \asc \gen{\Xi_0}{.\upsilon}, \Xi_1}$$
and there is some
$$\zeta_1 : \Delta_1, x \asc \gen{\Xi_0}{.\upsilon}, \Xi_1
    \leiR \Theta, x \asc \zeta_0\gen{\Xi_0}{.\upsilon}$$
such that
$\zeta_0 ||_{\Delta_0} \equiv \zeta_1 \compose \iota$
%   : \Delta_0, x \asc \gen{\Xi_0}{.\upsilon}$
%          \leiR \Theta, x \asc \zeta_0\gen{\Xi_0}{.\upsilon}.
and
$\Theta, x \asc \zeta_0\gen{\Xi_0}{.\upsilon} \entails \zeta_1\chi \equiv \tau$.

Now the \textsc{Let} rule applies to give
$$\Jtype{\Gamma}{\letIn{x}{s}{w}}{\chi}{\Delta_1, \Xi_1}$$
and we have
$\zeta_1 : \Delta_1, \Xi_1 \leiR \Theta$,
$\Theta \entails \zeta_1\chi \equiv \tau$
and $\theta \equiv \zeta_1 \compose \iota$.



\paragraph{$\lambda$-abstractions.}
If $t = \lambda x . w$ is an abstraction, then by inversion
$\Theta \entails \tau \equiv \tau_0 \arrow \tau_1$
for some types $\tau_0$ and $\tau_1$, and
$\Theta, x \asc .\tau_0 \entails w : \tau_1$.
Taking $\theta' = \subst{\tau_0}{\alpha}{\theta}$, we have that
$$\theta' : \Gamma, \hole{\alpha}, x \asc .\alpha
             \leiR  \Theta, x \asc .\tau_0$$
and hence, by induction,
$$\Jtype{\Gamma, \hole{\alpha}, x \asc .\alpha}{w}{\upsilon}
              {\Delta_0, x \asc .\alpha, \Xi}$$
with $\zeta : \Delta_0, x \asc .\alpha, \Xi \leiR \Theta, x \asc .\tau_0$
such that $\theta' \eqsubst \zeta \compose \iota$ and
$\Theta, x \asc .\tau_0 \entails \zeta\upsilon \equiv \tau_1$.

Thus the \textsc{Abs} rule applies, so we have
$$\Jtype{\Gamma}{\lambda x . w}{\alpha \arrow \upsilon}
              {\Delta_0, \Xi},$$
$\zeta : \Delta_0, \Xi \leiR \Theta$,
$\theta \eqsubst \zeta \compose \iota$ and
$\Theta \entails \zeta(\alpha \arrow \upsilon) \equiv \tau_0 \arrow \tau_1$.



\paragraph{Applications.}
If $t = f a$ is an application, then
$\Theta \entails f : \tau_0 \arrow \tau$,
so by induction
$\Jtype{\Gamma}{f}{\chi}{\Delta_0}$
and there exists
$\zeta_0 : \Delta_0 \leiR \Theta$
such that 
$\theta \eqsubst \zeta_0 \compose \iota$ and
$\Theta \entails \zeta_0\chi \equiv \tau_0 \arrow \tau$.

Now $\Theta \entails a : \tau_0$, so by induction
$\Jtype{\Delta_0}{a}{\upsilon}{\Delta_1}$
and there exists
$\zeta_1 : \Delta_1 \leiR \Theta$
such that
$\zeta_0 \eqsubst \zeta_1 \compose \iota$ and
$\Theta \entails \zeta_1\upsilon \equiv \tau_0$.

Let $\zeta_2 = \subst{\tau}{\beta}{\zeta_1}$, then
$\zeta_2 : \Delta_1, \hole{\beta} \leiR \Theta$.
Now
$\Theta \entails \zeta_2\chi \equiv \tau_0 \arrow \tau$
since $\chi$ is a $\Delta_0$ type so
$\Theta \entails \zeta_2\chi \equiv \zeta_0\chi$.
Similarly, and since $\zeta_2$ maps $\beta$ to $\tau$, we have
$\Theta \entails \zeta_2(\upsilon \arrow \beta) \equiv \tau_0 \arrow \tau$.
Hence $\Theta \entails \zeta_2\chi \equiv \zeta_2(\upsilon \arrow \beta)$ so
we have
$\JunifyR{\Delta_1, \hole{\beta}}{\chi}{\upsilon \arrow \beta}{\Delta}$
with
$\zeta : \Delta \leiR \Theta$ such that
$\zeta_2 \eqsubst \zeta \compose \iota$
by completeness of unification.
Hence by the \textsc{App} rule,
$\Jtype{\Gamma}{f a}{\beta}{\Delta}$,
and $\theta \eqsubst \zeta \compose \iota$.
\end{proof}




\end{document}
