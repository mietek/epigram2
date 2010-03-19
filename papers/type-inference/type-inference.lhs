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
%format :$  = ":\!\!\$ "
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

\newcommand{\extend}{\ensuremath{\wedge}}
\newcommand{\yields}{\ensuremath{\dashv}}
\newcommand{\entails}{\ensuremath{\vdash}}
\newcommand{\var}{\ensuremath{\defn \_}}
\newcommand{\fresh}{\ensuremath{~\mathbf{fresh}}}
\newcommand{\type}{\ensuremath{~\mathbf{type}}}
\newcommand{\scheme}{\ensuremath{~\mathbf{scheme}}}
\newcommand{\valid}{\ensuremath{\mathbf{valid}}}
\newcommand{\emptycontext}{\ensuremath{\varepsilon}}
\newcommand{\notTypeVar}{\ensuremath{\ldots}}
\newcommand{\letGoal}{\ensuremath{\mathbf{let}}}
\newcommand{\letIn}[3]{\ensuremath{\mathrm{let}~ #1 \!:=\! #2 ~\mathrm{in}~ #3}}
\newcommand{\letS}[3]{\ensuremath{(!#1 \!:=\! #2 ~\mathrm{in}~ #3)}}
\newcommand{\boxrule}[1]{\begin{center}\framebox{\ensuremath{#1}}\end{center}}
\newcommand{\boxrules}[2]{\begin{center}\framebox{\ensuremath{#1}}\quad\framebox{\ensuremath{#2}}\end{center}}

\newcommand{\tmvars}[1]{\ensuremath{tmvars(#1)}}
\newcommand{\tyvars}[1]{\ensuremath{tyvars(#1)}}
\newcommand{\types}[1]{\ensuremath{types(#1)}}
\newcommand{\FTV}[1]{\ensuremath{FTV(#1)}}

\newcommand{\lei}{\ensuremath{\sqsubseteq}}
\newcommand{\gei}{\ensuremath{\sqsupseteq}}

\newcommand{\arrow}{\ensuremath{\triangleright}}
\newcommand{\defn}{\ensuremath{\!:=\!}}
\newcommand{\asc}{\ensuremath{:\sim}}
\newcommand{\hole}[1]{\ensuremath{#1 \!:= ?}}

\newcommand{\unify}[4]{\ensuremath{#1 \extend #2 \equiv #3 \yields #4}}
\newcommand{\unifyInst}[5]{\ensuremath{#1 \extend #2 \equiv #3 ~[#4] \yields #5}}
\newcommand{\name}[1]{\ensuremath{\mathrm{\textsc{#1}} \;}}
\newcommand{\side}[1]{\ensuremath{\; #1}}

\newcommand{\br}[2]{\genfrac{}{}{0pt}{0}{#1}{#2}}
\newcommand{\BigRule}[3]{\ensuremath{\Rule{\br{#1}{#2}}{#3}}}

\newcommand{\sym}{\ensuremath{^\vee}}

\newcommand{\W}{\ensuremath{\mathcal{W}}}

\newcommand{\genarrow}{\ensuremath{\Uparrow}}
\newcommand{\gen}[2]{\ensuremath{(#1 \genarrow #2)}}
\newcommand{\forget}[1]{\ensuremath{\lfloor #1 \rfloor}}

\newcommand{\define}[1]{\emph{#1}}
\newcommand{\scare}[1]{`#1'}

\usepackage{amsthm}
\usepackage{amsmath}
\usepackage{enumerate}
\usepackage[T1]{fontenc}
\usepackage[draft=false]{hyperref}

\setlength{\parskip}{5pt}
\setlength{\parindent}{0pt}

\newtheorem{lemma}{Lemma}

\include{macros}
\setlength{\rulevgap}{0.05in}

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
We present a novel first-order unification algorithm and a type inference algorithm that
makes use of it. Both algorithms are based around the idea of a well-founded
linear context in which type variable bindings and type-schemes for terms may only
depend on types that appear earlier in the context. We ensure that the unification
algorithm produces a most general unifier by only moving definitions earlier in
the context when this is absolutely necessary.
\end{abstract}


\section{Introduction}

Algorithm \W, also known as the Damas-Milner algorithm, is a well-known type
inference algorithm for the Hindley-Milner type system due to
\citet{milner_theory_1978}, and proved correct by \citet{damas_principal_1982}.
It is based on the Unification Algorithm of
\citet{robinson_machine-oriented_1965}.

Successive presentations and formalisations of Algorithm \W\ have treated the
underlying unification algorithm as a \scare{black box}, but by considering both
simultaneously we are able to give a more elegant type inference algorithm.
In particular, the generalisation step (required when inferring the type of
a let-expression) becomes straightforward.

We present the algorithm using systems of inference rules to define judgements
of the form $\Gamma_0 \extend J \yields \Gamma_1$. Here $\Gamma_0$ is the input
context (before applying the rule), $J$ is the condition being established, and
$\Gamma_1$ is the output context (in which $J$ holds). The idea of separating
input and output contexts goes back to ???. In each case, at most one
rule matches the input context and condition, and we specify a termination order
so the rules define an algorithm. We additionally give an implementation of the
algorithm in Haskell.

Contexts here are not simply sets of assumptions, but lists containing
information about type and term variables. The unification problem thus
becomes finding a \scare{more informative} context in which two expressions are
equivalent up to definition. Order of entries in a context is important: they are
subject to well-foundedness conditions (any definition must be in terms of
definitions earlier in the context), and we obtain most general unifiers and
principal types by keeping entries as far to the right as possible, only moving
them left when necessary to satisfy a constraint. This idea of imposing order
restrictions on the entries of a context is similar to the \emph{ordered hypotheses}
of deduction systems for non-commutative logic \citep{polakow_natural_1999}.

In contrast to other presentations of unification and Hindley-Milner type
inference, our algorithm uses explicit definitions to avoid the need for a 
substitution operation. It thus lends itself to efficient implementation.
(We do use substitution in our reasoning about the system.) Many implementations
of (variations on) the Robinson unification algorithm are incorrect because they
do not handle substitutions correctly \citep{norvig_correctingwidespread_1991},
and substitutions often complicate mechanical correctness proofs.


%if False

> {-# LANGUAGE DeriveFunctor, DeriveFoldable, FlexibleInstances,
>     TypeSynonymInstances, TypeFamilies, StandaloneDeriving, TypeOperators #-}

First, let's get some imports out of the way.

> import Prelude hiding (any)
> import Control.Applicative (Applicative, (<$>), (<*>), pure)
> import Control.Monad (ap)
> import Control.Monad.State (StateT, get, gets, lift, put, runStateT)
> import Data.Foldable (any, Foldable, foldMap)
> import Data.Monoid (Monoid, mappend, mempty)

%endif


\section{Types and contexts}

The syntax of types is
$$\tau ::= \alpha ~||~ \tau \arrow \tau$$
where $\alpha$ ranges over some set of type variables.

For now, a \define{context entry} will be a type variable declaration
|alpha := mt|, where $\alpha$ is a variable that is either bound to a type $\tau$
(written |alpha := Just tau| or $\alpha := \tau$), or left unbound
(written |alpha := Nothing| or $\hole{\alpha}$).
Later, we will add other kinds of entry that are not relevant for unification.

In the sequel, $\Gamma$ and $\Delta$ are contexts, $\alpha$ and $\beta$ are type
variables and $\tau$ and $\upsilon$ are types. (All of these symbols may be
primed or subscripted.) We use $\Xi$ to denote a context suffix that will
contain only type variable declarations, and no other kinds of entry.  We write
$\emptycontext$ for the empty context.

Arguably the most basic judgement a context can support is a membership test.
We define $\Gamma \entails \alpha \defn mt$ to mean $\alpha \defn mt \in \Gamma$.
We write $\alpha \var$ for an entry that is either $\hole{\alpha}$ or
$\alpha \defn \tau$ for some $\tau$, and define
$\Gamma \entails \alpha ~\mathbf{fresh}$ to mean
$\Gamma \not\entails \alpha \var$.

We define the judgements $\Gamma \entails \valid$ ($\Gamma$ is a valid context)
and  $\Gamma \entails \tau \type$ ($\tau$ is a valid type in context $\Gamma$) by
the rules in Figure~\ref{fig:contextTypeValidityRules}.
As sanity conditions, observe that if $\Gamma \entails \tau \type$ for some
type $\tau$, then $\Gamma \entails \valid$ and $\Gamma$ is non-empty.

If $\Gamma$ is a valid context,
we write $\tyvars{\Gamma}$ for the set of type variables of $\Gamma$
and $\types{\Gamma}$ for the set of types $\tau$ such that
$\Gamma \entails \tau \type$. We define
\begin{align*}
\FTV{\tau}      &= \{ \alpha ~||~ \alpha \in \tau \}  \\
\FTV{\Xi}       &= \bigcup \{ \FTV{\tau} ~||~ \alpha \defn \tau \in \Xi \}  \\
\FTV{\tau, \Xi} &= \FTV{\tau} \cup \FTV{\Xi}.
\end{align*}

\begin{figure}[ht]
\boxrule{\Gamma \entails \valid}

$$
\Axiom{\emptycontext \entails \valid}
$$

$$
\Rule{\Gamma \entails \valid    \quad    \Gamma \entails \alpha \fresh}
     {\Gamma, \hole{\alpha} \entails \valid}
\qquad
\Rule{\Gamma \entails \tau \type    \quad    \Gamma \entails \alpha \fresh}
     {\Gamma, \alpha \defn \tau \entails \valid}
$$

\bigskip
\boxrule{\Gamma \entails \tau \type}

$$
\Rule{\Gamma \entails \valid    \quad     \Gamma \entails \alpha \var}
     {\Gamma \entails \alpha \type}
\qquad
\Rule{\Gamma \entails \tau \type \quad \Gamma \entails \upsilon \type}
     {\Gamma \entails \tau \arrow \upsilon \type}
$$

\caption{Rules for context and type validity}
\label{fig:contextTypeValidityRules}
\end{figure}


\subsection{Implementation}

The foldable functor |Ty| defines types in our object language parameterised by
the type of variable names, which will be useful later. Thanks to a language
extension in GHC 6.12 \citep{ghc_team_7.5.extensions_2009} we can simply
derive the required typeclass instances.
We define |Type| to use integers as names.

> data Ty a  =  V a |  Ty a :-> Ty a
>     deriving (Functor, Foldable)

%if False

> infixr 5 :->

%endif

> type Name  = Integer
> type Type  = Ty Name


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

We work in the |Contextual| monad (computations that can fail and mutate the context). 
The |Name| component is the next fresh type variable name to use;
it is an implementation detail that is not mentioned in the typing judgements.

> type Contextual  = StateT (Name, Context) Maybe


\section{Unification up to definition}

For a fixed context $\Gamma$, define a relation $\Gamma \entails \cdot \equiv \cdot$
on $\types{\Gamma}$ by taking the structural and equivalence closure generated
by the axiom
$$
\Rule{\Gamma \entails \alpha \defn \tau}
     {\Gamma \entails \alpha \equiv \tau}.
$$

We say that $\Gamma$ \define{contains less information than} $\Delta$, written
$\Gamma \lei \Delta$, if there exists a substitution
$\theta : \tyvars{\Gamma} \rightarrow \types{\Delta}$ that
\define{preserves definitions in $\Gamma$}, i.e.\ a substitution such that
$$\Gamma \entails \alpha \defn \tau  \Rightarrow   \Delta \entails \theta \alpha \equiv \theta \tau.$$
In this case, we write $\theta : \Gamma \lei \Delta$.
We require a substitution because the type inference algorithm will invent new
type variables, which must be interpreted over a more informative context that
will not contain them.
It is straightforward to verify that $\lei$ is a preorder and
  $$\theta : \Gamma \lei \Delta 
    \quad \mathrm{iff} \quad
    \Gamma \entails \tau \equiv \upsilon
        \Rightarrow \Delta \entails \theta\tau \equiv \theta\upsilon.$$

A \define{unifier} for the types $\tau$ and $\upsilon$ in a context $\Gamma$ is a pair
$(\Delta, \theta)$ such that $\theta : \Gamma \lei \Delta$ and
$\Delta \entails \theta\tau \equiv \theta\upsilon$.
$\Delta$ is said to be \define{most general} if it is
minimal with respect to $\lei$, i.e.\ for every unifier $\Delta'$ of
$\tau$ and $\upsilon$ in $\Gamma$, we have $\Delta \lei \Delta'$.

The rules in Figure~\ref{fig:unifyRules} define our unification algorithm. The
judgement
$\unify{\Gamma_0}{\tau}{\upsilon}{\Gamma_1}$
means that given inputs $\Gamma_0$, $\tau$ and $\upsilon$,
unification of $\tau$ with $\upsilon$ 
succeeds with output context $\Gamma_1$.
The judgement
$\unifyInst{\Gamma_0}{\alpha}{\tau}{\Xi}{\Gamma_1}$
means that given inputs $\Gamma_0$, $\tau$, $\upsilon$ and $\Xi$,
instantiation of $\alpha$ with $\tau$ succeds with output context $\Gamma_1$.
(Here $\Xi$ is a (possibly empty) list of type variable declarations.)
In each case, the idea is that the output context minimally extends the
input context to make the additional judgement hold.

We define the orthogonality relation $e \perp J$ (entry $e$ does not have any
effect on the judgement $J$) for unification and instantiation judgements
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

The rules \textsc{Coalesce}, \textsc{Expand} and \textsc{Instantiate} have symmetric counterparts
which are identical apart from interchanging the equated terms in the conclusion.
Usually we will ignore these without loss of generality, but where necessary we
refer to them as \textsc{Coalesce}\sym, \textsc{Expand}\sym and \textsc{Instantiate}\sym.
A fat semicolon ($\fatsemi$) indicates that the context is passed along unmodified.

\begin{figure}[ht]
\boxrule{\Gamma_0 \extend \tau \equiv \upsilon \yields \Gamma_1}

$$
\name{Id}
\Axiom{\unify{\Gamma}{\alpha}{\alpha}{\Gamma}}
$$

$$
\name{Coalesce}
\Axiom{\unify{\Gamma, \hole{\alpha}}{\alpha}{\beta}{\Gamma, \alpha \defn \beta}}
$$

$$
\name{Expand}
\Rule{\unify{\Gamma_0}{\tau}{\beta}{\Gamma_1}}
     {\unify{\Gamma_0, \alpha \defn \tau}{\alpha}{\beta}{\Gamma_1, \alpha \defn \tau}}
\side{\alpha \neq \beta}
$$

$$
\name{Orthogonal}
\Rule{\unify{\Gamma_0}{\tau}{\upsilon}{\Gamma_1}}
     {\unify{\Gamma_0, e}{\tau}{\upsilon}{\Gamma_1, e}}
\side{e \perp \tau \equiv \upsilon}
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
\Rule{\Gamma_0 \extend \tau_0 \equiv \upsilon_0 \fatsemi \tau_1 \equiv \upsilon_1 \yields \Gamma_1}
     {\Gamma_0 \extend \tau_0 \arrow \tau_1 \equiv \upsilon_0 \arrow \upsilon_1 \yields \Gamma_1}
$$

$$
\name{Instantiate}
\Rule{\unifyInst{\Gamma_0}{\alpha}{\tau}{\emptycontext}{\Gamma_1}}
     {\unify{\Gamma_0}{\alpha}{\tau}{\Gamma_1}}
\side{\tau \mathrm{~not~variable}}
$$

\bigskip

\boxrule{\unifyInst{\Gamma_0}{\alpha}{\tau}{\Xi}{\Gamma_1}}

$$
\name{InstCoalesce}
\Axiom{\unifyInst{\Gamma, \hole{\alpha}}{\alpha}{\tau}{\Xi}{\Gamma, \Xi, \alpha \defn \tau}}
\side{\alpha \notin \FTV{\tau, \Xi}}
$$

$$
\name{InstExpand}
\Rule{\unify{\Gamma_0, \Xi}{\upsilon}{\tau}{\Gamma_1}}
     {\unifyInst{\Gamma_0, \alpha \defn \upsilon}{\alpha}{\tau}{\Xi}{\Gamma_1, \alpha \defn \nu}}
$$

$$
\name{InstPass}
\Rule{\unifyInst{\Gamma_0}{\alpha}{\tau}{\beta \defn mt, \Xi}{\Gamma_1}}
     {\unifyInst{\Gamma_0, \beta \defn mt}{\alpha}{\tau}{\Xi}{\Gamma_1}}
\side{\alpha \neq \beta, \beta \in \FTV{\tau, \Xi}}
$$

$$
\name{InstOrthogonal}
\Rule{\unifyInst{\Gamma_0}{\alpha}{\tau}{\Xi}{\Gamma_1}}
     {\unifyInst{\Gamma_0, e}{\alpha}{\tau}{\Xi}{\Gamma_1, e}}
\side{e \perp \alpha \equiv \tau [\Xi]}
$$

% \begin{prooftree}
% \AxiomC{ $\Gamma_0 \focusbar \Xi \extend \alpha \equiv \tau \yields \Gamma_1$ }
% \LeftLabel{ \textsc{InstSkip$_1$} }
% \RightLabel{ $\beta \notin \FTV{\tau, \Xi}$ }
% \UnaryInfC{ $\Gamma_0, \beta \defn mt \focusbar \Xi \extend \alpha \equiv \tau \yields \Gamma_1, \beta \defn mt$ }
% \end{prooftree}

% \begin{prooftree}
% \AxiomC{ $\Gamma_0 \focusbar \Xi \extend \alpha \equiv \tau \yields \Gamma_1$ }
% \LeftLabel{ \textsc{InstSkip$_2$} }
% \RightLabel{ $\beta \notin \FTV{\tau, \Xi}$ }
% \UnaryInfC{ $\Gamma_0, \Diamond \focusbar \Xi \extend \alpha \equiv \tau \yields \Gamma_1, \Diamond$ }
% \end{prooftree}

\caption{Algorithmic rules for unification}
\label{fig:unifyRules}
\end{figure}


Observe that we have no rule for the case
$$\Gamma_0, \hole{\alpha} \extend \alpha \equiv \tau ~[\Xi]
  \quad \mathrm{when} \quad
  \alpha \in \FTV{\tau, \Xi}$$
so the algorithm fails if this situation arises. This is essentially an occur
check failure: $\alpha$ and $\tau$ cannot be unified if $\alpha$ occurs in
$\tau$ or in an entry that $\tau$ depends on. (Note that the trivial exception
$\tau = \alpha$ is dealt with by the \textsc{Id} rule.) Since we only have one
type constructor symbol (the function arrow $\arrow$), there are no failures due
to rigid-rigid mismatch. Adding these would not significantly complicate matters,
however.

\begin{lemma}[Soundness of unification]
\label{lem:unifySound}
(a) If $\Gamma_0 \extend \tau \equiv \upsilon \yields \Gamma_1$, then
$\Gamma_1 \entails \tau \equiv \upsilon$,
$\tyvars{\Gamma_0} = \tyvars{\Gamma_1}$ and
$\iota : \Gamma_0 \lei \Gamma_1$ where
$$\iota: \tyvars{\Gamma_0} \rightarrow \types{\Gamma_1} : \alpha \mapsto \alpha$$
is the inclusion substitution.

(b) Moreover, if
$\unifyInst{\Gamma_0}{\alpha}{\tau}{\Xi}{\Gamma_1}$, then
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
$\Gamma_0 \extend \tau \equiv \upsilon \yields \Gamma_1$ for some $\Gamma_1$ with
$\theta : \Gamma_1 \lei \Delta$. That is, if a unifier for $\tau$ and $\upsilon$
exists, then the algorithm succeeds and delivers a most general unifier.

(b) Moreover, if $\theta : \Gamma, \Xi \lei \Delta$ and
$\Delta \entails \theta\alpha \equiv \theta\upsilon$
where $\Xi$ contains only type variable declarations and $\upsilon$ is not a
variable, then $\unifyInst{\Gamma}{\alpha}{\upsilon}{\Xi}{\Gamma_1}$ for some
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
$\Gamma_0' \extend \beta \equiv \upsilon \yields \Gamma_1'$
for some $\Gamma_1'$ with $\theta_\alpha : \Gamma_1' \lei \Delta$.
Hence the \textsc{Expand} rule applies, $\Gamma_1 = \Gamma_1', \alpha \defn \upsilon$
and $\theta : \Gamma_1 \lei \Delta$.
The case $e = \beta \defn \upsilon$ is similar.

\item Otherwise, $e \perp \alpha \equiv \beta$ and the \textsc{Orthogonal} rule
applies by a similar argument.
\end{itemize}

Now suppose $\tau = \tau_0 \arrow \tau_1$ and $\upsilon = \upsilon_0 \arrow \upsilon_1$.
Then by induction, there are some contexts $\Gamma$ and $\Gamma_1$ such that
$\Gamma_0 \extend \tau_0 \equiv \upsilon_0 \yields \Gamma$ and
$\Gamma \extend \tau_1 \equiv \upsilon_1 \yields \Gamma_1$, with
$\theta : \Gamma \lei \Delta$ and $\theta : \Gamma_1 \lei \Delta$. Hence
the \textsc{Arrow} rule applies.

Finally, suppose wlog that $\tau = \alpha$ is a variable and $\upsilon$ is not a variable.
By part (b), $\unifyInst{\Gamma_0}{\alpha}{\upsilon}{}{\Gamma_1}$ and
the \textsc{Instantiate} rule applies.

(b) Suppose $\theta : \Gamma, \Xi \lei \Delta$ and
$\Delta \entails \theta\alpha \equiv \theta\upsilon$
where $\Xi$ contains only type variable declarations and $\upsilon$ is not a variable.
Let $\Gamma = \Gamma_0, e$. We proceed by induction as before.

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


The |(<?)| typeclass function tests if a name occurs in a type or context
suffix, since these are both |Foldable| functors containing names.

> class OccursIn a where
>     (<?) :: Name -> a -> Bool

> instance OccursIn Name where
>     (<?) = (==)

> instance Foldable ((::=) a) where
>     foldMap f (_ ::= x) = f x

> instance (Foldable t, OccursIn a) => OccursIn (t a) where
>     alpha <? t = any (alpha <?) t


\section{Type schemes}

A \define{type scheme} $\sigma$ is a type wrapped in one or more $\forall$
quantifiers or let bindings, with the syntax
$$\sigma ::= .\tau ~||~ \forall\alpha~\sigma ~||~ \letS{\alpha}{\tau}{\sigma}.$$
We use explicit definitions in type schemes to avoid the need for substitution
in the type inference algorithm. 

We now define a new judgement form $\Gamma \entails \sigma \scheme$ ($\sigma$ is
a valid scheme in $\Gamma$) by the rules in Figure~\ref{fig:schemeValidityRules}.
We also observe the further sanity condition
$\Gamma \entails \sigma \scheme$ implies $\Gamma \entails \valid$.

\begin{figure}[ht]
\boxrule{\Gamma \entails \sigma \scheme}

$$
\Rule{\Gamma \entails \tau \type}
     {\Gamma \entails .\tau \scheme}
\qquad
\Rule{\Gamma \entails \sigma \scheme}
     {\Gamma \entails \forall\alpha~\sigma \scheme}
$$

$$
\Rule{\Gamma \entails \sigma \scheme
      \quad
      \Gamma \entails \tau \type}
     {\Gamma \entails \letS{\alpha}{\tau}{\sigma} \scheme}
$$

\caption{Rules for scheme validity}
\label{fig:schemeValidityRules}
\end{figure}


The judgement $\Delta \entails \sigma \succ \tau$, defined in
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


It is convenient to represent bound variables using de Brujin indices and
free variables (i.e.\ those defined in the context) using names. Moreover, we can
use the Haskell type system to prevent some incorrect manipulations of the
indices by defining a natural number type

> data Index a = Z | S a
>     deriving (Functor, Foldable)

and representing schemes as

> data Schm a  =  Type (Ty a) 
>              |  All (Schm (Index a))
>              |  LetS (Ty a) (Schm (Index a))
>     deriving (Functor, Foldable)

> type Scheme = Schm Name

The outermost bound variable is represented by |Z| and the other variables
are wrapped in the |S| constructor. For example, the type scheme
$\forall\alpha\forall\beta.\beta \arrow 2$ is represented as

< All (All (Type (V (S Z) :-> V (S (S 2)))))

Note that the code forces us to distinguish a type $\tau$ and its corresponding
type scheme (written $.\tau$), as the latter will be represented by
|Type tau :: Scheme|.


\section{Making contexts more informative}

Now we can give the full definition of context entries that we postponed earlier.
As before, |alpha := mt| declares a type variable name $\alpha$; this is the only
kind of entry used in unification. A scheme assignment |x ::: sigma| defines a
term variable $x$ with type scheme $\sigma$. A |LetGoal| marker is used when
inferring the type of let bindings, to make it easy to determine which variables
can be generalised over.
The term variable definitions and |LetGoal| markers will record information about
progress through the structure of a term when inferring its type.

Since the additional context entries are not used in unification, it is
straightforward to extend the orthogonality judgements: if $e = \letGoal$ or
$e = x \asc \sigma$ we have $e \perp J$ for any $J$.
We also extend the context validity judgement with additional rules, as given in
Figure~\ref{fig:additionalContextValidityRules}.

\begin{figure}[ht]
\boxrule{\Gamma \entails \valid}

$$
\Rule{\Gamma \entails \sigma \scheme}
     {\Gamma, x \asc \sigma \entails \valid}
\qquad
\Rule{\Gamma \entails \valid}
     {\Gamma, \letGoal \entails \valid}
$$

\caption{Additional rules for context validity}
\label{fig:additionalContextValidityRules}
\end{figure}

Note that term variable names are not necessarily unique, so the most recent
definition of a name will shadow previous occurences. Thus we define
$\Gamma \entails x \asc \sigma$ to mean that $x \asc \sigma \in \Gamma$ and
moreover that this is the rightmost (i.e.\ most local) occurence of $x$.

The full data type of context entries is thus:

> data Entry  =  Name := Maybe Type
>             |  TermName ::: Scheme
>             |  LetGoal


\section{Type scheme operations}

\subsection{Specialisation}

The judgement $\Gamma \extend \sigma \succ \tau \yields \Gamma, \Xi$ means
that, starting with the context $\Gamma$, the scheme $\sigma$ specialises
to the type $\tau$ when the context is extended with some type variable
definitions $\Xi$. This judgement
is defined as shown in Figure~\ref{fig:specialiseAlgorithm}.

\begin{figure}[ht]
\boxrule{\Gamma \extend \sigma \succ \tau \yields \Gamma, \Xi}

$$
\name{T}
\Rule{\Gamma \entails \tau \type}
     {\Gamma \extend .\tau \succ \tau \yields \Gamma}
$$

$$
\name{All}
\Rule{\Gamma \entails \alpha \fresh    \quad
      \Gamma, \hole{\alpha} \extend \sigma \succ \tau \yields \Gamma, \hole{\alpha}, \Xi}
     {\Gamma \extend \forall\alpha~\sigma \succ \tau \yields \Gamma, \hole{\alpha}, \Xi}
$$

$$
\name{LetS}
\Rule{\Gamma \entails \alpha \fresh    \quad
      \Gamma, \alpha \defn \upsilon \extend \sigma \succ \tau \yields \Gamma, \alpha \defn \upsilon, \Xi}
     {\Gamma \extend \letS{\alpha}{\upsilon}{\sigma} \succ \tau \yields \Gamma, \alpha \defn \upsilon, \Xi}
$$

\caption{Algorithmic rules for specialisation}
\label{fig:specialiseAlgorithm}
\end{figure}


\begin{lemma}[Soundness of specialisation]
\label{lem:specialiseSound}
If $\Gamma_0 \extend \sigma \succ \tau \yields \Gamma_1$, then
$\Gamma_1 \entails \sigma \succ \tau$, $\tyvars{\Gamma_0} \subseteq \tyvars{\Gamma_1}$ and
$\iota : \Gamma_0 \lei \Gamma_1$.
\end{lemma}

\begin{proof}
By structural induction on $\sigma$.
\end{proof}

\begin{lemma}[Completeness of specialisation]
\label{lem:specialiseComplete}
If $\theta_0 : \Gamma_0 \lei \Delta$, $\Gamma_0 \entails \sigma \scheme$ and
$\Delta \entails \theta_0\sigma \succ \tau$,
then $\Gamma_0 \extend \sigma \succ \upsilon \yields \Gamma_1$ for some type
$\upsilon$ and context $\Gamma_1$ with $\theta_1 : \Gamma_1 \lei \Delta$,
$\Delta \entails \tau \equiv \theta_1\upsilon$ and
$\forall \alpha \in \tyvars{\Gamma_0} . \Delta \entails \theta_0 \alpha \equiv \theta_1 \alpha$.
\end{lemma}

\begin{proof}

\end{proof}


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
>     alpha <- freshVarDef tau
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
$$t ::= x ~||~ t~t ~||~ \lambda x . t ~||~ \letIn{x}{t}{t}$$
where $x$ ranges over some set of term variables.

We define the judgement $\Delta \entails t : \tau$ ($t$ can be assigned type $\tau$
in $\Delta$) by the rules in Figure~\ref{fig:typeAssignmentRules}.

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
               \Leftrightarrow  \Delta \entails x : \tau)$ and
\item $\forget{\Gamma}$ is a prefix of $\forget{\Delta}$.
\end{enumerate}

Furthermore, we define the judgement $\Gamma_0 \extend t : \tau \yields \Gamma_1$
(inferring the type of $t$ in $\Gamma_0$
yields $\tau$ in the more informative context $\Gamma_1$) by the rules in
Figure~\ref{fig:inferRules}.

\begin{figure}[ht]
\boxrule{\Delta \entails t : \tau}

$$
\Rule{\Delta \entails t : \tau
      \quad
      \Delta \entails \tau \equiv \upsilon}
     {\Delta \entails t : \upsilon}
\qquad
\Rule{\Delta \entails x \asc \sigma
      \quad
      \Delta \entails \sigma \succ \tau}
     {\Delta \entails x : \tau}
$$

$$
\Rule{\Delta, x \asc .\upsilon \entails t : \tau}
     {\Delta \entails \lambda x.t : \upsilon \arrow \tau}
\qquad
\Rule{\Delta \entails f : \upsilon \arrow \tau
      \quad
      \Delta \entails a : \upsilon}
     {\Delta \entails f a : \tau}
$$

%      \forall \upsilon . (\Gamma \entails \sigma \succ \upsilon
%              \Rightarrow \Gamma \entails s : \upsilon)

$$
\Rule{
      \forall \upsilon \Phi . (\theta : \Delta \lei \Phi
          \wedge \Phi \entails \theta\sigma \succ \upsilon
              \Leftrightarrow \Phi \entails s : \upsilon)
      \quad
      \Delta, x \asc \sigma \entails t : \tau}
     {\Delta \entails \letIn{x}{s}{t} : \tau}
$$

\caption{Declarative rules for type assignment}
\label{fig:typeAssignmentRules}
\end{figure}



\begin{figure}[ht]
\boxrule{\Gamma_0 \extend t : \tau \yields \Gamma_1}

$$
\name{Var}
\Rule{\Gamma_0 \entails x \asc \sigma
      \quad
      \Gamma_0 \extend \sigma \succ \tau \yields \Gamma_1}
     {\Gamma_0 \extend x : \tau \yields \Gamma_1}
$$

$$
\name{Abs}
\Rule{\Gamma_0 \entails \alpha \fresh    \quad
      \Gamma_0, \hole{\alpha}, x \asc .\alpha; \extend t:\tau
          \yields \Gamma_1, x \asc \_; \Xi}
     {\Gamma_0 \extend \lambda x.t : \alpha \arrow \tau \yields \Gamma_1, \Xi}
$$

$$
\name{App}
\BigRule{\Gamma_0 \extend f : \tau   ~\fatsemi~  a : \tau' \yields \Gamma
         \quad
         \Gamma \entails \beta \fresh}
        {\Gamma, \hole{\beta} \extend \tau \equiv \tau' \arrow \beta \yields \Gamma_1}
        {\Gamma_0 \extend f a : \beta \yields \Gamma_1}
$$

$$
\name{Let}
\BigRule{\Gamma_0, \letGoal; \extend s : \tau_0 \yields \Gamma, \letGoal; \Xi_0}
        {\Gamma, x \asc \gen{\Xi_0}{.\tau_0}; \extend t : \tau_1
                 \yields \Gamma_1, x \asc \_; \Xi_1}
        {\Gamma_0 \extend \letIn{x}{s}{t} : \tau_1 \yields \Gamma_1, \Xi_1}
$$

\caption{Algorithmic rules for type inference}
\label{fig:inferRules}
\end{figure}


\begin{lemma}[Soundness of type inference]
\label{lem:inferSound}
If $\Gamma_0 \extend t : \tau \yields \Gamma_1$, then
$\Gamma_1 \entails t : \tau$, $\tyvars{\Gamma_0} \subseteq \tyvars{\Gamma_1}$,
$\forget{\Gamma_0} = \forget{\Gamma_1}$
and $\iota : \Gamma_0 \lei \Gamma_1$, where $\iota$ is the inclusion substitution.
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

%endif


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

%if False

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


\subsection{Implementation}

A term $t$ may be a variable |(X)|, an application |(:$)|, an abstraction |(Lam)|
or a let binding |(Let)|. As with type variables, we parameterise over the type
of term variable names, so |Tm| is a foldable functor.

> data Tm a  =  X a
>            |  Tm a :$ Tm a 
>            |  Lam a (Tm a)
>            |  Let a (Tm a) (Tm a)
>     deriving (Functor, Foldable)

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
$t$ with its variable $x$ assigned type-scheme $.\alpha$, where $\alpha$
is a fresh type variable. The type is then $\alpha \arrow \tau$ in the context with
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


\section{Odds and ends}

\subsection{Fresh names}

The |freshVar| function generates a fresh name for a type variable and defines it as unbound,
and the |freshVarDef| function generates a fresh name and binds it to the given type.

> fresh :: Maybe Type -> Contextual Name
> fresh mt = do  (beta, _Gamma) <- get
>                put (succ beta, _Gamma :< beta := mt)
>                return beta

> freshVar :: Contextual Name
> freshVar = fresh Nothing

> freshVarDef :: Type -> Contextual Name
> freshVarDef = fresh . Just


\subsection{Context manipulation}

The |getContext| function retrieves the context.

> getContext :: Contextual Context
> getContext = gets snd

The |putContext| operator replaces the stored context.

> putContext :: Context -> Contextual ()
> putContext _Gamma = do  beta <- gets fst
>                         put (beta, _Gamma)

The |modifyContext| operator applies a function to the stored context.

> modifyContext :: (Context -> Context) -> Contextual ()
> modifyContext f = getContext >>= putContext . f

The |popEntry| function removes the topmost entry from the context and returns it.

> popEntry :: Contextual Entry
> popEntry = do  _Gamma :< e <- getContext
>                putContext _Gamma
>                return e


%if False

\subsection{Lists}

We define our own types of forward (|Fwd|) and backward (|Bwd|) lists,
which are foldable functors and monoids.

> data Fwd a = F0 | a :> Fwd a
>     deriving (Eq, Functor, Foldable, Show)
> infixr 8 :>

> data Bwd a = B0 | Bwd a :< a
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

> (<><) :: Context -> Suffix -> Context
> infixl 8 <><
> xs <>< F0 = xs
> xs <>< (alpha ::= mt :> ys) = (xs :< alpha := mt) <>< ys

> (<>>) :: Bwd a -> Fwd a -> Fwd a
> infixl 8 <>>
> B0 <>> ys         = ys
> (xs :< x) <>> ys  = xs <>> (x :> ys)


\section{Judgement typeclass}

> class Judgement j where
>     type Output j
>     fiat :: j -> Contextual (Output j)
>     orthogonal :: Entry -> j -> Bool

> instance Judgement () where
>     type Output () = ()
>     fiat () = return ()
>     orthogonal _ _ = True

> instance (Judgement j, Judgement k) => Judgement (j, k) where
>     type Output (j, k) = (Output j, Output k)
>     fiat (j, k) = do
>         a  <- fiat j
>         b  <- fiat k
>         return (a, b)
>     orthogonal e (a, b) = orthogonal e a && orthogonal e b

> instance Applicative Contextual where
>     pure = return
>     (<*>) = ap

> instance (Judgement j, Judgement k) => Judgement (Either j k) where
>     type Output (Either j k) = Either (Output j) (Output k)
>     fiat (Left j) = pure Left <*> fiat j
>     fiat (Right k) = pure Right <*> fiat k
>     orthogonal e = either (orthogonal e) (orthogonal e)

> data Unify = Type :==: Type
> infix 1 :==:

> data Instantiate = Name :===: (Type, Suffix)
> infix 1 :===:

> instance Judgement Unify where
>     type Output Unify = ()
>     fiat (tau    :==:   upsilon) = unify tau upsilon
>     orthogonal (delta := _) (V alpha :==: V beta) =
>         alpha /= delta && beta /= delta
>     orthogonal e (tau0 :-> tau1 :==: upsilon0 :-> upsilon1) =
>         orthogonal e (tau0 :==: upsilon0) && orthogonal e (tau1 :==: upsilon1)
>     orthogonal e (V alpha :==: tau) = orthogonal e (alpha :===: (tau, F0))
>     orthogonal e (tau :==: V alpha) = orthogonal e (alpha :===: (tau, F0))

> instance Judgement Instantiate where
>     type Output Instantiate = ()
>     fiat (alpha  :===:  (upsilon, _Xi)) = instantiate alpha _Xi upsilon
>     orthogonal (delta := _) (alpha :===: (tau, _Xi)) = not (alpha == delta) &&
>         not (delta <? tau) && not (delta <? _Xi)
>     orthogonal _ (_ :===: _) = True

> data Specialise = Specialise Scheme

> instance Judgement Specialise where
>     type Output Specialise = Type
>     fiat (Specialise sigma) = specialise sigma
>     orthogonal _ _ = False

> data Infer = Infer Term

> instance Judgement Infer where
>     type Output Infer = Type
>     fiat (Infer t) = infer t
>     orthogonal _ _ = False



> class Judgement j => Topmost j where
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

%endif

\perform{main}


\phantomsection
\addcontentsline{toc}{section}{References}
\bibliographystyle{plainnat}
\bibliography{lib}

\end{document}