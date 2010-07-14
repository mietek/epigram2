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
\newcommand{\emptycontext}{\ensuremath{\mathcal{E}}}
\newcommand{\letGoal}{\ensuremath{\fatsemi}}
\newcommand{\letIn}[3]{\ensuremath{\mathrm{let}\; #1 \!:=\! #2 \;\mathrm{in}\; #3}}
\newcommand{\letS}[3]{\ensuremath{(!#1 \!:=\! #2 ~\mathrm{in}~ #3)}}
\newcommand{\mathframe}[1]{\framebox{\ensuremath{#1}}}
\newcommand{\boxrule}[1]{\begin{center}\mathframe{#1}\end{center}}
\newcommand{\boxrules}[2]{\begin{center}\mathframe{#1}\quad\mathframe{#2}\end{center}}
\newcommand{\boxruless}[3]{\begin{center}\mathframe{#1}\quad\mathframe{#2}\quad\mathframe{#3}\end{center}}

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
\newcommand{\lep}{\ensuremath{\leq}}
\newcommand{\ppre}{\ensuremath{\subset}}

\newcommand{\arrow}{\ensuremath{\triangleright}}
\newcommand{\defn}{\ensuremath{\!:=\!}}
\newcommand{\asc}{\ensuremath{\hasc}}
\newcommand{\hasc}{\ensuremath{~\hat{::}~}}
\newcommand{\asch}{\ensuremath{\hasch}}
\newcommand{\hasch}{\ensuremath{~{::}~}}
\newcommand{\hole}[1]{\ensuremath{#1 \!:= ?}}
\newcommand{\contains}{\ensuremath{\ni}}
\newcommand{\transto}{\ensuremath{\twoheadrightarrow}}

\newcommand{\Alg}[3]{\ensuremath{#1 \transto #3 \vdash #2}}
\newcommand{\Judge}[3]{\ensuremath{#1 \lei #3 \vdash #2}}
\newcommand{\JudgeR}[3]{\ensuremath{#1 \leiR #3 \vdash #2}}
\newcommand{\Jmin}[3]{\ensuremath{#1 \LEI #3 \vdash #2}}
\newcommand{\Junify}[4]{\Alg{#1}{\Puni{#2}{#3}}{#4}}
\newcommand{\Jinstantiate}[5]{\Alg{#1 ~||~ #4}{\Puni{#2}{#3}}{#5}}
\newcommand{\Jtype}[4]{\Alg{#1}{\Pinf{#2}{#3}}{#4}}
\newcommand{\Jscheme}[4]{\Alg{#1}{\Psch{#2}{#3}}{#4}}

\newcommand{\JminR}[3]{\ensuremath{#1 \LEIR #3 \vdash #2}}

\newcommand{\InParam}[1]{(#1)}
\newcommand{\OutParam}[1]{#1}
\newcommand{\Prob}[3]{#1 \InParam{#2} \OutParam{#3}}
\newcommand{\Pinf}[2]{#1 : \OutParam{#2}}
\newcommand{\Psch}[2]{#1 \asch \OutParam{#2}}
\newcommand{\Puni}[2]{#1 \equiv #2}
\newcommand{\Pspec}[2]{\Prob{S}{#1}{#2}}

\newcommand{\name}[1]{\textsc{#1}}
\newcommand{\namer}[1]{\ensuremath{\mathrm{\name{#1}} \;}}
\newcommand{\side}[1]{\ensuremath{\; #1}}

\newcommand{\br}[2]{\genfrac{}{}{0pt}{0}{#1}{#2}}
\newcommand{\BigRule}[3]{\ensuremath{\Rule{\br{#1}{#2}}{#3}}}

% \newcommand{\sym}{\ensuremath{^\vee}}
\newcommand{\sem}[1]{\ensuremath{\llbracket #1 \rrbracket}}

\newcommand{\W}{\ensuremath{\mathcal{W}}}
\newcommand{\AlgorithmW}{Algorithm~\W}

\newcommand{\genarrow}{\ensuremath{\Uparrow}}
\newcommand{\gen}[2]{\ensuremath{(#1 \genarrow #2)}}
\newcommand{\gendot}[1]{\ensuremath{.{#1}}}
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

\newcommand{\pprec}[3]{#1 \entails #2 \ppre #3}
\newcommand{\pple}[4]{(#1, #2) \ppre (#3, #4)}
\newcommand{\pconj}[3]{\Sigma #1~#2.#3}
\newcommand{\Pmin}[4]{#1 ? #2 \LEI #4 ! #3}

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
\section{Introduction}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% \subsection{\AlgorithmW}

\AlgorithmW\ is a well-known type inference algorithm for the Hindley-Milner type
system \citep{milner_theory_1978, damas_principal_1982}, based on
\citeauthor{robinson_machine-oriented_1965}'s Unification Algorithm
\citeyearpar{robinson_machine-oriented_1965}. The system consists of
simply-typed $\lambda$-calculus with \scare{let-expressions} for polymorphic
definitions.
For example, the term
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
(section \TODO{??}).

\subsection{Motivating context}

Why revisit \AlgorithmW? This is a first step towards a longer-term objective:
explaining the elaboration of high-level \emph{dependently typed} programs into
fully explicit calculi. Elaboration involves inferring \emph{implicit arguments}
by solving constraints, just as \W\ specialises polymorphic type schemes, but
with fewer algorithmic guarantees. Pragmatically, we need to account for
stepwise progress in problem solving from states of partial knowledge.
We wish to identify local correctness criteria for type inference that
guarantee global correctness.


In contrast to other presentations of unification and Hindley-Milner type
inference, our algorithm is based on contexts carrying variable definitions as
well as declarations. This avoids having to consider substitutions, or
morphisms between contexts, explicitly.
(We do use substitution in reasoning about the system.)

This paper has been a long time brewing. Its origins lie in a constraint
engine cannibalised by McBride from an implementation of
\citeauthor{miller:mixed}'s \scare{mixed prefix}
unification~\citeyearpar{miller:mixed}, mutating the quantifier prefix into a
context. \citeauthor{mcbride:thesis}'s thesis~\citeyearpar{mcbride:thesis} gives
an early account of using typing contexts to represent the state of an
interactive construction system, the \scare{holes} in programs and proofs being 
specially designated variables. Contexts carry an information order: increase of
information preserves typing and equality judgments; proof tactics are
admissible context validity rules which increase information; unification is
specified as a tactic which increases information to make an equation hold, but
its imple-mentation is not discussed. This view of construction underpinned the
implementation of Epigram~\citep{mcbride.mckinna:view-from-the-left} and informed
\citeauthor{norell:agda}'s implementation of Agda~\citeyearpar{norell:agda}.
It is high time we began to explain how it works and perhaps to understand it.

We are grateful to an anonymous referee for pointing out the work of
\citet{dunfield_polymorphism_2009} on polymorphism in a bidirectional type system.
Dunfield uses well-founded contexts that contain existential type variables
(amongst other things). These variables can be solved, and there is an informal
notion of information increase between input and output contexts, though this is
used for different purposes. 

However, our concerns here are different: whilst Dunfield elaborates a
particular strategy for bidirectional polymorphic checking to a larger
class of type theories, we are pursuing a methodological understanding
of the problem-solving strategy in Hindley-Milner type inference.

\TODO{More crunchiness: forward pointers to claims and contributions}

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
supported by intuition.'' Experience has shown that the rules are well-chosen
indeed; perhaps we can recover the intuition.

In both cases, the occurs check is used to detect dependencies between variables.
Type variables are traditionally left floating in space and given meaning by
substitution, but by exposing structure we can manage definitions and
dependencies as we go. Recording type variables in the context is natural when
dealing with dependent types, since there is no distinction between type and term
variables. Even in a simply-typed setting, however, this approach has advantages.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Unification over a context}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We begin our study of type inference by revisiting unification for
type expressions containing free variables. Let us equip ourselves to
address the problem---solving equations---by explaining which types
are considered equal, raising the question of which things a given
context admits as types, and in turn which contexts make sense in the
first place.

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
of type variables, each of which may be unknown (written $\hole{\alpha}$) or
defined (written $\alpha \defn \tau$). A context is valid if the type in
every definition makes sense over its preceding context.
For example, the context
$\hole{\alpha}, \hole{\beta}, \gamma \defn \alpha \arrow \beta$
is valid, but the context
$\alpha \defn \beta, \hole{\beta}$
is not, because $\beta$ is not in scope for the definition of $\alpha$.
This topological sorting of the dependency graph means that 
entries on the right are harder to depend on, and correspondingly easier to
generalise just by the usual process of discharging as hypotheses.

Definitions in the context induce a nontrivial equational theory on types,
starting with $\alpha \equiv \tau$ for every definition $\alpha \defn \tau$ in
the context, then taking the congruence closure.
Unification is the problem of making variable definitions (increasing
information) to solve an equation.
The idea is that we decompose constraints on the syntactic structure of types
until we reach variables, then move through the context and update it to solve
the equation. 

For example, we might start in the context
$\hole{\alpha}, \hole{\beta}, \gamma \defn \alpha \arrow \beta$
and aim to solve the equation $\beta \arrow \alpha \equiv \gamma$.
%
% The definition of $\gamma$ tells us that we must
% solve $\beta \arrow \alpha \equiv \alpha \arrow \beta$ over the context
% $\hole{\alpha}, \hole{\beta}$. This constraint decomposes to
% $\beta \equiv \alpha$ and $\alpha \equiv \beta$, which are easily solved by
% defining $\beta \defn \alpha$, giving the final judgment
%
It suffices to define $\beta \defn \alpha$, giving the final judgment
$$\hole{\alpha}, \beta \defn \alpha, \gamma \defn \alpha \arrow \beta
    \entails \beta \arrow \alpha \equiv \gamma.$$

A context thus contains a `triangular substitution', applied on
demand, but that need not be all. As we proceed with the development,
the context structure will evolve to hold a variety of information
about variables of all sorts and some control markers, managing the
generalisation process.

\TODO{Relate contexts to traditional substitutions (triangular);
compare with Baader and Snyder.}


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

A Haskell implementation of our unification algorithm is given in
Figure~\ref{fig:unifyCode}.
\citet{NaraschewskiN-JAR} formally proved correctness of \AlgorithmW\ in
Isabelle/HOL using a counter for fresh variable generation and a monad to
silently propagate failure; we use similar techniques here.

Figure~\ref{subfig:typeCode} implements types as a foldable functor
parameterised by the type of variable names. Thanks to a language
extension in GHC 6.12 \citep{ghc_team_glorious_2009} we can simply
derive the required typeclass instances.
For simplicity, we use integers as names.
We can find free type variables using the typeclass |FTV| with membership
function |(<?)|. We get most of the required instances for free using |Foldable|.

Figure~\ref{subfig:contextCode} defines context entries, contexts and suffixes.
The types |Bwd| and |Fwd|, whose definitions are omitted, are backwards and forwards lists
with |B0| for both empty lists and |:<| and |:>| for snoc and cons respectively.
Lists are monoids with the append operator |<+>|, and the \scare{fish}
operator |(<><)| appends a suffix to a context. We will later extend |Entry| to
handle term variables, so this definition is incomplete.

Figure~\ref{subfig:monadCode} defines the |Contextual| monad of computations that
can fail and mutate the context. The |TyName| component is the next fresh type
variable name to use; it is an implementation detail not mentioned in the typing
rules. The |fresh| function generates a fresh variable name and appends a
declaration to the context. Our choice of |TyName| means that it is easy to
choose a name fresh with respect to a |Context|.

Figure~\ref{subfig:onTopCode} implements |onTop|, which delivers the
typical access pattern for contexts, locally bringing the top variable
declaration into focus and working over the remainder.  The local
operation, passed as an argument, may |restore| the previous entry, or
it may return a context extension (containing at least as much
information as the entry that has been removed) with which to
|replace| it.

Figure~\ref{subfig:unifyCode} gives the actual implementations of unification
and solution. Unification proceeds structurally over types. If it reaches a pair
of variables, it examines the context, using the |onTop| operator to pick out
a type variable declaration to consider. Depending on the variables, it will
then either succeed (by restoring the old entry or replacing it with a new one)
or continue unifying with an updated contraint.

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
\section{Modelling statements-in-context}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Having seen an implementation of unification, let us try to understand it.
We would like to give a general picture of \scare{statements-in-context} which
allows us to view unification and type inference in a uniform setting.
What is the common structure?

A \define{context} is a list of \define{declarations} assigning
\define{properties} to
variables (here, in particular, type variables). 
The empty context is written $\emptycontext$ and we let
$\Gamma, \Delta, \Theta$ range over contexts.
Let $\V_\TY$ be a set of type
variables and $\D_\TY$ the properties that may be given to them
(the \scare{unknown variable} property $~\hole{}$ and \scare{defined variable}
properties $~\defn{\tau}$ for each type $\tau$).

Later we will introduce corresponding definitions for term variables. Where
necessary we let $K \in \{ \TY, \TM \}$ represent an arbitrary sort of variable.
We write $\decl{x}{D}$ for an arbitrary property, where $x \in \V_K$ and
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
Note that $\valid$ and $\wedge$ give a unit and product for statements.

A statement has zero or more
\define{parameters}, each of which has an associated \define{sanity condition}, 
i.e.\ a statement whose truth is presupposed for the problem to make sense.
The $\valid$ statement has no parameter and hence no sanity conditions.
In $\tau \type$, the parameter $\tau$ has sanity condition $\valid$.
The type equivalence statement $\tau \equiv \upsilon$ has two parameters; the
sanity conditions are $\tau \type$ and $\upsilon \type$ respectively.
Finally, $S \wedge S'$ has parameters (and sanity conditions) taken from $S$ and
$S'$.

Each declaration in the context causes some statement to hold.
We maintain a map $\sem{\cdot}_K : \V_K \times \D_K \rightarrow \Ss$
from declarations to statements. (Typically we will omit the subscript $K$.)
The idea is that $\sem{\decl{x}{D}}$ is the statement that holds by virtue of the
declaration $\decl{x}{D}$ in the context. For type variables, we define
\begin{align*}
\sem{\hole{\alpha}} &= \alpha \type \\
\sem{\alpha \defn \tau} &= \alpha \type \wedge \alpha \equiv \tau.
\end{align*}

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
to declarations in the context are atoms of derivations.

We embed neutral into normal:
$$\namer{Neutral}
  \Rule{\entailsN S}
       {\entails S}.$$

The \name{Lookup} rule is our only means to extract information from the
context, so we will omit the contextual plumbing (almost) everywhere else.

\subsection{Validity of contexts}

It is not enough for contexts to be lists of declarations: they must
be well-founded, that is, each declaration should make sense in
\emph{its} context.  A context is valid if it declares each variable
at most once, and each property is meaningful in the
preceding context.

Accordingly, 
we maintain a map $\ok_K : \D_K \rightarrow \Ss$ for every $K \in \K$, which 
embeds properties in statements. For type properties:
\begin{align*}
\ok_\TY (\hole{}) &= \valid \\
\ok_\TY (\defn{\tau}) &= \tau \type
\end{align*}
Now we can define the context validity statement
$\valid$ as shown in Figure~\ref{fig:contextValidityRules}.
From now on we will implicitly assume that all contexts we work with are valid,
and will ensure that we only construct valid contexts. Mostly we will ignore the
issue of fresh names, since our simple counter implementation suffices for most
purposes.

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

\TODO{Relate to traditional presentation - give intuition.}


\subsection{Rules for establishing statements}

\TODO{Fix rule box sizes.}

\begin{figure}[ht]
\boxruless{\tau \type}{\tau \equiv \upsilon}{S \wedge S'}
$$
\Rule{\tau \type   \quad   \upsilon \type}
     {\tau \arrow \upsilon \type}
\qquad
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
$$\Rule{S \quad S'} {S \wedge S'}
  \qquad
  \Rule{\entailsN S \wedge S'}
       {\entailsN S}
  \qquad
  \Rule{\entailsN S \wedge S'}
       {\entailsN S'}
$$
\caption{Rules for types, equivalence and conjunction}
\label{fig:statementRules}
\end{figure}

Figure~\ref{fig:statementRules} gives rules for establishing statements other than
$\valid$.
We deduce that variables are types by looking up the context, but we need
a structural rule for the $\arrow$ type constructor.

The conjunction of statements $S \wedge S'$ allows us to package multiple facts
about a single variable, with a normal introduction rule (pairing) and neutral
elimination rules (projections).
This is but one instance of a general pattern: we add \emph{normal} introduction
forms for composite statements, but supply
eliminators only for statements which ultimately rest on (composite) hypotheses,
obtained by \name{Lookup}. This forces
derivations to be cut-free, facilitating reasoning by induction on
derivations.
If we added the corresponding projections for \emph{normal} judgments, we
would lose the hope of a syntax-directed rule system. In any case, we shall
ensure that the corresponding elimination rules are admissible. This is clearly
the case for conjunction.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Information and stable statements}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\subsection{Information order}

The transition from $\hole{\alpha}$ to $\alpha \defn \tau$ intuitively cannot
falsify existing equations.
More generally, if we rely on the context to tell us what we may
deduce about variables, then making contexts more informative must preserve
deductions. 

Let $\Gamma$ and $\Delta$ be contexts.
A \define{substitution from $\Gamma$ to $\Delta$} is a map from
$\tyvars{\Gamma}$ to $\{ \tau ~||~ \Delta \entails \tau \type \}$.
We could substitute for term variables as well, and give a more general
definition, but omit this for simplicity.
Substitutions apply to types and statements in the usual way.
Composition of substitutions is given by
$(\theta \compose \delta) (\alpha) = \theta (\delta \alpha)$.
We write $\subst{\tau}{\alpha}{}$ for the substitution that maps
$\alpha$ to $\tau$ and other variables to themselves.

Given a substitution $\delta$ from $\Gamma$ to $\Delta$, 
we write the \define{information increase} 
   relation 
$\delta : \Gamma \lei \Delta$ and say 
\define{$\Delta$ is more informative than $\Gamma$} if 
for all $\decl{x}{D} \in \Gamma$, we have 
$\Delta \entails \delta \sem{\decl{x}{D}}$. 
That is, $\Delta$ supports all the statements corresponding to declarations
in $\Gamma$.
We write $\Gamma \lei \Delta$ if 
$\iota : \Gamma \lei \Delta$, where  $\iota$ is the identity substitution.

\TODO{Can we call $\lei$ a relation if we do this?}

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

This partial order on contexts is sufficient to ensure stability, as described
in the following section, but in practice the algorithm will work with a more structured
subrelation of $\lei$. We give up more freedom to achieve a more comprehensible
algorithm. For example, our algorithm will always use the identity substitution.



\subsection{Stability}

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
\begin{proof}
By structural induction on derivations. If the proof is by \name{Lookup}, then
the result holds by definition of information increase. Otherwise, the proof is
by a neutral elimination rule, so the result follows by induction and
admissibility of the corresponding normal elimination rule.
\end{proof}

We have a standard strategy for proving stability of most statements, which is
effective by construction. In each case we proceed by induction on the structure
of derivations. Where the \name{Neutral} rule is applied, stability holds by 
Lemma~\ref{lem:neutrality}. Otherwise, we verify that non-recursive hypotheses
are stable and that recursive hypotheses occur in strictly positive positions,
so they are stable by induction. Applying this strategy shows that both 
$\tau \type$ and $\tau \equiv \upsilon$ are stable.

\begin{lemma}[Conjunction preserves stability]\label{lem:stab-pres-conj}
If $S$ and $S'$ are stable then $S \wedge S'$ is stable.
\end{lemma}
\begin{proof}
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
\begin{proof}
Reflexivity follows immediately by applying the \name{Lookup} and
\name{Neutral} rules.
For transitivity, suppose $\decl{x}{D} \in \Gamma$,
then $\Delta \entails \delta \sem{\decl{x}{D}}$ since
$\delta : \Gamma \lei \Delta$.
Now by stability applied to $\delta \sem{\decl{x}{D}}$ using $\theta$, we have
$\Theta \entails \theta\delta \sem{\decl{x}{D}}$ as required.
\end{proof}

\TODO{How do we use the following lemma?}
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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Constraints: problems at ground mode}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We define a \define{constraint problem} to be a pair of a context $\Gamma$ and a statement
$S$, where
the sanity conditions on the parameters of $S$ hold in $\Gamma$, but $S$ itself
may not. A \define{solution} to such a problem is then an information increase 
$\delta : \Gamma \lei \Delta$ such that
$\Delta \entails \delta S$. 
   In this setting, the \define{unification} problem \((\Gamma, \tau \equiv \upsilon)\) 
%%%is given $\Gamma$, $\tau$ and $\upsilon$ such that
   stipulates that 
$\Gamma \entails \tau \type \wedge \upsilon \type$, and 
   a solution to the problem ( a \define{unifier}) is given by 
%%%must find 
$\delta : \Gamma \lei \Delta$ such that
$\Delta \entails \delta \tau \equiv \delta \upsilon$.

We are interested in finding algorithms to solve problems, preferably in as
general a way as possible (that is, by making the smallest information increase
necessary to find a solution). 
   For the unification problem, this 
corresponds to finding a most general
unifier. The solution $\delta : \Gamma \lei \Delta$ is \define{minimal} if, for
any other solution $\theta: \Gamma \lei \Theta$, there exists a
substitution $\zeta : \Delta \lei \Theta$ such that
$\theta \eqsubst \zeta \compose \delta$ (we say $\theta$ \emph{factors through}
$\delta$ with \emph{cofactor} $\zeta$).

In fact, we will always find minimal solutions 
%%%that use the identity substitution. 
   in the form $\iota : \Gamma \lei \Delta$. 
We write $\Jmin{\Gamma}{P}{\Delta}$ to mean that $(\Gamma, P)$ is a
problem with minimal solution $\iota : \Gamma \lei \Delta$.

As one might expect, the rule
$$\Rule{\Judge{\Gamma}{P}{\Delta}
       \quad  \Judge{\Delta}{Q}{\Theta}}
       {\Judge{\Gamma}{P \wedge Q}{\Theta}}$$
is admissible, since stability ensures that if $\Delta$ solves $P$ then any more
informative context $\theta$ will also solve $P$. More surprisingly, this also
gives minimal solutions to composite problems, allowing a \scare{greedy} 
solution strategy.
%
% We can now state the following \scare{greedy} approach to finding minimal
% solutions to such composite problems: find a minimal solution of problem $P$,
% then extend it to (minimally) solve $Q$:
%
\begin{lemma}[The Optimist's lemma]
\label{lem:optimist}
The following inference rule is admissible:
$$\Rule{\Jmin{\Gamma}{P}{\Delta}
       \quad  \Jmin{\Delta}{Q}{\Theta}}
       {\Jmin{\Gamma}{P \wedge Q}{\Theta}}.$$
\end{lemma}

\begin{proof}[Sketch]
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
\section{The unification algorithm, formally}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We now present the algorithm formally. The structural rule means that
whenever we have rigid $\arrow$ symbols on each side, we decompose the problem
into two subproblems, and thanks to the Optimist's Lemma we can solve these
sequentially. Otherwise, we either have variables on both sides, or a variable
on one side and a type on the other. In each case, we look at the next type
variable in the context to see what information it gives us, and either solve
the problem or update our constraint and continue processing the context.
When solving a variable with a type, we need to accumulate
the type's dependencies as we encounter them, performing the occurs check to
ensure a solution exists.

The rules in Figure~\ref{fig:unifyRules} define our unification algorithm. The
judgment $\Junify{\Gamma}{\tau}{\upsilon}{\Delta}$ means that given inputs
$\Gamma$, $\tau$ and $\upsilon$, unification succeeds and produces output
context $\Delta$. This is subject to the input sanity condition
$\Gamma \entails \tau \type \wedge \upsilon \type$.

The judgment
$\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$
means that given inputs $\Gamma$, $\Xi$, $\alpha$ and $\tau$,
solving $\alpha$ with $\tau$ succeeds,  
yielding output context $\Delta$. The idea is that the bar ($||$) represents
%%%progress through the context, 
   progress in examining context elements in order, 
%%%and $\Xi$ contains dependencies of $\tau$ (which
%%%must be placed before $\tau$ for it to be well-defined). 
   and $\Xi$ contains exactly those declarations on which $\tau$ depends.  
Formally, the inputs 
must satisfy
\begin{itemize}
\item $\alpha \in \tyvars{\Gamma}$,
\item $\tau$ is not a variable,
\item $\Gamma, \Xi \entails \tau \type$,
\item $\Xi$ contains only type variable declarations and
\item $\beta \in \tyvars{\Xi} \Rightarrow \beta \in \FTV{\tau, \Xi}$.
\end{itemize}

By inspecting the rules, we observe that each rule preserves correct and minimal
solutions (using the Optimist's Lemma for the \name{Decompose} rule), so we
obtain the following lemma.

\begin{lemma}[Soundness and generality of unification]
\label{lem:unifySound}
\begin{enumerate}[(a)]
\item If $\Junify{\Gamma}{\tau}{\upsilon}{\Delta}$, then
$\tyvars{\Gamma} = \tyvars{\Delta}$ and
$\Jmin{\Gamma}{\tau \equiv \upsilon}{\Delta}$.

\item If
$\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$, then
$\tyvars{\Gamma, \Xi} = \tyvars{\Delta}$ and
$\Jmin{\Gamma, \Xi}{\tau \equiv \upsilon}{\Delta}$.
\end{enumerate}
\end{lemma}
\begin{proof}
By induction on the structure of derivations.
For each rule, we verify that it preserves the set of type variables and
that $\Gamma \lei \Delta$.

To show minimality, it suffices to assume there is some
$\theta : \Gamma \lei \Theta$ such that
$\Theta \entails \theta\tau \equiv \theta\upsilon$, and show
$\theta : \Delta \lei \Theta$. As the type variables of $\Gamma$ are
the same as $\Delta$, we simply note that definitions in $\Delta$ hold as
equations in $\Theta$ for each rule that rewrites or solves the problem.

The only rule not in this form is \name{Decompose}, but solutions to
$\tau_0 \arrow \tau_1 \equiv \upsilon_0 \arrow \upsilon_1$ are exactly those
that solve $\tau_0 \equiv \upsilon_0 \wedge \tau_1 \equiv \upsilon_1$,
so it gives a minimal solution by the Optimist's lemma.

\TODO{Do we need to say more about part (b)? Should we comment somewhere about
keeping things right not being necessary for generality at the moment, but
arising later?}
\end{proof}


Some context entries have no bearing on the unification problem being solved,
so they can be ignored.
We define the orthogonality relation $x \perp X$ (the variable $x$ is
independent of the set of type variables $X$) 
to capture this idea: 
\begin{align*}
\alpha \perp X &\mathrm{~if~} \alpha \in \V_\TY \setminus X  \\
x      \perp X &\mathrm{~if~} x \in \V_\TM
\end{align*}

The rules \name{Define} and \name{Expand} have
symmetric counterparts, identical apart from interchanging the equated
terms in the conclusion. Usually we will ignore these without loss of generality.

\begin{figure}[ht]
\boxrule{\Junify{\Gamma}{\tau}{\upsilon}{\Delta}}

$$
\namer{Decompose}
\Rule{\Junify{\Gamma}{\tau_0}{\upsilon_0}{\Delta_0}
      \quad
      \Junify{\Delta_0}{\tau_1}{\upsilon_1}{\Delta}}
    {\Junify{\Gamma}{\tau_0 \arrow \tau_1}{\upsilon_0 \arrow \upsilon_1}{\Delta}}
$$

$$
\namer{Idle}
% \Rule{\Gamma \entails \alpha \type}
\Axiom{\Junify{\Gamma_0, \alpha D}{\alpha}{\alpha}{\Gamma_0, \alpha D}}
$$

$$
\namer{Define}
%\Rule{\Gamma_0 \entails \beta \type}
\Axiom{\Junify{\Gamma_0, \hole{\alpha}}{\alpha}{\beta}{\Gamma_0, \alpha \defn \beta}}
\side{\alpha \neq \beta}
$$

$$
\namer{Ignore}
\Rule{\Junify{\Gamma_0}{\alpha}{\beta}{\Delta_0}}
     {\Junify{\Gamma_0, \decl{x}{D}}{\alpha}{\beta}{\Delta_0, \decl{x}{D}}}
\side{x \perp \{\alpha, \beta\} }
$$

$$
\namer{Expand}
\Rule{\Junify{\Gamma_0}{\tau}{\beta}{\Delta_0}}
     {\Junify{\Gamma_0, \alpha \defn \tau}{\alpha}{\beta}{\Delta_0, \alpha \defn \tau}}
\side{\alpha \neq \beta}
$$

$$
\namer{Solve}
\Rule{\Jinstantiate{\Gamma}{\alpha}{\tau}{\emptycontext}{\Delta}}
     {\Junify{\Gamma}{\alpha}{\tau}{\Delta}}
%% \side{\tau \neq \alpha}
\side{\tau \mathrm{~not~variable}}
$$

\bigskip

\boxrule{\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}}

$$
\namer{DefineS}
% \Rule{\Gamma_0, \Xi \entails \tau \type}
\Axiom{\Jinstantiate{\Gamma_0, \hole{\alpha}}{\alpha}{\tau}{\Xi}
                   {\Gamma_0, \Xi, \alpha \defn \tau}}
\side{\alpha \notin \FTV{\tau, \Xi}}
$$

$$
\namer{IgnoreS}
\Rule{\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\Xi}{\Delta_0}}
     {\Jinstantiate{\Gamma_0, \decl{x}{D}}{\alpha}{\tau}{\Xi}{\Delta_0, \decl{x}{D}}}
\side{x \perp \FTV{\alpha, \tau, \Xi}}
$$

$$
\namer{ExpandS}
\Rule{\Junify{\Gamma_0, \Xi}{\upsilon}{\tau}{\Delta_0}}
     {\Jinstantiate{\Gamma_0, \alpha \defn \upsilon}{\alpha}{\tau}{\Xi}
                   {\Delta_0, \alpha \defn \upsilon}}
\side{\alpha \notin \FTV{\tau, \Xi}}
$$

$$
\namer{DependS}
\Rule{\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\beta D, \Xi}{\Delta}}
     {\Jinstantiate{\Gamma_0, \beta D}{\alpha}{\tau}{\Xi}{\Delta}}
\side{\alpha \neq \beta, \beta \in \FTV{\tau, \Xi}}
$$

\caption{Algorithmic rules for unification}
\label{fig:unifyRules}
\end{figure}

Observe that we have no rule in the situation where 
$$\Jinstantiate{\Gamma_0, \alpha D}{\alpha}{\tau}{\Xi}{\Delta}
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
$\alpha \in \FTV{\tau}$. There is no context $\Gamma$ and substitution
$\theta$ such that $\Gamma \entails \theta\alpha \equiv \theta\tau$ or
$\Gamma \entails \theta\tau \equiv \theta\alpha$.
\end{lemma}
\begin{proof}
Suppose otherwise, and let $\Gamma$ and $\theta$ be such that the proof of
$\Gamma \entails \theta\alpha \equiv \theta\tau$ or
$\Gamma \entails \theta\tau \equiv \theta\alpha$ is minimal.

Since $\alpha$ is a variable but $\tau$ is not, neither reflexivity nor the
structural rule apply. Symmetry does not apply because its hypothesis requires
a proof that cannot exist by minimality. \TODO{Why not transitivity?}

By the well-formedness conditions for contexts, if
$\alpha \defn \upsilon \in \Gamma$ then $\alpha \notin \FTV{\upsilon}$, so
the proof is not neutral (using \name{Lookup}).
\end{proof}


\begin{lemma}[Completeness of unification]
\label{lem:unifyComplete}
\begin{enumerate}[(a)]
\item If $\theta : \Gamma \lei \Theta$,
$\Gamma \entails \upsilon \type \wedge \tau \type$ and
$\Theta \entails \theta\upsilon \equiv \theta\tau$, then
there is some context $\Delta$ such that
$\Junify{\Gamma}{\upsilon}{\tau}{\Delta}$.

% with
% $\theta : \Delta \lei \Theta$. That is, if a unifier for $\tau$ and $\upsilon$
% exists, then the algorithm succeeds and delivers a most general unifier.

\item Moreover, if $\theta : \Gamma, \Xi \lei \Theta$ is such that
$\Theta \entails \theta\alpha \equiv \theta\tau$ and
the input conditions are satisfied,
then there is some context $\Delta$ such that
$\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$.
\end{enumerate}
\end{lemma}

\begin{proof}
It suffices to show that the algorithm succeeds for every well-formed input in
which a solution can exist. We proceed by induction on the call graph; since the
algorithm terminates, this is well-founded. Each step preserves solutions
(i.e.\ if there is a solution to the equation in the conclusion then there is a
solution to the equations in the hypothesis).

The only case not covered by the rules is the case where an illegal occurrence
of a type variable is detected. In this case, we are seeking to solve the
problem $\alpha \equiv \tau$ in the context
$\Gamma_0, \decl{\alpha}{D} ~||~ \Xi$ and we have $\alpha \in \FTV{\tau, \Xi}$.
Substituting out the definitions in $\Xi$ from $\tau$, we obtain a type
$\upsilon$ such that $\alpha \in \FTV{\upsilon}$, $\upsilon$ is not a variable
and $\Gamma_0, \decl{\alpha}{D}, \Xi \entails \upsilon \equiv \tau$.
Now the problem $\alpha \equiv \upsilon$ has the same solutions as
$\alpha \equiv \tau$, but by Lemma~\ref{lem:occursCheck} it has no solutions.

\TODO{Is this enough?}
\end{proof}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Specifying Type Inference}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We aim to implement type inference for the Hindley-Milner system, so we need to
introduce type schemes and the term language. We extend the grammar of statements
to express additions to the context (binding statements), well-formed schemes,
type assignment and scheme assignment. The final grammar will be:
\begin{align*}S ::=~ \valid
    &~||~ \tau \type
    ~||~ \tau \equiv \upsilon
    ~||~ S \wedge S \\
    &~||~ \Sbind{\decl{x}{D}}{S}
    ~||~ \sigma \scheme
    ~||~ t : \tau
    ~||~ s \hasscheme \sigma
\end{align*}

\subsection{Binding statements}

To give rules for schemes and type assignment, we need the ability to add
variables to the context in a controlled way.
If $S$ is a statement and $\decl{x}{D}$ is a declaration, then we define the
binding statement $\Sbind{\decl{x}{D}}{S}$ with the introduction rule
$$
\Rule{\Gamma \entails \ok_K D    \quad    \Gamma, \decl{y}{D} \entails \subst{y}{x} S}
     {\Gamma \entails \Sbind{\decl{x}{D}}{S}}
\side{y \in \V_K \setminus \V_K(\Gamma)}.
$$
and neutral elimination rule
$$
\Rule{\entailsN \Sbind{\alpha D}{S}
      \quad
      \entails \subst{\tau}{\alpha}{\sem{\decl{\alpha}{D}}}}
     {\entailsN \subst{\tau}{\alpha}{S}}
\side{D \in \D_\TY}
.$$
\TODO{Explain why we only have this for $\TY$.}
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
\begin{proof}
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
and so $\Delta \entails \delta \Sbind{\decl{x}{D}}{S}$.
\end{proof}

We write $\Sbind{\Xi}{S}$ where $\Xi$ is a list of declarations, defining
$\Sbind{\emptycontext}{S} = S$ and
$\Sbind{(\Xi, \decl{x}{D})}{S} = \Sbind{\Xi}{\Sbind{\decl{x}{D}}{S}}$.

\TODO{Sanity conditions for binding statements?}

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
\begin{align*}
\emptycontext         &\genarrow \tau = \gendot{\tau}  \\
\hole{\alpha}, \Xi    &\genarrow \tau = \forall\alpha~\gen{\Xi}{\tau}  \\
\alpha \defn \upsilon, \Xi &\genarrow \tau = \letS{\alpha}{\upsilon}{\gen{\Xi}{\tau}}
\end{align*}

The statement $\sigma \scheme$ is then defined by
$$\gen{\Xi}{\tau} \scheme = \Sbind{\Xi}{\tau \type}.$$
The sanity condition is just $\valid$, as for $\tau \type$.

\subsection{Terms and type assignment}

Now we are in a position to reuse the framework already
introduced, by defining the sort $\TM$.
Let $\V_\TM$ be some set of term variables and let $x$ range over $\V_\TM$.
Term variable declarations $\D_\TM$ are scheme assignments of the form
$\asc \sigma$, with
$\ok_\TM (\asc \sigma) = \sigma \scheme$.

% Let $\Term$ be the set of terms, with syntax 
The set of terms has syntax
$$t ::= x ~||~ t~t ~||~ \lambda x . t ~||~ \letIn{x}{t}{t}$$
and $s$, $t$, $w$ range over terms.

The type assignment statement $t : \tau$ is established by the declarative
rules in Figure~\ref{fig:typeAssignmentRules}. It has two parameters $t$ and
$\tau$ with sanity conditions $\valid$ and $\tau \type$ respectively.
We define
$$t \hasscheme \gen{\Xi}{\tau} = \Sbind{\Xi}{t : \tau}$$
and observe this gives the parameters $t$ and $\sigma$ sanity conditions
$\valid$ and $\sigma \scheme$ as one might expect.
We can interpret term variable declarations as scheme assignment statements:
$$\sem{x \asc \sigma}_\TM = x \hasscheme \sigma.$$

\begin{figure}[ht]
\boxrule{t : \tau}

$$
\Rule{\Sbind{x \asc \gendot{\upsilon}}{t : \tau}}
     {\lambda x.t : \upsilon \arrow \tau}
\qquad
\Rule{f : \upsilon \arrow \tau
      \quad
      a : \upsilon}
     {f a : \tau}
$$

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Generalisation by Localization}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\subsection{Preserving order in the context}

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
Let $\semidrop$ be the partial function from contexts and natural numbers to
contexts taking $\Gamma \semidrop n$ to $\Gamma$ truncated after $n$
$\fatsemi$ separators, provided $\Gamma$ contains at least $n$ such: 
\begin{align*}
\Xi \semidrop 0 &= \Xi  \\
\Xi \fatsemi \Gamma \semidrop 0 &= \Xi  \\
\Xi \fatsemi \Gamma \semidrop n+1 &= \Xi \fatsemi (\Gamma \semidrop n)  \\
\Xi \semidrop n+1 &~\mathrm{undefined}
\end{align*}

We write $\delta : \Gamma \lei \Delta$ if $\delta$ is a
substitution from $\Gamma$ to $\Delta$ such that, for all 
$\decl{x}{D} \in \Gamma \semidrop n$, we have that
$\Delta \semidrop n$ is defined and 
$\Delta \semidrop n \entails \delta \sem{\decl{x}{D}}$.

This definition of $\Gamma \lei \Delta$ is stronger than the previous one, 
because it requires the $\fatsemi$-separated sections of $\Gamma$ and $\Delta$ 
to correspond in such a way that 
declarations in the first $n$ sections of
$\Gamma$ can be interpreted over the first $n$ sections of $\Delta$.
However, it is fairly straightforward to verify that the previous results 
hold for the new definition.

Note that if $\delta : \Gamma \fatsemi \Gamma' \lei \Delta \fatsemi \Delta'$,
where $\Gamma$ and $\Delta$ contain the same number of $\fatsemi$ separators,
then $\delta||_{\tyvars{\Gamma}} : \Gamma \lei \Delta$.
\TODO{Is this what we want for the generalist's lemma?}


\subsection{Fixing the unification algorithm}

The only place where changing the $\lei$ relation requires extra work is in the
unification algorithm,
because it acts structurally over the context, so we need to specify what happens
when it finds a $\fatsemi$ separator. 
In fact it suffices to add the following algorithmic rules:
$$
\namer{Skip}
\Rule{\Junify{\Gamma_0}{\alpha}{\beta}{\Delta_0}}
     {\Junify{\Gamma_0 \fatsemi}{\alpha}{\beta}{\Delta_0 \fatsemi}}
$$
$$
\namer{Repossess}
\Rule{\Jinstantiate{\Gamma_0}{\alpha}{\tau}{\Xi}{\Delta_0}}
     {\Jinstantiate{\Gamma_0 \fatsemi}{\alpha}{\tau}{\Xi}{\Delta_0 \fatsemi}}
$$
Proving correctness of the \name{Skip} rule is relatively straightforward,
thanks to the following lemma.

\begin{lemma}
\TODO{Update this.}
If $\delta : \Jmin{\Gamma}{\Prob{P}{a}{b}}{\Delta}$ then
$\delta : \Jmin{\Gamma \fatsemi}{\Prob{P}{a}{b}}{\Delta \fatsemi}$.
\end{lemma}

The \name{Repossess} rule is so named because it moves
declarations in $\Xi$ to the left of the $\fatsemi$ separator,
thereby \scare{repossessing} them. Despite such complications, 
unification still yields a most general solution:

\begin{lemma}[Soundness and generality of \name{Repossess} rule]
\TODO{Update this.}
If $\Jinstantiate{\Gamma \fatsemi}{\alpha}{\tau}{\Xi}{\Delta \fatsemi}$
then $\tyvars{\Gamma \fatsemi \Xi} = \tyvars{\Delta \fatsemi}$ and
$\iota : \Jmin{\Gamma \fatsemi \Xi}{\Puni{\alpha}{\tau}}{\Delta \fatsemi}$.
\end{lemma}
\begin{proof}
Suppose $\Jinstantiate{\Gamma \fatsemi}{\alpha}{\tau}{\Xi}{\Delta \fatsemi}$,
so $\Jinstantiate{\Gamma}{\alpha}{\tau}{\Xi}{\Delta}$ as only the
\name{Repossess} rule applies.
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




\begin{lemma}[The Generalist's lemma]
\label{lem:generalist}
$$
\Rule{\Jmin{\Gamma \fatsemi}{t : \tau}{\Delta \fatsemi \Xi}}
     {\Jmin{\Gamma \fatsemi}{t :: \gen{\Xi}{\tau}}{\Delta}}
$$
\end{lemma}
\begin{proof}
\TODO{Prove this.}
\end{proof}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Type Inference Problems and Solutions}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\subsection{Inference problems: multiple-mode }

\TODO{Tidy up and improve motivation for definitions in this section.}

Type inference involves making the statement $t : \tau$ hold. However,
a crucial difference from the unification problem is that the type should
be an \emph{output} of problem-solving, along with the solution context. We need
a more liberal definition than that of constraint problems.

We associate a \define{mode} with each parameter in a statement: either
\scare{input} or \scare{output}. For simplicity, assume statements always have
one parameter of each mode (which may be unit or a product).
% An
% \define{inference problem}
% is a triple $(\Gamma, S, Q)$ where $\Gamma$ is a context, $S$ is a statement
% \TODO{(?)} and
% $Q$ is a value for the input parameter that satisfies its sanity condition in
% $\Gamma$.
% \TODO{Clarify notation for statements and parameter values. What is $Q A$?}

Let $I$ be a set of inputs closed under substitution. For a fixed context
$\Gamma$, suppose we have a
preorder $\ppre$ on $I$ written $\pprec{\Gamma}{\cdot}{\cdot}$. This induces a
preorder on context-input pairs, with $\delta : \pple{\Gamma}{a}{\Delta}{b}$ if
$\delta : \Gamma \lei \Delta$ and $\pprec{\Delta}{\delta a}{b}$.

An \define{$I$-indexed problem family} $x.Q$ with solutions in $J$ is a family
of input values for a
statement, indexed by elements of $I$, such that for all $a, a' \in I$, contexts
$\Gamma$ and output values $b \in J$,
$$\pprec{\Gamma}{a}{a'} ~\wedge~ \Gamma \entails Q[a'] b
    \quad\Rightarrow\quad  \Gamma \entails Q[a] b,$$
where we write $Q[a] b$ for the statement with input at index $a$ and output
value $b$.

An \define{inference problem} consists of a context $\Gamma$, an
$I$-indexed problem $Q$ and an index $a \in I$ such that the sanity condition of $Q[a]$
holds in $\Gamma$.

A \define{solution} of $(\Gamma, Q[a])$ consists of an information increase
$\delta : \Gamma \lei \Delta$ and a value for the output parameter $b \in J$
such that $(\delta (Q[a])) b$ and the sanity condition on $b$ hold in $\Delta$.

The conjunction of problems $\pconj{P}{x}{Q}$ generalises $P \wedge Q$ and allows
the output of $P$ to be used in the input of $Q$; in this way it resembles a
dependent sum type. We define
$(\pconj{P}{x}{Q}) (a, b) = P a \wedge Q[a] b$.
We compare solutions pointwise, so define $\pprec{\Gamma}{(a, b)}{(a', b')}$ to
mean $\pprec{\Gamma}{a}{a'}$ and $\pprec{\Gamma}{b}{b'}$.

We write $\Pmin{\Gamma}{P}{a}{\Delta}$ if
$\Gamma \lei \Delta \entails (\delta P) a$,
and for all $\theta : \Gamma \lei \Theta$ and $b$ such that
$\Delta \entails (\theta P) b$, we have
$\zeta : \pple{\Delta}{a}{\Theta}{b}$ for some $\zeta$ such that
$\theta \eqsubst \zeta \compose \iota$.

This allows us to state the fully general version of
the Optimist's lemma:

\begin{lemma}[The Optimist's lemma for inference problems]
\label{lem:optimistInference}
The following inference rule is admissible:
$$\Rule{\Pmin{\Gamma}{P}{b}{\Delta}
       \quad  \Pmin{\Delta}{Q[b]}{c}{\Theta}}
       {\Pmin{\Gamma}{(\pconj{P}{x}{Q})}{(b, c)}{\Theta}}.$$
\end{lemma}
\begin{proof}
We have $\Gamma \lei \Theta$ by Lemma~\ref{lei:preorder}.
Furthermore, $\Theta \entails (\pconj{P}{x}{Q}) (b, c)$ since
stability gives $\Theta \entails P b$, and
$\Theta \entails Q[b] c$ by assumption.

Now suppose there is some other solution
$(\phi : \Gamma \lei \Phi, (b', c'))$, so
$\Phi \entails (\phi P) b'$ and
$\Phi \entails (\phi Q)[b'] c'$.
Since $\Pmin{\Gamma}{P}{b}{\Delta}$, there exists
$\zeta : \Delta \lei \Phi$
with $\pprec{\Phi}{\zeta b}{b'}$ and $\phi \eqsubst \zeta \compose \iota$.

By definition of an indexed problem family,
$\Phi \entails (\phi Q)[\zeta b] c'$
and hence $\Phi \entails (\zeta (Q[b])) c'$.
But $\Pmin{\Delta}{Q[b]}{c}{\Theta}$, so there exists
$\xi : \Theta \lei \Phi$ such that $\pprec{\Phi}{\xi c}{c'}$
and $\zeta \eqsubst \xi \compose \iota$.

Hence $\xi : \Theta \lei \Phi$ and $\pprec{\Phi}{\xi (b, c)}{(b', c')}$
so $\xi : \pple{\Theta}{(b, c)}{\Phi}{(b', c')}$. Moreover
$\phi \eqsubst \zeta \compose \iota
      \eqsubst (\xi \compose \iota) \compose \iota
      \eqsubst \xi \compose \iota$
so we are done.
\end{proof}




When the output is a scheme, we define
$\pprec{\Gamma}{\gen{\Xi}{\tau}}{\gen{\Psi}{\upsilon}}$
if there is some $\psi : \Gamma \fatsemi \Xi \lei \Gamma \fatsemi \Psi$
such that $\Gamma \fatsemi \Psi \entails \psi \tau \equiv \upsilon$
and $\psi ||_\Gamma \eqsubst \iota$.

When the output is a type, we just instantiate the above definition with
$\Xi = \emptycontext = \Psi$, i.e.\ we have
$\pprec{\Gamma}{\tau}{\upsilon}$
if $\Gamma \entails \tau \equiv \upsilon$.

Thus the type inference problem is given by a context $\Gamma$ and the
statement $t : ~?$ where $t$ is a term and $?$ represents the output parameter.
A solution is then an information increase $\delta : \Gamma \lei \Delta$ and a
type $\tau$ such that $\Delta \entails \tau \type \wedge t : \tau$.




\subsection{Transforming type assignment into type inference}

To transform a rule into an algorithmic form, we proceed clockwise starting from
the conclusion. For each hypothesis, we must ensure that the problem is fully
specified, inserting variables to stand for unknown problem inputs. Moreover, we
cannot pattern match on problem outputs, so we ensure there are schematic
variables in output positions, fixing things up with appeals to unification. 

Figure~\ref{fig:transformedRules} shows the transformed version of the
declarative rule system. The rule for $\lambda$-abstractions now binds a fresh
type variable for the argument type, which we will replace with an unknown
in the algorithm. The rule for application assigns types to the function and
argument separately, then inserts an equation with a fresh variable for the
codomain type.

\begin{figure}[ht]
\boxrule{t : \tau}

$$\Rule{\Sbind{\beta \defn \upsilon, x \asc \gendot{\beta}}{\Pinf{t}{\tau}}}
       {\Pinf{\lambda x . t}{\upsilon \arrow \tau}}
\qquad
\Rule{\Pinf{f}{\chi}
        \quad
        \Pinf{a}{\upsilon}
        \quad
        \Sbind{\beta \defn \tau}{\Puni{\chi}{\upsilon \arrow \beta}}
       }
       {\Pinf{f a}{\tau}}
$$

$$
\Rule{
      s \hasscheme \OutParam{\sigma}
      \quad
      \Sbind{x \asc \sigma}{\Pinf{w}{\tau}}
     }
     {\Pinf{\letIn{x}{s}{w}}{\tau}}
\qquad
\Rule{t : \tau
      \quad
      \tau \equiv \upsilon}
     {t : \upsilon}
$$

\caption{Transformed rules for type assignment}
\label{fig:transformedRules}
\end{figure}

We must verify that the rule systems in Figures~\ref{fig:typeAssignmentRules}
and \ref{fig:transformedRules} are equivalent. This is mostly straightforward,
as the fresh variable bindings can be substituted out.
The only difficulty is in the application rule, where an equation has been
introduced. If an application has a type in the old system, it can be assigned
the same type in the new system with the equation being reflexive. Conversely,
if an application has a type in the new system, then using the conversion
with the equation allows the same type to be assigned in the old system.
\TODO{Make this a lemma?}

\TODO{Segue...}

We define 
   the scheme inference assertion $\Jscheme{\Gamma}{t}{\sigma}{\Delta}$ and 
   the type inference assertion $\Jtype{\Gamma}{t}{\tau}{\Delta}$
% (inferring the type of $t$ in $\Gamma_0$ yields $\tau$ in the more informative
% context $\Gamma_1$)
by the rules in Figure~\ref{fig:inferRules}.
These rules are clearly structural on terms, so yield a terminating
algorithm, leading naturally to an implementation, given in
subsection~\ref{sec:inferImplementation}.

%%%\TODO{Say something about freshness of $\Xi$ in \name{Var} rule.}
% We use Lemma~\ref{lem:specialise} to ensure in rule \name{Var} that
% we compute a suffix \(\Xi\) consisting of fresh names, such that the
% output \ensuremath{\Gamma, \Xi} is well-formed.

\begin{figure}[ht]
\boxrule{\Jscheme{\Gamma}{s}{\sigma}{\Delta}}

$$
\namer{Gen}
\Rule{\Jtype{\Gamma \fatsemi}{s}{\upsilon}{\Delta \fatsemi \Xi}}
     {\Jscheme{\Gamma}{s}{\gen{\Xi}{\upsilon}}{\Delta}}
$$ 

\boxrule{\Jtype{\Gamma}{t}{\tau}{\Delta}}

$$
\namer{Var}
\Rule{x \asc \gen{\Xi}{\upsilon} \in \Gamma}
     {\Jtype{\Gamma}{x}{\upsilon}{\Gamma, \Xi}}
$$

$$
\namer{Abs}
\Rule{\Jtype{\Gamma, \hole{\alpha}, x \asc \gendot{\alpha}}{w}{\upsilon}
          {\Delta_0, x \asc \gendot{\alpha}, \Xi}}
     {\Jtype{\Gamma}{\lambda x.w}{\alpha \arrow \upsilon}{\Delta_0, \Xi}}
\side{\alpha \notin \tyvars{\Gamma}}
$$

$$
\namer{App}
\BigRule{\Jtype{\Gamma}{f}{\chi}{\Delta_0}
         \quad
         \Jtype{\Delta_0}{a}{\upsilon}{\Delta_1}}
        {\Junify{\Delta_1, \hole{\beta}}{\chi}{\upsilon \arrow \beta}{\Delta}}
        {\Jtype{\Gamma}{f a}{\beta}{\Delta}}
\side{\beta \notin \tyvars{\Delta_1}}
$$

$$
\namer{Let}
\BigRule%%%{\Jtype{\Gamma \fatsemi}{s}{\upsilon}{\Delta_0 \fatsemi \Xi_0}}
        %%%{\Jtype{\Delta_0, x \asc \gen{\Xi_0}{\upsilon}}{w}{\chi}
        %%%       {\Delta_1, x \asc \gen{\Xi_0}{\upsilon}, \Xi_1}}
        %%%{\Jtype{\Gamma}{\letIn{x}{s}{w}}{\chi}{\Delta_1, \Xi_1}}
        {\Jscheme{\Gamma}{s}{\sigma}{\Delta_0}}
        {\Jtype{\Delta_0, x \asc \sigma}{w}{\chi}
               {\Delta_1, x \asc \sigma, \Xi_1}}
        {\Jtype{\Gamma}{\letIn{x}{s}{w}}{\chi}{\Delta_1, \Xi_1}}
$$

\caption{Algorithmic rules for type inference}
\label{fig:inferRules}
\end{figure}


\subsection{Soundness and completeness}

% We say $\Theta$ is a \define{subcontext} of $\Gamma$, written
% $\Theta \subcontext \Gamma$, if $\Gamma = \Theta; \Gamma'$ for some context
% extension $\Gamma'$.

Recall that we defined $\sem{x \asc \sigma}_\TM = x \hasscheme \sigma$, so
$\Gamma \lei \Delta$ requires $\Delta$ to assign a term variable all the types
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
does (modulo substitution). Since the unification algorithm ignores term
variables, it is easy to see that all the previous results hold if we
replace $\lei$ with $\leiR$ throughout.

Corresponding to $\Jmin{\Gamma}{S}{\Delta}$, we write
$\JminR{\Gamma}{S}{\Delta}$ if $\iota : \Gamma \leiR \Delta$, and for any
$\theta : \Gamma \leiR \Theta$ such that $\Theta \entails \theta S$ we
have $\zeta : \Delta \leiR \Theta$ with
$\theta \eqsubst \zeta \compose \iota$.
\TODO{Update with notation for inference problems. Why does the Optimist's
lemma still hold?}

\begin{lemma}[Soundness of type inference]
\label{lem:inferSound}
If $\Jtype{\Gamma}{t}{\upsilon}{\Delta}$ then
$\Gamma \leiR \Delta \entails t : \upsilon$.
\end{lemma}
\begin{proof}
By induction on the structure of derivations.
The rules correspond directly to rules in Figure~\ref{fig:transformedRules},
so if the algorithm infers a type then it can be assigned in the transformed
declarative system. \TODO{Say more about \name{Let} and \name{Gen}?}
\end{proof}


\begin{lemma}[Completeness and generality of type inference]
\label{lem:inferComplete}
If $t$ can be assigned a type in a more informative context, i.e.\ if there exist
$\theta : \Gamma \leiR \Theta$ and $\tau$ such that $\Theta \entails t : \tau$,
then $\Jtype{\Gamma}{t}{\upsilon}{\Delta}$
for some type $\upsilon$ and context $\Delta$.
\TODO{Need same thing about type schemes as well.}

Moreover, there is a substitution $\zeta : \Delta \leiR \Theta$ such that
$\Theta \entails \zeta\upsilon \equiv \tau$ and
$\theta \eqsubst \zeta \compose \iota$. It follows immediately that
$\JminR{\Gamma}{t : \upsilon}{\Delta}$ since the output of the algorithm does
not depend on $\theta$ or $\tau$.
\end{lemma}
\begin{proof}
The algorithm is structurally recursive over terms, so it must terminate.
Each step locally preserves all possible solutions, and
it fails only when unification fails or a term variable is not in scope.
We proceed by induction on the derivation of $\Theta \entails t : \tau$ in the
transformed rule system, noting that for each rule this ensures the inductive
hypothesis applies. Without loss of generality, we ignore the conversion rule,
as we are only working up to equivalence of types.

If $t = x$ is a variable, then the proof of $\Theta \entails x : \tau$ must
consist of applying
$\Theta \entailsN x \hasscheme \gen{\theta\Xi}{\theta\upsilon}$
to some $\Theta$-types, so it determines a map from the unbound type variables
of $\Xi$ to types over $\Theta$, and hence a substitution
$\zeta : \Gamma, \Xi \leiR \Theta$ that agrees with $\theta$ on $\Gamma$ and
maps type variables in $\Xi$ to their definitions in $\Theta$.

If $t = (\letIn{x}{s}{w})$...
For let-expressions, observe that any type specialising any scheme
for $s$ must certainly specialise the type we infer for $s$, and
\emph{ipso facto}, the principal type scheme we assign to $x$.
\TODO{More!}

If $t = \lambda x . w$ is an abstraction, then the proof in the declarative
system gives
$\Theta, \alpha \defn \upsilon, x \asc \gendot{\alpha} \entails w : \chi$
and the inductive hypothesis applies immediately.
\TODO{Observation about permuting $x$ past $\Xi$?}

If $t = f a$ is an application, then we can apply the Optimist's lemma twice
and use the hypotheses.
\TODO{Explain why indexed problem condition is satisfied.}
\TODO{There is a subtlety here about $\beta$ being an output.}

\end{proof}


\subsection{Implementation of type inference}
\label{sec:inferImplementation}

\begin{figure*}[p]

\begin{minipage}[t]{0.5\linewidth}

\subfigure[][Type schemes]{\frame{\parbox{\textwidth}{\fixpars\medskip

> data Index a = Z | S a
>     deriving (Functor, Foldable)

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

The Haskell implementation of our type inference algorithm is given in
Figure~\ref{fig:inferCode}. Note that the monadic |fail| is called when
scope checking fails, whereas |error| indicates that one of the algorithmic
invariants have been violated.

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
specialisation and generalisation of type schemes. The former unpacks a type
scheme with fresh variables, while the latter \scare{skims} type variables off
the top of the context as far as the |LetGoal| marker.

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
\section{Discussion}  %%% Concussion?
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We have arrived at an implementation of Hindley-Milner type inference
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
\bibliography{lib}



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
