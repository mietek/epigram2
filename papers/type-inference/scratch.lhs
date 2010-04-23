%if False

\section{Abstract nonsense}

\subsection{Statements}

% A \define{substitution} $\theta$ is a partial map from $\V_K$ to $\D_K$
% for each $K \in \K$,
% and we assume $\D_K$ and $\Ss$ are closed under application of substitutions.

% For any variable $v$ and object $D$ we define a context membership statement
% $\contains v D$ in the obvious way, and write $\Gamma \contains v D$ for
% $\Gamma \entails (\contains v D)$. 

% We assume that $\Ss$ is closed under conjunction $(\wedge)$ with
% $$\Gamma \entails (S_0 \wedge S_1)
%     \quad  \Leftrightarrow  \quad
%     \Gamma \entails S_0  ~\wedge~  \Gamma \entails S_1.$$


\subsection{Increasing information}

% Let $\D_K(\Gamma) = \{ D \in \D_K ~||~ \Gamma \entails D \ok_K \}$.


% $$\Gamma \contains v D  \Rightarrow  \Delta \entails \delta\sem{v D}$$
% and if $\Gamma$ is $\Xi \fatsemi \Gamma'$ then $\Delta$ is
% $\Psi \fatsemi \Delta'$ with $\delta||_{\Xi} : \Xi \lei \Psi$ and
% $\delta : \Xi, \Gamma' \lei \Psi, \Delta'$. This definition is well-founded by
% induction on the number of $\fatsemi$ separators in $\Gamma$.
% (We write $\delta||_{\Xi}$ for the substitution formed by restricting each
% $\delta_K$ to variables in $V_K(\Xi)$.)


% We require a substitution because the type inference algorithm will invent new
% type variables, which must be interpreted over a more informative context that
% will not contain them.


% From now on we will assume that the statement $\sem{v D}_K$ is stable for any
% $v \in \V_K$ and $D \in \D_K$, and that stable statementss are closed under 
% substitution. 


\subsection{Problems}

%if False

A \define{problem domain} $R_\le$ is a set $R$ equipped with a relation $\le$
such that $R$ is closed under substitution. 
A \define{problem on $R_\le$} is a map $P: R_\le \rightarrow \Ss$ such that
$\theta P(r) = P(\theta r)$ for any $r \in R_\le$ and
substitution $\theta$. 
Statements themselves can be seen 
as problems on the unit set. 
We say %%%that 
$r \in R_\le$
\define{solves $P$ in $\Gamma$} if $\Gamma \entails P(r)$.

We will be interested in finding the minimal information increase required to
solve a given problem, so we write
$\delta : \Jmin{\Gamma}{P(r)}{\Delta}$ if
$\delta : \Gamma \lei \Delta$, $\Delta \entails P(r)$ and
for all $\theta : \Gamma \lei \Theta$ and $r'$ such that
$\Theta \entails P(r')$, there exists $\zeta : \Delta \lei \Theta$
such that $\theta = \zeta \compose \delta$ and $r' \le \zeta r$.
We then say that $r$ is a \define{minimal solution of $P$ in $\Delta$}.

If $P_1$ and $P_2$ are problems on $R_\le$ and $S_\ll$, then since $\Ss$ is
closed under conjunction, $P_1 \wedge P_2$ is a problem on
$R \times S_{\langle \le , \ll \rangle}$ given by
$$P_1 \wedge P_2 : R \times S \rightarrow \Ss :
      (r, s) \mapsto P_1(r) \wedge P_2(s)$$
where $(r, s) \langle \le , \ll \rangle (r', s')$ if
$r \le r'$ and $s \ll s'$.

%endif


We now proceed as follows. First we instantiate the above definitions and give
a version of the unification algorithm in this setting. Using this, we can
describe a general technique for converting a collection of inference rules that
give the declarative specification for a problem into an algorithm for solving
the problem minimally. We 
%%%give 
   illustrate with 
the example of Hindley-Milner type inference.


% Later, we will add other sorts of declaration that are not relevant
% for unification.

%%%We write $\tyvars{\Gamma}$ for the 
%   Let $\tyvars{\Gamma}$ be the 
%%%set of type variables of $\Gamma$, i.e.\ $\V_0 \cap \V(\Gamma)$.
%   set $\V_0 \cap \V(\Gamma)$ of type variables declared in $\Gamma$,  

% and hence define the statement $D \ok_\TY$.




\section{Unification up to definition}


% A \define{unifier} for the types $\tau$ and $\upsilon$ in a context $\Gamma$ is
% a pair $(\Delta, \theta)$ such that $\theta : \Gamma \lei \Delta$ and
% $\Delta \entails \theta\tau \equiv \theta\upsilon$.


% since the first 
%%%inference rule
%   rule 
% ensures that
% $\Gamma \contains \alpha \defn \tau
%     \Rightarrow  \Gamma \entails \alpha \equiv \tau$,
% and 
%%%we have
% $$\Gamma \contains \hole{\alpha}
%     \Rightarrow  \alpha \in \tyvars{\Gamma}
%     \Rightarrow  \Gamma \entails \alpha \type
%     \Rightarrow  \Gamma \entails \alpha \equiv \alpha.$$

% \begin{lemma}
% The statement $\tau \equiv \upsilon$ is stable, i.e.\ if
% $\Gamma \entails \tau \equiv \upsilon$ and $\delta : \Gamma \lei \Delta$ then
% $\Delta \entails \delta\tau \equiv \delta\upsilon$.
% \end{lemma}
% \begin{proof}
% By induction on the structure of derivations, observing that leaves are either
% of the form
% $\Gamma \contains \alpha \defn \tau$,
% in which case $\Delta \entails \delta\alpha \equiv \delta\tau$ by definition
% of $\lei$, or they are of the form
% $\Gamma \entails \tau \type$,
% in which case $\Delta \entails \delta\tau \type$ by stability of
% $\tau \type$.
% \end{proof}


% Note that reflexivity and symmetry are admissible rules.

%endif


%if False



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

%endif



Reflexivity follows immediately from the \textsc{Lookup} rule.
For transitivity, suppose $v D \in \Gamma_0 \semidrop n$ and $S \in \sem{v D}$.
Then $\Gamma_1 \semidrop n \entails \gamma_1 S$ since
$\gamma_1 : \Gamma_0 \lei \Gamma_1$.
Now by stability applied to $\gamma_1 S$ using
$\gamma_2||_{\Gamma_1 \semidrop n} :
    \Gamma_1 \semidrop n \lei \Gamma_2 \semidrop n$, we have
$\Gamma_2 \semidrop n \entails \gamma_2\gamma_1\sem{v D}$ .






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



\subsection{Specialisation}

The statement $\sigma \succ \tau$, defined in
Figure~\ref{fig:specRules}, means that $\sigma$ has
generic instance $\tau$ obtained by substituting types
for the generic variables of $\sigma$.
We observe the sanity condition
$$\Gamma \entails \sigma \succ \tau
    \Rightarrow  \Gamma \entails \sigma \scheme  \wedge  \tau \type.$$

\begin{figure}[ht]
\boxrule{\Delta \entails \sigma \spec \tau}

$$
\Rule{\tau \type}
     {.\tau \spec \tau}
\qquad
\Rule{\upsilon \type
      \quad
      \subst{\upsilon}{\alpha}{\sigma} \spec \tau}
     {\forall\alpha~\sigma \spec \tau}
$$

$$
\Rule{\subst{\upsilon}{\alpha}{\sigma} \succ \tau}
     {\letS{\alpha}{\upsilon}{\sigma} \succ \tau}
\qquad
\Rule{\sigma \succ \tau
      \quad
      \tau \equiv \upsilon}
     {\sigma \succ \upsilon}
$$

\caption{Declarative rules for specialisation}
\label{fig:specRules}
\end{figure}



%if False

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

%endif



The |popEntry| function removes and returns the topmost entry from the context.
\TODO{Since |popEntry| is only used twice, perhaps we should remove it?}

> popEntry :: Contextual Entry
> popEntry = do  _Gamma :< e <- getContext
>                putContext _Gamma
>                return e




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



% For our running example, the sort $\TY$ of type variables, substitution is
% defined as one would expect.
% Let $\types{\Delta}$ be the set of types $\tau$ such that
% $\Delta \entails \tau \type$. 
% A $\TY$-substitution then maps type variables to types, so it can be applied
% to types and statements in the usual way.









%if False

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
$$
\Rule{x \hasc .\tau  ~\wedge~   \tau \equiv \upsilon}
     {x \hasc .\upsilon}
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

%endif






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




%if False

\section{The specialisation problem}

\TODO{How much of this section can we get rid of?}

Let $S$ be the problem given by
\begin{align*}
\In{S}                   &= \V_\TM  \\
\Out{S}                  &= \Type  \\
\Pre{S} (x)         &= \valid  \\
\Post{S} (x, \tau)  &= \tau \type \wedge x : \tau  \\
\R{S} (\tau, \upsilon)   &= \tau \equiv \upsilon
\end{align*}

\subsection{Constructing a specialisation algorithm}

% Consider the variable rule for type assignment, which is
% $$\Rule{x \hasc \sigma   \quad   \sigma \spec \tau}
%        {\Pinf{x}{\tau}}.$$
% We need an algorithm that, given a term variable as input, finds a type that
% can be assigned to it (by specialising its scheme).


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
If $\Jspec{\Gamma}{\sigma}{\tau}{\Gamma, \Xi}$, then
$\iota : \Jmin{\Gamma}{\Pspec{\sigma}{\tau}}{\Gamma, \Xi}$.
\end{lemma}

\begin{proof}
Clearly $\iota : \Gamma \lei \Gamma, \Xi$.
By structural induction on $\sigma$,
$$\Gamma, \Xi \entails \tau \type \wedge \sigma \spec \tau.$$

\TODO{This needs updating.}
For minimality, suppose $\sigma = \gen{\Psi}{\chi}$,
$\theta : \Gamma \lei \Theta$
and $\Theta \entails \Pspec{\sigma}{\upsilon}$.
% Then there is a substitution $\psi : \Theta, \Psi \lei \Theta$

% For minimality, suppose
% $\theta : \Gamma \lei \Theta \entails \Pspec{\sigma}{\upsilon}$.
% By stability, $\Theta \entails x \hasc \sigma$.
% Examining the rules in Figure~\ref{fig:termVarSchemeRules}, the proof of
% $\Theta \entails x \hasc .\tau$ must specialise $\sigma$ with types
% $\Psi$ for its generic variables. Let $\theta' = \subst{\Psi}{\Xi}{\theta}$,
% then $\theta' : \Gamma, \Xi \lei \Theta$ and $\theta = \theta' \compose \iota$.
\end{proof}


\begin{lemma}[Completeness of specialisation]
\label{lem:specialiseComplete}
If $\Gamma \entails \sigma \scheme$ then
$\Jspec{\Gamma}{\sigma}{\tau}{\Gamma, \Xi}$
for some list of type variables $\Xi$.

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
By structural induction on $\sigma$.
\end{proof}


\subsection{Implementing specialisation}

If a $\forall$ quantifier is outermost, it is removed and an unbound fresh type
variable is substituted in its place (applying the \textsc{All} rule).

If a let binding is outermost, it is removed and added to the context with a
fresh variable name (applying the \textsc{LetS} rule).

This continues until a scheme with no quantifiers is reached, which can simply be
converted into a type (applying the \textsc{T} rule).


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


%endif




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




%if False

\begin{lemma}
\label{lem:schemeInfoIncrease}
Let $\Theta$ be a context such that
$\Theta \entails \gen{\Xi}{.\upsilon} \scheme$ and $\Theta \entails \tau \type$.
Then $\Theta, x \asc \gen{\Xi}{.\upsilon} \entails x \hasc \tau$
if and only if there exists a list of type variable declarations $\Phi$ such that
$$\iota : \Theta \fatsemi \Xi \lei \Theta \fatsemi \Phi
    \quad \text{and} \quad
    \Theta \fatsemi \Phi \entails \upsilon \equiv \tau$$
\end{lemma}


\begin{lemma}
\label{lem:schemeSameInstances}
Suppose $\theta : \Delta_0 \fatsemi \Xi_0 \lei \Theta \fatsemi \Psi$,
$\Theta \fatsemi \Psi \entails \theta\upsilon \equiv \tau_s$ and
$\Theta, x \asc \gen{\Psi}{.\tau_s} \entails x \hasc .\tau$. Then
$\Theta, x \asc \theta \gen{\Xi_0}{.\upsilon} \entails x \hasc .\tau$.
\end{lemma}

\begin{proof}
By lemma~\ref{lem:schemeInfoIncrease}, there exists $\Phi$ such that
$\iota : \Theta \fatsemi \Psi \lei \Theta \fatsemi \Phi$ and
$\Theta \fatsemi \Phi \entails \tau_s \equiv \tau$.
Then $\iota : \Theta \fatsemi \theta \Xi_0 \lei \Theta \fatsemi \Phi$
and $\Theta \fatsemi \Phi \entails \theta\upsilon \equiv \tau$ by
stability and transitivity, so by lemma~\ref{lem:schemeInfoIncrease},
$\Theta, x \asc \gen{\theta\Xi_0}{.\theta\upsilon} \entails x \hasc \tau$.
\end{proof}


\begin{lemma}
\label{lem:schemeInstancesSuffice}
Given $\Theta, x, \sigma, \sigma'$ suppose
$$\forall \upsilon \forall \Phi .
    \Theta, x \hasc \sigma, \Phi \entails x : \upsilon
        \Rightarrow  \Theta, x \hasc \sigma', \Phi \entails x : \upsilon$$
and given $\Psi, w, \tau$ suppose
$\Theta, x \hasc \sigma, \Psi \entails w : \tau$.
Then $\Theta, x \hasc \sigma', \Psi \entails w : \tau$. 

% If $\Theta, x \asc \sigma, \Theta' \entails w : \tau$
% and for all types $\upsilon$,
% $$\Theta, x \asc \sigma, \Theta' \entails x \hasc .\upsilon
%     ~\Rightarrow~ \Theta, x \asc \sigma', \Theta' \entails x \hasc .\upsilon$$
% then $\Theta, x \asc \sigma', \Theta' \entails w : \tau$.
\end{lemma}

\begin{proof}
By induction on the structure of derivations; the hypothesis ensures that
appeals to the variable rule hold in the new context.
\end{proof}

%endif




% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0;}{t}{\upsilon}{\Gamma_1; \Xi}$,
% \item $\theta_1 : \Gamma_1; \lei \Delta$ with 
% $\theta_0\alpha = \theta_1\alpha$ for any $\alpha \in \tyvars{\Gamma_0}$, and
% \item $\Gamma_1; \entails t :: \gen{\Xi}{\upsilon}$ principal.
% \end{enumerate}




% with
% $$\forall \upsilon. \Theta \entails \theta\sigma' \succ \upsilon
%     \Leftrightarrow \Theta \entails x : \upsilon.$$
% so by completeness of specialisation (lemma~\ref{lem:specialiseComplete}),
% $\Jhast{\Gamma}{x}{\sigma}{\upsilon}{\Gamma, \Xi}$
% and
% $$\forall\tau \forall \phi: \Gamma_0 \lei \Phi . (
%     \Phi \entails \phi\sigma' \succ \tau
%         \Leftrightarrow  \Phi \entails \phi\gen{\Xi}{\upsilon} \succ \tau.$$
% Hence the \textsc{Var} rule applies giving
% $\Jtype{\Gamma}{x}{\upsilon}{\Gamma, \Xi}$.
% (b) holds trivially with $\theta_1 = \theta_0$, and
% $\Gamma_0 \entails x \hasscheme \gen{\Xi}{\upsilon}$ principal.





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
$$\iota : \Theta, x \asc \gen{\Psi}{.\tau_s}
    \lei  \Theta, x \asc \theta_0\gen{\Xi_0}{.\upsilon}$$
so by stability of type assignment under the $\lei$ relation,
$$\Theta, x \asc \theta_0\gen{\Xi_0}{.\upsilon} \entails w : \tau.$$

% since if $\Theta, x \asc \sigma \entails x \hasc .\tau_x$ then
% $\Theta, x \asc \theta_0\gen{\Xi_0}{.\upsilon} \entails x \hasc .\tau_x$.
% \TODO{Prove this as a lemma.}





% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_1, x \asc \gen{\Xi_1}{.\upsilon};}{w}{\chi}
% {\Gamma_2; x \asc \gen{\Xi_1}{.\upsilon}; \Xi_2}$
% \item $\theta_2 : \Gamma_2; x \asc \gen{\Xi_1}{.\upsilon};
%   \lei \Delta, x \asc \gen{\Xi_1}{.\upsilon}; \Psi$
% \item $\Gamma_2; x \asc \gen{\Xi_1}{.\upsilon};
%   \entails w \hasscheme \gen{\Xi_2}{.\chi}$ principal
% \end{enumerate}




% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0;}{\letIn{x}{s}{w}}{\chi}{\Gamma_2; \Xi_2}$
% \item $\theta_2 : \Gamma_2; \lei \Delta;$ \TODO{Why?}
% \item $\Gamma_2; \entails \letIn{x}{s}{w} \hasscheme \gen{\Xi_2}{.\chi}$
% principal by
% lemma \ref{lem:letSchemePrincipal}.
% \end{enumerate}




% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0; \hole{\alpha}, x \asc .\alpha;}{w}{\upsilon}
%              {\Gamma_1; \Phi, x \asc .\alpha; \Xi}$
% \item $\theta_1 : \Gamma_1; \Phi, x \asc .\alpha; \lei \Delta, x \asc .\tau_0;$
% \item $\Gamma_1; \Phi, x \asc .\alpha;
%   \entails w \hasscheme \gen{\Xi}{\upsilon}$
%          principal.
% \end{enumerate}



% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0;}{\lambda x . w}{\alpha \arrow \upsilon}
%              {\Gamma_1; \Phi, \Xi}$
% \item $\theta_1 : \Gamma_1; \lei \Delta$
% \item $\Gamma_1; \entails \lambda x . w \hasscheme \gen{\Phi, \Xi}{\upsilon}$
%           principal. \TODO{Why?}
% \end{enumerate}



% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0;}{f}{\upsilon}{\Gamma; \Xi}$
% \item $\theta : \Gamma; \lei \Delta$ 
% \item $\Gamma; \entails f \hasscheme \gen{\Xi}{\upsilon}$ principal.
% \end{enumerate}


% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma;}{a}{\upsilon_0}{\Gamma_1; \Xi_1}$
% \item $\theta' : \Gamma_1; \lei \Delta$ 
% \item $\Gamma_1; \entails a \hasscheme \gen{\Xi_1}{\upsilon_0}$ principal.
% \end{enumerate}


% \begin{enumerate}[(a)]
% \item $\Jtype{\Gamma_0}{f a}{\beta}{\Gamma_2}$
% \item $\theta_1 : \Gamma_2; \lei \Delta$
% \item $\Gamma_2; \entails f a \hasscheme \gen{???}{\beta}$ principal.
% \end{enumerate}




% \item If $v = \alpha$ and $\alpha \in \FTV{\Xi}$ then $\alpha \in \FTV{\chi}$
% for some $\chi$ with $\Xi = \Xi_0, \beta \defn \chi, \Xi_1$ and
% $\beta \in \FTV{\tau, \Xi_1}$.
% \TODO{Prove this is contradictory.}





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