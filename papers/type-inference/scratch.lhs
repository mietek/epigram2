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
