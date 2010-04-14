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

Let $\semidrop$ be a partial function from contexts and natural numbers to
contexts, defined by
\begin{align*}
\Xi \semidrop 0 &= \Xi  \\
\Xi \fatsemi \Gamma \semidrop 0 &= \Xi  \\
\Xi \fatsemi \Gamma \semidrop n+1 &= \Xi \fatsemi (\Gamma \semidrop n)  \\
\Xi \semidrop n+1 &~\mathrm{undefined}
\end{align*}

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