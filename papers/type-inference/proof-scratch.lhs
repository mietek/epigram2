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
