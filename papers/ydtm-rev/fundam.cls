% $Id: fundam.cls,v 1.2 2000/06/24 06:57:31 piotrek Exp $
% This file fuin.cls defines LaTeX 2e document class 
% for Fundamenta Informaticae.
% 
% To be used with LaTeX 2e.
%


\newif\iffour\fourfalse
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{fundam}[1998/08/19 v1.1
 Fundamenta Informaticae document class]
\DeclareOption{manyauthors}{\fourtrue}
\DeclareOption{draft}{\PassOptionsToClass{draft}{article}}
\DeclareOption{times}{\AtEndOfClass{\RequirePackage{times}}}
\DeclareOption{cmtt}{\AtEndOfClass{\renewcommand{\ttdefault}{cmtt}}}
\DeclareOption{theoremsf}{\def\THstyle{\theorembodyfont{\sffamily}
    \theoremheaderfont{\bfseries\sffamily}}
  \def\PRstyle{\sffamily}}
\DeclareOption{theoremnormal}{\def\THstyle{\theorembodyfont{\upshape}}
  \def\PRstyle{\relax}}
\ExecuteOptions{final,theoremnormal,times,cmtt}
\ProcessOptions
\relax
\LoadClass[11pt,twoside,onecolumn]{article}
\RequirePackage{theorem}
\RequirePackage{amsmath}
%=======================================================================
\def\@seccntformat#1{\csname the#1\endcsname.\quad} %% PU - 19 VIII
                                      %% zmiana \enspace na \quad
%=======================================================================
%\def\ii{\footnotesize\em}
%=======================================================================
\def\issue#1{\gdef\@issue{#1}}
\issue{XX~(\number\year)}  % zmiana (PU)
\def\runninghead#1#2{\gdef\@shortauthor{#1}\gdef\@shorttitle{#2}}
\runninghead{author}{short title}
% this ugly thing for backwards compatibility:
\let\markboth\runninghead
%%%\setcounter{page}{163} 

\AtEndDocument{\label{::last page of FI article:\jobname::}}

\def\@maketitle{\newpage%
    \renewcommand\thefootnote{\ifnum\c@footnote=7\relax C\else\@fnsymbol\c@footnote\fi}%
    \def\@makefnmark{\hbox{\@textsuperscript{\normalfont\@thefnmark}}}%
    \long\def\@makefntext##1{\parindent 0em\noindent
            {%
                \@textsuperscript{\normalfont\@thefnmark }}##1}%    
  {\noindent\footnotesize\textit{Fundamenta Informaticae
      \ignorespaces\@issue\unskip\space
      \thepage--\pageref{::last page of FI article:\jobname::}}% zmiana - na -- (PU)
      \hfill \thepage}
  \vskip .01em 
  {\noindent\footnotesize\textit{IOS Press}}
  \vskip 1.6em
  \par\hangindent=30pt\hangafter=0
  \pretolerance=10000
  \begin{flushleft}%
    {\Large\bfseries \@title\par}
    \vskip 1.7em
    {\normalsize\fontsize{10}{\f@baselineskip}\itshape
      \tabcolsep=0pt
      \lineskip0pt %??
\iffour\@fourauthors\else
      \begin{tabular}[t]{l}
        \reset@font\normalsize\bfseries\@author\relax
      \end{tabular}\par\fi}%
    \nointerlineskip
  \end{flushleft}%
  \vskip .2em 
  \footnoterule
  \vskip 3cm
  }

\def\and{\\[5pt]\reset@font\normalsize\bfseries}

\def\abstract{%
\list{}{\advance\topsep by0.35cm\relax\small\rm
 \leftmargin=1cm
 \labelwidth\listparindent
 \itemindent\listparindent
 \rightmargin\leftmargin}\item[\hskip\labelsep\bf\abstractname.]}
\let\endabstract=\endlist

\def\keywords{%
\list{}{\advance\topsep by0.35cm\relax\small\rm
 \leftmargin=1cm
 \labelwidth=\z@
 \listparindent=\z@
 \itemindent\listparindent
 \rightmargin\leftmargin}\item[\hskip\labelsep\bf Keywords: ]}
\let\endkeywords=\endlist
%=======================================================================
\let\ps@plain\ps@empty
\def\ps@fuin{\let\@mkboth\@gobbletwo
  \def\@oddhead{\footnotesize\phantom{\thepage}%
    \hfil\textit{\@shortauthor\,/\,\@shorttitle}\hfil
    \thepage}
  \def\@oddfoot{}
  \def\@evenhead{\footnotesize\thepage
    \hfil \textit{\@shortauthor\,/\,\@shorttitle}\hfil
    \phantom{\thepage}}
  \def\@evenfoot{}
  }
\pagestyle{fuin}

\textwidth 16cm
\textheight 21cm
%\topmargin -2cm
\oddsidemargin 0.1cm
\evensidemargin 0.0cm

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Theorem like environments

\gdef\th@plain{\normalfont\itshape
  \def\@begintheorem##1##2{%
        \item[\hskip\labelsep \theorem@headerfont ##1\ ##2.]}%

\def\@opargbegintheorem##1##2##3{%
  \item[\rlap{\vbox{\hbox{\hskip \labelsep \theorem@headerfont
                     ##1\ ##2.\ (##3)}%
                    \hbox{\strut}}}]}}
%\def\@opargbegintheorem##1##2##3{%
%   \item[\hskip\labelsep \theorem@headerfont ##1\ ##2.\ (##3)]\hfill\newline}}

\theoremstyle{plain}
\THstyle
\newtheorem{definition}{Definition}[section]
\newtheorem{theorem}{Theorem}[section]
\newtheorem{fact}{Fact}[section]
\newtheorem{lemma}{Lemma}[section]
\newtheorem{example}{Example}[section]
\newtheorem{assumption}{Assumption}[section]
\newtheorem{proposition}{Proposition}[section]
\newtheorem{remark}{Remark}[section]
\newtheorem{corollary}{Corollary}[section]
\newtheorem{claim}{Claim}[section]
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newenvironment{proof}
  {\trivlist\PRstyle\item[]{\bfseries Proof:}\newline}{\QED\endtrivlist}
\def\squareforqed{\hbox{\rlap{$\sqcap$}$\sqcup$}}
\def\QED{\ifmmode\squareforqed\else{\unskip\nobreak\hfil
\penalty50\hskip1em\null\nobreak\hfil\squareforqed
\parfillskip=0pt\finalhyphendemerits=0\endgraf}\fi}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\renewcommand\arraystretch{1.2}
\setlength\tabcolsep{9\p@}
\setlength\belowcaptionskip{5\p@}

\long\def\@makecaption#1#2{%
  \small
  \vskip\abovecaptionskip
  \sbox\@tempboxa{#1.\quad #2}%
  \ifdim \wd\@tempboxa >\hsize
    #1.\quad #2\par
  \else
    \hb@xt@\hsize{\hfil\box\@tempboxa\hfil}%
  \fi
  \vskip\belowcaptionskip}

\abovedisplayskip=7pt plus 2pt minus 5pt
\abovedisplayshortskip=0pt plus 2pt
\belowdisplayskip=7pt plus 2pt minus 5pt
\belowdisplayshortskip=5pt plus 2pt minus 3pt

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcounter{ttmp}\setcounter{ttmp}{0}

\def\QQQ{
\setcounter{ttmp}{\thetmp}
\setlength\maxl{0pt}
\setbox0=\vbox{\def\corresponding{\relax}\def\thanks##1{\relax}%
  \csname @author\thettmp\endcsname}
\setlength\tmpl{\ht0}\addtolength\tmpl{\dp0}
\ifnum\tmpl>\maxl\relax\setlength\maxl{\tmpl}\fi
\stepcounter{ttmp}
\setbox0=\vbox{\def\corresponding{\relax}\def\thanks##1{\relax}%
  \csname @author\thettmp\endcsname}
\setlength\tmpl{\ht0}\addtolength\tmpl{\dp0}
\ifnum\tmpl>\maxl\relax\setlength\maxl{\tmpl}\fi
%\message{\the\maxl}
\addtolength\maxl{0.8\baselineskip}
%
\halign{##&##\cr
\hbox{\global\stepcounter{tmp}
\vbox to \maxl{\hsize=0.5\hsize\upshape\bfseries\csname @author\thetmp\endcsname\vfill}}&
\hbox{\global\stepcounter{tmp}
\vbox to \maxl{\hsize=0.5\hsize\upshape\bfseries\csname @author\thetmp\endcsname\vfill}}\cr}
}

\def\END{\relax}
\def\AUTORZY#1{\doAUTOR#1\and\END
\setcounter{tmp}{0}
\let\ORIGBS=\\
\def\\{\fontsize{10}{\f@baselineskip}\mdseries\itshape\ORIGBS}
\vbox{\loop
\QQQ
\ifnum\thetmp<\theauthor
\repeat}\par}
\def\doAUTOR#1\and#2{\formatauthor{#1}%\message{^^J}
\if#2\relax%\message{KONIEC^^J}
\let\next\relax\else\let\next\doAUTOR\fi\next#2}

\def\@fourauthors{\expandafter\expandafter\AUTORZY{\@author}}

\newcounter{author}\setcounter{author}{0}
\newcounter{tmp}\setcounter{tmp}{0}

\newlength\maxl
\newlength\tmpl 

\def\formatauthor#1{\stepcounter{author}%\message{****\theauthor}
  \expandafter\def\csname @author\theauthor\endcsname{#1}
\setcounter{tmp}{\theauthor}\stepcounter{tmp}
  \expandafter\def\csname @author\thetmp\endcsname{\relax}
%\message{^^J<<<<<<<<<<<<<<<<<<<<<<<<^^J}
%\expandafter\show\csname @author\theauthor\endcsname
%\message{^^J>>>>>>>>>>>>>>>>>>>>>>>>^^J}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\renewcommand\@makefntext[1]{%
    \parindent 0em%
    \noindent
    {\@makefnmark }#1}
\def\@makefnmark{{\@textsuperscript{\normalfont\@thefnmark}}}%

\def\acknowledgements{\section*{Acknowledgements}}

\def\corresponding{\advance\c@footnote by -1\global\renewcommand\thefootnote{C}
    \long\def\@makefntext##1{\parindent 0em\noindent
            {%
                \@textsuperscript{C}}##1}%    
\footnotemark
\protected@xdef\@thanks{\@thanks
  \protect\footnotetext[7]{Corresponding author}}%
}

\def\address#1{{\renewcommand\thefootnote{\relax}%
\footnotetext{Address for correspondence: #1}}}
\def\thanksas#1{\@textsuperscript{\@fnsymbol#1}}


\renewenvironment{thebibliography}[1]
     {\section*{\refname
        \@mkboth{\MakeUppercase\refname}{\MakeUppercase\refname}}%
      \small
      \list{\@biblabel{\@arabic\c@enumiv}}%
           {\settowidth\labelwidth{\@biblabel{#1}}%
            \leftmargin\labelwidth
            \advance\leftmargin\labelsep
            \@openbib@code
            \usecounter{enumiv}%
            \let\p@enumiv\@empty
            \renewcommand\theenumiv{\@arabic\c@enumiv}}%
      \sloppy
      \clubpenalty4000
      \@clubpenalty \clubpenalty
      \widowpenalty4000%
      \sfcode`\.\@m}
     {\def\@noitemerr
       {\@latex@warning{Empty `thebibliography' environment}}%
      \endlist}

\gdef\@ltag{\relax}
\def\ltag#1{\gdef\@ltag{$#1$}}

\def\mkltag{\if\@ltag\relax\else\llap{\hbox to \hsize{\@ltag\hss}}\fi\gdef\@ltag{\relax}}

%\def\endequation{\eqno \hbox{\@eqnnum\mkltag}$$\@ignoretrue}

\def\@@eqncr{\let\reserved@a\relax
    \ifcase\@eqcnt \def\reserved@a{& & &}\or \def\reserved@a{& &}%
     \or \def\reserved@a{&}\else
       \let\reserved@a\@empty
       \@latex@error{Too many columns in eqnarray environment}\@ehc\fi
     \reserved@a \if@eqnsw\@eqnnum\mkltag\stepcounter{equation}\fi
     \global\@eqnswtrue\global\@eqcnt\z@\cr}


\def\tagform@#1{\maketag@@@{(\ignorespaces#1\unskip\@@italiccorr)}\mkltag} 
