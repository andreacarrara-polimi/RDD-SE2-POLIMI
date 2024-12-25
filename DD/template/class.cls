\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{template/class}[PoliMi template]
\ProcessOptions\relax

\LoadClass[12pt, twoside]{book}
\RequirePackage[
    a4paper,
    includehead,headheight=.6cm,
    inner=2.5cm,outer=2.5cm,top=2.5cm,bottom=2.5cm
]{geometry}

\RequirePackage[bf,font=onehalfspacing]{caption}
\newcommand{\documentspacing}{\onehalfspacing}

\newcommand\backgroundbl{
    \put(-150,-200){
		\parbox[b][\paperheight]{\paperwidth}{
			\vfill
			\centering
			\transparent{.4}
			\includegraphics[width=.85\paperwidth]{template/background.eps}
		    \vfill
        }
    }
}

\newcommand\backgroundtr{
	\put(200,330){
		\parbox[b][\paperheight]{\paperwidth}{
			\vfill
			\centering
			\transparent{.4}
			\includegraphics[width=.7\paperwidth]{template/background.eps}
			\vfill
        }
    }
}

\RequirePackage{xkeyval}
\define@key[OIST]{title}{title}{\def\title{#1}}
\define@key[OIST]{title}{subtitle}{\def\subtitle{#1}}
\define@key[OIST]{title}{authors}{\def\authors{#1}}
\define@key[OIST]{title}{date}{\def\date{#1}}

\providecommand{\puttitle}{}
\renewcommand{\puttitle}[1]{
    \@puttitle{}{#1}
}

\providecommand{\@puttitle}{}
\renewcommand{\@puttitle}[2]{
    \setkeys[OIST]{title}{#2}
	\begin{titlepage}
		\AddToShipoutPicture*{\backgroundtr}
		\begin{minipage}{.95\textwidth}
            \includegraphics[
                clip,trim={1.2cm 0 0 0},
                width=.7\textwidth
            ]{template/logo.eps}
    		\vspace{2.5cm}
    		\color{polimiblue}\singlespacing\huge\bfseries\title\par
    		\vspace{1.5cm}
    		\color{polimiblue}\bfseries\large\textsc\subtitle\par
    		\vspace{1.5cm}
    		\color{black}\bfseries\authors
        \end{minipage}
		\vfill
		\begin{minipage}{.85\textwidth}
    		\normalsize\date
		\end{minipage}
	\end{titlepage}
}

\let\latexchapter\chapter
\renewcommand{\chapter}{\@ifstar{\polimichapterstar}{\polimichapter}}

\newcommand{\polimichapter}[1]{
    \latexchapter{#1}
    \renewcommand{\headrulewidth}{0pt}
    \fancyhead[LO,RE]{\textbf{
        \textcolor{polimiblue}
        \thechapter\hsp\textcolor{polimiblue}{|   }
        \hsp\leftmark
    }}
    \fancyhead[LE,RO]{\thepage}
    \vspace{-1cm}
}

\newcommand{\polimichapterstar}[1]{
    \phantomsection
    \latexchapter*{#1} 
    \renewcommand{\headrulewidth}{0pt}
    \addcontentsline{toc}{chapter}{#1}
    \fancyhead[LO,RE]{\bfseries\textcolor{polimiblue}{|   } #1}
    \fancyhead[LE,RO]\thepage
    \vspace{-1cm}
}
