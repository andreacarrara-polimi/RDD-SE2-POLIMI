# Requirements and Design Documents for Software Engineering 2 at Polytechnic of Milan

This repository contains the Requirements Analysis and Specification Document (RASD) and the Design Document (DD) for the Software Engineering 2 course at Polytechnic of Milan.
Coupled with the following README, it serves as a guide on how to replicate our work for future assignments without losing your mind or strangling your teammates.

## Content

We have included our assignment for reference.

### Documents

The "Documents" folder contains deliverables and their source code.
They are are written in [LaTeX](https://www.latex-project.org) and can be imported into [Overleaf](https://www.overleaf.com) for reuse.
The template was adapted from [this one](https://it.overleaf.com/latex/templates/classical-format-thesis-scuola-di-ingegneria-industriale-e-dellinformazione-politecnico-di-milano/dkmvtndqkyxg) and improved for clarity and functionality.
For example, it includes a predefined table for use cases.

### Assets

The "Assets" folder stores the raw files for diagrams, including sequence diagrams.
You can open the diagrams on [draw.io](https://www.draw.io) and the sequence diagrams on [sequencediagrams.org](https://www.sequencediagrams.org).
This keeps everything easy to update.

### Presentation

The "Presentation" folder contains the slides used for the presentation, created with [Beamer](https://it.overleaf.com/learn/latex/Beamer). We used [this template](https://github.com/pcafrica/beamerthemepolimi) and imported it into Overleaf using [this port](https://it.overleaf.com/latex/templates/polimi-beamertheme/rjsxsvfzkpnv).
It’s not perfect, but it gets the job done. The corresponding script can be found [here](https://docs.google.com/document/d/1RVW6rwd48ViAyB4GCoNGyPHEAefgPEQRiPMS8HO172c), where each paragraph corresponds to one slide.

## Mistakes

We made a few mistakes that are worth pointing out so you can avoid them:

* We used some abbreviations before they had been defined in the glossary. To avoid confusion, explain them when first introduced.
* We labeled BPMN diagrams as state diagrams. Both are fine, but make sure to label them correctly.
* In the sequence diagrams, we used dashed lines for both responses and asynchronous messages, namely emails.
Instead, asynchronous messages have a distinct notation, but we don’t recall the correct one and found conflicting information online.
Sorry.
* In the component views, we inverted the symbols of the interfaces. The lollipop  should be  on the side offering the service and the socket on the side consuming it.
* In the last implementation step, the notification manager was depicted as depending on the other managers, when it’s actually the other way around.

Unexpectedly, no comments were made about the formal analysis, even though we anticipated criticism for not modeling the dynamic behavior of the system. Still, be cautious about this in your work.

## Discussion

During the  discussion, each issue was addressed.
For example, the professor noted missing cardinalities in the class diagram.
We explained that only cardinalities from A to B were specified because A stores the reference to B in the code of the model.
She accepted the explanation.
Other times, she correctly identified flaws and we agreed with her while explaining our reasoning.
This secured us a full mark despite the aforementioned mistakes.
While this was with Professor Di Nitto, we suppose a similar approach would work with other professors.
