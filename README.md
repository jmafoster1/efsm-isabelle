# efsm-isabelle
We provide a formalisation of extended finite state machines (EFSMs) where models are represented as finite sets of transitions between states. EFSMs execute traces to produce observable outputs. We also define various simulation and equality metrics for EFSMs in terms of traces and prove their strengths in relation to each other. Another key contribution is a framework of function definitions such that LTL properties can be phrased over EFSMs. Finally, we provide a simple example case study in the form of a drinks machine.

This is now openly available as an [AFP entry](https://www.isa-afp.org/entries/Extended_Finite_State_Machines.html) which can be imported into your own theory files with `import EFSM.EFSM`. This can be cited as
```
@article{Extended_Finite_State_Machines-AFP,
author  = {Michael Foster and Achim D. Brucker and Ramsay G. Taylor and John Derrick},
title   = {A Formal Model of Extended Finite State Machines},
journal = {Archive of Formal Proofs},
month   = sep,
year    = 2020,
note    = {\url{https://isa-afp.org/entries/Extended_Finite_State_Machines.html},
          Formal proof development},
ISSN    = {2150-914x},
}
```
