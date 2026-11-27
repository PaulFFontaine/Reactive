# Reactive

The aim of the project is for me to do some Lean proofs and explore Lean features.
I chosed reactive programs and reactive programms specifications as the field of these proofs. 


A program is said to be reactive, when you see it as a way to produce a (potentially infinite) sequence of outputs from a sequence of inputs of same length (instead of considering input and output as a single piece of data). The sequence of outputs is such that any single piece of output can be computed only using previous pieces of input. Moreover, if you assume that a computer has a finite number of states, and so, you see it as a Moore or Mealy machine, rather than a Turing machine, you can wonder which functionnal programms can be computed by a finite state machine. 

From a software engeneering perspective you can wonder which is the smarter/the more elegant way of rewriting a given reactive program, I can't reply to this question but I always have it in mind working on this project.

The ArrowizedFRP module is inspired by Haskell Yampa library https://hackage.haskell.org/package/Yampa except that only discrete time representation is used for now.
