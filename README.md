# Russell-paradox-in-TT

Might be the easiest way to formalize Russell's paradox in Type Theory with type in type. Requires the use of sigma and identity types and UIP (This is not required if you are using extensional identity).

The formalization is so simple but I did not see it before, and it seems that some of people think that [Russell's paradox cannot be easily constructed, so we need Girard's paradox](https://math.stackexchange.com/questions/1962145/is-the-russell-paradox-formalizable-in-type-theories?newreg=b84c28ebab8a4da59706cd6989b24890).

See [here](https://konjacsource.github.io/assets/Russell_in_TT.pdf) for the note in pdf.

Note that this construction is not [Coquand's paradox of tree](https://1lab.dev/1Lab.Counterexamples.Russell.html).

After some research, this is what I found.

In [Coquand 1992](https://www.researchgate.net/profile/Thierry-Coquand/publication/225267298_The_paradox_of_trees_in_type_theory/links/56b08e4108ae8e37214fbd14/The-paradox-of-trees-in-type-theory.pdf), he said that it is possible to construct Russell's paradox in ETT without W-types, and referred to a communication in Types Forum, Aug. 1987. But I cannot find this communication since the archives only started in Nov. 1987. I think the construction in the communication is just as same as my construction. They could not make it work in ITT only because axiom K was not introduced until 1993! They do not have it at that time. And then maybe no one ever looks back at the problem after that.
