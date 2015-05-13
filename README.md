# mess
Martin-Löf Extensible Specification and Simulator

A simple implmentation of a MLTT system, prepared for a talk at LispNYC on 12 May, 2015.

The code is in mess.rkt, and the slides are in scheme-to-type-theory.pdf

The precis of the talk, as announced, follows:

From Scheme to Dependent Type Theory in 100 Lines

a.k.a. Lambda: The Ultimate Realizer

a.k.a. Homotopy Spaces: The Ultimate Extensional Realizer?

In this talk we will introduce Dependent Type Theory through the one of the typically nicest ways to understand anything at all — implementing it in Scheme! As it turns out, the untyped lambda calculus provides excellent raw material over which to construct a proof theory, based on the notion that a proposition may be verified through the construction of a lambda-term which realizes its meaning.

A dependent type theory can also be thought of as a programming language, and the system we develop, following Martin-Löf’s 1979 “Constructive Mathematics and Computer Programming” [1] can be thought of as a “little language” embedded in Scheme that comes with a system of judgments by which we can verify properties of our programs, and which includes a foreign function interface to the whole of mathematics.

We will point towards some questions that immediately arise when asking “what does it mean for some value to be equal to some other value” and “what does it mean for some type to be equal to some other type,” and consider some of the approaches to answering these sorts of questions. This invariably leads to the Univalence Axiom -- the proposition that equality is equivalent to equivalence.

We will then proceed to a sketch of the homotopy interpretation of type theory [2], in which the univalence axiom is validated. Finally, we will conclude some ideas of how we can understand the homotopy interpretation (and implement it) in light of the system presented.

The talk will be conducted using the racket variant of the Scheme language, making frequent use of pattern matching.

[1] http://www.cs.tufts.edu/~nr/cs257/archive/per-martin-lof/constructive-math.pdf

[2] http://homotopytypetheory.org/book/
