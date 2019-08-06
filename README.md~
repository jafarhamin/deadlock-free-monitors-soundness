# Deadlock-Free Monitors and Channels
* A Formalization and Soundness Proof in Coq
* A Number of Examples Verified in VeriFast

[This repository](https://github.com/jafarhamin/deadlock-free-monitors-soundness) contains a formalization and a soundness proof, carried out by [Coq proof assistant v8.6](https://coq.inria.fr), for deadlock-free monitors, a modular approach to verify deadlock-freedom of programs synchronized using condition variables.

Additionally, [this repository](https://github.com/jafarhamin/deadlock-free-monitors-soundness) contains a number of programs, which are synchronized using condition variables or communicate through channels, verified by the [VeriFast program verifier](https://people.cs.kuleuven.be/~bart.jacobs/verifast/).

An HTML representation of this formalization can be found [here](https://www.hamin.be/dfm/html/dfm.html).

For more details about the approach please look at the following papers:
* [Deadlock-Free Monitors](https://link.springer.com/chapter/10.1007/978-3-319-89884-1_15), published in [27th European Symposium on Programming, ESOP 2018](https://link.springer.com/book/10.1007/978-3-319-89884-1)
* [Transferring Obligations Through Synchronizations](http://drops.dagstuhl.de/opus/volltexte/2019/10811/), published in [33rd European Conference on Object-Oriented Programming, ECOOP 2019)](https://2019.ecoop.org/home)
* [Starvation-Free Monitors](http://www.redcad.org/events/ictac2019/index.html), published in [16th International Colloquium on Theoretical Aspects of Computing, ICTAC 2019)](http://www.redcad.org/events/ictac2019/index.html)

This project has received funding from [the European Union’s Horizon 2020 research and innovation programme](https://ec.europa.eu/programmes/horizon2020/en) under grant agreement No 731453 ([VESSEDIA](https://vessedia.eu/)) as well as [Flemish Research Fund project](https://www.fwo.be/en/) under grant agreement No G.0962.17N.

# Contents 
* html : An HTML representation of the proof scripts
* VeriFast examples : a number of programs verified by VeriFast
* Util_Z.v : Some basic lemmas related to Integers
* Util_list.v : Some basic lemmas related to lists
* RelaxedPrecedenceRelation.v : A lemma proving that a valid graph is deadlock-free
* Programs.v : Definitions of a simple programming language, and its semantics
* Assertions.v : Definitions of heaps, assertions, and satisfaction relation along with some related lemmas
* WeakestPreconditions.v : The definition of the weakest precondition of a command along with some related lemmas
* ValidityOfConfigurations.v : The definition of the validity of configurations along with some lemmas proving that the small step preseves it
* ValidityOfGhostCommands.v : Lemmas proving that ghost commands preseve validity of configurations
* ProofRules.v : The proposed proof rules
* Soundness.v : The soundness proof of the proposed proof rules, i.e. any program that is verified by the proposed proof rules is deadlock-free
* Examples_Channels.v : The proof of a deadlock-free program, which sends and receives on a channel in two threads

# Contact

* [Jafar Hamin](https://hamin.be/), imec-Distrinet reseach group, KU Leuven, Belgium
* [Bart Jacobs](https://distrinet.cs.kuleuven.be/people/bartj), imec-Distrinet reseach group, KU Leuven, Belgium
